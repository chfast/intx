#!/usr/bin/env python3
# intx: extended precision integer library.
# Copyright 2026 Pawel Bylica.
# Licensed under the Apache License, Version 2.0.
"""Runs `lake build` with the Lean processes in a budget of memory.

  lake_build.py [--budget GB] [--log FILE] TARGET...

Lake runs as many Lean processes as LEAN_NUM_THREADS, and the proofs of some modules take more
memory than the runner of CI has for 4 of them. Lake runs this script as `lean`, from a directory
of links to the Lean toolchain (LEAN_SYSROOT): the script starts the Lean process of a module when
the peaks of the running processes and of the module (PEAKS) fit in the budget, or when no other
process runs, in the order of the requests. It prints the modules whose peak exceeded their peak
in PEAKS, and --log gets the peak and the time of each module.
"""

import fcntl
import json
import os
import signal
import subprocess
import sys
import tempfile
import time
from pathlib import Path

# The peak memory (RssAnon, GB) of the Lean process of a module, from the --log of a build with 12
# threads, and of the modules without an entry by the prefix of the name.
PEAKS = {
    "IntxRV.Api.udivrem_knuth_normalized": 11.6,
    "IntxRV.Api.udivrem_knuth_320": 9.0,
    "IntxRV.Div512K4": 7.4,
    "IntxRV.SDiv": 6.7,
    "IntxRV.Div512K3": 6.2,
    "IntxRV.Exp": 6.2,
    "IntxRV.KnuthN": 5.8,
    "IntxRV.Api.mulmod_256": 5.7,
    "IntxRV.Api.udivrem_top1_3_320": 5.5,
    "IntxRV.Api.be_load_256": 5.1,
    "IntxRV.Api.mul_256": 4.8,
    "IntxRV.ExpLoop": 4.3,
    "IntxRV.Api.udivrem_by2": 3.9,
    "IntxRV.Api.udivrem_top1_3": 3.5,
    "IntxRV.Api.udivrem_knuth_normalized_4": 3.5,
    "IntxRV.Api.udivrem_top1_2": 3.5,
    "IntxRV.Api.udivrem_knuth_normalized_3": 3.4,
    "IntxRV.Div256By2": 3.3,
    "IntxRV.Api.udivrem_by1": 3.3,
    "IntxRV.Api.umul_256": 3.3,
    "IntxRV.AddMod": 3.1,
}
DEFAULT_PEAKS = [("IntxRV.Gen.", 1.5), ("", 3.0)]


def peak_of(module):
    if module in PEAKS:
        return PEAKS[module]
    return next(p for prefix, p in DEFAULT_PEAKS if module.startswith(prefix))


def rss_anon(pid):
    try:
        with open(f"/proc/{pid}/status") as f:
            for line in f:
                if line.startswith("RssAnon:"):
                    return int(line.split()[1]) * 1024
    except OSError:
        pass
    return 0


def alive(pid):
    try:
        os.kill(pid, 0)
        return True
    except ProcessLookupError:
        return False
    except PermissionError:
        return True


class State:
    """The running processes and the queue of the waiting ones, in a file under a lock."""

    def __init__(self, path):
        self.path = path

    def __enter__(self):
        self.f = open(self.path, "a+")
        fcntl.flock(self.f, fcntl.LOCK_EX)
        self.f.seek(0)
        text = self.f.read()
        s = json.loads(text) if text else {"running": {}, "queue": []}
        # A process killed without its release frees its memory.
        self.running = {p: m for p, m in s["running"].items() if alive(int(p))}
        self.queue = [p for p in s["queue"] if alive(int(p))]
        return self

    def __exit__(self, *exc):
        self.f.seek(0)
        self.f.truncate()
        json.dump({"running": self.running, "queue": self.queue}, self.f)
        self.f.flush()
        fcntl.flock(self.f, fcntl.LOCK_UN)
        self.f.close()


def run_lean(args):
    real = os.environ["LAKE_BUILD_LEAN"]
    source = next((a for a in args if a.endswith(".lean")), None)
    if source is None:
        os.execv(real, [real] + args)
    path = Path(source).resolve()
    try:
        module = ".".join(path.relative_to(Path.cwd()).with_suffix("").parts)
    except ValueError:
        module = str(path)
    budget = float(os.environ["LAKE_BUILD_BUDGET"])
    need = min(peak_of(module), budget)
    state = Path(os.environ["LAKE_BUILD_STATE"])
    me = str(os.getpid())
    lake = os.getppid()
    t0 = time.monotonic()
    while True:
        # A stopped build starts no more processes.
        if os.getppid() != lake:
            sys.exit(1)
        with State(state) as s:
            if me not in s.queue:
                s.queue.append(me)
            if s.queue[0] == me and (not s.running or sum(s.running.values()) + need <= budget):
                s.queue.pop(0)
                s.running[me] = need
                break
        time.sleep(0.2)
    t1 = time.monotonic()
    if os.getppid() != lake:
        sys.exit(1)
    child = subprocess.Popen([real] + args)
    for sig in (signal.SIGTERM, signal.SIGINT):
        signal.signal(sig, lambda n, _: child.send_signal(n))
    peak = 0
    while True:
        peak = max(peak, rss_anon(child.pid))
        try:
            rc = child.wait(timeout=1)
            break
        except subprocess.TimeoutExpired:
            pass
    with State(state) as s:
        s.running.pop(me, None)
    gb = peak / 2**30
    if log := os.environ.get("LAKE_BUILD_LOG"):
        with open(log, "a") as f:
            f.write(f"{module} {gb:.2f} GB {time.monotonic() - t1:.0f} s, waited {t1 - t0:.0f} s\n")
    if gb > need and need < budget:
        print(f"lake_build.py: {module} took {gb:.1f} GB, more than its {need:.1f} GB in PEAKS",
              file=sys.stderr)
    sys.exit(rc)


def main():
    args = sys.argv[1:]
    budget, log = 13.0, None
    while args and args[0] in ("--budget", "--log"):
        if args[0] == "--budget":
            budget = float(args[1])
        else:
            log = str(Path(args[1]).resolve())
        args = args[2:]
    prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
    with tempfile.TemporaryDirectory(prefix="lake_build.") as tmp:
        root = Path(tmp) / "toolchain"
        (root / "bin").mkdir(parents=True)
        for p in prefix.iterdir():
            if p.name != "bin":
                (root / p.name).symlink_to(p)
        for p in (prefix / "bin").iterdir():
            (root / "bin" / p.name).symlink_to(Path(__file__).resolve() if p.name == "lean" else p)
        env = dict(os.environ, LAKE_OVERRIDE_LEAN="true", LEAN_SYSROOT=str(root),
                   LAKE_BUILD_LEAN=str(prefix / "bin" / "lean"),
                   LAKE_BUILD_BUDGET=str(budget), LAKE_BUILD_STATE=str(Path(tmp) / "state.json"))
        if log:
            env["LAKE_BUILD_LOG"] = log
        sys.exit(subprocess.run(["lake", "build"] + args, env=env).returncode)


if __name__ == "__main__":
    if Path(sys.argv[0]).name == "lean":
        run_lean(sys.argv[1:])
    else:
        main()
