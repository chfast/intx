#!/usr/bin/env python3
"""Checks that the C++ code that Intx/Model renders has not changed since the model was checked.

SOURCE.json lists the modeled definitions of include/intx/intx.hpp: a regular expression of the
first line, which match of it, and the SHA-256 of the definition (from that line to the closing
brace, or the line alone for "line" entries). After a change of the C++ code, update the model and
the proofs, then record the new hashes with --update.
"""
import hashlib
import json
import pathlib
import re
import sys

LEAN = pathlib.Path(__file__).resolve().parent.parent
HEADER = LEAN.parent / "include" / "intx" / "intx.hpp"
SOURCE = LEAN / "SOURCE.json"


def close_brace(text, i):
    """The index of the brace closing the one at text[i], skipping literals and comments."""
    depth = 0
    n = len(text)
    while i < n:
        c = text[i]
        if c in "\"'":
            j = i + 1
            while text[j] != c:
                j += 2 if text[j] == "\\" else 1
            i = j
        elif text.startswith("//", i):
            i = text.index("\n", i)
        elif text.startswith("/*", i):
            i = text.index("*/", i) + 1
        elif c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0:
                return i
        i += 1
    raise ValueError("unbalanced braces")


def extract(text, entry):
    matches = list(re.finditer(entry["pattern"], text, re.M))
    if len(matches) <= entry.get("match", 0):
        raise ValueError(f"{entry['name']}: pattern not found")
    m = matches[entry.get("match", 0)]
    start = text.rfind("\n", 0, m.start()) + 1
    if entry.get("kind") == "line":
        return text[start:text.index("\n", m.end())]
    return text[start:close_brace(text, text.index("{", m.end())) + 1]


def main():
    update = "--update" in sys.argv[1:]
    text = HEADER.read_text()
    entries = json.loads(SOURCE.read_text())
    changed = []
    for entry in entries:
        digest = hashlib.sha256(extract(text, entry).encode()).hexdigest()
        if digest != entry.get("sha256"):
            changed.append(entry["name"])
            entry["sha256"] = digest
    if update:
        SOURCE.write_text(json.dumps(entries, indent=2) + "\n")
        print(f"{len(entries)} definitions recorded")
        return 0
    for name in changed:
        print(f"changed: {name}")
    print(f"{len(entries)} definitions, {len(changed)} changed")
    return 1 if changed else 0


if __name__ == "__main__":
    sys.exit(main())
