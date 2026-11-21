#!/usr/bin/env python3
# intx: extended precision integer library.
# Copyright 2026 Pawel Bylica.
# Licensed under the Apache License, Version 2.0.
"""Generates the machine code of IntxRV/Gen/Code.lean from IntxRV/Api.cpp.

  rv_gen.py OUT_DIR STACK_JSON OBJECT IMAGE

OBJECT is compiled for RV64 (see scripts/rv_build.sh). For every [[gnu::used]] pointer variable
`p` of it pointing to a function `f` without relocations, IntxRV/Gen/Code.lean gets
`Gen.p_code`: the words of the machine code of `f`, `Gen.p_prog`: their instructions, and
`Gen.p_decodes`: the proof that the decoder of the Sail model decodes the words to them. A
function with relocations (calls, constant data) is linked with what it reaches into its own image,
IMAGE with `-p` before the suffix (scripts/rv_image.ld, the linker LD, default ld.lld):
`Gen.p_image_code`, `Gen.p_image_prog`, `Gen.p_image_decodes`, the data `Gen.p_image_data` at
`Gen.p_image_dataOff`, `Gen.p_entry` the index of the first instruction of `f`, and
`Gen.p_image_q_in` for the functions in the image with the code of an instance `q` without
relocations. An instance `q` whose relocations are only the PC-relative addresses of its data
(`auipc` and `addi` or a load) gets `Gen.q_progAt`: its instructions with the immediates of the
addresses as parameters, which differ in each image, and `Gen.p_image_q_in` states it with the
immediates of the image `p` that holds its code. STACK_JSON gets the bytes of the stack that each function uses below sp, with those
of the functions it calls, for scripts/rv_api.py.
"""

import json
import os
import re
import struct
import subprocess
import sys
import zlib
from pathlib import Path

# The number of the files of the decode proofs (IntxRV/Gen/Decode/). Each proof adds ~120 MB to
# the Lean process of its file: about 10 words a file keep 3 processes in the 8 GB of CI.
DECODE_FILES = 192

SHT_SYMTAB = 2
SHT_RELA = 4
STT_FUNC = 2
STT_OBJECT = 1
EM_RISCV = 243
R_RISCV_PCREL_HI20 = 23
R_RISCV_PCREL_LO12_I = 24


def read_elf(data: bytes):
    if data[:4] != b"\x7fELF" or data[4] != 2 or data[5] != 1:
        sys.exit("not a little-endian ELF64 file")
    (e_machine,) = struct.unpack_from("<H", data, 18)
    if e_machine != EM_RISCV:
        sys.exit("not a RISC-V object")
    e_shoff, = struct.unpack_from("<Q", data, 40)
    e_shentsize, e_shnum, e_shstrndx = struct.unpack_from("<HHH", data, 58)
    sections = []
    for i in range(e_shnum):
        name, typ, flags, addr, off, size, link, info, align, entsize = struct.unpack_from(
            "<IIQQQQIIQQ", data, e_shoff + i * e_shentsize)
        sections.append(dict(name=name, type=typ, addr=addr, off=off, size=size, link=link,
                             info=info, entsize=entsize))
    shstr = sections[e_shstrndx]

    def cstr(sec, off):
        start = sec["off"] + off
        return data[start:data.index(b"\0", start)].decode()

    for s in sections:
        s["name"] = cstr(shstr, s["name"])
    symtab = next(s for s in sections if s["type"] == SHT_SYMTAB)
    strtab = sections[symtab["link"]]
    symbols = []
    for i in range(symtab["size"] // symtab["entsize"]):
        name, info, other, shndx, value, size = struct.unpack_from(
            "<IBBHQQ", data, symtab["off"] + i * symtab["entsize"])
        symbols.append(dict(name=cstr(strtab, name), type=info & 0xf, shndx=shndx, value=value,
                            size=size))
    relocs = {}  # The relocations by the index of the section they apply to.
    for s in sections:
        if s["type"] == SHT_RELA:
            entries = []
            for i in range(s["size"] // s["entsize"]):
                offset, info, addend = struct.unpack_from("<QQq", data, s["off"] + i * s["entsize"])
                entries.append(dict(offset=offset, sym=info >> 32, type=info & 0xffffffff,
                                    addend=addend))
            relocs.setdefault(s["info"], []).extend(entries)
    return sections, symbols, relocs


def function_code(data, sections, symbols, relocs, fn):
    shndx = fn["shndx"]
    sec = sections[shndx]
    if fn["value"] != 0 or fn["size"] != sec["size"]:
        sys.exit(f"{fn['name']}: the function must fill its section (use -ffunction-sections)")
    if relocs.get(shndx):
        sys.exit(f"{fn['name']}: the machine code has relocations (calls or non-PC-relative "
                 "addresses; build with -mno-relax)")
    code = data[sec["off"]:sec["off"] + sec["size"]]
    if len(code) % 4 != 0:
        sys.exit(f"{fn['name']}: the code size is not a multiple of 4 (compressed instructions?)")
    return [struct.unpack_from("<I", code, i)[0] for i in range(0, len(code), 4)]


def data_rel_code(data, sections, relocs, fn):
    """The code of a function whose relocations are only the PC-relative addresses of its data,
    `auipc` and an I-type instruction (`addi` or a load): the words, with 0 immediates at the
    relocations, and the pairs of the indices of the two instructions. None for other functions."""
    shndx = fn["shndx"]
    sec = sections[shndx]
    rs = relocs.get(shndx, [])
    if fn["value"] != 0 or fn["size"] != sec["size"] or not rs:
        return None
    his = [r["offset"] for r in rs if r["type"] == R_RISCV_PCREL_HI20]
    los = [r["offset"] for r in rs if r["type"] == R_RISCV_PCREL_LO12_I]
    if len(his) + len(los) != len(rs) or len(his) != len(los):
        return None
    code = data[sec["off"]:sec["off"] + sec["size"]]
    words = [struct.unpack_from("<I", code, i)[0] for i in range(0, len(code), 4)]
    # A LO12 relocation names the label of its auipc; clang emits each pair in order.
    pairs = list(zip(sorted(o // 4 for o in his), sorted(o // 4 for o in los)))
    if any(words[h] & 0x7f != 0x17 or words[h] >> 12 or words[lo] >> 20 for h, lo in pairs):
        sys.exit(f"{fn['name']}: unexpected PC-relative relocations")
    return words, pairs


def pointer_targets(sections, symbols, relocs, ptrs=None):
    """The [[gnu::used]] pointer variables: name -> the function symbol they point to (and their
    symbols to `ptrs`)."""
    targets = {}
    for sym in symbols:
        if sym["type"] != STT_OBJECT or sym["size"] != 8 or sym["shndx"] >= len(sections):
            continue
        for r in relocs.get(sym["shndx"], []):
            if r["offset"] == sym["value"] and r["addend"] == 0:
                target = symbols[r["sym"]]
                if target["type"] == STT_FUNC:
                    targets[demangle_var(sym["name"])] = target
                    if ptrs is not None:
                        ptrs[demangle_var(sym["name"])] = sym
    return targets


def demangle_var(name):
    """The unqualified C++ name of a variable with internal linkage: `_ZL4umul` -> `umul`,
    `_ZN4intx3apiL7add_256E` -> `add_256`."""
    m = re.fullmatch(r"_ZL(\d+)(\w+)", name)
    if m and len(m.group(2)) == int(m.group(1)):
        return m.group(2)
    m = re.fullmatch(r"_ZN(\w+)E", name)
    if m:
        s, parts = m.group(1), []
        while s:
            s = s.removeprefix("L")
            n = re.match(r"\d+", s)
            if not n:
                return name
            k = len(n.group(0))
            parts.append(s[k:k + int(n.group(0))])
            s = s[k + int(n.group(0)):]
        return parts[-1]
    return name


def sext(v, bits):
    return v - (1 << bits) if v & (1 << (bits - 1)) else v


def lean_bv(v, bits):
    """A BitVec literal in Lean of the `bits`-bit two's complement value v."""
    return f"0x{v & ((1 << bits) - 1):x}#{bits}"


R_OPS = {(0, 0): "ADD", (0, 0x20): "SUB", (1, 0): "SLL", (2, 0): "SLT", (3, 0): "SLTU",
         (4, 0): "XOR", (5, 0): "SRL", (5, 0x20): "SRA", (6, 0): "OR", (7, 0): "AND"}
MUL_OPS = {0: "⟨.Low, .Signed, .Signed⟩", 1: "⟨.High, .Signed, .Signed⟩",
           2: "⟨.High, .Signed, .Unsigned⟩", 3: "⟨.High, .Unsigned, .Unsigned⟩"}
I_OPS = {0: "ADDI", 2: "SLTI", 3: "SLTIU", 4: "XORI", 6: "ORI", 7: "ANDI"}
B_OPS = {0: "BEQ", 1: "BNE", 4: "BLT", 5: "BGE", 6: "BLTU", 7: "BGEU"}
RW_OPS = {(0, 0): "ADDW", (0, 0x20): "SUBW", (1, 0): "SLLW", (5, 0): "SRLW", (5, 0x20): "SRAW"}


def decode(w):
    """The instruction of the Sail model that the 32-bit word w decodes to (a Lean term), for the
    instructions IntxRV.exec supports. The Lean proofs check it with the decoder of the model."""
    opcode, rd, f3 = w & 0x7f, (w >> 7) & 0x1f, (w >> 12) & 7
    rs1, rs2, f7 = (w >> 15) & 0x1f, (w >> 20) & 0x1f, w >> 25
    reg = lambda r: f".Regidx {r}#5"
    if opcode == 0x33 and f7 == 1 and f3 in MUL_OPS:
        return f".MUL ({reg(rs2)}, {reg(rs1)}, {reg(rd)}, {MUL_OPS[f3]})"
    if opcode == 0x33 and (f3, f7) in R_OPS:
        return f".RTYPE ({reg(rs2)}, {reg(rs1)}, {reg(rd)}, .{R_OPS[(f3, f7)]})"
    if opcode == 0x3b and (f3, f7) in RW_OPS:
        return f".RTYPEW ({reg(rs2)}, {reg(rs1)}, {reg(rd)}, .{RW_OPS[(f3, f7)]})"
    if opcode in (0x37, 0x17):
        op = "LUI" if opcode == 0x37 else "AUIPC"
        return f".UTYPE ({lean_bv(w >> 12, 20)}, {reg(rd)}, .{op})"
    if opcode == 0x6f:
        imm = (((w >> 31) & 1) << 20 | ((w >> 12) & 0xff) << 12 | ((w >> 20) & 1) << 11 |
               ((w >> 21) & 0x3ff) << 1)
        return f".JAL ({lean_bv(imm, 21)}, {reg(rd)})"
    if opcode == 0x13 and f3 in I_OPS:
        return f".ITYPE ({lean_bv(w >> 20, 12)}, {reg(rs1)}, {reg(rd)}, .{I_OPS[f3]})"
    if opcode == 0x13 and f3 in (1, 5) and (w >> 26) in (0, 0x10):
        op = "SLLI" if f3 == 1 else ("SRAI" if w >> 26 else "SRLI")
        return f".SHIFTIOP ({lean_bv((w >> 20) & 0x3f, 6)}, {reg(rs1)}, {reg(rd)}, .{op})"
    if opcode == 0x63 and f3 in B_OPS:
        imm = (((w >> 31) & 1) << 12 | ((w >> 7) & 1) << 11 | ((w >> 25) & 0x3f) << 5 |
               ((w >> 8) & 0xf) << 1)
        return f".BTYPE ({lean_bv(imm, 13)}, {reg(rs2)}, {reg(rs1)}, .{B_OPS[f3]})"
    if opcode == 0x03 and f3 == 3:
        return f".LOAD ({lean_bv(w >> 20, 12)}, {reg(rs1)}, {reg(rd)}, false, 8)"
    if opcode == 0x03 and f3 == 6:
        return f".LOAD ({lean_bv(w >> 20, 12)}, {reg(rs1)}, {reg(rd)}, true, 4)"
    if opcode == 0x03 and f3 == 4:
        return f".LOAD ({lean_bv(w >> 20, 12)}, {reg(rs1)}, {reg(rd)}, true, 1)"
    if opcode == 0x23 and f3 == 3:
        imm = (w >> 25) << 5 | (w >> 7) & 0x1f
        return f".STORE ({lean_bv(imm, 12)}, {reg(rs2)}, {reg(rs1)}, 8)"
    if opcode == 0x67 and f3 == 0:
        return f".JALR ({lean_bv(w >> 20, 12)}, {reg(rs1)}, {reg(rd)})"
    sys.exit(f"unsupported instruction 0x{w:08x}")


def write_if_changed(path, text):
    """Writes the file only if its text changes, so that lake does not rebuild it."""
    if not path.exists() or path.read_text() != text:
        path.write_text(text)


def stack_size(var, code):
    """The bytes of the stack below sp that the function uses: the frame that `addi sp, sp, -F`
    allocates, or 0. The allocation may be after the first branch (shrink wrapping)."""
    frames = {-sext(w >> 20, 12) for w in code
              if w & 0xfffff == 0x10113 and sext(w >> 20, 12) < 0}  # addi sp, sp, imm < 0
    if len(frames) > 1 or any(f % 16 for f in frames):
        sys.exit(f"{var}: unexpected stack frames {sorted(frames)}")
    if frames:
        return frames.pop()
    if any(w & 0xf8000 == 0x10000 and w & 0x7f in (0x03, 0x23) for w in code):  # base sp
        sys.exit(f"{var}: uses the stack without a frame")
    return 0


def code_lines(name, desc, code, var):
    """The Lean definitions of the machine code `code` named `name`."""
    words_text = ",\n  ".join(", ".join(lean_bv(w, 32) for w in code[i:i + 4])
                              for i in range(0, len(code), 4))
    prog_text = ",\n  ".join(decode(w) for w in code)
    cases = "\n".join(f"  | {k}, _, _ => decode_{w:08x}" for k, w in enumerate(code))
    return [f"/-! ## {desc} -/", "",
            f"/-- The machine code of {desc}. -/",
            f"def {name}_code : Code := [\n  {words_text}]", "",
            f"/-- The instructions of {var}. -/",
            f"def {name}_prog : List instruction := [\n  {prog_text}]", "",
            f"theorem {name}_decodes : Decodes {name}_code {name}_prog :=",
            f"  decodes_of (by rfl) fun",
            cases, f"  | _ + {len(code)}, hk, _ => absurd hk (by simp [{name}_code])", "", ""]


def prog_at_lines(var, code, pairs):
    """The Lean definition of the instructions of `var`, whose code has the PC-relative address of
    its data at the instruction pairs `pairs`, with the immediates of the pairs as parameters."""
    names = ([("hi", "lo")] if len(pairs) == 1 else
             [(f"hi{k}", f"lo{k}") for k in range(len(pairs))])
    texts = [decode(w) for w in code]
    for (h, lo), (hn, ln) in zip(pairs, names):
        texts[h] = texts[h].replace(lean_bv(0, 20), hn, 1)
        texts[lo] = texts[lo].replace(lean_bv(0, 12), ln, 1)
    params = " ".join(f"({hn} : BitVec 20) ({ln} : BitVec 12)" for hn, ln in names)
    prog_text = ",\n  ".join(texts)
    return [f"/-! ## `{var}` in an image -/", "",
            f"/-- The instructions of `{var}`, with the immediates of the `auipc` and of the "
            f"instruction after it that address its data, which differ in each image. -/",
            f"def {var}_progAt {params} : List instruction := [\n  {prog_text}]", ""]


def call_targets(code, base):
    """The functions that the code at the address `base` calls: `auipc ra` and `jalr ra, ra`."""
    targets = []
    for k in range(len(code) - 1):
        a, b = code[k], code[k + 1]
        if a & 0xfff == 0x097 and b & 0xfffff == 0x080e7:  # auipc ra, hi; jalr ra, lo(ra)
            targets.append(base + 4 * k + sext(a & 0xfffff000, 32) + sext(b >> 20, 12))
    return targets


def main():
    out, stack_json, obj, image = map(Path, sys.argv[1:])
    data = obj.read_bytes()
    sections, symbols, relocs = read_elf(data)
    ptrs = {}
    targets = pointer_targets(sections, symbols, relocs, ptrs)
    if not targets:
        sys.exit(f"{obj}: no [[gnu::used]] function pointers found")
    # The functions without relocations are proved on their own code, the others in the image.
    funcs = {var: function_code(data, sections, symbols, relocs, fn)
             for var, fn in targets.items() if not relocs.get(fn["shndx"])}
    funcs = dict(sorted(funcs.items()))
    in_image = sorted(var for var in targets if var not in funcs)
    # The functions whose relocations are only the addresses of their data: their instructions
    # with the immediates of the addresses as parameters, for their proofs in any image.
    rel_funcs = {var: rc for var in in_image
                 if (rc := data_rel_code(data, sections, relocs, targets[var])) is not None}

    # The images: each function with relocations linked at 0 with what it reaches, so that its
    # code and data do not move when other functions are added.
    images = {}
    for var in in_image:
        keep = f"KEEP(*({sections[ptrs[var]['shndx']]['name']}))"
        script = Path(__file__).with_name("rv_image.ld").read_text().replace(
            "/* ROOTS */", f".data : {{ {keep} }}")
        elf = image.with_name(f"{image.stem}-{var}{image.suffix}")
        elf.with_suffix(".ld").write_text(script)
        subprocess.run([os.environ.get("LD", "ld.lld"), "--no-relax", "-T",
                        str(elf.with_suffix(".ld")), "-e", "0", "--gc-sections", "-o",
                        str(elf), str(obj)], check=True)
        idata = elf.read_bytes()
        isecs, isyms, _ = read_elf(idata)
        text = next(s for s in isecs if s["name"] == ".text")
        rodata = next((s for s in isecs if s["name"] == ".rodata"), None)
        img = [struct.unpack_from("<I", idata, text["off"] + i)[0]
               for i in range(0, text["size"], 4)]
        ro = idata[rodata["off"]:rodata["off"] + rodata["size"]] if rodata else b""
        ro += b"\0" * (-len(ro) % 8)
        data_off = rodata["addr"] if rodata else 4 * len(img)
        if data_off % 8 or data_off < 4 * len(img):
            sys.exit(f"{var}: unexpected layout of the image")
        data_words = [struct.unpack_from("<Q", ro, i)[0] for i in range(0, len(ro), 8)]
        addr = {s["name"]: s for s in isyms if s["type"] == STT_FUNC}
        images[var] = dict(img=img, data_words=data_words, data_off=data_off, addr=addr)

    # The stack below sp of a function of an image: its frame and the most of its callees.
    def image_stack(im, name, seen=()):
        img, addr = im["img"], im["addr"]
        fn = addr[name]
        code = img[fn["value"] // 4:(fn["value"] + fn["size"]) // 4]
        by_addr = {s["value"]: s["name"] for s in addr.values()}
        callees = [by_addr[t] for t in call_targets(code, fn["value"])]
        if any(c in seen for c in callees):
            sys.exit(f"{name}: recursion")
        frame = stack_size(name, code)
        return frame + max([image_stack(im, c, seen + (name,)) for c in callees], default=0)

    words = sorted({w for code in funcs.values() for w in code} |
                   {w for im in images.values() for w in im["img"]})
    # The proofs that the decoder decodes the words, in DECODE_FILES files: each file is a
    # separate Lean process with its own memory, and the files build in parallel. A word is in
    # the file of its hash, so that new code rebuilds only the files with its new words.
    gen = out / "IntxRV" / "Gen"
    (gen / "Decode").mkdir(parents=True, exist_ok=True)
    parts = [[] for _ in range(DECODE_FILES)]
    for w in words:
        parts[zlib.crc32(w.to_bytes(4, "little")) % DECODE_FILES].append(w)
    for k, part in enumerate(parts):
        dl = ["-- Generated by scripts/rv_gen.py from IntxRV/Api.cpp. Do not edit.",
              "import IntxRV.Decode", "", "open LeanRV64D.Defs", "",
              "-- The decoder of the Sail model is a chain of a few hundred cases.",
              "set_option maxRecDepth 100000", "set_option maxHeartbeats 4000000", "",
              "namespace IntxRV.Gen", ""]
        for w in part:
            dl += [f"theorem decode_{w:08x} :",
                   f"    DecodesTo {lean_bv(w, 32)} ({decode(w)}) := by", "  rv_decode", ""]
        dl += ["end IntxRV.Gen", ""]
        write_if_changed(gen / "Decode" / f"D{k:03}.lean", "\n".join(dl))
    # The files of an earlier layout: lake would build every module of IntxRV/.
    for f in (gen / "Decode").glob("D*.lean"):
        if f.stem not in {f"D{k:03}" for k in range(DECODE_FILES)}:
            f.unlink()
    lines = ["-- Generated by scripts/rv_gen.py from IntxRV/Api.cpp. Do not edit.",
             "import IntxRV.Decode"] + [f"import IntxRV.Gen.Decode.D{k:03}"
                                        for k in range(DECODE_FILES)] + [
             "", "open LeanRV64D.Defs", "", "namespace IntxRV.Gen", ""]
    for var, code in funcs.items():
        name = targets[var]["name"]
        lines += code_lines(var, f"`{name}`", code, f"`{var}`")
    for var, (code, pairs) in rel_funcs.items():
        lines += prog_at_lines(var, code, pairs)
    info = {var: dict(stack=stack_size(var, code)) for var, code in funcs.items()}
    for var, im in images.items():
        img, data_words, addr = im["img"], im["data_words"], im["addr"]
        n = f"{var}_image"
        data_text = ",\n  ".join(", ".join(lean_bv(w, 64) for w in data_words[i:i + 4])
                                 for i in range(0, len(data_words), 4))
        # The image in chunks: a proof by cases of a long list is slow to elaborate.
        chunks = [img[i:i + 64] for i in range(0, len(img), 64)]
        lines += [f"/-! ## The image of `{var}` -/", ""]
        for c, chunk in enumerate(chunks):
            words_text = ",\n  ".join(", ".join(lean_bv(w, 32) for w in chunk[i:i + 4])
                                      for i in range(0, len(chunk), 4))
            prog_text = ",\n  ".join(decode(w) for w in chunk)
            proof = "".join(f"\n    (decodes_cons decode_{w:08x}" for w in chunk)
            lines += [f"def {n}_code_{c} : Code := [\n  {words_text}]", "",
                      f"def {n}_prog_{c} : List instruction := [\n  {prog_text}]", "",
                      f"theorem {n}_decodes_{c} : Decodes {n}_code_{c} {n}_prog_{c} :="
                      f"{proof} decodes_nil" + ")" * len(chunk), ""]
        names = range(len(chunks))
        cat = lambda f: " ++\n    ".join(f(c) for c in names)
        proof = f"{n}_decodes_0"
        for c in names[1:]:
            proof = f"decodes_append ({proof})\n    {n}_decodes_{c}"
        lines += [f"/-- The machine code of the image of `{var}`. -/",
                  f"def {n}_code : Code :=\n  " + cat(lambda c: f"{n}_code_{c}"), "",
                  f"/-- The instructions of the image of `{var}`. -/",
                  f"def {n}_prog : List instruction :=\n  " + cat(lambda c: f"{n}_prog_{c}"),
                  "", f"theorem {n}_decodes : Decodes {n}_code {n}_prog :=\n  " + proof, ""]
        lines += [f"/-- The read-only data of the image of `{var}`, as 64-bit words. -/",
                  f"def {n}_data : List (BitVec 64) := [\n  {data_text}]", "",
                  f"/-- The offset of the data in the image of `{var}`. -/",
                  f"def {n}_dataOff : Nat := {im['data_off']}", ""]
        fn = addr[targets[var]["name"]]
        lines += [f"/-- The instruction where `{var}` starts in its image. -/",
                  f"def {var}_entry : Nat := {fn['value'] // 4}", ""]
        info[var] = dict(stack=image_stack(im, fn["name"]), image=True)
        # The functions of the image with the code of an instance q: the same function, or a
        # function that the instance inlines (the operators by uint64_t of the shifts by uint256).
        for q, code in funcs.items():
            fq = next((f for f in sorted(addr.values(), key=lambda f: f["value"])
                       if img[f["value"] // 4:(f["value"] + f["size"]) // 4] == code), None)
            if fq is not None:
                lines += [f"/-- The instruction where the code of `{q}` is in the image of "
                          f"`{var}`. -/",
                          f"def {n}_{q}_offset : Nat := {fq['value'] // 4}", "",
                          f"theorem {n}_{q}_in :",
                          f"    ({n}_prog.drop {n}_{q}_offset).take {q}_prog.length = "
                          f"{q}_prog := by rfl", ""]
        # The functions of the image with the code of an instance q with the addresses of its
        # data: the same words but the immediates of the addresses.
        for q, (code, pairs) in rel_funcs.items():
            rel = {k for p in pairs for k in p}

            def same(f):
                o = f["value"] // 4
                return f["size"] == 4 * len(code) and all(
                    img[o + k] == w if k not in rel else
                    img[o + k] & (0xfff if any(k == h for h, _ in pairs) else 0xfffff) ==
                    w & (0xfff if any(k == h for h, _ in pairs) else 0xfffff)
                    for k, w in enumerate(code))
            fq = next((f for f in sorted(addr.values(), key=lambda f: f["value"]) if same(f)),
                      None)
            if fq is not None:
                o = fq["value"] // 4
                at = f"{q}_progAt " + " ".join(
                    f"{lean_bv(img[o + h] >> 12, 20)} {lean_bv(img[o + lo] >> 20, 12)}"
                    for h, lo in pairs)
                # The comparison of the instructions recurses over the list.
                lines += [f"/-- The instruction where the code of `{q}` is in the image of "
                          f"`{var}`. -/",
                          f"def {n}_{q}_offset : Nat := {o}", "",
                          "set_option maxRecDepth 100000 in",
                          f"theorem {n}_{q}_in :",
                          f"    ({n}_prog.drop {n}_{q}_offset).take ({at}).length = "
                          f"{at} := by rfl", ""]
    lines += ["end IntxRV.Gen", ""]
    stack_json.write_text(json.dumps(dict(sorted(info.items())), indent=1) + "\n")
    write_if_changed(gen / "Code.lean", "\n".join(lines))


if __name__ == "__main__":
    main()
