#!/usr/bin/env python3
# intx: extended precision integer library.
# Copyright 2026 Pawel Bylica.
# Licensed under the Apache License, Version 2.0.
"""Generates the machine code of IntxRV/Gen/Code.lean from IntxRV/Api.cpp.

  rv_gen.py OUT_DIR STACK_JSON OBJECT IMAGE

OBJECT is compiled for RV64 (see scripts/rv_build.sh). For every [[gnu::used]] pointer variable
`p` of it pointing to a function `f` without relocations, IntxRV/Gen/Code.lean gets
`Gen.p_code`: the words of the machine code of `f`, `Gen.p_prog`: their instructions, and
`Gen.p_decodes`: the proof that the decoder of the Sail model decodes the words to them. The
functions with relocations (calls, constant data) are linked with what they reach into IMAGE
(scripts/rv_image.ld, the linker LD, default ld.lld): `Gen.image_code`, `Gen.image_prog`,
`Gen.image_decodes`, the data `Gen.image_data` at `Gen.image_dataOff`, `Gen.p_entry` the index of
the first instruction of `f`, and `Gen.q_in_image` for the functions `q` without relocations in
the image. STACK_JSON gets the bytes of the stack that each function uses below sp, with those of
the functions it calls, for scripts/rv_api.py.
"""

import json
import os
import re
import struct
import subprocess
import sys
from pathlib import Path

SHT_SYMTAB = 2
SHT_RELA = 4
STT_FUNC = 2
STT_OBJECT = 1
EM_RISCV = 243


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
    if opcode == 0x23 and f3 == 3:
        imm = (w >> 25) << 5 | (w >> 7) & 0x1f
        return f".STORE ({lean_bv(imm, 12)}, {reg(rs2)}, {reg(rs1)}, 8)"
    if opcode == 0x67 and f3 == 0:
        return f".JALR ({lean_bv(w >> 20, 12)}, {reg(rs1)}, {reg(rd)})"
    sys.exit(f"unsupported instruction 0x{w:08x}")


def stack_size(var, code):
    """The bytes of the stack below sp that the function uses: the frame that the first
    instruction `addi sp, sp, -F` allocates, or 0."""
    w = code[0]
    if w & 0xfffff == 0x10113:  # addi sp, sp, imm
        imm = sext(w >> 20, 12)
        if imm >= 0 or -imm % 16:
            sys.exit(f"{var}: unexpected stack frame {imm}")
        return -imm
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

    # The image: the functions with relocations and what they reach, linked at 0.
    img, data_words, data_off, addr = [], [], 0, {}
    if in_image:
        # The roots: the sections of the pointers of the functions.
        keep = " ".join(f"KEEP(*({sections[ptrs[var]['shndx']]['name']}))" for var in in_image)
        script = Path(__file__).with_name("rv_image.ld").read_text().replace(
            "/* ROOTS */", f".data : {{ {keep} }}")
        image.with_suffix(".ld").write_text(script)
        subprocess.run([os.environ.get("LD", "ld.lld"), "--no-relax", "-T",
                        str(image.with_suffix(".ld")), "-e", "0", "--gc-sections", "-o",
                        str(image), str(obj)], check=True)
        idata = image.read_bytes()
        isecs, isyms, _ = read_elf(idata)
        text = next(s for s in isecs if s["name"] == ".text")
        rodata = next((s for s in isecs if s["name"] == ".rodata"), None)
        img = [struct.unpack_from("<I", idata, text["off"] + i)[0]
               for i in range(0, text["size"], 4)]
        ro = idata[rodata["off"]:rodata["off"] + rodata["size"]] if rodata else b""
        ro += b"\0" * (-len(ro) % 8)
        data_off = rodata["addr"] if rodata else 4 * len(img)
        if data_off % 8 or data_off < 4 * len(img):
            sys.exit("unexpected layout of the image")
        data_words = [struct.unpack_from("<Q", ro, i)[0] for i in range(0, len(ro), 8)]
        addr = {s["name"]: s for s in isyms if s["type"] == STT_FUNC}

    # The stack below sp of a function of the image: its frame and the most of its callees.
    def image_stack(name, seen=()):
        fn = addr[name]
        code = img[fn["value"] // 4:(fn["value"] + fn["size"]) // 4]
        by_addr = {s["value"]: s["name"] for s in addr.values()}
        callees = [by_addr[t] for t in call_targets(code, fn["value"])]
        if any(c in seen for c in callees):
            sys.exit(f"{name}: recursion")
        frame = stack_size(name, code)
        return frame + max([image_stack(c, seen + (name,)) for c in callees], default=0)

    words = sorted({w for code in funcs.values() for w in code} | set(img if in_image else []))
    lines = ["-- Generated by scripts/rv_gen.py from IntxRV/Api.cpp. Do not edit.",
             "import IntxRV.Decode", "", "open LeanRV64D.Defs", "",
             "-- The decoder of the Sail model is a chain of a few hundred cases.",
             "set_option maxRecDepth 100000", "set_option maxHeartbeats 4000000", "",
             "namespace IntxRV.Gen", "",
             "/-! ## The instructions decoded by the Sail model -/", ""]
    for w in words:
        lines += [f"theorem decode_{w:08x} :",
                  f"    DecodesTo {lean_bv(w, 32)} ({decode(w)}) := by", "  rv_decode", ""]
    for var, code in funcs.items():
        name = targets[var]["name"]
        lines += code_lines(var, f"`{name}`", code, f"`{var}`")
    info = {var: dict(stack=stack_size(var, code)) for var, code in funcs.items()}
    if in_image:
        data_text = ",\n  ".join(", ".join(lean_bv(w, 64) for w in data_words[i:i + 4])
                                 for i in range(0, len(data_words), 4))
        # The image in chunks: a proof by cases of a long list is slow to elaborate.
        chunks = [img[i:i + 64] for i in range(0, len(img), 64)]
        lines += ["/-! ## The image -/", ""]
        for c, chunk in enumerate(chunks):
            words_text = ",\n  ".join(", ".join(lean_bv(w, 32) for w in chunk[i:i + 4])
                                      for i in range(0, len(chunk), 4))
            prog_text = ",\n  ".join(decode(w) for w in chunk)
            proof = "".join(f"\n    (decodes_cons decode_{w:08x}" for w in chunk)
            lines += [f"def image_code_{c} : Code := [\n  {words_text}]", "",
                      f"def image_prog_{c} : List instruction := [\n  {prog_text}]", "",
                      f"theorem image_decodes_{c} : Decodes image_code_{c} image_prog_{c} :="
                      f"{proof} decodes_nil" + ")" * len(chunk), ""]
        names = range(len(chunks))
        cat = lambda f: " ++\n    ".join(f(c) for c in names)
        proof = "image_decodes_0"
        for c in names[1:]:
            proof = f"decodes_append ({proof})\n    image_decodes_{c}"
        lines += ["/-- The machine code of the image. -/",
                  "def image_code : Code :=\n  " + cat(lambda c: f"image_code_{c}"), "",
                  "/-- The instructions of the image. -/",
                  "def image_prog : List instruction :=\n  " + cat(lambda c: f"image_prog_{c}"),
                  "", "theorem image_decodes : Decodes image_code image_prog :=\n  " + proof, ""]
        lines += ["/-- The read-only data of the image, as 64-bit words. -/",
                  f"def image_data : List (BitVec 64) := [\n  {data_text}]", "",
                  "/-- The offset of the data in the image. -/",
                  f"def image_dataOff : Nat := {data_off}", ""]
        for var in in_image:
            fn = addr[targets[var]["name"]]
            lines += [f"/-- The instruction where `{var}` starts in the image. -/",
                      f"def {var}_entry : Nat := {fn['value'] // 4}", ""]
            info[var] = dict(stack=image_stack(fn["name"]), image=True)
        for var, code in funcs.items():
            fn = addr.get(targets[var]["name"])
            if fn is not None:
                lines += [f"/-- The instruction where the code of `{var}` is in the image. -/",
                          f"def {var}_offset : Nat := {fn['value'] // 4}", "",
                          f"theorem {var}_in_image :",
                          f"    (image_prog.drop {var}_offset).take {var}_prog.length = "
                          f"{var}_prog := by rfl", ""]
    lines += ["end IntxRV.Gen", ""]
    stack_json.write_text(json.dumps(dict(sorted(info.items())), indent=1) + "\n")
    (out / "IntxRV" / "Gen").mkdir(parents=True, exist_ok=True)
    (out / "IntxRV" / "Gen" / "Code.lean").write_text("\n".join(lines))


if __name__ == "__main__":
    main()
