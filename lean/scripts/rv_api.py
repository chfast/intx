#!/usr/bin/env python3
# intx: extended precision integer library.
# Copyright 2026 Pawel Bylica.
# Licensed under the Apache License, Version 2.0.
"""Generates the specifications of the instances of IntxRV/Api.cpp from the documentation of
include/intx/intx.hpp.

  rv_api.py AST_JSON OUT_DIR

AST_JSON is the AST of IntxRV/Api.cpp that clang dumps for the declarations of the namespace intx
(see scripts/rv_build.sh). Every [[gnu::used]] pointer variable `p` of the namespace intx::api must
be initialized by a lambda whose body is a single call of a function of intx with a documentation
comment; the @pre and @post commands of the comment are its specification, a Lean term in which a
parameter name stands for the value of the parameter as a natural number, `result` for the value
of the result (a natural number, or a proposition for `bool`) and `N` for the width of the
template. IntxRV/Gen/Api.lean gets `Api.p.spec`: the specification of the machine code of `p`
(`Gen.p_code`) for the RISC-V calling convention. Checks/IntxRVApi.lean checks that every
specification has the proof `Api.p.proof`, with the allowed axioms only.
"""

import json
import re
import sys
from pathlib import Path


def read_ast(path):
    """The top-level declarations that clang dumped (one JSON value each)."""
    text = path.read_text()
    dec = json.JSONDecoder()
    decls, i = [], 0
    while True:
        while i < len(text) and text[i].isspace():
            i += 1
        if i == len(text):
            return decls
        d, i = dec.raw_decode(text, i)
        decls.append(d)


def walk(node, parents=()):
    yield node, parents
    for c in node.get("inner", []):
        yield from walk(c, parents + (node,))


def comment_text(node):
    """The text of a comment node. Clang splits the text of a line at `<` (for HTML tags), so the
    pieces are joined as they are."""
    text = "".join(n.get("text", "") for n, _ in walk(node) if n.get("kind") == "TextComment")
    return " ".join(text.split())


def documented_functions(decls):
    """The specifications of the documented functions by (name, offset of the declaration)."""
    specs = {}
    for d in decls:
        for n, _ in walk(d):
            if n.get("kind") not in ("FunctionDecl", "CXXMethodDecl"):
                continue
            comment = next((c for c in n.get("inner", []) if c.get("kind") == "FullComment"), None)
            if comment is None:
                continue
            pre = [comment_text(c) for c in comment["inner"]
                   if c.get("kind") == "BlockCommandComment" and c.get("name") == "pre"]
            post = [comment_text(c) for c in comment["inner"]
                    if c.get("kind") == "BlockCommandComment" and c.get("name") == "post"]
            if not post:
                continue
            brief = " ".join(comment_text(c) for c in comment["inner"]
                             if c.get("kind") == "ParagraphComment").strip()
            params = [p["name"] for p in n.get("inner", []) if p.get("kind") == "ParmVarDecl"]
            specs[(n["name"], n["loc"]["offset"])] = dict(
                name=n["name"], line=n["loc"].get("line"), brief=brief, pre=pre, post=post,
                params=params, type=n["type"]["qualType"])
    return specs


def instances(decls, namespace):
    """The lambda variables of intx::<namespace>: name -> the declaration of the function they
    call."""
    by_id = {n["id"]: n for d in decls for n, _ in walk(d) if "id" in n}
    result = {}
    for d in decls:
        for n, parents in walk(d):
            if n.get("kind") != "VarDecl" or not any(
                    p.get("kind") == "NamespaceDecl" and p.get("name") == namespace
                    for p in parents):
                continue
            lambdas = [m for m, _ in walk(n) if m.get("kind") == "LambdaExpr"]
            if len(lambdas) != 1:
                sys.exit(f"{n['name']}: must be initialized by a lambda")
            body = [c for c in lambdas[0]["inner"] if c.get("kind") == "CompoundStmt"]
            calls = [m for m, _ in walk(body[-1])
                     if m.get("kind") in ("CallExpr", "CXXOperatorCallExpr")]
            if len(calls) != 1:
                sys.exit(f"{n['name']}: the lambda must call one function")
            callee = next(m["referencedDecl"] for m, _ in walk(calls[0])
                          if m.get("kind") == "DeclRefExpr"
                          and m["referencedDecl"].get("kind") == "FunctionDecl")
            decl = by_id[callee["id"]]
            result[n["name"]] = dict(name=callee["name"], offset=decl["loc"]["offset"],
                                     type=callee["type"]["qualType"])
    return result


def norm_type(t):
    t = re.sub(r"\bintx::", "", t.strip())
    return {"uint<128>": "uint128", "unsigned long": "uint64_t", "_Bool": "bool"}.get(t, t)


def uint_width(t):
    m = re.fullmatch(r"(?:const )?uint<(\d+)>(?: &)?", norm_type(t).replace("uint256", "uint<256>"))
    return int(m.group(1)) if m else None


def signature(var, inst, spec):
    """The result type and the parameter types of the instance `var`."""
    m = re.fullmatch(r"(.+?) \((.*)\)(?: noexcept)?", inst["type"])
    ret = norm_type(m.group(1))
    args = [norm_type(a) for a in m.group(2).split(",") if a.strip()]
    if len(args) != len(spec["params"]):
        sys.exit(f"{var}: the parameters do not match the declaration")
    return ret, args


def apply(term, width, result, values):
    """The term with N, result and the parameters bound to their values: `result` is
    (type, value) or None, `values` are (name, type, value)."""
    binders = "(N : Nat)" + (f" (result : {result[0]})" if result else "")
    binders += "".join(f" ({n} : {t})" for n, t, _ in values)
    args = [str(width)] + ([result[1]] if result else []) + [f"({v})" for _, _, v in values]
    return f"(fun {binders} =>\n      {term})\n      " + " ".join(args)


def header(var, spec):
    doc = spec["brief"] + "\n\n" if spec["brief"] else ""
    doc += "\n".join(f"@pre {p}" for p in spec["pre"])
    doc += ("\n" if spec["pre"] else "") + "\n".join(f"@post {p}" for p in spec["post"])
    return [f"/-! ## `{var}`: `{spec['name']}` (intx.hpp:{spec['line']})", "", doc, "-/", "",
            f"namespace {var}", ""]


# The results in registers (the RISC-V calling convention): the Lean type, the value and the
# facts about the registers that the type implies.
REG_RESULTS = {
    "bool": ("Bool", "(decide (x'.get 10#5 = 1))", ["(x'.get 10#5 = 0 ∨ x'.get 10#5 = 1)"]),
    "uint64_t": ("Nat", "(x'.get 10#5).toNat", []),
    "uint128": ("Nat", "((x'.get 10#5).toNat + 2 ^ 64 * (x'.get 11#5).toNat)", []),
    "result_with_carry<uint64_t>": (
        "ResultWithCarry", "⟨(x'.get 10#5).toNat, decide (x'.get 11#5 = 1)⟩",
        ["(x'.get 11#5 = 0 ∨ x'.get 11#5 = 1)"]),
    "div_result<uint64_t>": ("DivResult", "⟨(x'.get 10#5).toNat, (x'.get 11#5).toNat⟩", []),
}


def spec_rv(var, inst, spec):
    """The Lean definitions of the specification of the machine code of the instance `var`."""
    ret, args = signature(var, inst, spec)
    reg = 10  # The arguments are in a0 (x10), a1 (x11), ...
    bufs, pre, values = [], [], []
    ret_width = uint_width(ret)
    if ret_width is not None and ret_width > 128:
        if ret_width % 64:
            sys.exit(f"{var}: unsupported result type {ret}")
        result_reg, reg = reg, reg + 1  # The result is returned in memory at a0 (sret).
    elif ret not in REG_RESULTS:
        sys.exit(f"{var}: unsupported result type {ret}")
    widths = []
    for name, t in zip(spec["params"], args):
        w = uint_width(t)
        if t == "uint64_t":
            values.append((name, "Nat", f"(x {reg}#5).toNat"))
            reg += 1
        elif t == "bool":
            pre.append(f"(x {reg}#5 = 0 ∨ x {reg}#5 = 1)")
            values.append((name, "Bool", f"decide (x {reg}#5 = 1)"))
            reg += 1
        elif t == "uint128":
            values.append((name, "Nat", f"(x {reg}#5).toNat + 2 ^ 64 * (x {reg + 1}#5).toNat"))
            reg += 2
        elif w is not None and t.endswith("&") and w % 64 == 0:
            bufs.append(f"bufWords (x {reg}#5) {w // 64}")
            pre.append(f"Buf (x {reg}#5) {w // 8}")
            values.append((name, "Nat", f"words m (x {reg}#5) {w // 64}"))
            widths.append((reg, w))
            reg += 1
        else:
            sys.exit(f"{var}: unsupported parameter type {t}")
    if ret_width is not None and ret_width > 128:
        bufs.append(f"bufWords (x {result_reg}#5) {ret_width // 64}")
        pre.insert(0, f"Buf (x {result_reg}#5) {ret_width // 8}")
        for r, w in widths:
            pre.append(f"Disjoint (x {result_reg}#5) {ret_width // 8} (x {r}#5) {w // 8}")
        result = ("Nat", f"(words m' (x {result_reg}#5) {ret_width // 64})")
        frame = [f"UnchangedExcept m m' (x {result_reg}#5) {ret_width // 8}"]
    else:
        t, v, frame = REG_RESULTS[ret]
        result = (t, v)
        frame = frame + (["m' = m"] if bufs else [])
    width = ret_width or uint_width(args[0]) or 64
    pre += [apply(p, width, None, values) for p in spec["pre"]]
    post = [apply(p, width, result, values) for p in spec["post"]] + frame + [
        "∀ i ∈ calleeSaved, x' i = x i"]
    lines = header(var, spec)
    if bufs:
        m_used = "m" if spec["pre"] else "_m"
        lines += ["/-- The addresses of the words of the arguments and the result. -/",
                  "def bufs (x : Regs) : List (BitVec 64) :=\n  " + " ++\n    ".join(bufs), "",
                  f"def pre (x : Regs) ({m_used} : Mem) : Prop :=\n  " + " ∧\n    ".join(pre),
                  "", "def post (x : Regs) (m : Mem) (x' : Regs) (m' : Mem) : Prop :=\n  " +
                  " ∧\n    ".join(post), "",
                  f"/-- The specification of the machine code of `{var}`. -/",
                  f"def spec : Prop := RunsM {var}_code bufs pre post"]
    else:
        lines += ["def pre (x : Regs) : Prop :=\n  " + (" ∧\n    ".join(pre) or "True"), "",
                  "def post (x x' : Regs) : Prop :=\n  " + " ∧\n    ".join(post), "",
                  f"/-- The specification of the machine code of `{var}`. -/",
                  f"def spec : Prop := Runs {var}_code pre post"]
    return lines + ["", f"end {var}", "", ""], bool(bufs), bool(pre)


def spec_model(var, inst, spec):
    """The Lean definitions of the specification of the model `Intx.Model.var` of the instance."""
    ret, args = signature(var, inst, spec)
    ret_width = uint_width(ret)
    if ret_width is None or ret_width % 64:
        sys.exit(f"{var}: unsupported result type {ret}")
    if spec["pre"]:
        sys.exit(f"{var}: @pre of a model is not supported")
    vectors, values = [], []
    for name, t in zip(spec["params"], args):
        w = uint_width(t)
        if w is None or w % 64:
            sys.exit(f"{var}: unsupported parameter type {t}")
        vectors.append(f"({name} : Vector Word {w // 64})")
        values.append((name, "Nat", f"val {name}.toList"))
    names = " ".join(n for n, _, _ in values)
    post = " ∧\n      ".join(apply(p, ret_width, ("Nat", "(val res.toList)"), values)
                              for p in spec["post"])
    lines = header(var, spec) + [
        f"/-- The specification of the model of `{var}`, for every code path (`Platform`). -/",
        f"def spec : Prop :=\n  ∀ (P : Model.Platform) {' '.join(vectors)},\n    "
        f"∃ res, Model.{var} P {names} = some res ∧\n      {post}",
        "", f"end {var}", "", ""]
    return lines


def main():
    ast, out = map(Path, sys.argv[1:])
    decls = read_ast(ast)
    specs = documented_functions(decls)

    def spec_of(var, inst):
        spec = specs.get((inst["name"], inst["offset"]))
        if spec is None:
            sys.exit(f"{var}: {inst['name']} has no @post in its documentation")
        return spec

    api = instances(decls, "api")
    if not api:
        sys.exit("no instances in the namespace intx::api")
    lines = ["-- Generated by scripts/rv_api.py from IntxRV/Api.cpp and the documentation of",
             "-- include/intx/intx.hpp. Do not edit.", "import IntxRV.Gen.Code",
             "import IntxRV.Words", "",
             "-- A specification need not use all of N, result and the parameters.",
             "set_option linter.unusedVariables false", "",
             "namespace IntxRV.Api", "open IntxRV.Gen", ""]
    checks = ["-- Generated by scripts/rv_api.py from IntxRV/Api.cpp. Do not edit.",
              "import Checks.IntxRV", "import IntxRV.Api", "import IntxRV.EnvM",
              "set_option warningAsError true", "",
              "/-! The specification of every instance of IntxRV/Api.cpp has a proof, and its",
              "assumptions hold in an environment (they are not vacuous). -/", ""]
    for var in sorted(api):
        spec_lines, mem, has_pre = spec_rv(var, api[var], spec_of(var, api[var]))
        lines += spec_lines
        a = f"IntxRV.Api.{var}"
        checks += [f"example : {a}.spec := {a}.proof", f"#check_rv_axioms {a}.proof"]
        if mem:
            checks += ["example :", f"    IntxRV.NonVacuous IntxRV.Gen.{var}_code {a}.bufs "
                       f"{a}.pre := by",
                       f"  rv_nonvacuous using [{a}.bufs, {a}.pre, IntxRV.Gen.{var}_code]", ""]
        elif has_pre:
            checks += [f"example : ∃ x, {a}.pre x := {a}.nonvacuous", ""]
        else:
            checks += [""]
    lines += ["end IntxRV.Api", ""]
    (out / "IntxRV" / "Gen" / "Api.lean").write_text("\n".join(lines))
    (out / "Checks" / "IntxRVApi.lean").write_text("\n".join(checks))

    model = instances(decls, "model")
    lines = ["-- Generated by scripts/rv_api.py from IntxRV/Api.cpp and the documentation of",
             "-- include/intx/intx.hpp. Do not edit.", "import Intx.Spec",
             "import Intx.Model.Div", "",
             "-- A specification need not use all of N, result and the parameters.",
             "set_option linter.unusedVariables false", "", "namespace Intx.Spec", ""]
    checks = ["-- Generated by scripts/rv_api.py from IntxRV/Api.cpp. Do not edit.",
              "import Intx", "set_option warningAsError true", "",
              "/-! The specification of every model instance of IntxRV/Api.cpp has a proof that",
              "uses only the axioms of Lean and Mathlib: no `sorry` (`sorryAx`), no `native_decide`",
              "(`Lean.ofReduceBool`) and no axioms of this project. -/", ""]
    for var in sorted(model):
        lines += spec_model(var, model[var], spec_of(var, model[var]))
        a = f"Intx.Spec.{var}"
        checks += [f"example : {a}.spec := {a}.proof", "",
                   f"/-- info: '{a}.proof' depends on axioms: [propext, Classical.choice, "
                   "Quot.sound] -/", "#guard_msgs in", f"#print axioms {a}.proof", ""]
    lines += ["end Intx.Spec", ""]
    (out / "Intx" / "Gen" / "Spec.lean").write_text("\n".join(lines))
    (out / "Checks" / "IntxSpec.lean").write_text("\n".join(checks))


if __name__ == "__main__":
    main()
