# Proofs of intx in Lean

Machine-checked proofs that functions of intx compute the specifications in their documentation
(the `@pre` and `@post` commands in `include/intx/intx.hpp`):

* [`IntxRV/`](IntxRV/README.md): the RV64 machine code that clang emits, in the Sail RISC-V model.
* [`Intx/`](Intx/): the models of the word functions in Lean (`Intx.Model`, the C++ code rendered
  in Lean) and their proofs (`Intx.Proofs`), which the proofs of the machine code use: `umul()`,
  `addc()`, `subc()`, `udivrem_2by1()` with the reciprocal, `shl()` and others.

## The specifications

The `@pre` and `@post` commands in the documentation of `include/intx/intx.hpp` are terms of Lean 4
([Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/) introduces the
notation). A parameter name stands for its value as a natural number (an integer for a signed type,
a list of bytes for a buffer of bytes, a list for a parameter pack), `result` for the result, `self`
for the object of a member function, `old(p)` for the value of a written buffer `p` at the entry,
`N` for the width of `uint<N>` and `sizeof(T)` for the size of a type; `p.size()` of a pointer `p`
is the number of the elements that it points to. `|||`, `&&&` and `^^^` are the bitwise operations,
`bigEndian b` is the number of the bytes `b` in big-endian order
([`IntxRV/Bytes.lean`](IntxRV/Bytes.lean)) and `signed N x` is `x` as a signed `N`-bit integer
([`IntxRV/Words.lean`](IntxRV/Words.lean)).

The RV64 machine code that clang 21 emits for the instances in [`IntxRV/Api.cpp`](IntxRV/Api.cpp) is
proved to satisfy these specifications (the table of
[`IntxRV/README.md`](IntxRV/README.md#the-proof-of-a-function) lists the proofs, and [its section on
the specifications](IntxRV/README.md#the-specifications) has the details). A specification of a
template is proved for these instances, mostly of `uint256`. It assumes that the buffers that a
function writes do not overlap its other arguments, and `@note FV:` marks what else it does not
cover. The documentation on `main` has the specifications proved here, so a function without `@post`
is not verified; the proofs follow this branch, not each change of `main`. What the proofs trust is
in [`IntxRV/README.md`](IntxRV/README.md#what-the-proofs-trust).

## Audit map

| file | review |
|---|---|
| `include/intx/intx.hpp` | The specifications: the `@pre` and `@post` commands. `scripts/rv_api.py` states them in `IntxRV/Gen/Api/` and `Intx/Gen/Spec.lean` (generated); [`Intx/Spec.lean`](Intx/Spec.lean) and [`IntxRV/Words.lean`](IntxRV/Words.lean) are their vocabulary. The proof file of each function quotes its specification. |
| [`Intx/Model/`](Intx/Model/) | The C++ code rendered in Lean. Compare it with `include/intx/intx.hpp`: each definition shows its C++ code. |
| [`Intx/ProofSupport/`](Intx/ProofSupport/), [`Intx/Proofs/`](Intx/Proofs/) | The proofs of the models, checked by Lean. |
| [`IntxRV/`](IntxRV/) | The proofs of the machine code, see [`IntxRV/README.md`](IntxRV/README.md): the proof of each function in [`IntxRV/Api/`](IntxRV/Api/), one file per function. |
| [`Checks/`](Checks/) | The checks that every specification has a proof with the allowed axioms only (`Checks/Gen/`, generated). |
| [`SOURCE.json`](SOURCE.json) | The hashes of the modeled C++ definitions. |

## What the models trust

* Lean and Mathlib.
* The model renders the C++ code faithfully. Lean cannot read C++, so this is checked by review and
  by the hashes of the modeled definitions (`scripts/check-source.py`), which make a later change of
  the C++ code fail the check until the model is updated. The proofs of the machine code do not
  depend on this: they use the models only as a step to the specifications.
* The modeling choices, documented in the model:
  * The C++ types are Lean types: `uint64_t` is `UInt64`, an array or a `uint<64 * n>` is a
    `Vector` of `n` words and a shift amount is a `Fin 64`. The array sizes, the indices, the
    `static_assert`s and the `INTX_REQUIRE`s on sizes are proved when the model is compiled.
  * The undefined behavior that depends on values, a false `INTX_REQUIRE` (an assumption of the
    compiler in release builds) or a `div` that faults, makes the model return `none`.
  * The word operations have the semantics of their portable code; the builtins and the x86-64
    asm compute the same.
  * The code paths that the build and the context select are the argument `P : Platform` of the
    model. With `P.div_wide_x86`, `udivrem_2by1()` and `reciprocal_2by1()` use the x86-64 `div`
    instruction (`INTX_HAS_DIV_WIDE_X86` outside constant evaluation). Without it they use the
    reciprocal of `internal::reciprocal()`, as constant evaluation and the other architectures do.
  * The uninitialized arrays are zeros: the C++ code writes every word of them before reading it.

## Build and check

```sh
lake exe cache get
CXX=clang++-21 scripts/rv_build.sh
lake build Intx IntxRV Checks
scripts/check-source.py
```

`scripts/rv_build.sh` generates the Lean files of the machine code and of the specifications (the
`Gen/` directories, not in git) with clang 21, lld and the riscv64 libstdc++ headers (see
[`IntxRV/README.md`](IntxRV/README.md#build)). Run it again after a change of `intx.hpp`. The
models and their proofs (`lake build Intx`) do not need it.

## Updates

After a change of the modeled C++ code, update the model and the proofs and record the new hashes
with `scripts/check-source.py --update`.
