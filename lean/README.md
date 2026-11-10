# Proofs of intx in Lean

Machine-checked proofs that functions of intx compute the specifications in their documentation
(the `@pre` and `@post` commands in `include/intx/intx.hpp`):

* [`IntxRV/`](IntxRV/README.md): the RV64 machine code that clang emits, in the Sail RISC-V model.
* [`Intx/`](Intx/): the models of the word functions in Lean (`Intx.Model`, the C++ code rendered
  in Lean) and their proofs (`Intx.Proofs`), which the proofs of the machine code use: `umul()`,
  `addc()`, `subc()`, `udivrem_2by1()` with the reciprocal, `shl()` and others.

## Audit map

| file | review |
|---|---|
| `include/intx/intx.hpp` | The specifications: the `@pre` and `@post` commands. `scripts/rv_api.py` states them in `IntxRV/Gen/Api.lean` and `Intx/Gen/Spec.lean` (generated); [`Intx/Spec.lean`](Intx/Spec.lean) and [`IntxRV/Words.lean`](IntxRV/Words.lean) are their vocabulary. |
| [`Intx/Model/`](Intx/Model/) | The C++ code rendered in Lean. Compare it with `include/intx/intx.hpp`: each definition shows its C++ code. |
| [`Intx/ProofSupport/`](Intx/ProofSupport/), [`Intx/Proofs/`](Intx/Proofs/) | The proofs of the models, checked by Lean. |
| [`IntxRV/`](IntxRV/) | The proofs of the machine code, see [`IntxRV/README.md`](IntxRV/README.md). |
| [`Checks/`](Checks/) | The checks that every specification has a proof with the allowed axioms only (generated). |
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
CXX=clang++ scripts/rv_build.sh
lake build Intx IntxRV Checks
scripts/check-source.py
```

## Updates

After a change of the modeled C++ code, update the model and the proofs and record the new hashes
with `scripts/check-source.py --update`.
