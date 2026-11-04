# The proof of `mulmod()`

A machine-checked proof that `intx::mulmod()` computes `x * y mod m` for every nonzero `m`, without
undefined behavior. It covers `internal::mulmod_fold<N>()` for `N` from 1 to 4 and the helpers it
calls, from the word operations up, with and without the x86-64 `div` instruction.

## Audit map

| file | review |
|---|---|
| [`Intx/Spec.lean`](Intx/Spec.lean) | The statement `MulmodCorrect`, which the main theorem proves for the model. It uses only the Lean core. |
| [`Intx/Model/`](Intx/Model/) | The C++ code rendered in Lean. Compare it with `include/intx/intx.hpp`: each definition shows its C++ code. |
| [`Intx/ProofSupport/`](Intx/ProofSupport/), [`Intx/Proofs/`](Intx/Proofs/) | The proof, checked by Lean. The main theorem is `Intx.mulmod_correct` in [`Intx/Proofs/MulmodFold.lean`](Intx/Proofs/MulmodFold.lean). |
| [`Checks/`](Checks/) | The axioms the main theorem depends on. |
| [`SOURCE.json`](SOURCE.json) | The hashes of the modeled C++ definitions. |

## What the proof trusts

* Lean and Mathlib.
* The model renders the C++ code faithfully. Lean cannot read C++, so this is checked by review, by
  the differential test against the compiled C++ (`scripts/difftest.sh`) and by the hashes of the
  modeled definitions (`scripts/check-source.py`), which make a later change of the C++ code fail
  the check until the model is updated.
* The modeling choices, documented in the model:
  * The C++ types are Lean types: `uint64_t` is `UInt64`, an array or a `uint<64 * n>` is a
    `Vector` of `n` words and a shift amount is a `Fin 64`. The array sizes, the indices, the
    `static_assert`s and the `INTX_REQUIRE`s on sizes are proved when the model is compiled.
  * The undefined behavior that depends on values, a false `INTX_REQUIRE` (an assumption of the
    compiler in release builds) or a `div` that faults, makes the model return `none`, and the main
    theorem shows that it does not happen. The correction loop of `udivrem_top1()` gets the 2
    iterations its comment promises, and the proof shows they are enough.
  * The word operations have the semantics of their portable code; the builtins and the x86-64
    asm compute the same.
  * The code paths that the build and the context select are the argument `P : Platform` of the
    model. With `P.div_wide_x86`, `udivrem_2by1()` and `reciprocal_2by1()` use the x86-64 `div`
    instruction (`INTX_HAS_DIV_WIDE_X86` outside constant evaluation). Without it they use the
    reciprocal of `internal::reciprocal()`, as constant evaluation and the other architectures do.
    The main theorem holds for both.
  * The uninitialized arrays are zeros: the C++ code writes every word of them before reading it.

## Build and check

```sh
lake exe cache get
lake build
lake env lean Checks.lean
scripts/difftest.sh 1000000
scripts/check-source.py
```

The differential test checks the model on both paths against the C++ results of the build. The
vectors of a build without the `div` instruction, such as aarch64 under qemu, go in a file:

```sh
aarch64-linux-gnu-g++ -std=c++20 -O2 -static -I ../include scripts/difftest.cpp -o gen-a64
qemu-aarch64 ./gen-a64 1000000 > vectors-a64.txt
VECTORS=vectors-a64.txt scripts/difftest.sh
```

## Updates

After a change of the modeled C++ code, update the model and the proofs, run the differential
test, and record the new hashes with `scripts/check-source.py --update`.
