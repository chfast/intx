# The proofs of the RV64 machine code

Machine-checked proofs that the RV64 machine code of intx functions, as the compiler emits it,
computes the models of `Intx.Model`. The machine is the Sail RISC-V model, the official
specification of the ISA, translated to Lean (`LeanRV64D` of
[sail-riscv-lean](https://github.com/opencompl/sail-riscv-lean)). The correctness proofs of the
models (`Intx.Proofs`) then give the specification of the machine code.

## The pipeline

1. [`Examples.cpp`](Examples.cpp) lists the intx functions to verify, each with its theorems in a
   `/* lean ... */` block. A `[[gnu::used]]` pointer to a function makes the compiler emit its
   out-of-line copy.
2. [`../scripts/rv_build.sh`](../scripts/rv_build.sh) compiles `Examples.cpp` for RV64 (clang,
   `-O2 -march=rv64imafd`) and runs [`../scripts/rv_gen.py`](../scripts/rv_gen.py), which writes:
   * [`Gen/Code.lean`](Gen/Code.lean): the machine code of each function (the words of its
     section of the object file, which must have no relocations), the instructions that the words
     decode to, and the proofs that the decoder of the Sail model decodes them so;
   * [`Examples.lean`](Examples.lean): the lean blocks of `Examples.cpp`.
3. `lake build IntxRV` checks the proofs. CI regenerates the files and fails if they differ from
   the committed ones, so a new compiler or a change of the C++ code shows up as a diff.

## The theorems

`Runs code pre post` (in [`Run.lean`](Run.lean)): for every state of the Sail model in the
environment `Env` (below), every address of the code and every return address, aligned to 4
bytes, and every value of the registers with the return address in ra satisfying `pre`, the Sail
model runs the code until it returns, and the registers at the return satisfy `post`. The state
at the return is the start state with only the general purpose registers and the program counters
changed: the memory, the CSRs and everything else are unchanged (`Inv`). The assumptions are not
vacuous: [`Env.lean`](Env.lean) builds a state of the model in `Env` and a start state in `Inv`
for every value of the registers.

The theorem of a function states that the result registers (a0, a1) are the model of the function
on the argument registers (a0 to a7), as the RISC-V calling convention passes them, and that the
callee-saved registers are preserved. The tactic `rv_run` proves it without proof text for the
function: it runs the instructions on symbolic registers, splits the paths at the branches, and
proves each path by `bv_omega` (and `ring` for products). The reuse is at the model level: the
model of `udivrem_2by1()` calls the model of `umul()`, and the RISC-V `mul` and `mulhu` are the
model's `umul` by the lemmas `umul_lo_toBitVec` and `umul_hi_toBitVec` of
[`Values.lean`](Values.lean), proved from the correctness of the model.

## What the proofs trust

* The Lean kernel. The proofs use only the axioms of Lean (`propext`, `Classical.choice`,
  `Quot.sound`) and the opaque functions that the Sail model declares as axioms (the platform
  callbacks, the reservations of the A extension and the softfloat functions, none of which the
  verified functions execute). The theorems hold for every implementation of the latter. No
  `native_decide` and no `bv_decide`: `bv_decide` checks its SAT proofs by compiled code.
  [`../Checks/IntxRV.lean`](../Checks/IntxRV.lean) pins the axioms.
* The Sail RISC-V model and its translation to Lean by the Lean backend of Sail.
* The step of the Sail model, which [`Run.lean`](Run.lean) renders from `try_step` and
  `run_hart_active` of the model (`Step.lean`): decode, the landing pad check (Zicfilp),
  `nextPC := PC + 4`, execute, `PC := nextPC`. Not modeled: interrupts, the waiting states of the
  hart, the counting of the retired instructions (`minstret`), and the fetch, which is the code at
  its address (the model of the fetch translates the address and reads the memory). So "nothing
  else changes" excludes `minstret`.
* The environment `Env`: every register of the model exists, no landing pad is expected, the M
  extension is enabled and the privilege level is machine, supervisor or user.
* The statements of the theorems in `Examples.cpp`: which registers hold the arguments and the
  results.
* The extraction of the machine code from the object file by `rv_gen.py`.

Not covered: other compilers, other flags, the linking.

## Build

```sh
sudo apt install clang g++-riscv64-linux-gnu
scripts/rv_build.sh
lake build IntxRV Checks
```
