# The proofs of the RV64 machine code

Machine-checked proofs that the RV64 machine code of intx functions, as the compiler emits it,
computes the models of `Intx.Model`. The machine is the Sail RISC-V model, the official
specification of the ISA, translated to Lean (`LeanRV64D` of
[sail-riscv-lean](https://github.com/opencompl/sail-riscv-lean)). The correctness proofs of the
models (`Intx.Proofs`) then give the specification of the machine code.

## The pipeline

1. The documentation of a function in `intx.hpp` states its specification (below).
   [`Api.cpp`](Api.cpp) lists the instances to verify: in `intx::api` the functions whose machine
   code is proved (a lambda that calls the function, or the address of a function template
   instance; a lambda with `[[gnu::flatten]]` has the code of a function that clang does not
   inline otherwise, as the shifts), in `intx::model` those whose model is proved (none at
   present). A `[[gnu::used]]` pointer to a function makes the compiler emit its out-of-line
   copy.
2. [`../scripts/rv_build.sh`](../scripts/rv_build.sh) compiles `Api.cpp` for RV64 (clang 21,
   `-O2 -march=rv64imafd`) and runs [`../scripts/rv_gen.py`](../scripts/rv_gen.py), which writes
   `Gen/Code.lean`: the machine code of each function (the words of its section of the object
   file, which must have no relocations), the instructions that the words decode to, and the
   bytes of the stack each function uses (its frame); `Gen/Decode/`: the proofs that the decoder
   of the Sail model decodes the words so, in 64 files by the hash of the word, which build in
   parallel and of which new code rebuilds only those with its new words; and
   [`../scripts/rv_api.py`](../scripts/rv_api.py), which writes the specifications of the
   instances to `Gen/Api.lean` and `../Intx/Gen/Spec.lean`, and their checks to
   `../Checks/Gen/IntxRVApi.lean` and `../Checks/Gen/IntxSpec.lean`.
3. `lake build IntxRV Checks` checks the proofs.

The generated files are not in git: run `scripts/rv_build.sh` before `lake build`, and again after
a change of `intx.hpp` or `Api.cpp`. CI generates them in every build, so the proofs must hold for
the code and the documentation of the commit. Another compiler emits other code: `rv_build.sh`
requires clang 21.

## The proof of a function

The proof of the instance `p` of `Api.cpp` is in `Api/p.lean`, and the file holds only it. The
file quotes the documentation and the declaration of the function from `intx.hpp`, so it reads
without the generated files: `Api.p.spec` states the quoted `@pre` and `@post` for the machine code
of `p` (see [the specifications](#the-specifications)), and `Api.p.proof` proves it. `rv_api.py`
fails if a quote differs from `intx.hpp`, if the file is missing, or if this table does not link
it. The lemmas and the tactics that the proofs share are in the other files of `IntxRV/`.

| function | proof |
|---|---|
| `umul()` of two words | [`umul`](Api/umul.lean) |
| `addc()` | [`addc`](Api/addc.lean) |
| `udivrem_2by1()` | [`udivrem_2by1`](Api/udivrem_2by1.lean) |
| `udivrem_3by2()` | [`udivrem_3by2`](Api/udivrem_3by2.lean) |
| `umul()` of `uint256` | [`umul_256`](Api/umul_256.lean) |
| `reciprocal_2by1()` | [`reciprocal_2by1`](Api/reciprocal_2by1.lean) |
| `reciprocal_3by2()` | [`reciprocal_3by2`](Api/reciprocal_3by2.lean) |
| `operator+` of `uint256` | [`add_256`](Api/add_256.lean) |
| `operator-` of `uint256` | [`sub_256`](Api/sub_256.lean) |
| `operator*` of `uint256` | [`mul_256`](Api/mul_256.lean) |
| `operator==` of `uint256` | [`eq_256`](Api/eq_256.lean) |
| `operator!=` of `uint256` | [`ne_256`](Api/ne_256.lean) |
| `operator<` of `uint256` | [`lt_256`](Api/lt_256.lean) |
| `operator>` of `uint256` | [`gt_256`](Api/gt_256.lean) |
| `operator>=` of `uint256` | [`ge_256`](Api/ge_256.lean) |
| `operator<=` of `uint256` | [`le_256`](Api/le_256.lean) |
| `slt()` of `uint256` | [`slt_256`](Api/slt_256.lean) |
| `operator\|` of `uint256` | [`or_256`](Api/or_256.lean) |
| `operator&` of `uint256` | [`and_256`](Api/and_256.lean) |
| `operator^` of `uint256` | [`xor_256`](Api/xor_256.lean) |
| `operator~` of `uint256` | [`not_256`](Api/not_256.lean) |
| `shl<9, 8>()` | [`shl_9_8`](Api/shl_9_8.lean) |
| `operator<<` of `uint256` by `uint64_t` | [`shl_256`](Api/shl_256.lean) |
| `operator>>` of `uint256` by `uint64_t` | [`shr_256`](Api/shr_256.lean) |
| `operator<<` of `uint256` by `uint256` | [`shl_256_by_256`](Api/shl_256_by_256.lean) |
| `operator>>` of `uint256` by `uint256` | [`shr_256_by_256`](Api/shr_256_by_256.lean) |
| `bit_test()` of `uint256` | [`bit_test_256`](Api/bit_test_256.lean) |
| `count_significant_words()` of `uint256` | [`count_significant_words_256`](Api/count_significant_words_256.lean) |
| `clz()` of `uint256` | [`clz_256`](Api/clz_256.lean) |
| `bit_width()` of `uint256` | [`bit_width_256`](Api/bit_width_256.lean) |
| `ctz()` of `uint256` | [`ctz_256`](Api/ctz_256.lean) |

## The theorems

`Runs code pre post` (in [`Run.lean`](Run.lean)): for every state of the Sail model in the
environment `Env` (below), every address of the code and every return address, aligned to 4
bytes, and every value of the registers with the return address in ra satisfying `pre`, the Sail
model runs the code until it returns, and the registers at the return satisfy `post`. The state
at the return is the start state with only the general purpose registers and the program counters
changed: the memory, the CSRs and everything else are unchanged (`Inv`). The assumptions are not
vacuous: [`Env.lean`](Env.lean) builds a state of the model in `Env` and a start state in `Inv`
for every value of the registers.

The proof of the specification of a function goes through its model: a theorem states that the
result registers (a0, a1) are the model of the function on the argument registers (a0 to a7), and
that the callee-saved registers are preserved. The tactic `rv_run` proves it without proof text for the
function: it runs the instructions on symbolic registers, splits the paths at the branches, and
proves each path by `bv_omega` (and `ring` for products). The reuse is at the model level: the
model of `udivrem_2by1()` calls the model of `umul()`, and the RISC-V `mul` and `mulhu` are the
model's `umul` by the lemmas `umul_lo_toBitVec` and `umul_hi_toBitVec` of
[`Values.lean`](Values.lean), proved from the correctness of the model.

## The specifications

The documentation of a function in `intx.hpp` states its specification with the Doxygen commands
`@pre` and `@post`, as Lean terms in which a parameter name stands for the value of the parameter
as a natural number (a `Bool` for `bool`), `result` for the value of the result and `N` for the
width of the `uint<N>`. A `result_with_carry<uint64_t>` or `div_result<uint64_t>` result is a
structure of these (`ResultWithCarry`, `DivResult` in [`Words.lean`](Words.lean)):

```cpp
/// The sum modulo 2^N.
/// @post result = (x + y) % 2 ^ N
friend constexpr uint operator+(const uint& x, const uint& y) noexcept
```

`rv_api.py` reads the comments from the AST that clang dumps for `Api.cpp` (clang-doc drops `@pre`
and `@post`). The operators are hidden friends, so an instance in `Api.cpp` is a lambda that calls
the function; the generator finds the function in the AST, and so binds the machine code of the
instance to the documentation of the function. A member function has its object as the parameter
`self`; `x != y`, which C++20 rewrites to `!(x == y)`, gets the specification of `==` with the
result negated. `Api.p.spec` states the specification for the machine code of the instance `p` for
the RISC-V calling convention: a `uint64_t` or `bool` is in one register, a `uint128` in two, an
`unsigned` is its 32 bits sign-extended to the register (the code may test the whole register), a
`const uint<N>&` argument or a `std::span<const uint64_t, n>` is the address of its words in the
next argument register, a `uint<N>` result wider than 128 bits is written to the buffer at the
address in a0 (`sret`), as is a `div_result<uint64_t, uint128>` (24 bytes), a `bool` is 0 or 1. A `std::span<uint64_t, n>` parameter of a `void`
function is the buffer it writes: its name stands for its value at the return, and `N` for its
width. With registers only the specification is a `Runs`; with memory a `RunsM` (in
[`RunM.lean`](RunM.lean)), the `Runs` with memory: the buffers are aligned, do not wrap around and
the result does not overlap the arguments; the memory outside the result is unchanged. A function
with a stack frame gets the frame below sp as one more buffer that overlaps no other, and the memory
outside the result and the frame is unchanged.

The proofs are in [`Api/`](Api/): the generated `Checks/Gen/IntxRVApi.lean` requires a proof
`Api.p.proof : Api.p.spec` for every instance, with the allowed axioms only, and that the
assumptions of the specification hold: with `NonVacuous` ([`EnvM.lean`](EnvM.lean)) in an
environment for the functions with memory, by a proof `Api.p.nonvacuous` otherwise. `umul()`,
`addc()` and `udivrem_2by1()` are proved through their models,
the bitwise operators through `List.zipWith` (and `~` through `List.map`) of the word operation; the
comparisons and `slt()` directly. `operator+` and `operator-` are proved through the models `add4`
and `sub4` (the chains of `addc()` and `subc()` of `Intx.Model`, [`ApiModel.lean`](ApiModel.lean));
the tactic `rv_runm` ([`TacticM.lean`](TacticM.lean)) proves that the machine code computes them.

`rv_runm` evaluates the whole run in one `simp`, which takes seconds per instruction. Longer
functions are run one instruction at a time ([`Step.lean`](Step.lean),
[`StepTactic.lean`](StepTactic.lean)): `Reach` ([`Reach.lean`](Reach.lean)) states that the run
reaches an address, and `rv_exec` proves it by `Reach.step`. The value of each instruction gets a
name with its definition (`Defn`) in the context, so a step does not grow with the length of the
run. The specification then follows from the definitions by `rv_arith`
([`Arith.lean`](Arith.lean)): the carries and the words of the products as exact linear facts,
the sums that cannot overflow by `omega` from the facts they depend on, and the result by
`linarith`. `shl<9, 8>()`, the shift of a 512-bit number, is proved this way, through the model
`Intx.Model.shl` and its proof; `operator<<` and `operator>>` of `uint256` with the lemmas of
[`Shift.lean`](Shift.lean) on the funnel shifts of the words. `udivrem_3by2()` is proved through
`div3by2BV` ([`Div3by2.lean`](Div3by2.lean)), the operations of its code on the words, whose
quotient and remainder follow from Möller and Granlund, Theorem 3 (`Intx.div3by2_bounds` in
[`../Intx/Proofs/DivMath.lean`](../Intx/Proofs/DivMath.lean)): on each path `rv_fold` writes this
specification with the names of the run, and `rv_conds` adds the conditions of the branches on the
results of `sltu`, which select its words. `reciprocal_3by2()` is proved the same way through
`recip3BV` ([`Recip3.lean`](Recip3.lean)): its `v2` is the one of the model
`Intx.Model.reciprocal_approx`, and `Intx.recip3_nat` gives the reciprocal from the Newton step
against the whole divisor and the exact correction. `umul()` of `uint256`, the 512-bit
product, is proved through `umul256_words` ([`Umul256.lean`](Umul256.lean)), the product from the
definitions of the values of its run: the high word of each `mac()` does not overflow by the bound
of its sum, and the last `mac()` of a row, which clang adds to the next row a summand at a time,
needs the bound of the one of the row before. `rv_loads` writes the loaded words with their names,
and `apply` with `assumption` finds the definitions by the names of the stored words. `operator*`
of `uint256` runs two loops, the rows of the product and the words of a row: their counters and
pointers run to constant bounds, so `rv_exec_loop` decides the branches and unrolls them. It is
proved the same way through `mul256_words` ([`Mul256.lean`](Mul256.lean)), the product modulo
`2^256`, after `rv_cse` gives the words that each row loads again one name.

### Calls and constant data

A function that calls other functions or reads constant data (the table of the reciprocal) has
relocations. `rv_gen.py` links each of these functions `p` with what it reaches into its own image
at 0 ([`../scripts/rv_image.ld`](../scripts/rv_image.ld)), so that other functions do not move its
code and data: the code `Gen.p_image_code` and the read-only data `Gen.p_image_data` after it,
and the stack that the function uses with its callees. `RunsI` ([`Image.lean`](Image.lean)) is
`RunsM` for the function at the instruction `entry` of the image, with the data in the memory. A
call is `auipc ra` and `jalr ra`; `Reach.call` ([`Call.lean`](Call.lean)) runs the callee by its
proof: `f.reach` of a function `f` on its own code is lifted into the image by `Reach.lift`.
`Gen.p_image_f_in` states that the image holds the code of `f`: the function `f` itself, or another
function with the same code, as the operators by `uint64_t` that the shifts by `uint256` call
(`Reach.call_sub`). The instances of `intx::wip` in `Api.cpp` get their specifications without the checks of their proofs,
until they are proved (none at present).

`bit_test()` and `count_significant_words()` are proved directly, with lemmas on the bits of
`words` and on `log2` ([`Bits.lean`](Bits.lean)).

`reciprocal_2by1()` reads the table of the image ([`Reciprocal.lean`](Reciprocal.lean))
and is proved through its model `Intx.Model.reciprocal`. `NonVacuousI`
([`EnvImage.lean`](EnvImage.lean)) checks that the assumptions of `RunsI` hold: the data stored in
the RAM of the environment.

[`Clz.lean`](Clz.lean) proves the count of the leading zeros that clang computes without the Zbb
extension (spreading the top bit down and the SWAR population count) to be `63 - log2 x`.

### Memory

[`Mem.lean`](Mem.lean) proves that `ld` and `sd` of an aligned word read and write its 8 bytes in
the memory of the Sail state, little-endian, through the whole memory access of the Sail model:
the address translation, the PMP and PMA checks and the memory-mapped devices. The environment
`EnvM` makes these pass through: machine mode without `MPRV` (no translation), no pointer masking
and no PMP entries enabled. `WordOk` assumes that each word of a buffer is in a readable and
writable PMA region and not in the CLINT, HTIF or signature region, and its 4-byte halves and its
bytes in a readable one (`HalfOk`, `ByteOk`). [`Mem4.lean`](Mem4.lean) proves that `lwu` of a
half reads its 4 bytes, zero-extended, and [`Mem1.lean`](Mem1.lean) that `lbu` reads a byte,
zero-extended. `EnvM.lean` builds such an environment with 4 KiB of RAM, the stack at its end.

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
  extension is enabled and the privilege level is machine, supervisor or user. For the functions
  with memory, `EnvM` and `WordOk` (above).
* The specifications in the documentation, and `rv_api.py`: the extraction of the comments, the
  binding of an instance to its function and the calling convention.
* The extraction of the machine code from the object file and the image by `rv_gen.py`.

Not covered: other compilers, other flags; loops (so not the multiplication modulo 2^256, the
shifts and the division of `uint256` yet). The linking of the image is by `ld.lld` with the
linker script; its output is checked as the machine code is.

## Build

```sh
sudo apt install clang-21 lld g++-riscv64-linux-gnu
CXX=clang++-21 scripts/rv_build.sh
lake build IntxRV Checks
```
