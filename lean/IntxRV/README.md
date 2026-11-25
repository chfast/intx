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
   `-O2 -march=rv64im`) and runs [`../scripts/rv_gen.py`](../scripts/rv_gen.py), which writes
   `Gen/Code/p.lean` for each instance `p`: its machine code (the words of its section of the
   object file, which must have no relocations, or of its image) and the instructions that the
   words decode to; `Gen/Decode/`: the proofs that the decoder of the Sail model decodes the
   words so, in 192 files by the hash of the word, which build in parallel and of which new code
   rebuilds only those with its new words; `Gen/Decodes/p.lean`: the proof that the code of `p`
   decodes to its instructions; and, for the specifications, the bytes of the stack that each
   function uses (its frame). Then
   [`../scripts/rv_api.py`](../scripts/rv_api.py) writes the specification of each instance to
   `Gen/Api/p.lean`, the proof of the specification to `Gen/Proof/p.lean`, the specifications of
   the models to `../Intx/Gen/Spec.lean`, and their checks to `../Checks/Gen/IntxRVApi.lean` and
   `../Checks/Gen/IntxSpec.lean`.
3. `lake build IntxRV Checks` checks the proofs.

The generated files are not in git: run `scripts/rv_build.sh` before `lake build`, and again after
a change of `intx.hpp` or `Api.cpp`. CI generates them in every build, so the proofs must hold for
the code and the documentation of the commit. Another compiler emits other code: `rv_build.sh`
requires clang 21.

Lake rebuilds a module when its text or the text of a module that it imports changes. A proof
imports only the modules of the instances that it uses, and not the proofs of the decoding: a change
of the code or of the specification of an instance rebuilds only the proofs that import its modules,
through the images that hold its code or through the lemma modules. The lemmas that the proofs of
several functions use are in modules without generated code (`DivShared.lean` for the division): a
change of `udivrem_by2()` rebuilds 14 proofs, its own, the 8 of the instances whose images hold its
code and 5 through the lemma modules. A new word of machine code and a change of other lines of
`intx.hpp` rebuild no proof: the generated files have no line numbers of `intx.hpp`.

## The proof of a function

The proof of the instance `p` of `Api.cpp` is in `Api/p.lean`, and the file holds only it. The
file quotes the documentation and the declaration of the function from `intx.hpp`, so it reads
without the generated files: `Api.p.spec` states the quoted `@pre` and `@post` for the machine code
of `p` (see [the specifications](#the-specifications)), and `Api.p.proof_of_decodes` proves it
from `Api.p.decodes`, that the machine code decodes to its instructions. `Api.p.proof` in the
generated `Gen/Proof/p.lean` adds the proof of the decoding. `rv_api.py` fails if a quote differs
from `intx.hpp`, if the file is missing, or if this table does not link it. The lemmas and the tactics that the proofs share are in the other files of `IntxRV/`.

| function | proof |
|---|---|
| `umul()` of two words | [`umul`](Api/umul.lean) |
| `addc()` | [`addc`](Api/addc.lean) |
| `udivrem_2by1()` | [`udivrem_2by1`](Api/udivrem_2by1.lean) |
| `udivrem_3by2()` | [`udivrem_3by2`](Api/udivrem_3by2.lean) |
| `umul()` of `uint256` | [`umul_256`](Api/umul_256.lean) |
| `internal::udivrem_by1()` of a span | [`udivrem_by1`](Api/udivrem_by1.lean) |
| `internal::udivrem_by2()` of a span | [`udivrem_by2`](Api/udivrem_by2.lean) |
| `internal::udivrem_top1()` of `uint256` by the top word 2 | [`udivrem_top1_2`](Api/udivrem_top1_2.lean) |
| `internal::udivrem_top1()` of `uint256` by the top word 3 | [`udivrem_top1_3`](Api/udivrem_top1_3.lean) |
| `internal::udivrem_top2()` of `uint256` by the top word 3 | [`udivrem_top2_3`](Api/udivrem_top2_3.lean) |
| `udivrem()` of `uint256` by `uint256` | [`udivrem_256`](Api/udivrem_256.lean) |
| `internal::submul()` in place | [`submul`](Api/submul.lean) |
| `internal::udivrem_knuth_normalized<3>()` | [`udivrem_knuth_normalized_3`](Api/udivrem_knuth_normalized_3.lean) |
| `internal::udivrem_knuth_normalized<4>()` | [`udivrem_knuth_normalized_4`](Api/udivrem_knuth_normalized_4.lean) |
| `udivrem()` of `uint512` by `uint256` | [`udivrem_512_256`](Api/udivrem_512_256.lean) |
| `mulmod()` of `uint256` | [`mulmod_256`](Api/mulmod_256.lean) |
| `internal::udivrem_by1()` of 5 words | [`udivrem_by1_5`](Api/udivrem_by1_5.lean) |
| `internal::udivrem_by2()` of 4 quotient words | [`udivrem_by2_4`](Api/udivrem_by2_4.lean) |
| `internal::udivrem_top1<2>()` of `uint320` by `uint256` | [`udivrem_top1_2_320`](Api/udivrem_top1_2_320.lean) |
| `internal::udivrem_top1<3>()` of `uint320` by `uint256` | [`udivrem_top1_3_320`](Api/udivrem_top1_3_320.lean) |
| `internal::udivrem_top2<3>()` of `uint320` by `uint256` | [`udivrem_top2_3_320`](Api/udivrem_top2_3_320.lean) |
| `internal::udivrem_knuth_normalized()` with a dynamic size of d | [`udivrem_knuth_normalized`](Api/udivrem_knuth_normalized.lean) |
| `internal::udivrem_knuth<320, 256>()` with a dynamic size of d | [`udivrem_knuth_320`](Api/udivrem_knuth_320.lean) |
| `internal::udivrem_top2<3, true>()` of `uint320` by `uint256` | [`udivrem_top2_3_equal_320`](Api/udivrem_top2_3_equal_320.lean) |
| `internal::udivrem_top2<4>()` of `uint320` by `uint256` | [`udivrem_top2_4_320`](Api/udivrem_top2_4_320.lean) |
| `udivrem()` of `uint320` by `uint256` | [`udivrem_320_256`](Api/udivrem_320_256.lean) |
| `addmod()` of `uint256` | [`addmod_256`](Api/addmod_256.lean) |
| `operator-()` of `uint256` | [`neg_256`](Api/neg_256.lean) |
| `sdivrem()` of `uint256` | [`sdivrem_256`](Api/sdivrem_256.lean) |
| `count_significant_bytes()` of `uint256` | [`count_significant_bytes_256`](Api/count_significant_bytes_256.lean) |
| `exp()` of `uint256` | [`exp_256`](Api/exp_256.lean) |
| `operator bool` of `uint256` | [`bool_256`](Api/bool_256.lean) |
| `operator uint64_t` of `uint256` | [`to_u64_256`](Api/to_u64_256.lean) |
| `operator int64_t` of `uint256` | [`to_i64_256`](Api/to_i64_256.lean) |
| `operator uint8_t` of `uint256` | [`to_u8_256`](Api/to_u8_256.lean) |
| `operator int` of `uint256` | [`to_i32_256`](Api/to_i32_256.lean) |
| the constructor of `uint256` from an `int` | [`from_i32_256`](Api/from_i32_256.lean) |
| `operator=` of `uint256` by `uint64_t` | [`assign_256`](Api/assign_256.lean) |
| `operator+=` of `uint256` | [`add_assign_256`](Api/add_assign_256.lean) |
| `operator&=` of `uint256` | [`and_assign_256`](Api/and_assign_256.lean) |
| `operator\|=` of `uint256` | [`or_assign_256`](Api/or_assign_256.lean) |
| `operator^=` of `uint256` | [`xor_assign_256`](Api/xor_assign_256.lean) |
| `operator*=` of `uint256` | [`mul_assign_256`](Api/mul_assign_256.lean) |
| `operator<<=` of `uint256` | [`shl_assign_256`](Api/shl_assign_256.lean) |
| `operator>>=` of `uint256` | [`shr_assign_256`](Api/shr_assign_256.lean) |
| `operator<` of `uint256` and `int` | [`lt_256_i32`](Api/lt_256_i32.lean) |
| `operator<` of `uint256` and `int64_t` | [`lt_256_i64`](Api/lt_256_i64.lean) |
| `operator<` of `uint256` and `uint64_t` | [`lt_256_u64`](Api/lt_256_u64.lean) |
| `operator<` of `uint64_t` and `uint256` | [`lt_u64_256`](Api/lt_u64_256.lean) |
| `operator<` of `unsigned` and `uint256` | [`lt_u32_256`](Api/lt_u32_256.lean) |
| `operator<` of `int` and `uint256` | [`lt_i32_256`](Api/lt_i32_256.lean) |
| `be::unsafe::load<uint64_t>()` | [`be_load_u64`](Api/be_load_u64.lean) |
| `be::unsafe::load<uint16_t>()` | [`be_load_u16`](Api/be_load_u16.lean) |
| `be::unsafe::store()` of `uint64_t` | [`be_store_u64`](Api/be_store_u64.lean) |
| `be::unsafe::load<uint32_t>()` | [`be_load_u32`](Api/be_load_u32.lean) |
| `be::unsafe::load<uint256>()` | [`be_load_256`](Api/be_load_256.lean) |
| `be::load<uint256>()` from `uint8_t[32]` | [`be_load_256_32`](Api/be_load_256_32.lean) |
| `be::load<uint256>()` from `evmc::bytes32` | [`be_load_256_bytes32`](Api/be_load_256_bytes32.lean) |
| `be::load<uint256>()` from `evmc::address` | [`be_load_256_address`](Api/be_load_256_address.lean) |
| `be::unsafe::store()` of `uint256` | [`be_store_256`](Api/be_store_256.lean) |
| `be::store<evmc::bytes32>()` | [`be_store_bytes32`](Api/be_store_bytes32.lean) |
| `be::trunc<evmc::address>()` | [`be_trunc_address`](Api/be_trunc_address.lean) |
| `reciprocal_2by1()` | [`reciprocal_2by1`](Api/reciprocal_2by1.lean) |
| `reciprocal_3by2()` | [`reciprocal_3by2`](Api/reciprocal_3by2.lean) |
| `operator+` of `uint256` | [`add_256`](Api/add_256.lean) |
| `operator-` of `uint256` | [`sub_256`](Api/sub_256.lean) |
| `operator*` of `uint256` | [`mul_256`](Api/mul_256.lean) |
| `operator/` of `uint256` | [`div_256`](Api/div_256.lean) |
| `operator%` of `uint256` | [`mod_256`](Api/mod_256.lean) |
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
/// @post result = (x + y) % 2^N
friend constexpr uint operator+(const uint& x, const uint& y) noexcept
```

A `@note FV:` in the documentation marks what a specification does not cover, as `x += x` (the
specification of an operator in place requires y not to overlap the object). A function without
`@post` is not verified: on `main`, the documentation shows the specifications proved here.

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
width. A span of dynamic extent (`std::span<uint64_t>`) is its address and its number of words in
two registers, a buffer of that many words; `p.size()` of a span `p` in a `@pre` or `@post` is its
number of words, and a span of non-const words is the buffer written, as in
`internal::udivrem_by1()`. A raw pointer `uint64_t p[]` is the address of its words in one
register, and the `@pre p.size() = n` gives their number (it is not a precondition then), as in
`internal::submul()`. A function may write several buffers, and `old(p)` in a `@post` is the
value of the written buffer `p` at the entry: `internal::udivrem_knuth_normalized()` turns the
words of `u` into the remainder in place. With registers only the specification is a `Runs`; with
memory a `RunsM` (in [`RunM.lean`](RunM.lean)), the `Runs` with memory: the buffers are aligned, do
not wrap around and the written buffers overlap neither each other nor the arguments; the memory
outside the written buffers is unchanged. (The comment of `udivrem_knuth_normalized()` allows the
quotient to alias `u`; its specification does not, and `udivrem_knuth()` passes a quotient outside
`u`.) A function with a stack frame gets the frame below sp as one more buffer that overlaps no
other, and the memory outside the written buffers and the frame is unchanged (`UnchangedExcept`,
`UnchangedExcept2` and `UnchangedExcept3` in [`Words.lean`](Words.lean)).

The instance of a lambda has the registers of the types of the lambda, so a parameter that the
function takes by reference may be a value of the lambda. An `int` or `int64_t` is an `Int`
(`toInt` of the register; an `int` is sign-extended from 32 bits); a `uint8_t` or `uint16_t`
result is zero-extended to the register and an `int` result sign-extended from 32 bits. A non-const
`uint<N>&`, as the object of an operator in place such as `+=`, is a written buffer: `self` is its
value at the return and `old(self)` at the entry. A conversion operator template has
`sizeof(Int)` of the type of its instance; a constructor has the constructed object, the result,
as `self`, and its parameter pack `v` is the list of the values as integers. Bytes are of any
alignment ([`Bytes.lean`](Bytes.lean)): a `const uint8_t*` with the `@pre p.size() = n`, a
`const uint8_t (&)[n]`, and a struct whose only field is the array `bytes` (the layouts of
`evmc::bytes32` and `evmc::address`, `Bytes32` and `Address` in `Api.cpp`) are the list of their
bytes (`bytes`), `t.bytes` of a struct `t` too, and `bigEndian` their number in big-endian order.
A `uint8_t*` and a struct result (in memory at a0, as it is wider than two registers) are written
buffers of bytes. A buffer of bytes needs only not to wrap around (`BufBytes`), and its words are
the aligned words of its bytes (`bufBytes`).

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

### Loops

`internal::udivrem_by1()` of a span divides it a word at a time in a loop that runs `u.size() - 2`
times. `Reach.loop` ([`Loop.lean`](Loop.lean)) proves the run from the head of a loop by induction
on the iterations left, from an invariant at the head; `rv_exec_cut` runs the code to the cut
points, the head and the exit, and stops at the loads and stores of the words at the addresses that
depend on the counter, which the proof steps with `mem_bufWords`. The invariant of
`udivrem_by1()` (`by1Head` in [`DivBy1.lean`](DivBy1.lean)) holds the registers at the head, the
quotient words stored above the word `i` and the remainder of the digits above it, of the numerator
shifted left to normalize the divisor; each iteration divides the digit `i`, the funnel shift of
the words `i` and `i - 1` (`norm_digit` in [`DivWords.lean`](DivWords.lean)), by the inlined
`udivrem_2by1()` (`div2by1BV` in [`Div2by1.lean`](Div2by1.lean)). The inlined `reciprocal_2by1()`
is `recip2BV`. `rv_has`, `rv_lacks` and `rv_get` select the paths of a run by the conditions of their
branches without unfolding the hypotheses, and an anonymous assumption such as
`‹Defn _ ((_ : BitVec 64) >>> s)›` passes a name of the run, which the proof cannot write, to a
lemma.

`internal::udivrem_by2()` divides by two words in the same way, with the inlined
`reciprocal_3by2()` and three inlined copies of `udivrem_3by2()`, each with branches. The block
lemmas of [`DivBy2.lean`](DivBy2.lean) (`by2_div_top`, `by2_div_loop`, `by2_div_last` and
`by2_sub_top`) run the paths of a copy to its end, and the proof takes a copy as one step
(`Reach.trans`), continuing from the registers after it with the registers that it changes set
(`regs_eq_sets`). The paths of the top digits meet at `by2Top`, the state before the loop.

`internal::udivrem_top1<3>()` estimates the quotient word from the normalized top words with an
inlined `udivrem_2by1()` (`div2by1BVc`, with the products in the other order). The estimate is not
less than the quotient (`top1_est`, Knuth's Theorem B), and the correction loop adds v back to the
remainder of the operands while the borrow is not 0. The lemmas of [`DivTop1.lean`](DivTop1.lean)
state the 4-word `submul()` and the addition of the loop by the definitions of their values
(`submul4_words`, `top1_body_sm`), in an order in which `apply` and `assumption` find the
definitions from the names in the goal, and run the code from the test of the borrow to the return
(`top1_3_tail`): the loop by `Reach.loop` with the excess of the quotient as the measure, and the
stores of the result. `udivrem_top1<2>()` is the same with 3 words of v and the word u[3] above
them, and the paths of its test of u < v meet in `top1_2_main`. `nonVacuousI_of_args` stores the
words of the arguments in the RAM, for a precondition on their values.

`internal::udivrem_top2<3>()` divides the top digits of the normalized u by the top 128 bits of
the normalized v with two inlined copies of `udivrem_3by2()`, which
[`DivTop2.lean`](DivTop2.lean) runs as block lemmas (`top2_div_top`, `top2_div_low`, the second
with the restore of the frame), and corrects the quotient with `u - q * v`, which the code computes
from the remainder of the top digits and the low words (`top2_nat`). In a large context, the
inlined copies fold their results badly and `apply` with `assumption` can recurse: the end of the
code substitutes the definitions (`subst_vars`) and takes the lemmas of the sums with `rfl`.

`udivrem<256, 256>()` dispatches to the five functions above by the significant words of u and v.
A lemma of [`Div256.lean`](Div256.lean) runs each path from its first instruction to the return,
with the call by `Reach.call_sub` and the proof of the callee for the immediates of the table, and
the proof routes the paths of the run to them. A call lemma over the registers
that the paths set, as hypotheses, serves several paths (`u256_by1_call`): with the calls inlined
in each path, a module took 8.6 GB. The table is a list of 256 words: the proof generalizes it to
a variable `D`, so that the checks of the loads and the stores do not expand it, and keeps the fact
`∀ a ∈ bufWords T 256, a ∈ D`, which `subst_vars` cannot undo. `/` and `%` of `uint256` call
`udivrem<256, 256>()` in their own images, where the table is at another distance from the code
([`Div256Op.lean`](Div256Op.lean)): `udivrem_256.reach` holds for any immediates of the table in
the five callees, with the address that each gives as an assumption. The proof hides these
assumptions from `omega` and `subst_vars` in `PLift`: `bv_omega` would expand their sign
extensions in every call, and `subst_vars` would replace the address of the table.

`internal::udivrem_knuth_normalized<3>()` divides the normalized u by 3 words of d a digit at a time
([`Knuth.lean`](Knuth.lean), [`Knuth3.lean`](Knuth3.lean)). The invariant of its loop (`k3Head`)
is the quotient and the remainder of the digits of u above the digit j (`knuth_digit`); a digit is
the estimate of the inlined `udivrem_3by2()` of the top 3 words of the remainder by the top 2
words of d (`k3_div`, `knuth_sub`, `knuth_est`), less 1 with d added back if the subtraction of
the estimate times d borrows (`k3_sub`, `knuth_addback`), or `2^64 - 1` by the call of
`submul()` if the top 2 words of the remainder are the top 2 words of d (`k3_over`,
`knuth_overflow`). The paths of a digit meet at the store of the digit (`k3_tail`), and the
epilogue is a lemma over abstract registers (`k3_exit`). The 4-word instance
([`Knuth4.lean`](Knuth4.lean)) is the same with the 2-word `submul()` of the low words of d and the
4-word add-back, in its image after `submul()`: its code starts at the instruction 22. An `omega`
in the context of a run makes a proof over all its hypotheses, which the kernel checks for minutes
in tens of GB: the arithmetic of the runs is in lemmas over a few variables, and `omega` there
follows `clear * - h`.

`udivrem<512, 256>()` ([`Div512.lean`](Div512.lean)) has the paths of `udivrem<256, 256>()` with
calls of `memset()` and `shl<9, 8>()` and the inlined normalization of the divisor and shift of the
remainder for the 3- and 4-word Knuth divisions. Each path keeps the frame of 160 bytes, a
predicate over the registers and the memory (`U512Frame`). After `memset()` the memory is
`memFill` outside the bytes that the later calls write, which gives the zero words above the ones
that a callee writes. `rv_subst` substitutes the names of the values of a run: `subst_vars` also
tries the other equations of the context, which took a minute in these. The counts of the words
of v and u meet at 54, and each of the 7 exits of the count of u tries the dispatch for each count
(`u512_exit`).

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
(`Reach.call_sub`). The code of a function that reads its data differs in each image in the
immediates of the address of the data, `auipc` and the `addi` or the load after it. Its
instructions with these immediates as parameters are `Gen.f_progAt`, and `Gen.p_image_f_in` states
them with the immediates of the image. The proof of `f` over any immediates, with the address of
the data that they give as an assumption, is a proof in every image, as `udivrem_by1.reach`. A
function `f` with calls that other functions call gets `Gen.f_progAt` too: the code of its image,
with the immediates of the data of all its functions as parameters (`udivrem_256_progAt`). For
this, an image that no other image holds has its function first and then the functions that it
calls, depth first, and the image of a function that another image holds has the order of that
image: the image of `internal::udivrem_knuth_normalized<4>()` is `submul()` and then the function,
as in the image of `udivrem<512, 256>()`, where `submul()` follows the 3-word instance, which calls
it too. `Reach.call_sub_at` calls a function that does not start its image. The instances of
`intx::wip` in `Api.cpp` get their specifications without the checks of their proofs, until they
are proved.

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
writable PMA region and not in the CLINT, HTIF or signature region, its 4-byte halves in a
readable one (`HalfOk`) and its bytes in a readable and writable one (`ByteOk`).
[`Mem4.lean`](Mem4.lean) proves that `lwu` of a half reads its 4 bytes, zero-extended, and
[`Mem1.lean`](Mem1.lean) that `lbu` reads a byte, zero-extended, and `sb` writes the low byte of a
register. A byte is accessed through the word of `A` that holds it (`a &&& ~~~7`). `EnvM.lean`
builds such an environment with 4 KiB of RAM, the stack at its end.

The code of clang calls `memset()` to zero more than 64 bytes. `Api.cpp` defines it with a loop of
`sb`, which clang does not turn into a call of itself (`no_builtin`), and points to it from
`intx::lib`: `rv_gen.py` generates its code as of an instance, and the images of its callers hold
it. [`Memset.lean`](Memset.lean) proves it by hand (`memset.reach`): it has no specification in
`intx.hpp`.

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

  This rendering is not necessary: [`../Hart.lean`](../Hart.lean) proves that the hart of the Sail
  model, `try_step` itself, runs the code as the proofs do (`hart_simM`). It fetches each
  instruction from the memory through the address translation and the PMP and PMA checks, takes
  no interrupt with `mstatus.MIE` clear, and counts the instruction in `minstret`; the stores do
  not overwrite the code. The specifications could state the runs of `try_step`, but they do not
  because of the cost: `try_step` imports `LeanRV64D.RvfiDii` of the model, whose build takes
  28 minutes and 13.3 GiB, and 50 minutes under a limit of 14 GiB: barely within the 16 GB runner
  of CI. The specifications would also
  assume more: the code in an executable region of the memory, outside the buffers, the
  interrupts off, and machine mode for the functions without memory. `lake build Hart` checks the
  proof; CI does not.
* The environment `Env`: every register of the model exists, no landing pad is expected, the M
  extension is enabled and the privilege level is machine, supervisor or user. For the functions
  with memory, `EnvM` and `WordOk` (above).
* The specifications in the documentation, and `rv_api.py`: the extraction of the comments, the
  binding of an instance to its function and the calling convention.
* The extraction of the machine code from the object file and the image by `rv_gen.py`.

Not covered: other compilers, other flags. The linking of the image is by `ld.lld` with the
linker script; its output is checked as the machine code is. The images link the `memset()` of
`Api.cpp`: a program links the one of its C library, which must set the bytes and keep the
registers as `memset.reach` states.

## Build

```sh
sudo apt install clang-21 lld g++-riscv64-linux-gnu
CXX=clang++-21 scripts/rv_build.sh
lake build IntxRV Checks
```
