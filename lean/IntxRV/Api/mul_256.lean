import IntxRV.Gen.Api.mul_256
import IntxRV.Mul256
/-!
# `operator*` of `uint256`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Multiplication implementation using word access
/// and discarding the high part of the result product.
///
/// The words of y form the outer loop. In chained products pass the previous product as y:
/// each row then needs only one of its words, so consecutive products overlap.
/// @post result = x * y % 2^N
friend constexpr uint operator*(const uint& x, const uint& y) noexcept
```

`mul_256.spec` states it for the RV64 machine code of `mul_256` in `IntxRV/Api.cpp` (generated in
`IntxRV/Gen/Api/`, see `IntxRV/README.md`). The function zeroes the result and runs the loops of
`operator*`: the rows `y[j] * x` with `mac()` to the words below the top one, and the top word.
`rv_exec_loop` unrolls them, deciding the branches on the counters and on the pointers to the words
of `x`. `rv_cse` gives the words of `x` that each row loads again the names of the first loads, and
`mul256_words` (`IntxRV/Mul256.lean`) gives the product modulo `2^256` from the definitions of the
values of the run.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

theorem mul_256.proof_of_decodes (hdec : mul_256.decodes) : mul_256.spec :=
  runsM_of_reach hdec fun base ret _ hr _ x m hx1 hpre => by
    simp only [mul_256.pre, mul_256.bufs, Buf, Disjoint] at hpre ⊢
    simp (disch := decide) only [Regs.eq_get x] at hpre hx1 ⊢
    subst hx1
    refine Reach.start ?_
    rv_exec_loop
    rv_copies
    rv_val
    simp only [update_aligned hr]
    refine Reach.refl ?_
    simp only [mul_256.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    simp (disch := decide) only [Regs.eq_get x]
    refine ⟨?_, ?_, ?_⟩
    · simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
        Nat.add_zero]
      simp (disch := first | bv_omega | fail) only [memWord_memStore_self, memWord_memStore_of_ne]
      rv_cse
      rv_loads
      apply mul256_words
      all_goals assumption
    · simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore,
        unchangedExcept2_refl]
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte, BitVec.ofNat_eq_ofNat,
        true_and]
      simp (disch := decide) only [Regs.eq_get x, and_self]

end IntxRV.Api
