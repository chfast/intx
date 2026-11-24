import IntxRV.Gen.Api
import IntxRV.Mul256
import IntxRV.Loop
/-!
# `operator*=` of `uint256`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Multiplies by y modulo 2^N.
/// @post self = old(self) * y % 2 ^ N
/// @note FV: not proved for x *= x.
constexpr uint& operator*=(const uint& y) noexcept
```

`mul_assign_256.spec` states it for the RV64 machine code of `mul_assign_256` in `IntxRV/Api.cpp`
(generated in `IntxRV/Gen/Api.lean`, see `IntxRV/README.md`). The function multiplies y by the
object as `operator*` does, its two loops into a temporary in its frame, and copies the temporary to
the object: as for `operator*` (`IntxRV/Api/mul_256.lean`), `rv_exec_loop` unrolls the loops and
`mul256_words` (`IntxRV/Mul256.lean`) gives the product modulo 2^256 of the words that the run
stores.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem mul_assign_256.proof : mul_assign_256.spec :=
  runsM_of_reach mul_assign_256_decodes fun base ret _ hr _ x m hx1 hpre => by
    simp only [mul_assign_256.pre, mul_assign_256.bufs, Buf, Disjoint] at hpre ⊢
    simp (disch := decide) only [Regs.eq_get x] at hpre hx1 ⊢
    subst hx1
    refine Reach.start ?_
    rv_exec_loop
    rv_copies
    rv_val
    simp only [update_aligned hr]
    refine Reach.refl ?_
    simp only [mul_assign_256.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    simp (disch := decide) only [Regs.eq_get x]
    refine ⟨?_, ?_, ?_⟩
    · simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
        Nat.add_zero]
      simp (disch := first | bv_omega | fail) only [memWord_memStore_self, memWord_memStore_of_ne]
      rv_cse
      rv_loads
      conv => rhs; arg 1; rw [Nat.mul_comm]
      apply mul256_words
      all_goals assumption
    · simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore,
        unchangedExcept2_refl]
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte, BitVec.ofNat_eq_ofNat,
        true_and]
      simp (disch := decide) only [Regs.eq_get x, and_self]

end IntxRV.Api
