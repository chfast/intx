import IntxRV.Gen.Api.neg_256
import IntxRV.Neg
/-!
# `operator-()` of `uint256`

The specification, from `include/intx/intx.hpp`:

```cpp
/// The negation modulo 2^N.
/// @post result = (2^N - self) % 2^N
constexpr uint operator-() const noexcept { return uint{} - *this; }
```

`neg_256.spec` states it for the RV64 machine code of `neg_256` in `IntxRV/Api.cpp` (generated in
`IntxRV/Gen/Api/`, see `IntxRV/README.md`). The function loads the words of x, subtracts them
from 0 with the borrows and stores the result: `neg4_words` (`IntxRV/Neg.lean`) gives its number
from the definitions of the values of the run.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 4000000

theorem neg_256.proof_of_decodes (hdec : neg_256.decodes) : neg_256.spec :=
  runsM_of_reach hdec fun base ret _ hr _ x m hx1 hpre => by
    simp only [neg_256.pre, neg_256.bufs, Buf, Disjoint] at hpre ⊢
    simp (disch := decide) only [Regs.eq_get x] at hpre hx1 ⊢
    subst hx1
    refine Reach.start ?_
    rv_exec
    rv_val
    simp only [update_aligned hr]
    refine Reach.refl ?_
    simp only [neg_256.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    simp (disch := decide) only [Regs.eq_get x]
    refine ⟨?_, ?_, ?_⟩
    · simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
        Nat.add_zero]
      simp (disch := first | bv_omega | fail) only [memWord_memStore_self, memWord_memStore_of_ne]
      rv_loads
      apply neg4_words
      all_goals assumption
    · simp (disch := first | bv_omega | fail) only [unchangedExcept_memStore,
        unchangedExcept_refl]
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte, BitVec.ofNat_eq_ofNat]
      simp (disch := decide) only [Regs.eq_get x, and_self]

end IntxRV.Api
