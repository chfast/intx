import IntxRV.Gen.Api
import IntxRV.Arith
import IntxRV.Conv
/-!
# `operator bool` of `uint256`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Tests that the value is not 0.
/// @post result <-> self ≠ 0
constexpr explicit operator bool() const noexcept { return *this != uint{}; }
```

`bool_256.spec` states it for the RV64 machine code of `bool_256` in `IntxRV/Api.cpp` (generated in
`IntxRV/Gen/Api.lean`, see `IntxRV/README.md`). The function ors the 4 words and compares the or
with 0 (`sltu`); `words4_eq_zero_iff` (`IntxRV/Conv.lean`) gives the number 0.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 4000000

theorem bool_256.proof : bool_256.spec :=
  runsM_of_reach bool_256_decodes fun base ret _ hr _ x m hx1 hpre => by
    simp only [bool_256.pre, bool_256.bufs, Buf] at hpre ⊢
    simp (disch := decide) only [Regs.eq_get x] at hpre hx1 ⊢
    subst hx1
    refine Reach.start ?_
    rv_exec
    rv_val
    simp only [update_aligned hr]
    refine Reach.refl ?_
    simp only [bool_256.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    simp (disch := decide) only [Regs.eq_get x]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    simp only [Defn] at *
    subst_vars
    simp only [BitVec.ofNat_eq_ofNat] at *
    refine ⟨?_, ite_cases _, trivial, ?_⟩
    · rw [decide_eq_true_eq, ite_eq_one, zero_lt_iff_ne_zero]
      simp only [words, Nat.mul_zero, Nat.add_zero, BitVec.add_assoc, BitVec.reduceAdd, ne_eq,
        words4_eq_zero_iff, BitVec.or_eq_zero_iff]
      tauto
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
      simp (disch := decide) only [Regs.eq_get x, and_self]

end IntxRV.Api
