import IntxRV.Gen.Api
import IntxRV.Arith
/-!
# `operator=` of `uint256` by `uint64_t`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Assigns the value v.
/// @post self = v
constexpr uint& operator=(uint64_t v) noexcept
```

`assign_256.spec` states it for the RV64 machine code of `assign_256` in `IntxRV/Api.cpp` (generated
in `IntxRV/Gen/Api.lean`, see `IntxRV/README.md`). The function stores v and three words 0.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 4000000

theorem assign_256.proof : assign_256.spec :=
  runsM_of_reach assign_256_decodes fun base ret _ hr _ x m hx1 hpre => by
    simp only [assign_256.pre, assign_256.bufs, Buf] at hpre ⊢
    simp (disch := decide) only [Regs.eq_get x] at hpre hx1 ⊢
    subst hx1
    refine Reach.start ?_
    rv_exec
    try rv_val
    simp only [update_aligned hr]
    refine Reach.refl ?_
    simp only [assign_256.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    simp (disch := decide) only [Regs.eq_get x]
    try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    try simp only [Defn] at *
    try subst_vars
    refine ⟨?_, ?_, ?_⟩
    · simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
        Nat.add_zero]
      simp (disch := first | bv_omega | fail) only [memWord_memStore_self, memWord_memStore_of_ne]
      have hz : (x.get 0#5).toNat = 0 := by
        rw [show (0#5 : BitVec 5) = 0 from rfl, Regs.get_zero]; rfl
      simp only [hz, Nat.mul_zero, Nat.add_zero]
      try simp only [List.foldr, toInt_emod_toNat, Nat.mul_zero, Nat.add_zero]
    · simp (disch := first | bv_omega | fail) only [unchangedExcept_memStore,
        unchangedExcept_refl]
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte, BitVec.ofNat_eq_ofNat]
      simp (disch := decide) only [Regs.eq_get x, and_self]

end IntxRV.Api
