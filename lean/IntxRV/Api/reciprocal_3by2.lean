import IntxRV.Gen.Api
import IntxRV.Arith
import IntxRV.EnvImage
import IntxRV.ApiModel
import IntxRV.Reciprocal
import IntxRV.Recip3
/-!
# `reciprocal_3by2()`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Computes the reciprocal (2^192 - 1) / d - 2^64 for normalized d.
/// @pre 2^127 ≤ d
/// @post result = (2^192 - 1) / d - 2^64
constexpr uint64_t reciprocal_3by2(uint128 d) noexcept
```

`reciprocal_3by2.spec` states it for the RV64 machine code of `reciprocal_3by2` in `IntxRV/Api.cpp`
(generated in `IntxRV/Gen/Api.lean`, see `IntxRV/README.md`). The function reads the entry of
`RECIPROCAL_TABLE` for the top 9 bits of the top word `d1` (two `lwu` from the data of the image,
as `reciprocal_2by1()`) and computes the reciprocal with the Newton steps for `d1`, the step against
the whole divisor and the exact correction of `internal::reciprocal()` for `uint128`. `rv_exec`
runs its 57 instructions, without branches. `recip3BV_spec` (`IntxRV/Recip3.lean`) gives the
reciprocal of the words that the code computes, and `rv_fold` writes it with the names of the run.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

theorem reciprocal_3by2.proof : reciprocal_3by2.spec := by
  apply runsI_of_reach reciprocal_3by2_image_decodes
  intro base ret hb hr hc hl hw x m hx1 hbufs hhold hpre
  simp only [reciprocal_3by2.pre, reciprocal_3by2.bufs, List.nil_append] at hpre ⊢
  simp (disch := decide) only [Regs.eq_get x] at hpre hx1 ⊢
  simp only [reciprocal_3by2_entry, show reciprocal_3by2_image_data.length = 256 from rfl,
    show reciprocal_3by2_image_dataOff = 232 from rfl] at *
  have hd1 : 2 ^ 63 ≤ (x.get 11#5).toNat := by have := (x.get 10#5).isLt; omega
  have hi : (x.get 11#5).toNat / 2 ^ 55 - 256 < 256 := by have := (x.get 11#5).isLt; omega
  rv_exec
  refine Reach.step (by decide) rfl ?_
  simp only [StepGoal, Nat.reduceAdd]
  simp only [Defn] at *
  subst_vars
  rv_val
  rw [table_addr3 _ _ hd1]
  refine ⟨Or.inl (mem_bufWords hi), fun wL hwL => ?_⟩
  rw [memHalf_lo,
    holdsData_get hhold (by rw [show reciprocal_3by2_image_data.length = 256 from rfl]; exact hi),
    ← List.getD_eq_getElem _ 0, reciprocal_3by2_image_data_eq, image_data_get _ hi] at hwL
  rv_exec
  refine Reach.step (by decide) rfl ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  rw [table_addr3_hi _ _ hd1]
  have hnw : (base + BitVec.ofNat 64 232 + BitVec.ofNat 64 (8 * ((x.get 11#5).toNat / 2 ^ 55 - 256))
      + 4).toNat = (base + BitVec.ofNat 64 232 +
        BitVec.ofNat 64 (8 * ((x.get 11#5).toNat / 2 ^ 55 - 256))).toNat + 4 := by bv_omega
  refine ⟨Or.inr (by
    rw [show ∀ a : BitVec 64, a + 4 - 4#64 = a from fun a => by bv_omega]; exact mem_bufWords hi),
    fun wH hwH => ?_⟩
  rw [hnw, memHalf_hi,
    holdsData_get hhold (by rw [show reciprocal_3by2_image_data.length = 256 from rfl]; exact hi),
    ← List.getD_eq_getElem _ 0, reciprocal_3by2_image_data_eq, image_data_get _ hi] at hwH
  rv_exec
  rv_val
  simp only [update_aligned hr]
  refine Reach.refl ?_
  simp only [reciprocal_3by2.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  simp (disch := decide) only [Regs.eq_get x]
  refine ⟨?_, ?_⟩
  rotate_left
  · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte, BitVec.ofNat_eq_ofNat]
    simp (disch := decide) only [Regs.eq_get x, and_self]
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  -- The table entry: v0 * v0 in the low half, 2^11 * v0 - 1 in the high half.
  have hv0 := Intx.Model.reciprocal_table_entry _ hi
  rw [show (x.get 11#5).toNat / 2 ^ 55 - 256 + 256 = (x.get 11#5).toNat / 2 ^ 55 by omega]
    at hv0 hwL hwH
  obtain ⟨-, hv0b, -, -⟩ := hv0
  have hVV := Nat.mul_le_mul hv0b hv0b
  simp only [Defn] at hwL hwH
  have hL : wL.toNat = 523520 / ((x.get 11#5).toNat / 2 ^ 55) *
      (523520 / ((x.get 11#5).toNat / 2 ^ 55)) := by
    rw [hwL]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  have hH : wH.toNat = 2 ^ 11 * (523520 / ((x.get 11#5).toNat / 2 ^ 55)) - 1 := by
    rw [hwH]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    omega
  have hs := recip3BV_spec (x.get 10#5) (x.get 11#5) wL wH hd1 hL hH
  simp only [recip3BV] at hs
  rv_fold hs
  exact hs

theorem reciprocal_3by2.nonvacuous :
    NonVacuousI reciprocal_3by2_image_code reciprocal_3by2_image_data
      reciprocal_3by2_image_dataOff reciprocal_3by2.bufs reciprocal_3by2.pre :=
  nonVacuousI_of (fun i => if i = 11#5 then 0x8000000000000000#64 else 0) (by decide) (by decide)
    (by decide) (by decide) (by simp [reciprocal_3by2.bufs])
    (fun _ => by simp (config := { decide := true }) [reciprocal_3by2.pre])

end IntxRV.Api
