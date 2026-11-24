import IntxRV.DivTop1
/-!
# `internal::udivrem_top1()` of `uint256` by the top word 3

The specification, from `include/intx/intx.hpp`:

```cpp
/// Divides u by v when the quotient fits in a single word: v has TOP + 1 significant words
/// and u has at most one more significant word, which is less than v[TOP].
///
/// The quotient is estimated from the top word of the normalized divisor with 2/1 division
/// and corrected with the remainder computed on the original (not normalized) operands.
/// The word v[TOP] must not be zero.
/// @pre 2^(64 * TOP) ≤ v
/// @pre v < 2^(64 * (TOP + 1))
/// @pre u / 2^(64 * (TOP + 1)) < v / 2^(64 * TOP)
/// @post result.quot = u / v
/// @post result.rem = u % v
template <size_t TOP, unsigned M, unsigned N>
constexpr div_result<uint<M>, uint<N>> udivrem_top1(const uint<M>& u, const uint<N>& v) noexcept
```

`udivrem_top1_3.spec` states it for the RV64 machine code of `udivrem_top1_3` in
`IntxRV/Api.cpp`, the instance that `udivrem<256, 256>()` calls for a divisor with its top word
set. The function returns u as the remainder when u[3] < v[3]. Otherwise it normalizes the top
words of v with the count of the leading zeros of v[3], computes the reciprocal of the top word
with the table of the image (`recip2BV_spec`), estimates the quotient with the inlined
`udivrem_2by1()` (`div2by1BVc_spec`), not less than the quotient (`top1_est`), subtracts q * v
from u (`submul4_words`) and runs the correction loop while the borrow is not 0 (`top1_3_tail`,
in `IntxRV/DivTop1.lean`). It saves s0 in a frame of 16 bytes. `udivrem_top1_3.reach` is the run
for any immediates of the address of the table (`udivrem_top1_3_progAt`).
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- The run of `udivrem_top1<3, 256, 256>()` for any immediates `hi` and `lo` of the address `T`
of the table of the reciprocal, with the frame of 16 bytes below sp outside the table. -/
theorem udivrem_top1_3.reach (hi : BitVec 20) (lo : BitVec 12) (base T : BitVec 64) (x : Regs)
    (m : Mem) (hT : pcAt base 75 + ((hi ++ 0x000#12).signExtend 64 + lo.signExtend 64) = T)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64) (hr : x.get 1#5 &&& 3 = 0)
    (hstk : (x.get 2#5 - 16#64).toNat + 16 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 2#5 - 16#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hpre : udivrem_top1_3.pre x m) :
    Reach (udivrem_top1_3.bufs x ++ bufWords T 256) (udivrem_top1_3_progAt hi lo) base
      (pcAt base 0) x m (x.get 1#5) (udivrem_top1_3.post x m) := by
  have hpre0 := hpre
  simp only [udivrem_top1_3.pre, udivrem_top1_3.bufs, Buf] at hpre ⊢
  simp (disch := decide) only [Regs.eq_get x] at hpre ⊢
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr, hv1, hv2,
    hu3⟩ := hpre
  simp only [Disjoint] at hdru hdsu hdsv
  have hv3 := top4_ne_zero m (x.get 12#5) hv1
  have hv3' : (memWord m (x.get 12#5 + 24#64).toNat).toNat ≠ 0 :=
    fun h => hv3 (BitVec.eq_of_toNat_eq (by simpa using h))
  rv_exec_cut 127 176
  -- u[3] < v[3]: the quotient 0 and the remainder u.
  all_goals first
    | (fail_if_success rv_not_at 80; skip)
    | (rv_val
       rw [update_aligned hr]
       refine Reach.refl ?_
       simp only [udivrem_top1_3.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
         forall_eq_or_imp, forall_eq]
       simp (disch := decide) only [Regs.eq_get x]
       simp only [zopz0zKzJ_u_eq, decide_eq_false_iff_not, BitVec.le_def, not_le] at *
       have hlt := words_lt_of_top4 m (x.get 11#5) (x.get 12#5)
       rv_fold hlt
       have hUV := hlt (by assumption)
       refine ⟨?_, ?_, ?_, ?_⟩
       · rw [(words_ret8 m (x.get 10#5) _ _ _ _ _ 0 rfl hrn _ rfl).1, Nat.div_eq_of_lt hUV]; rfl
       · rw [(words_ret8 m (x.get 10#5) _ _ _ _ _ 0 rfl hrn _ rfl).2.1, Nat.mod_eq_of_lt hUV]
         simp only [Defn] at *
         subst_vars
         simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
           Nat.add_zero]
       · exact unchangedExcept2_of _ _ (words_ret8 m (x.get 10#5) _ _ _ _ _ 0 rfl hrn _ rfl).2.2
       · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
         refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
         exact Regs.eq_get x (by decide))
  -- The words v[3], v[2], u[3] and u[2] by names.
  all_goals
    set v3 := memWord m (x.get 12#5 + 24#64).toNat with hv3e
    set v2 := memWord m (x.get 12#5 + 16#64).toNat with hv2e
    set u3 := memWord m (x.get 11#5 + 24#64).toNat with hu3e
    set u2 := memWord m (x.get 11#5 + 16#64).toNat with hu2e
    rv_copies
    -- The count of the leading zeros of v[3], S.
    have hs := clz_ite v3
    rw [if_neg hv3, swarClz_expand, smear_expand] at hs
    rv_fold hs
    rv_fold hs
    subst hs
    have hL64 : v3.toNat.log2 < 64 := (Nat.log2_lt hv3').mpr v3.isLt
    have hSt : (BitVec.ofNat 64 (63 - v3.toNat.log2)).toNat = 63 - v3.toNat.log2 := ofNat_S_toNat (by omega)
    have hS1 : v3.toNat * 2 ^ (63 - v3.toNat.log2) < 2 ^ 64 := by
      have := Nat.lt_log2_self (n := v3.toNat)
      calc v3.toNat * 2 ^ (63 - v3.toNat.log2)
          < 2 ^ (v3.toNat.log2 + 1) * 2 ^ (63 - v3.toNat.log2) :=
            Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos _)
        _ = 2 ^ 64 := by rw [← pow_add]; congr 1; omega
    have hS63 : 2 ^ 63 ≤ v3.toNat * 2 ^ (63 - v3.toNat.log2) := by
      have := Nat.log2_self_le hv3'
      calc 2 ^ 63 = 2 ^ v3.toNat.log2 * 2 ^ (63 - v3.toNat.log2) := by
            rw [← pow_add]; congr 1; omega
        _ ≤ _ := Nat.mul_le_mul_right _ this
  -- The normalized top word vt of v, the funnel shift of v[3] and v[2] for s ≠ 0.
  all_goals first
    | (rv_lacks ¬BitVec.ofNat 64 (63 - v3.toNat.log2) = 0#64; skip)
    | (have h1 := toNat_fshl_code v3 v2 (BitVec.ofNat 64 (63 - v3.toNat.log2)) (by rw [hSt]; omega)
       rv_fold h1
       rv_fold h1
       rw [hSt] at h1
       have hdn63 := norm2_hi (d0 := v2.toNat) (by omega) v2.isLt hS1 hS63
       rw [← h1] at hdn63)
  all_goals first
    | (rv_lacks BitVec.ofNat 64 (63 - v3.toNat.log2) = 0#64; skip)
    | (rv_get hz : BitVec.ofNat 64 (63 - v3.toNat.log2) = 0#64
       have hS0 := ofNat_S_eq (by omega) hz
       have hdn63 : 2 ^ 63 ≤ v3.toNat := by rw [hS0] at hS63; simpa using hS63)
  -- The table entry of vt: the low half.
  all_goals
    simp only [hT] at *
    refine Reach.step (by decide) rfl ?_
    simp only [StepGoal, Nat.reduceAdd]
    rv_val
    have ha := table_addr_by1 _ T hdn63
    rv_fold ha
    have hix := index_lt_256 hdn63
    rw [ha]
    refine ⟨Or.inl (List.mem_append_right _ (mem_bufWords hix)), fun wL hwL => ?_⟩
    try simp (disch := bv_omega) only [memHalf_memStore_of_ne] at hwL
    rw [memHalf_lo, holdsData_get hhold
        (by rw [show reciprocal_2by1_image_data.length = 256 from rfl]; exact hix),
      ← List.getD_eq_getElem _ 0, image_data_get _ hix] at hwL
    rv_exec_cut 127 176
    -- The high half.
    refine Reach.step (by decide) rfl ?_
    simp only [StepGoal, Nat.reduceAdd]
    rv_val
    have hah := table_addr_by1_hi _ T hdn63
    rv_fold hah
    rw [hah]
    refine ⟨Or.inr (by
      rw [show ∀ a : BitVec 64, a + 4 - 4#64 = a from fun a => by bv_omega]
      exact List.mem_append_right _ (mem_bufWords hix)), fun wH hwH => ?_⟩
    try simp (disch := bv_omega) only [memHalf_memStore_of_ne] at hwH
    rw [table_entry_add4 T hdn63 hw, memHalf_hi, holdsData_get hhold
        (by rw [show reciprocal_2by1_image_data.length = 256 from rfl]; exact hix),
      ← List.getD_eq_getElem _ 0, image_data_get _ hix] at hwH
    rv_exec_cut 127 176
  -- The reciprocal of vt.
  all_goals
    rv_cse
    obtain ⟨hL, hH⟩ := table_LH hdn63 hwL hwH
    have hv := recip2BV_spec _ wL wH hdn63 hL hH
    simp only [recip2BV] at hv
    rv_fold hv
    rv_fold hv
  all_goals rv_exec_cut 176
  all_goals
    rv_copies
    try simp only [zopz0zI_u_eq, decide_eq_true_eq, decide_eq_false_iff_not] at *
  -- The quotient estimate: s ≠ 0.
  all_goals first
    | (rv_lacks ¬BitVec.ofNat 64 (63 - v3.toNat.log2) = 0#64; skip)
    | (rv_get hne : ¬BitVec.ofNat 64 (63 - v3.toNat.log2) = 0#64
       have hS0 := ofNat_S_ne (by omega) hne
       have hs := div2by1BVc_spec (u3 >>> ((BitVec.signExtend 64 (BitVec.setWidth 32 0#64 -
         BitVec.setWidth 32 (BitVec.ofNat 64 (63 - v3.toNat.log2)))).toNat % 64))
         ((u3 <<< ((BitVec.ofNat 64 (63 - v3.toNat.log2)).toNat % 64)) |||
           ((u2 >>> 1) >>> ((BitVec.ofNat 64 (63 - v3.toNat.log2) ^^^
             18446744073709551615#64).toNat % 64))) _ _ hdn63
         (top_hi_lt hdn63 (by omega) hS0) hv
       simp only [div2by1BVc] at hs
       rv_fold hs
       rv_fold hs
       try simp (disch := assumption) only [if_pos, if_neg] at hs
       rv_fold hs
       try (simp only [BitVec.add_assoc] at hs; rv_fold hs)
       have hhi : (u3 >>> ((BitVec.signExtend 64 (BitVec.setWidth 32 0#64 - BitVec.setWidth 32
           (BitVec.ofNat 64 (63 - v3.toNat.log2)))).toNat % 64)).toNat =
           u3.toNat / 2 ^ (64 - (63 - v3.toNat.log2)) := by
         rw [negw_shift _ (by omega) hS0, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
       have hlo := toNat_fshl_code u3 u2 (BitVec.ofNat 64 (63 - v3.toNat.log2)) (by rw [hSt]; omega)
       rv_fold hhi
       rv_fold hhi
       rv_fold hlo
       rv_fold hlo
       rw [hSt] at hlo
       rw [hhi, hlo, top1_ut _ _ _ (by omega) u2.isLt, h1,
         Nat.mod_eq_of_lt (fshl_lt (by omega) v2.isLt hS1)] at hs)
  -- s = 0.
  all_goals first
    | (rv_lacks BitVec.ofNat 64 (63 - v3.toNat.log2) = 0#64; skip)
    | (have hs := div2by1BVc_spec (BitVec.ofNat 64 (63 - v3.toNat.log2)) u3 _ _ hdn63
         (by rw [hz]; simp; omega) hv
       simp only [div2by1BVc] at hs
       rv_fold hs
       rv_fold hs
       try simp (disch := assumption) only [if_pos, if_neg] at hs
       rv_fold hs
       try (simp only [BitVec.add_assoc] at hs; rv_fold hs)
       rw [hz] at hs
       have e1 : u3.toNat = u3.toNat * 2 ^ (63 - v3.toNat.log2) +
           u2.toNat / 2 ^ (64 - (63 - v3.toNat.log2)) := by
         rw [hS0, Nat.div_eq_of_lt u2.isLt]; simp
       have e2 : v3.toNat = v3.toNat * 2 ^ (63 - v3.toNat.log2) +
           v2.toNat / 2 ^ (64 - (63 - v3.toNat.log2)) := by
         rw [hS0, Nat.div_eq_of_lt v2.isLt]; simp
       simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.mul_zero, Nat.zero_add] at hs
       have hN : u3.toNat / v3.toNat = (u3.toNat * 2 ^ (63 - v3.toNat.log2) +
           u2.toNat / 2 ^ (64 - (63 - v3.toNat.log2))) /
           (v3.toNat * 2 ^ (63 - v3.toNat.log2) + v2.toNat / 2 ^ (64 - (63 - v3.toNat.log2))) := by
         rw [← e1, ← e2]
       rw [hN] at hs)
  -- The estimate is not less than the quotient.
  all_goals
    have hest := top1_est (U := words m (x.get 11#5) 4) (V := words m (x.get 12#5) 4) (by omega)
      (words4_lt_top2 m (x.get 11#5)) (words4_ge_top2 m (x.get 12#5))
      (Nat.lt_of_lt_of_le (by norm_num) (Nat.le_add_right_of_le hS63)) hs
  -- The submul() and the correction.
  all_goals
    refine top1_3_tail base T x m hpre0 hr _ _ ?_ ?_ ?_ (unchangedExcept2_s0 _ _ _ _ hsn) ?_ ?_ ?_
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · intro i hi
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] <;>
        exact (Regs.eq_get x (by decide)).symm
    · simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
        Nat.add_zero]
      rv_loads
      rfl
    · simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
        Nat.add_zero]
      rv_loads
      try rw [← hu2e]
      try rw [← hu3e]
      apply submul4_words
      all_goals assumption
    · exact hest

theorem udivrem_top1_3.proof : udivrem_top1_3.spec := by
  apply runsI_of_reach udivrem_top1_3_image_decodes
  intro base ret _ hr _ _ hw x m hx1 hbufs hhold hpre
  rw [show udivrem_top1_3_image_dataOff = 840 from rfl] at hw hhold hbufs ⊢
  rw [show udivrem_top1_3_image_data.length = 256 from rfl] at hw hbufs ⊢
  have hx : x.get 1#5 = ret := by rw [← Regs.eq_get x (by decide)]; exact hx1
  have hpre' := hpre
  simp only [udivrem_top1_3.pre, Buf] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  have hst := frame16_outside (x 2#5) base 840 (8 * 256)
    (hbufs _ (List.mem_append_right _ (mem_bufWords_zero (by norm_num))))
    (hbufs _ (List.mem_append_right _ (mem_bufWords (by norm_num))))
    (by rw [Regs.eq_get x (by decide)]; exact hpre'.2.2.2.2.2.1.2) (by norm_num)
  rw [Regs.eq_get x (by decide)] at hst
  rw [show udivrem_top1_3_entry = udivrem_top1_3_image_udivrem_top1_3_offset from rfl, dataWords,
    ← hx]
  refine Reach.lift udivrem_top1_3_image_udivrem_top1_3_in (by decide) ?_
  have hT : (base + BitVec.ofNat 64 840).toNat = base.toNat + 840 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have h := udivrem_top1_3.reach 0x0#20 0x21c#12
    (pcAt base udivrem_top1_3_image_udivrem_top1_3_offset) _ x m
    (by simp only [udivrem_top1_3_image_udivrem_top1_3_offset, pcAt, BitVec.reduceAppend,
      BitVec.reduceSignExtend]; bv_omega)
    (by rw [hT]; omega) (hx ▸ hr) (by rw [hT]; omega) hhold hpre
  rwa [pcAt_zero] at h

/-- The registers of the nonvacuous instance: the result, u = 2^192 and v = 2^192 above the data,
and the frame below sp. -/
theorem udivrem_top1_3.nonvacuous :
    NonVacuousI udivrem_top1_3_image_code udivrem_top1_3_image_data udivrem_top1_3_image_dataOff
      udivrem_top1_3.bufs udivrem_top1_3.pre :=
  nonVacuousI_of_args (fun i => if i = 10#5 then 0x80000C00#64 else if i = 11#5 then 0x80000C40#64
      else if i = 12#5 then 0x80000C60#64 else if i = 2#5 then 0x80000CA0#64 else 0)
    0x80000C40 [0, 0, 0, 1, 0, 0, 0, 1]
    (by decide) (by decide) (by decide) (by decide)
    (by rw [show udivrem_top1_3_image_dataOff = 840 from rfl,
          show udivrem_top1_3_image_data.length = 256 from rfl]
        simp only [udivrem_top1_3.bufs, ↓reduceIte, BitVec.reduceEq, BitVec.reduceSub, bufWords,
          List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq]
        repeat' apply And.intro
        all_goals decide)
    (by decide)
    (fun m => by
      simp only [udivrem_top1_3.pre, Buf, Disjoint, words, ↓reduceIte, BitVec.reduceEq,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, BitVec.toNat_ofNat,
        Nat.reducePow, Nat.reduceMod, Nat.mul_zero, Nat.add_zero]
      simp (disch := decide) only [memWord_storeWords_getD]
      decide)

end IntxRV.Api
