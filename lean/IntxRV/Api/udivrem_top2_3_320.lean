import IntxRV.DivTop2_320
/-!
# `internal::udivrem_top2()` of `uint320` by `uint256`, the top word 3

The specification, from `include/intx/intx.hpp`:

```cpp
/// Divides u by v when the quotient fits in two words: v has TOP significant words
/// and u has one more word, or two more words with the top one less than v[TOP - 1].
/// With EQUAL (TOP 3 only) the top word of u may also equal v[TOP - 1]: the quotient has then
/// up to 129 bits.
///
/// The quotient is estimated from the top 2 words of the normalized divisor with two 3/2
/// divisions and corrected with the remainder, computed from the remainder of the 3/2 divisions
/// and the low words of the original (not normalized) operands.
/// The word v[TOP - 1] must not be zero.
/// @pre 2^(64 * (TOP - 1)) ≤ v
/// @pre v < 2^(64 * TOP)
/// @pre u / 2^(64 * (TOP + 1)) < v / 2^(64 * (TOP - 1)) + EQUAL
/// @post result.quot = u / v
/// @post result.rem = u % v
template <size_t TOP, bool EQUAL = false, unsigned M, unsigned N>
constexpr div_result<uint<M>, uint<N>> udivrem_top2(const uint<M>& u, const uint<N>& v) noexcept
```

`udivrem_top2_3_320.spec` states it for the RV64 machine code of `udivrem_top2_3_320` in
`IntxRV/Api.cpp`, the instance that `udivrem<320, 256>()` calls for a divisor of 3 words when the
quotient may have two words. The numerator has the word u[4] above the divisor, less than v[2]
(`top2_320_ue`). The function normalizes the top words of u and v with the count of the leading
zeros of v[2], with the funnel shift of u[4] and u[3] for the top word (`norm5_words`); the two
paths meet at 81 (`top2_320_main`). From there the code is that of the instance of `uint256`
(`IntxRV/Api/udivrem_top2_3.lean`), with the block lemmas of `IntxRV/DivTop2_320.lean`. It saves s0
to s3 in a frame of 32 bytes. `udivrem_top2_3_320.reach` is the run for any immediates of the
address of the table.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- The run of `udivrem_top2<3>()` of `uint320` from 81, where the paths of the normalization meet:
the normalized top words of v in `a6:a7` and of u in `t2:a1:t3:t1`, the shift in a4. -/
theorem top2_320_main (hi : BitVec 20) (lo : BitVec 12) (base T : BitVec 64) (x : Regs)
    (m : Mem) (hT : pcAt base 87 + ((hi ++ 0x000#12).signExtend 64 + lo.signExtend 64) = T)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64) (hr : x.get 1#5 &&& 3 = 0)
    (hstk : (x.get 2#5 - 32#64).toNat + 32 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 2#5 - 32#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hpre : udivrem_top2_3_320.pre x m)
    (x' : Regs) (h0 : x' 0#5 = x 0#5)
    (hfr : ∀ r, r ∉ [5#5, 6#5, 7#5, 11#5, 13#5, 14#5, 15#5, 16#5, 17#5, 28#5, 29#5, 30#5, 31#5] →
      x' r = x r)
    (hS : (x' 14#5).toNat < 64) (h15 : x' 15#5 = x' 14#5 ^^^ 18446744073709551615#64)
    (hv0 : x' 13#5 = memWord m (x.get 12#5).toNat) (hu0 : x' 5#5 = memWord m (x.get 11#5).toNat)
    (hDw : (x' 17#5).toNat + 2 ^ 64 * (x' 16#5).toNat =
      words m (x.get 12#5) 4 / 2 ^ (64 - (x' 14#5).toNat))
    (hd63 : 2 ^ 63 ≤ (x' 16#5).toNat)
    (hTw : (x' 6#5).toNat + 2 ^ 64 * ((x' 28#5).toNat + 2 ^ 64 * ((x' 11#5).toNat +
      2 ^ 64 * (x' 7#5).toNat)) = words m (x.get 11#5) 5 / 2 ^ (64 - (x' 14#5).toNat))
    (hT3 : (x' 7#5).toNat < (x' 16#5).toNat) :
    Reach (bufWords (x.get 11#5) 5 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 9 ++
        bufWords (x.get 2#5 - 32#64) 4 ++ bufWords T 256) (udivrem_top2_3_320_progAt hi lo) base
      (pcAt base 81) x' m (x.get 1#5) (udivrem_top2_3_320.post x m) := by
  rw [regs_eq_sets x x' _ h0 hfr]
  simp only [setRegs]
  have hpre0 := hpre
  simp only [udivrem_top2_3_320.pre, Buf] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr, hv1, hv2,
    hu3⟩ := hpre
  rv_exec_cut 142
  -- The table entry of vt: the low half.
  all_goals
    simp only [hT] at *
    refine Reach.step (by decide) (by rv_fetch) ?_
    simp only [StepGoal, Nat.reduceAdd]
    rv_val
    have ha := table_addr_by1 _ T hd63
    rv_fold ha
    have hix := index_lt_256 hd63
    rw [ha]
    refine ⟨Or.inl (List.mem_append_right _ (mem_bufWords hix)), fun wL hwL => ?_⟩
    try simp (disch := bv_omega) only [memHalf_memStore_of_ne] at hwL
    rw [memHalf_lo, holdsData_get hhold
        (by rw [show reciprocal_2by1_image_data.length = 256 from rfl]; exact hix),
      ← List.getD_eq_getElem _ 0, image_data_get _ hix] at hwL
    rv_exec_cut 142
    -- The high half.
    refine Reach.step (by decide) (by rv_fetch) ?_
    simp only [StepGoal, Nat.reduceAdd]
    rv_val
    have hah := table_addr_by1_hi _ T hd63
    rv_fold hah
    rw [hah]
    refine ⟨Or.inr (by
      rw [show ∀ a : BitVec 64, a + 4 - 4#64 = a from fun a => by bv_omega]
      exact List.mem_append_right _ (mem_bufWords hix)), fun wH hwH => ?_⟩
    try simp (disch := bv_omega) only [memHalf_memStore_of_ne] at hwH
    rw [table_entry_add4 T hd63 hw, memHalf_hi, holdsData_get hhold
        (by rw [show reciprocal_2by1_image_data.length = 256 from rfl]; exact hix),
      ← List.getD_eq_getElem _ 0, image_data_get _ hix] at hwH
    rv_exec_cut 142
  -- The reciprocal of vt.
  all_goals
    rv_cse
    obtain ⟨hL, hH⟩ := table_LH hd63 hwL hwH
    have hv := recip3BV_spec (x' 17#5) (x' 16#5) wL wH hd63 hL hH
    simp only [recip3BV] at hv
    rw [show (0 : BitVec 64) = 0#64 from rfl] at hv
    rv_fold hv
    rv_fold hv
  -- The first division of the top digits t2:a1:t3.
  all_goals
    refine Reach.trans (top2_320_div_top base _ _ ?_ ?_ ?_) ?_
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      omega
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      have := (x' 11#5).isLt
      omega
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      exact hv
    intro x'' m'' ⟨hm, h30, hq1, hr1, h00, hfr'⟩
    subst hm
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte] at hq1 hr1 h30
    have h30' : x'' 30#5 = 0#64 := by rw [Regs.eq_get x'' (by decide)]; exact h30
    rw [regs_eq_sets _ x'' _ h00 hfr']
    simp only [setRegs]
    rw [← Regs.eq_get x'' (by decide : (11#5 : BitVec 5) ≠ 0)] at hq1
    rw [← Regs.eq_get x'' (by decide : (7#5 : BitVec 5) ≠ 0),
      ← Regs.eq_get x'' (by decide : (28#5 : BitVec 5) ≠ 0)] at hr1
    have hD1 : 2 ^ 127 ≤ (x' 17#5).toNat + 2 ^ 64 * (x' 16#5).toNat := by omega
    have hX : (x'' 28#5).toNat * 2 ^ 64 + (x'' 7#5).toNat <
        (x' 17#5).toNat + 2 ^ 64 * (x' 16#5).toNat := by
      have := Nat.mod_lt ((x' 7#5).toNat * 2 ^ 128 + (x' 11#5).toNat * 2 ^ 64 + (x' 28#5).toNat)
        (show 0 < (x' 17#5).toNat + 2 ^ 64 * (x' 16#5).toNat by omega)
      omega
    -- The second division of r1:t1 by vt, with the restore of s0 to s3.
    refine Reach.trans (top2_320_div_low base _ _ ?_ ?_ ?_ ?_ ?_) ?_
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · exact hD1
    · exact hX
    · exact hv
    · exact h30'
    · intro k hk
      exact List.mem_append_left _ (List.mem_append_right _ (frame32_mem _ k hk))
    intro x3 m3 ⟨hm3, hsp3, hs0, hs1, hs2, hs3, hq0, hr0, h03, hfr3⟩
    subst hm3
    obtain ⟨hf0, hf1, hf2, hf3⟩ := frame32_reads m (x.get 2#5) (x.get 8#5) (x.get 9#5)
      (x.get 18#5) (x.get 19#5)
    rw [hf0] at hs0
    rw [hf1] at hs1
    rw [hf2] at hs2
    rw [hf3] at hs3
    rw [← Regs.eq_get x3 (by decide : (6#5 : BitVec 5) ≠ 0)] at hq0
    rw [← Regs.eq_get x3 (by decide : (7#5 : BitVec 5) ≠ 0),
      ← Regs.eq_get x3 (by decide : (28#5 : BitVec 5) ≠ 0)] at hr0
    rw [regs_eq_sets _ x3 _ h03 hfr3]
    simp only [setRegs]
    have hsp' : x3.get 2#5 = x.get 2#5 := by rw [hsp3]; bv_omega
    -- The end from 208.
    refine top2_320_shift base T x m hpre0 hr _ _ ?_ ?_ ?_ ?_ (unchangedExcept2_frame32_72 _ _ _ _ _ _ _ hsn)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    all_goals try first | exact hS | exact h15 | exact hv0 | exact hu0
    · refine fun i hi => ?_
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] <;>
        first
          | rfl
          | (rw [Regs.eq_get x3 (by decide), Regs.eq_get x (by decide)]
             first | exact hsp' | exact hs0 | exact hs1 | exact hs2 | exact hs3)
    · rw [← hDw]; omega
    · rw [← hDw, ← hTw]
      exact top2_digits rfl hq1 hr1 hq0 hr0
    · rw [← hDw, hr0]
      exact Nat.mod_lt _ (by omega)

/-- The run of `udivrem_top2<3, false, 320, 256>()` for any immediates `hi` and `lo` of the address
`T` of the table of the reciprocal, with the frame of 32 bytes below sp outside the table. -/
theorem udivrem_top2_3_320.reach (hi : BitVec 20) (lo : BitVec 12) (base T : BitVec 64)
    (x : Regs) (m : Mem)
    (hT : pcAt base 87 + ((hi ++ 0x000#12).signExtend 64 + lo.signExtend 64) = T)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64) (hr : x.get 1#5 &&& 3 = 0)
    (hstk : (x.get 2#5 - 32#64).toNat + 32 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 2#5 - 32#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hpre : udivrem_top2_3_320.pre x m) :
    Reach (udivrem_top2_3_320.bufs x ++ bufWords T 256) (udivrem_top2_3_320_progAt hi lo) base
      (pcAt base 0) x m (x.get 1#5) (udivrem_top2_3_320.post x m) := by
  have hpre0 := hpre
  simp only [udivrem_top2_3_320.pre, udivrem_top2_3_320.bufs, Buf] at hpre ⊢
  simp (disch := decide) only [Regs.eq_get x] at hpre ⊢
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr, hv1, hv2,
    hu3⟩ := hpre
  have hv3 := top4_zero m (x.get 12#5) hv2
  have hv2' := top3_ne_zero m (x.get 12#5) hv1 hv3
  have hue := top2_320_ue m (x.get 11#5) (x.get 12#5) hu3 hv3
  rv_exec_cut 81
  all_goals
    set v2 := memWord m (x.get 12#5 + 16#64).toNat with hv2e
    set v1 := memWord m (x.get 12#5 + 8#64).toNat with hv1e
    set v0 := memWord m (x.get 12#5).toNat with hv0e
    set ue := memWord m (x.get 11#5 + 32#64).toNat with huee
    set u3 := memWord m (x.get 11#5 + 24#64).toNat with hu3e
    set u2 := memWord m (x.get 11#5 + 16#64).toNat with hu2e
    set u1 := memWord m (x.get 11#5 + 8#64).toNat with hu1e
    set u0 := memWord m (x.get 11#5).toNat with hu0e
    rv_copies
    have hv2n : v2 ≠ 0 := fun h => hv2' (by rw [h]; rfl)
    -- The count of the leading zeros of v[2], S.
    have hs := clz_ite v2
    rw [if_neg hv2n, swarClz_expand, smear_expand] at hs
    rv_fold hs
    rv_fold hs
    subst hs
    have hL64 : v2.toNat.log2 < 64 := (Nat.log2_lt hv2').mpr v2.isLt
    have hSt : (BitVec.ofNat 64 (63 - v2.toNat.log2)).toNat = 63 - v2.toNat.log2 :=
      ofNat_S_toNat (by omega)
    have hS1 : v2.toNat * 2 ^ (63 - v2.toNat.log2) < 2 ^ 64 := by
      have := Nat.lt_log2_self (n := v2.toNat)
      calc v2.toNat * 2 ^ (63 - v2.toNat.log2)
          < 2 ^ (v2.toNat.log2 + 1) * 2 ^ (63 - v2.toNat.log2) :=
            Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos _)
        _ = 2 ^ 64 := by rw [← pow_add]; congr 1; omega
    have hS63 : 2 ^ 63 ≤ v2.toNat * 2 ^ (63 - v2.toNat.log2) := by
      have := Nat.log2_self_le hv2'
      calc 2 ^ 63 = 2 ^ v2.toNat.log2 * 2 ^ (63 - v2.toNat.log2) := by
            rw [← pow_add]; congr 1; omega
        _ ≤ _ := Nat.mul_le_mul_right _ this
    have hVw : words m (x.get 12#5) 4 = v0.toNat + 2 ^ 64 * (v1.toNat + 2 ^ 64 * v2.toNat) :=
      (words_v3 m (x.get 12#5) hv3).symm
    have hUw : words m (x.get 11#5) 5 = u0.toNat + 2 ^ 64 * (u1.toNat + 2 ^ 64 * (u2.toNat +
        2 ^ 64 * (u3.toNat + 2 ^ 64 * ue.toNat))) := by
      simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
        Nat.add_zero]
      rfl
    -- u[4] < 2^(64 - S): the top word of the shifted u is 0.
    have hueQ : ue.toNat < 2 ^ (64 - (63 - v2.toNat.log2)) := by
      have hP : 2 ^ (63 - v2.toNat.log2) * 2 ^ (64 - (63 - v2.toNat.log2)) = 2 ^ 64 := by
        rw [← pow_add]; congr 1; omega
      by_contra hc
      have := Nat.mul_le_mul_right (2 ^ (63 - v2.toNat.log2)) (Nat.le_of_not_lt hc)
      rw [Nat.mul_comm (2 ^ (64 - _)), hP] at this
      have : ue.toNat * 2 ^ (63 - v2.toNat.log2) < v2.toNat * 2 ^ (63 - v2.toNat.log2) :=
        Nat.mul_lt_mul_of_pos_right hue (Nat.two_pow_pos _)
      omega
  -- s ≠ 0: the normalized words by the funnel shifts.
  all_goals first
    | (rv_lacks ¬BitVec.ofNat 64 (63 - v2.toNat.log2) = 0#64; skip)
    | (rv_get hne : ¬BitVec.ofNat 64 (63 - v2.toNat.log2) = 0#64
       have hS0 := ofNat_S_ne (by omega) hne
       have hd0 := toNat_fshl_code v1 v0 (BitVec.ofNat 64 (63 - v2.toNat.log2)) (by rw [hSt]; omega)
       have hd1 := toNat_fshl_code v2 v1 (BitVec.ofNat 64 (63 - v2.toNat.log2)) (by rw [hSt]; omega)
       have ht3 := toNat_fshl_code ue u3 (BitVec.ofNat 64 (63 - v2.toNat.log2)) (by rw [hSt]; omega)
       have ht2 := toNat_fshl_code u3 u2 (BitVec.ofNat 64 (63 - v2.toNat.log2)) (by rw [hSt]; omega)
       have ht1 := toNat_fshl_code u2 u1 (BitVec.ofNat 64 (63 - v2.toNat.log2)) (by rw [hSt]; omega)
       have ht0 := toNat_fshl_code u1 u0 (BitVec.ofNat 64 (63 - v2.toNat.log2)) (by rw [hSt]; omega)
       rv_fold hd0
       rv_fold hd0
       rv_fold hd1
       rv_fold hd1
       rv_fold ht3
       rv_fold ht3
       rv_fold ht2
       rv_fold ht2
       rv_fold ht1
       rv_fold ht1
       rv_fold ht0
       rv_fold ht0
       conv at hd0 => rhs; rw [hSt]
       conv at hd1 => rhs; rw [hSt]
       conv at ht3 => rhs; rw [hSt]
       conv at ht2 => rhs; rw [hSt]
       conv at ht1 => rhs; rw [hSt]
       conv at ht0 => rhs; rw [hSt]
       refine top2_320_main hi lo base T x m hT hw hr hstk hhold hpre0 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
         ?_
       · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
       · intro r hr
         simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
         obtain ⟨h5, h6, h7, h11, h13, h14, h15, h16, h17, h28, h29, -, -⟩ := hr
         simp (config := { decide := true }) only [Regs.set_apply, h5, h6, h7, h11, h13, h14, h15,
           h16, h17, h28, h29, ↓reduceIte]
       all_goals simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
       all_goals try first | exact hv0e | exact hu0e
       · rw [hSt]; omega
       · rw [hSt, hd0, hd1, hVw, norm2_low _ _ _ _ v1.isLt v0.isLt (by omega) ?_,
           div_low_word _ _ _ (by omega)]
         have := fshl_lt (by omega) v1.isLt hS1
         have hP : 2 ^ (63 - v2.toNat.log2) * 2 ^ (64 - (63 - v2.toNat.log2)) = 2 ^ 64 := by
           rw [← pow_add]; congr 1; omega
         have : v1.toNat * 2 ^ (63 - v2.toNat.log2) < 2 ^ 64 * 2 ^ (63 - v2.toNat.log2) :=
           Nat.mul_lt_mul_of_pos_right v1.isLt (Nat.two_pow_pos _)
         have hv2Q : v2.toNat < 2 ^ (64 - (63 - v2.toNat.log2)) := by
           by_contra hc
           have := Nat.mul_le_mul_right (2 ^ (63 - v2.toNat.log2)) (Nat.le_of_not_lt hc)
           rw [Nat.mul_comm (2 ^ (64 - _)), hP] at this
           omega
         have hv2P : (v2.toNat + 1) * 2 ^ (63 - v2.toNat.log2) ≤ 2 ^ 64 := by
           rw [← hP, Nat.mul_comm (2 ^ (63 - _))]
           exact Nat.mul_le_mul_right _ hv2Q
         nlinarith
       · rw [hd1]; exact norm2_hi (d0 := v1.toNat) (by omega) v1.isLt hS1 hS63
       · rw [hSt, ht0, ht1, ht2, ht3, hUw, norm5_words _ _ _ _ _ _ u0.isLt u1.isLt u2.isLt u3.isLt
           hueQ (by omega), div_low_word _ _ _ (by omega)]
       · have hue1 : ue.toNat * 2 ^ (63 - v2.toNat.log2) < 2 ^ 64 :=
           Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.le_of_lt hue)) hS1
         rw [ht3, hd1, Nat.mod_eq_of_lt (fshl_lt (by omega) u3.isLt hue1)]
         exact top1_2_hi_lt (by omega) u3.isLt v1.isLt hue hS1)
  -- s = 0: the words not shifted.
  all_goals
    rv_get hz : BitVec.ofNat 64 (63 - v2.toNat.log2) = 0#64
    have hS0 := ofNat_S_eq (by omega) hz
    have hd63 : 2 ^ 63 ≤ v2.toNat := by rw [hS0] at hS63; simpa using hS63
    refine top2_320_main hi lo base T x m hT hw hr hstk hhold hpre0 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨h5, h6, h7, h11, h13, h14, h15, h16, h17, h28, -, -, -⟩ := hr
      simp (config := { decide := true }) only [Regs.set_apply, h5, h6, h7, h11, h13, h14, h15,
        h16, h17, h28, ↓reduceIte]
    all_goals simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    all_goals try first | exact hv0e | exact hu0e
    · rw [hSt]; omega
    · rw [hSt, hS0, hVw, div_low_word _ _ _ (by omega), Nat.div_eq_of_lt v0.isLt]
      simp
    · exact hd63
    · rw [hSt, hS0, hUw, div_low_word _ _ _ (by omega), Nat.div_eq_of_lt u0.isLt]
      simp
    · exact hue

theorem udivrem_top2_3_320.proof_of_decodes (hdec : udivrem_top2_3_320.decodes) :
    udivrem_top2_3_320.spec := by
  apply runsI_of_reach hdec
  intro base ret _ hr _ _ hw x m hx1 hbufs hhold hpre
  rw [show udivrem_top2_3_320_image_dataOff = 1152 from rfl] at hw hhold hbufs ⊢
  rw [show udivrem_top2_3_320_image_data.length = 256 from rfl] at hw hbufs ⊢
  have hx : x.get 1#5 = ret := by rw [← Regs.eq_get x (by decide)]; exact hx1
  have hpre' := hpre
  simp only [udivrem_top2_3_320.pre, Buf] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  have hst := frame32_outside (x 2#5) base 1152 (8 * 256)
    (hbufs _ (List.mem_append_right _ (mem_bufWords_zero (by norm_num))))
    (hbufs _ (List.mem_append_right _ (mem_bufWords (by norm_num))))
    (by rw [Regs.eq_get x (by decide)]; exact hpre'.2.2.2.2.2.1.2) (by norm_num)
  rw [Regs.eq_get x (by decide)] at hst
  rw [show udivrem_top2_3_320_entry = udivrem_top2_3_320_image_udivrem_top2_3_320_offset from rfl,
    dataWords, ← hx]
  refine Reach.lift udivrem_top2_3_320_image_udivrem_top2_3_320_in (by decide) ?_
  have hT : (base + BitVec.ofNat 64 1152).toNat = base.toNat + 1152 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have h := udivrem_top2_3_320.reach 0x0#20 0x324#12
    (pcAt base udivrem_top2_3_320_image_udivrem_top2_3_320_offset) _ x m
    (by simp only [udivrem_top2_3_320_image_udivrem_top2_3_320_offset, pcAt, BitVec.reduceAppend,
      BitVec.reduceSignExtend]; bv_omega)
    (by rw [hT]; omega) (hx ▸ hr) (by rw [hT]; omega) hhold hpre
  rwa [pcAt_zero] at h

/-- The registers of the nonvacuous instance: the result, u = 0 and v = 2^128 above the data, and
the frame below sp. -/
theorem udivrem_top2_3_320.nonvacuous :
    NonVacuousI udivrem_top2_3_320_image_code udivrem_top2_3_320_image_data
      udivrem_top2_3_320_image_dataOff udivrem_top2_3_320.bufs udivrem_top2_3_320.pre :=
  nonVacuousI_of_args (fun i => if i = 10#5 then 0x80000D00#64 else if i = 11#5 then 0x80000D48#64
      else if i = 12#5 then 0x80000D70#64 else if i = 2#5 then 0x80000DB0#64 else 0)
    0x80000D48 [0, 0, 0, 0, 0, 0, 0, 1, 0]
    (by decide) (by decide) (by decide) (by decide)
    (by rw [show udivrem_top2_3_320_image_dataOff = 1152 from rfl,
          show udivrem_top2_3_320_image_data.length = 256 from rfl]
        simp only [udivrem_top2_3_320.bufs, ↓reduceIte, BitVec.reduceEq, BitVec.reduceSub,
          bufWords, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq]
        repeat' apply And.intro
        all_goals decide)
    (by decide)
    (fun m => by
      simp only [udivrem_top2_3_320.pre, Buf, Disjoint, words, ↓reduceIte, BitVec.reduceEq,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, BitVec.toNat_ofNat,
        Nat.reducePow, Nat.reduceMod, Nat.mul_zero, Nat.add_zero]
      simp (disch := decide) only [memWord_storeWords_getD]
      decide)

end IntxRV.Api
