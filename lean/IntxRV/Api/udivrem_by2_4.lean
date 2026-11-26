import IntxRV.DivBy24
/-!
# `internal::udivrem_by2()` of 4 quotient words

The specification, from `include/intx/intx.hpp`:

```cpp
/// Divides arbitrary long unsigned integer by 128-bit unsigned integer (2 words).
/// @tparam Q The fixed size of q, one less than the size of u, or std::dynamic_extent. u is not
///           deduced, so spans of non-const words convert to it.
/// @param q  The quotient words: u.size() - 1 of them. It may be u.
/// @param u  The numerator words.
/// @param d  The divisor.
/// @return   The remainder.
/// @pre 3 ≤ u.size()
/// @pre q.size() + 1 = u.size()
/// @pre 2^64 ≤ d
/// @post q = u / d
/// @post result = u % d
/// @note FV: not proved for q that overlaps u.
template <size_t Q>
constexpr uint128 udivrem_by2(std::span<uint64_t, Q> q,
    std::type_identity_t<std::span<const uint64_t, Q == std::dynamic_extent ? Q : Q + 1>> u,
    uint128 d) noexcept
```

`udivrem_by2_4.spec` states it for the RV64 machine code of `udivrem_by2_4` in `IntxRV/Api.cpp`,
the instance for a quotient of 4 words, which `udivrem<320, 256>()` calls. The function normalizes
`d` with the count of the leading zeros of its top word, computes the reciprocal with the table of
the image (`recip3BV_spec`) as the dynamic instance does (`IntxRV/Api/udivrem_by2.lean`), divides
the top digits of the shifted numerator into q[3] (`by24_b1`, or `by24_sub_top` when u[4] is at
most the top word of d) on the four kinds of path of the shift 0 or not, and runs the unrolled
digits 2 to 0 (`IntxRV/DivBy24.lean`). `udivrem_by2_4.reach` is the run for any immediates of the
address of the table, for the functions that call it.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
-- The guards that select the paths do not change the goals.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- The run of `udivrem_by2<4>()` from its start to the return address in ra, for the immediates
`hi` and `lo` of the address `T` of the table of the reciprocal, which differ in each image. -/
theorem udivrem_by2_4.reach (hi : BitVec 20) (lo : BitVec 12) (base T : BitVec 64) (x : Regs)
    (m : Mem) (hT : pcAt base 50 + ((hi ++ 0x000#12).signExtend 64 + lo.signExtend 64) = T)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64) (hr : x.get 1#5 &&& 3 = 0)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hpre : udivrem_by2_4.pre x m) :
    Reach (udivrem_by2_4.bufs x ++ bufWords T 256) (udivrem_by2_4_progAt hi lo) base (pcAt base 0)
      x m (x.get 1#5) (udivrem_by2_4.post x m) := by
  have hpre0 := hpre
  simp only [udivrem_by2_4.pre, udivrem_by2_4.bufs, Buf, Disjoint] at hpre ⊢
  simp (disch := decide) only [Regs.eq_get x] at hpre ⊢
  obtain ⟨⟨hqa, hqn⟩, ⟨hua, hun⟩, hdis, -, -, hdd⟩ := hpre
  obtain ⟨hd1', hL64, hD127⟩ := by24_dn hpre0
  have hd1 : x.get 13#5 ≠ 0 := fun h => hd1' (by rw [h]; rfl)
  have hS1 : (x.get 13#5).toNat * 2 ^ (63 - Nat.log2 (x.get 13#5).toNat) < 2 ^ 64 := by
    have := Nat.lt_log2_self (n := (x.get 13#5).toNat)
    calc (x.get 13#5).toNat * 2 ^ (63 - Nat.log2 (x.get 13#5).toNat)
        < 2 ^ (Nat.log2 (x.get 13#5).toNat + 1) * 2 ^ (63 - Nat.log2 (x.get 13#5).toNat) :=
          Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos _)
      _ = 2 ^ 64 := by rw [← pow_add]; congr 1; omega
  have hS63 : 2 ^ 63 ≤ (x.get 13#5).toNat * 2 ^ (63 - Nat.log2 (x.get 13#5).toNat) := by
    have := Nat.log2_self_le hd1'
    calc 2 ^ 63 = 2 ^ Nat.log2 (x.get 13#5).toNat * 2 ^ (63 - Nat.log2 (x.get 13#5).toNat) := by
          rw [← pow_add]; congr 1; omega
      _ ≤ _ := Nat.mul_le_mul_right _ this
  have hSt : (BitVec.ofNat 64 (63 - (x.get 13#5).toNat.log2)).toNat =
      63 - (x.get 13#5).toNat.log2 := ofNat_S_toNat (by omega)
  have hS64' : 63 - Nat.log2 (x.get 13#5).toNat < 64 := by omega
  have hDp : 0 < ((x.get 12#5).toNat + 2 ^ 64 * (x.get 13#5).toNat) *
      2 ^ (63 - Nat.log2 (x.get 13#5).toNat) := by omega
  rv_exec_cut 69
  all_goals
    -- The count of the leading zeros of d1, s.
    have hs := clz_ite (x.get 13#5)
    rw [if_neg hd1, swarClz_expand, smear_expand] at hs
    rv_fold hs
    subst hs
    -- The low word of the normalized divisor.
    have h0 : (x.get 12#5 <<< ((BitVec.ofNat 64 (63 - (x.get 13#5).toNat.log2)).toNat % 64)).toNat =
        (x.get 12#5).toNat * 2 ^ (63 - (x.get 13#5).toNat.log2) % 2 ^ 64 := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hSt, Nat.mod_eq_of_lt (by omega : 63 - _ < 64)]
    rv_fold h0
  -- The normalized divisor, with the funnel shift for s ≠ 0 and d1 for s = 0.
  all_goals first
    | (rv_lacks ¬BitVec.ofNat 64 (63 - (x.get 13#5).toNat.log2) = 0#64; skip)
    | (have h1 := toNat_fshl_code (x.get 13#5) (x.get 12#5)
         (BitVec.ofNat 64 (63 - (x.get 13#5).toNat.log2)) (by rw [hSt]; omega)
       rv_fold h1
       rv_fold h1
       rw [hSt] at h1
       have hdn := norm2_words (d0 := (x.get 12#5).toNat) (by omega) (x.get 12#5).isLt hS1
       rw [← h0, ← h1] at hdn
       have hdn63 := norm2_hi (d0 := (x.get 12#5).toNat) (by omega) (x.get 12#5).isLt hS1 hS63
       rw [← h1] at hdn63)
  all_goals first
    | (rv_lacks BitVec.ofNat 64 (63 - (x.get 13#5).toNat.log2) = 0#64; skip)
    | (rv_get hz : BitVec.ofNat 64 (63 - (x.get 13#5).toNat.log2) = 0#64
       have hS0 := ofNat_S_eq (by omega) hz
       have hdn : (x.get 12#5).toNat * 2 ^ (63 - (x.get 13#5).toNat.log2) % 2 ^ 64 +
           2 ^ 64 * (x.get 13#5).toNat = ((x.get 12#5).toNat + 2 ^ 64 * (x.get 13#5).toNat) *
             2 ^ (63 - (x.get 13#5).toNat.log2) := by
         rw [hS0]; simp only [pow_zero, Nat.mul_one]; rw [Nat.mod_eq_of_lt (x.get 12#5).isLt]
       rw [← h0] at hdn
       have hdn63 : 2 ^ 63 ≤ (x.get 13#5).toNat := by rw [hS0] at hS63; simpa using hS63)
  all_goals
    -- The address of the table in the run.
    simp only [hT] at *
    -- The table entry of the top word of the normalized divisor: the low half.
    refine Reach.step (by decide) (by rv_fetch) ?_
    simp only [StepGoal, Nat.reduceAdd]
    rv_val
    have ha := table_addr_by1 _ T hdn63
    rv_fold ha
    have hix := index_lt_256 hdn63
    rw [ha]
    refine ⟨Or.inl (List.mem_append_right _ (mem_bufWords hix)), fun wL hwL => ?_⟩
    rw [memHalf_lo, holdsData_get hhold
        (by rw [show reciprocal_2by1_image_data.length = 256 from rfl]; exact hix),
      ← List.getD_eq_getElem _ 0, image_data_get _ hix] at hwL
    rv_exec_cut 69
    -- The high half.
    refine Reach.step (by decide) (by rv_fetch) ?_
    simp only [StepGoal, Nat.reduceAdd]
    rv_val
    have hah := table_addr_by1_hi _ T hdn63
    rv_fold hah
    rw [hah]
    refine ⟨Or.inr (by
      rw [show ∀ a : BitVec 64, a + 4 - 4#64 = a from fun a => by bv_omega]
      exact List.mem_append_right _ (mem_bufWords hix)), fun wH hwH => ?_⟩
    rw [table_entry_add4 T hdn63 hw, memHalf_hi, holdsData_get hhold
        (by rw [show reciprocal_2by1_image_data.length = 256 from rfl]; exact hix),
      ← List.getD_eq_getElem _ 0, image_data_get _ hix] at hwH
    rv_exec_cut 69
    -- The top word of the numerator, u[4].
    refine Reach.step (by decide) (by rv_fetch) ?_
    simp only [StepGoal, Nat.reduceAdd]
    rv_val
    refine ⟨List.mem_append_left _ (List.mem_append_left _ (mem_bufWords (i := 4) (by norm_num))),
      fun wT hwT => ?_⟩
    rv_exec_cut 108 121 152
  -- The reciprocal of the normalized divisor.
  all_goals
    rv_cse
    obtain ⟨hL, hH⟩ := table_LH hdn63 hwL hwH
    have hv := recip3BV_spec_of h0 _ wL wH hdn63 hL hH
    simp only [recip3BV] at hv
    rw [show (0 : BitVec 64) = 0#64 from rfl] at hv
    rv_fold hv
    rv_fold hv
  -- The paths that test s against 0 twice with different outcomes do not run.
  all_goals first
    | (rv_get hz : BitVec.ofNat 64 (63 - (x.get 13#5).toNat.log2) = 0#64
       rv_get hnz : ¬BitVec.ofNat 64 (63 - (x.get 13#5).toNat.log2) = 0#64
       exact absurd hz hnz)
    | skip
  -- u[4] > d1, s ≠ 0: the words u[2] and u[3] for the funnel shifts of the top digits.
  all_goals first
    | (rv_not_at 108; skip)
    | (refine Reach.step (by decide) (by rv_fetch) ?_
       simp only [StepGoal, Nat.reduceAdd]
       rv_val
       refine ⟨List.mem_append_left _ (List.mem_append_left _
         (mem_bufWords (i := 2) (by norm_num))), fun wC hwC => ?_⟩
       refine Reach.step (by decide) (by rv_fetch) ?_
       simp only [StepGoal, Nat.reduceAdd]
       rv_val
       refine ⟨List.mem_append_left _ (List.mem_append_left _
         (mem_bufWords (i := 3) (by norm_num))), fun wA hwA => ?_⟩
       rv_exec_cut 154)
  -- u[4] > d1, s = 0: the word u[3].
  all_goals first
    | (rv_not_at 152; skip)
    | (refine Reach.step (by decide) (by rv_fetch) ?_
       simp only [StepGoal, Nat.reduceAdd]
       rv_val
       refine ⟨List.mem_append_left _ (List.mem_append_left _
         (mem_bufWords (i := 3) (by norm_num))), fun wA hwA => ?_⟩
       rv_exec_cut 154)
  -- u[4] > d1: the inlined udivrem_3by2() of the top digits.
  all_goals first
    | (rv_not_at 154; skip)
    | (refine Reach.trans (by24_b1 base _ _ ?_ ?_ ?_) ?_
       · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
         rw [hdn]; exact hD127
       · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
         rw [hdn]
         first
           | (simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_mul, Nat.zero_add]
              have := wT.isLt
              omega)
           | (rv_get hne : ¬BitVec.ofNat 64 (63 - (x.get 13#5).toNat.log2) = 0#64
              have hS0 := ofNat_S_ne (by omega) hne
              have hhi : (wT >>> ((BitVec.signExtend 64 (BitVec.setWidth 32 0#64 -
                  BitVec.setWidth 32 (BitVec.ofNat 64 (63 - (x.get 13#5).toNat.log2)))).toNat %
                    64)).toNat = wT.toNat / 2 ^ (64 - (63 - (x.get 13#5).toNat.log2)) := by
                rw [negw_shift _ (by omega) hS0, BitVec.toNat_ushiftRight,
                  Nat.shiftRight_eq_div_pow]
              rv_fold hhi
              rv_fold hhi
              exact top2_lt (S := 63 - (x.get 13#5).toNat.log2) (by omega)
                (by rw [hhi]; exact shr_lt_pow wT _ (by omega)) (BitVec.isLt _) hD127)
       · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
         exact hv
       intro x' m' ⟨hm, hq0, hr0, h00, hfr⟩
       subst hm
       rw [regs_eq_sets _ x' _ h00 hfr]
       simp only [setRegs]
       rv_exec_cut 184
       -- The quotient word q[3].
       refine Reach.step (by decide) (by rv_fetch) ?_
       simp only [StepGoal, Nat.reduceAdd]
       rv_val
       refine ⟨List.mem_append_left _ (List.mem_append_right _
         (mem_bufWords (i := 3) (by norm_num))), ?_⟩
       -- The word u[2] of the digit 2.
       refine Reach.step (by decide) (by rv_fetch) ?_
       simp only [StepGoal, Nat.reduceAdd]
       rv_val
       refine ⟨List.mem_append_left _ (List.mem_append_left _
         (mem_bufWords (i := 2) (by norm_num))), fun wE hwE => ?_⟩
       rv_exec_cut 188 197)
  all_goals first
    | (rv_get hz : BitVec.ofNat 64 (63 - (x.get 13#5).toNat.log2) = 0#64
       rv_get hnz : ¬BitVec.ofNat 64 (63 - (x.get 13#5).toNat.log2) = 0#64
       exact absurd hz hnz)
    | skip
  -- u[4] ≤ d1: the word u[3] and d subtracted from the top two words at most once.
  all_goals first
    | (rv_not_at 121; skip)
    | (refine Reach.step (by decide) (by rv_fetch) ?_
       simp only [StepGoal, Nat.reduceAdd]
       rv_val
       refine ⟨List.mem_append_left _ (List.mem_append_left _
         (mem_bufWords (i := 3) (by norm_num))), fun wA hwA => ?_⟩
       simp only [zopz0zKzJ_u_eq, decide_eq_true_eq] at *
       refine Reach.trans (by24_sub_top base _ _ ?_ ?_) ?_
       · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
         omega
       · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
         rv_get hle : wT ≤ x.get 13#5
         exact BitVec.le_def.mp hle
       intro x' m' ⟨hm, hq0, hr0, h00, hfr⟩
       subst hm
       rw [regs_eq_sets _ x' _ h00 hfr]
       simp only [setRegs]
       -- The quotient word q[3], 0 or 1.
       refine Reach.step (by decide) (by rv_fetch) ?_
       simp only [StepGoal, Nat.reduceAdd]
       rv_val
       refine ⟨List.mem_append_left _ (List.mem_append_right _
         (mem_bufWords (i := 3) (by norm_num))), ?_⟩
       rv_exec_cut 141 195)
  all_goals first
    | (rv_get hz : BitVec.ofNat 64 (63 - (x.get 13#5).toNat.log2) = 0#64
       rv_get hnz : ¬BitVec.ofNat 64 (63 - (x.get 13#5).toNat.log2) = 0#64
       exact absurd hz hnz)
    | skip
  -- u[4] ≤ d1: the word u[2] for the remainder (s ≠ 0) and the digit 2.
  all_goals first
    | (rv_not_at 141; rv_not_at 195; skip)
    | (refine Reach.step (by decide) (by rv_fetch) ?_
       simp only [StepGoal, Nat.reduceAdd]
       rv_val
       refine ⟨List.mem_append_left _ (List.mem_append_left _
         (mem_bufWords (i := 2) (by norm_num))), fun wE hwE => ?_⟩
       rv_exec_cut 188 197)
  -- s ≠ 0: the word u[1] for the funnel shift of the digit 2.
  all_goals first
    | (rv_not_at 188; skip)
    | (refine Reach.step (by decide) (by rv_fetch) ?_
       simp only [StepGoal, Nat.reduceAdd]
       rv_val
       refine ⟨List.mem_append_left _ (List.mem_append_left _
         (mem_bufWords (i := 1) (by norm_num))), fun wB hwB => ?_⟩
       rv_exec_cut 197)
  -- The quotient word q[3] and the remainder of the top digits on the four kinds of path.
  all_goals
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte] at hq0 hr0
    have hwTm : wT.toNat = wordAt m' (x.get 11#5) 4 := by rw [hwT.eq]; try rfl
    have hwAm : wA.toNat = wordAt m' (x.get 11#5) 3 := by rw [hwA.eq]; try rfl
    have hwEm : wE.toNat = wordAt m' (x.get 11#5) 2 := by rw [hwE.eq]; try rfl
    have htop := by2_top3 m' (x.get 11#5) 5 _ hS64' (by norm_num)
    have htop0 := by2_top3_s0 m' (x.get 11#5) 5 (by norm_num)
    simp only [show 5 - 1 = 4 from rfl, show 5 - 2 = 3 from rfl, show 5 - 3 = 2 from rfl]
      at htop htop0
    first
      | (rv_has LeanRV64D.Functions.zopz0zKzJ_u (x.get 13#5) wT = false
         rv_get hz : BitVec.ofNat 64 (63 - (x.get 13#5).toNat.log2) = 0#64
         have hS0 := ofNat_S_eq (by omega) hz
         have hU : (0#64).toNat * 2 ^ 128 + wT.toNat * 2 ^ 64 + wA.toNat =
             words m' (x.get 11#5) 5 * 2 ^ (63 - (x.get 13#5).toNat.log2) / 2 ^ (64 * 3) := by
           rw [hS0, pow_zero, Nat.mul_one, htop0, hwTm, hwAm]; simp
         rw [hU, hdn] at hq0 hr0
         have h9 : (x' 6#5).toNat + 2 ^ 64 * (x' 7#5).toNat < ((x.get 12#5).toNat +
             2 ^ 64 * (x.get 13#5).toNat) * 2 ^ (63 - (x.get 13#5).toNat.log2) := by
           rw [Regs.eq_get x' (show (6#5 : BitVec 5) ≠ 0 by decide),
             Regs.eq_get x' (show (7#5 : BitVec 5) ≠ 0 by decide), hr0]
           exact Nat.mod_lt _ hDp
         have h10 : (x' 12#5).toNat * (((x.get 12#5).toNat + 2 ^ 64 * (x.get 13#5).toNat) *
             2 ^ (63 - (x.get 13#5).toNat.log2)) + ((x' 6#5).toNat + 2 ^ 64 * (x' 7#5).toNat) =
             words m' (x.get 11#5) 5 * 2 ^ (63 - (x.get 13#5).toNat.log2) / 2 ^ (64 * 3) := by
           rw [Regs.eq_get x' (show (6#5 : BitVec 5) ≠ 0 by decide),
             Regs.eq_get x' (show (7#5 : BitVec 5) ≠ 0 by decide),
             Regs.eq_get x' (show (12#5 : BitVec 5) ≠ 0 by decide), hq0, hr0]
           exact Nat.div_add_mod' _ _)
      | (rv_has LeanRV64D.Functions.zopz0zKzJ_u (x.get 13#5) wT = false
         rv_get hne : ¬BitVec.ofNat 64 (63 - (x.get 13#5).toNat.log2) = 0#64
         have hS0 := ofNat_S_ne (by omega) hne
         have hwCm : wC.toNat = wordAt m' (x.get 11#5) 2 := by rw [hwC.eq]; try rfl
         have hhi : (wT >>> ((BitVec.signExtend 64 (BitVec.setWidth 32 0#64 -
             BitVec.setWidth 32 (BitVec.ofNat 64 (63 - (x.get 13#5).toNat.log2)))).toNat %
               64)).toNat = wT.toNat / 2 ^ (64 - (63 - (x.get 13#5).toNat.log2)) := by
           rw [negw_shift _ (by omega) hS0, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
         rv_fold hhi
         rv_fold hhi
         have hu1 := toNat_fshl_code wT wA (BitVec.ofNat 64 (63 - (x.get 13#5).toNat.log2))
           (by rw [hSt]; omega)
         rv_fold hu1
         rv_fold hu1
         have hu0 := toNat_fshl_code wA wC (BitVec.ofNat 64 (63 - (x.get 13#5).toNat.log2))
           (by rw [hSt]; omega)
         rv_fold hu0
         rv_fold hu0
         rw [hSt] at hu1 hu0
         rw [hhi, hu1, hu0, hwTm, hwAm, hwCm, ← htop, hdn] at hq0 hr0
         have h9 : (x' 6#5).toNat + 2 ^ 64 * (x' 7#5).toNat < ((x.get 12#5).toNat +
             2 ^ 64 * (x.get 13#5).toNat) * 2 ^ (63 - (x.get 13#5).toNat.log2) := by
           rw [Regs.eq_get x' (show (6#5 : BitVec 5) ≠ 0 by decide),
             Regs.eq_get x' (show (7#5 : BitVec 5) ≠ 0 by decide), hr0]
           exact Nat.mod_lt _ hDp
         have h10 : (x' 12#5).toNat * (((x.get 12#5).toNat + 2 ^ 64 * (x.get 13#5).toNat) *
             2 ^ (63 - (x.get 13#5).toNat.log2)) + ((x' 6#5).toNat + 2 ^ 64 * (x' 7#5).toNat) =
             words m' (x.get 11#5) 5 * 2 ^ (63 - (x.get 13#5).toNat.log2) / 2 ^ (64 * 3) := by
           rw [Regs.eq_get x' (show (6#5 : BitVec 5) ≠ 0 by decide),
             Regs.eq_get x' (show (7#5 : BitVec 5) ≠ 0 by decide),
             Regs.eq_get x' (show (12#5 : BitVec 5) ≠ 0 by decide), hq0, hr0]
           exact Nat.div_add_mod' _ _)
      | (rv_has wT ≤ x.get 13#5
         rv_get hne : ¬BitVec.ofNat 64 (63 - (x.get 13#5).toNat.log2) = 0#64
         have hS0 := ofNat_S_ne (by omega) hne
         have hf0 := toNat_fshl_code (x' 6#5) wE (BitVec.ofNat 64 (63 - (x.get 13#5).toNat.log2))
           (by rw [hSt]; omega)
         rv_fold hf0
         rv_fold hf0
         have hf1 := toNat_fshl_code (x' 7#5) (x' 6#5)
           (BitVec.ofNat 64 (63 - (x.get 13#5).toNat.log2)) (by rw [hSt]; omega)
         rv_fold hf1
         rv_fold hf1
         rw [hSt] at hf0 hf1
         rw [Regs.eq_get x' (show (6#5 : BitVec 5) ≠ 0 by decide)] at hf0
         rw [Regs.eq_get x' (show (6#5 : BitVec 5) ≠ 0 by decide),
           Regs.eq_get x' (show (7#5 : BitVec 5) ≠ 0 by decide)] at hf1
         have hT : (x'.get 6#5).toNat + 2 ^ 64 * (x'.get 7#5).toNat <
             (x.get 12#5).toNat + 2 ^ 64 * (x.get 13#5).toNat := by
           rw [hr0]; exact Nat.mod_lt _ (by omega)
         have hrem := norm2_low (x'.get 6#5).toNat (x'.get 7#5).toNat wE.toNat _ (BitVec.isLt _)
           (BitVec.isLt _) hS64'
           ((Nat.mul_lt_mul_of_pos_right hT (Nat.two_pow_pos _)).trans (lt_2_128_of_words hdn))
         rw [← hf0, ← hf1, hr0] at hrem
         have hUn : words m' (x.get 11#5) 5 * 2 ^ (63 - (x.get 13#5).toNat.log2) / 2 ^ (64 * 3) =
             (wA.toNat + 2 ^ 64 * wT.toNat) * 2 ^ (63 - (x.get 13#5).toNat.log2) +
             wE.toNat / 2 ^ (64 - (63 - (x.get 13#5).toNat.log2)) := by
           rw [norm3_words _ _ _ _ (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _) hS64', hwTm,
             hwAm, hwEm, htop]
         obtain ⟨hdq, hdr⟩ := div_norm_low (T := wA.toNat + 2 ^ 64 * wT.toNat)
           (d := (x.get 12#5).toNat + 2 ^ 64 * (x.get 13#5).toNat)
           (S := 63 - (x.get 13#5).toNat.log2) (by omega) (shr_lt_pow wE _ hS64')
         have h9 : ∀ r, r = (wA.toNat + 2 ^ 64 * wT.toNat) % ((x.get 12#5).toNat +
             2 ^ 64 * (x.get 13#5).toNat) * 2 ^ (63 - (x.get 13#5).toNat.log2) +
             wE.toNat / 2 ^ (64 - (63 - (x.get 13#5).toNat.log2)) → r < ((x.get 12#5).toNat +
             2 ^ 64 * (x.get 13#5).toNat) * 2 ^ (63 - (x.get 13#5).toNat.log2) := by
           intro r hr; rw [hr, ← hdr]; exact Nat.mod_lt _ hDp
         have h10 : ∀ r, r = (wA.toNat + 2 ^ 64 * wT.toNat) % ((x.get 12#5).toNat +
             2 ^ 64 * (x.get 13#5).toNat) * 2 ^ (63 - (x.get 13#5).toNat.log2) +
             wE.toNat / 2 ^ (64 - (63 - (x.get 13#5).toNat.log2)) →
             (x' 12#5).toNat * (((x.get 12#5).toNat + 2 ^ 64 * (x.get 13#5).toNat) *
               2 ^ (63 - (x.get 13#5).toNat.log2)) + r =
             words m' (x.get 11#5) 5 * 2 ^ (63 - (x.get 13#5).toNat.log2) / 2 ^ (64 * 3) := by
           intro r hr
           rw [hr, Regs.eq_get x' (show (12#5 : BitVec 5) ≠ 0 by decide), hq0, ← hdr, ← hdq, hUn]
           exact Nat.div_add_mod' _ _)
      | (rv_has wT ≤ x.get 13#5
         rv_get hz : BitVec.ofNat 64 (63 - (x.get 13#5).toNat.log2) = 0#64
         have hS0 := ofNat_S_eq (by omega) hz
         have hU : wA.toNat + 2 ^ 64 * wT.toNat =
             words m' (x.get 11#5) 5 * 2 ^ (63 - (x.get 13#5).toNat.log2) / 2 ^ (64 * 3) := by
           rw [hS0, pow_zero, Nat.mul_one, htop0, hwTm, hwAm]; ring
         have hD1 : ((x.get 12#5).toNat + 2 ^ 64 * (x.get 13#5).toNat) *
             2 ^ (63 - (x.get 13#5).toNat.log2) = (x.get 12#5).toNat + 2 ^ 64 * (x.get 13#5).toNat := by
           rw [hS0]; simp
         have h9 : (x' 6#5).toNat + 2 ^ 64 * (x' 7#5).toNat < ((x.get 12#5).toNat +
             2 ^ 64 * (x.get 13#5).toNat) * 2 ^ (63 - (x.get 13#5).toNat.log2) := by
           rw [Regs.eq_get x' (show (6#5 : BitVec 5) ≠ 0 by decide),
             Regs.eq_get x' (show (7#5 : BitVec 5) ≠ 0 by decide), hr0, hD1]
           exact Nat.mod_lt _ (by omega)
         have h10 : (x' 12#5).toNat * (((x.get 12#5).toNat + 2 ^ 64 * (x.get 13#5).toNat) *
             2 ^ (63 - (x.get 13#5).toNat.log2)) + ((x' 6#5).toNat + 2 ^ 64 * (x' 7#5).toNat) =
             words m' (x.get 11#5) 5 * 2 ^ (63 - (x.get 13#5).toNat.log2) / 2 ^ (64 * 3) := by
           rw [Regs.eq_get x' (show (6#5 : BitVec 5) ≠ 0 by decide),
             Regs.eq_get x' (show (7#5 : BitVec 5) ≠ 0 by decide),
             Regs.eq_get x' (show (12#5 : BitVec 5) ≠ 0 by decide), hq0, hr0, hD1, ← hU]
           exact Nat.div_add_mod' _ _)
    refine by24_d2 base x _ hpre0 hr _ _ ?_ ?_
    · simp only [By24St]
      simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      refine ⟨hdn, by rw [← hdn]; exact hv, trivial, trivial, trivial, trivial, trivial, ?_, ?_,
        (unchangedExcept_memStore _ _ ⟨by bv_omega, by bv_omega⟩).mpr (unchangedExcept_refl _ _ _),
        trivial, ?_⟩
      · first | exact h9 | exact h9 _ hrem
      · rw [show x.get 10#5 + BitVec.ofNat 64 (8 * (2 + 1)) = x.get 10#5 + 24#64 from rfl,
          show 3 - 2 = 1 from rfl, words_one_memStore, show 64 * (2 + 1) = 64 * 3 from rfl]
        first | exact h10 | exact h10 _ hrem
      · intro r hr'
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl <;>
        first | rfl | simp (config := { decide := true }) only [↓reduceIte]
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      rw [norm_digit m' (x.get 11#5) 5 _ 2 hS64' (by norm_num) (by norm_num)]
      first
        | (rv_get hnz : ¬BitVec.ofNat 64 (63 - (x.get 13#5).toNat.log2) = 0#64
           have hwBm : wB.toNat = wordAt m' (x.get 11#5) (2 - 1) := by rw [hwB.eq]; try rfl
           have hf := toNat_fshl_code wE wB (BitVec.ofNat 64 (63 - (x.get 13#5).toNat.log2))
             (by rw [hSt]; omega)
           rv_fold hf
           rv_fold hf
           rw [hwEm, hwBm, hSt] at hf
           exact hf)
        | (rv_get hz : BitVec.ofNat 64 (63 - (x.get 13#5).toNat.log2) = 0#64
           have hS0 := ofNat_S_eq hS64' hz
           rw [hwEm, hS0]
           simp only [pow_zero, Nat.mul_one, Nat.sub_zero, wordAt]
           rw [Nat.div_eq_of_lt (BitVec.isLt _), Nat.add_zero, Nat.mod_eq_of_lt (BitVec.isLt _)])

theorem udivrem_by2_4.proof_of_decodes (hdec : udivrem_by2_4.decodes) : udivrem_by2_4.spec := by
  apply runsI_of_reach hdec
  intro base ret _ hr _ _ hw x m hx1 _ hhold hpre
  rw [show udivrem_by2_4_image_dataOff = 1376 from rfl] at hw hhold ⊢
  rw [show udivrem_by2_4_image_data.length = 256 from rfl] at hw ⊢
  have hx : x.get 1#5 = ret := by rw [← Regs.eq_get x (by decide)]; exact hx1
  rw [show udivrem_by2_4_entry = udivrem_by2_4_image_udivrem_by2_4_offset from rfl, dataWords, ← hx]
  refine Reach.lift udivrem_by2_4_image_udivrem_by2_4_in (by decide) ?_
  have h := udivrem_by2_4.reach 0x0#20 0x498#12 (pcAt base udivrem_by2_4_image_udivrem_by2_4_offset)
    _ x m
    (by simp only [udivrem_by2_4_image_udivrem_by2_4_offset, pcAt, BitVec.reduceAppend,
      BitVec.reduceSignExtend]; bv_omega)
    (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (hx ▸ hr) hhold hpre
  rwa [pcAt_zero] at h

/-- The registers of the nonvacuous instance: q and u above the data, and the divisor 2^64. -/
theorem udivrem_by2_4.nonvacuous :
    NonVacuousI udivrem_by2_4_image_code udivrem_by2_4_image_data udivrem_by2_4_image_dataOff
      udivrem_by2_4.bufs udivrem_by2_4.pre :=
  nonVacuousI_of (fun i => if i = 10#5 then 0x80000E00#64 else if i = 11#5 then 0x80000E28#64
      else if i = 13#5 then 1#64 else 0)
    (by decide) (by decide) (by decide) (by decide)
    (by rw [show udivrem_by2_4_image_dataOff = 1376 from rfl,
          show udivrem_by2_4_image_data.length = 256 from rfl]
        simp only [udivrem_by2_4.bufs, ↓reduceIte, BitVec.reduceEq, bufWords, List.cons_append,
          List.nil_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        repeat' apply And.intro
        all_goals decide)
    (fun _ => by simp only [udivrem_by2_4.pre, Buf, Disjoint]; decide)

end IntxRV.Api
