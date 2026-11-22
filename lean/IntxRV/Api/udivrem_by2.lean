import IntxRV.DivBy2
/-!
# `internal::udivrem_by2()` of a span

The specification, from `include/intx/intx.hpp`:

```cpp
/// Divides arbitrary long unsigned integer by 128-bit unsigned integer (2 words).
/// @tparam Q The fixed size of q, one less than the size of u, or std::dynamic_extent. u is not
///           deduced, so spans of non-const words convert to it.
/// @param q  The quotient words: u.size() - 1 of them. It may be u.
/// @param u  The numerator words.
/// @param d  The divisor.
/// @return   The remainder.
/// @pre 3 <= u.size()
/// @pre q.size() + 1 = u.size()
/// @pre 2 ^ 64 <= d
/// @post q = u / d
/// @post result = u % d
template <size_t Q>
constexpr uint128 udivrem_by2(std::span<uint64_t, Q> q,
    std::type_identity_t<std::span<const uint64_t, Q == std::dynamic_extent ? Q : Q + 1>> u,
    uint128 d) noexcept
```

`udivrem_by2.spec` states it for the RV64 machine code of `udivrem_by2` in `IntxRV/Api.cpp`, the
version for spans of dynamic extent, for `q` and `u` that do not overlap. The function normalizes
`d` with the count of the leading zeros of its top word, computes the reciprocal with the table of
the image (`recip3BV_spec`), divides the top digits of the shifted numerator into the quotient word
q[n - 2] (`by2_div_top`, or `by2_sub_top` when the top word of u is at most the top word of d),
runs the loop over the words below it (`by2_loop`) and divides the last digit (`by2_exit`), in
`IntxRV/DivBy2.lean`. It saves s0, s1 and s2 in a frame of 32 bytes. `udivrem_by2.reach` is the run
for any immediates of the address of the table (`udivrem_by2_progAt`).
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
-- The guards that select the paths do not change the goals.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- The run of `udivrem_by2` from its start to the return address in ra, for the immediates `hi`
and `lo` of the address `T` of the table of the reciprocal, which differ in each image. -/
theorem udivrem_by2.reach (hi : BitVec 20) (lo : BitVec 12) (base T : BitVec 64) (x : Regs)
    (m : Mem) (hT : pcAt base 54 + ((hi ++ 0x000#12).signExtend 64 + lo.signExtend 64) = T)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64) (hr : x.get 1#5 &&& 3 = 0)
    -- The frame is outside the table, which the code reads after it saves registers there.
    (hstk : (x.get 2#5 - 32#64).toNat + 32 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 2#5 - 32#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hpre : udivrem_by2.pre x m) :
    Reach (udivrem_by2.bufs x ++ bufWords T 256) (udivrem_by2_progAt hi lo) base (pcAt base 0) x m
      (x.get 1#5) (udivrem_by2.post x m) := by
  have hpre0 := hpre
  simp only [udivrem_by2.pre, udivrem_by2.bufs, Buf, Disjoint] at hpre ⊢
  simp (disch := decide) only [Regs.eq_get x] at hpre ⊢
  have hd1 : x.get 15#5 ≠ 0 := by
    intro h; rw [h] at hpre; simp at hpre; have := (x.get 14#5).isLt; omega
  have hd1' : (x.get 15#5).toNat ≠ 0 := fun h => hd1 (BitVec.eq_of_toNat_eq (by simpa using h))
  have hL64 : Nat.log2 (x.get 15#5).toNat < 64 := (Nat.log2_lt hd1').mpr (x.get 15#5).isLt
  have hS1 : (x.get 15#5).toNat * 2 ^ (63 - Nat.log2 (x.get 15#5).toNat) < 2 ^ 64 := by
    have := Nat.lt_log2_self (n := (x.get 15#5).toNat)
    calc (x.get 15#5).toNat * 2 ^ (63 - Nat.log2 (x.get 15#5).toNat)
        < 2 ^ (Nat.log2 (x.get 15#5).toNat + 1) * 2 ^ (63 - Nat.log2 (x.get 15#5).toNat) :=
          Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos _)
      _ = 2 ^ 64 := by rw [← pow_add]; congr 1; omega
  have hS63 : 2 ^ 63 ≤ (x.get 15#5).toNat * 2 ^ (63 - Nat.log2 (x.get 15#5).toNat) := by
    have := Nat.log2_self_le hd1'
    calc 2 ^ 63 = 2 ^ Nat.log2 (x.get 15#5).toNat * 2 ^ (63 - Nat.log2 (x.get 15#5).toNat) := by
          rw [← pow_add]; congr 1; omega
      _ ≤ _ := Nat.mul_le_mul_right _ this
  have hSt : (BitVec.ofNat 64 (63 - (x.get 15#5).toNat.log2)).toNat =
      63 - (x.get 15#5).toNat.log2 := ofNat_S_toNat (by omega)
  have hq8 : 8 * (x.get 11#5).toNat < 2 ^ 64 := by omega
  have hn3 : 3 ≤ (x.get 13#5).toNat := by omega
  have hn8 : 8 * (x.get 13#5).toNat ≤ 2 ^ 64 := by omega
  have hS64' : 63 - Nat.log2 (x.get 15#5).toNat < 64 := by omega
  have hDp : 0 < ((x.get 14#5).toNat + 2 ^ 64 * (x.get 15#5).toNat) *
      2 ^ (63 - Nat.log2 (x.get 15#5).toNat) := Nat.mul_pos (by omega) (Nat.two_pow_pos _)
  have hpre1 := hpre
  obtain ⟨⟨hqa, hqn⟩, ⟨hua, hun8⟩, hdqu, ⟨hsa, hsn⟩, hdsu, hdsq, -, hqs, hdd⟩ := hpre1
  rv_exec_cut 201
  all_goals
    -- The count of the leading zeros of d1, s.
    have hs := clz_ite (x.get 15#5)
    rw [if_neg hd1, swarClz_expand, smear_expand] at hs
    rv_fold hs
    subst hs
    -- The low word of the normalized divisor t1:t0.
    have h0 : (x.get 14#5 <<< ((BitVec.ofNat 64 (63 - (x.get 15#5).toNat.log2)).toNat % 64)).toNat =
        (x.get 14#5).toNat * 2 ^ (63 - (x.get 15#5).toNat.log2) % 2 ^ 64 := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hSt, Nat.mod_eq_of_lt (by omega : 63 - _ < 64)]
    rv_fold h0
  -- The normalized divisor t1:t0, with the funnel shift for s ≠ 0 and t1 = d1 for s = 0.
  all_goals first
    | (rv_lacks ¬BitVec.ofNat 64 (63 - (x.get 15#5).toNat.log2) = 0#64; skip)
    | (have h1 := toNat_fshl_code (x.get 15#5) (x.get 14#5)
         (BitVec.ofNat 64 (63 - (x.get 15#5).toNat.log2)) (by rw [hSt]; omega)
       rv_fold h1
       rv_fold h1
       rw [hSt] at h1
       have hdn := norm2_words (d0 := (x.get 14#5).toNat) (by omega) (x.get 14#5).isLt hS1
       rw [← h0, ← h1] at hdn
       have hdn63 := norm2_hi (d0 := (x.get 14#5).toNat) (by omega) (x.get 14#5).isLt hS1 hS63
       rw [← h1] at hdn63)
  all_goals first
    | (rv_lacks BitVec.ofNat 64 (63 - (x.get 15#5).toNat.log2) = 0#64; skip)
    | (rv_get hz : BitVec.ofNat 64 (63 - (x.get 15#5).toNat.log2) = 0#64
       have hS0 := ofNat_S_eq (by omega) hz
       have hdn : (x.get 14#5).toNat * 2 ^ (63 - (x.get 15#5).toNat.log2) % 2 ^ 64 +
           2 ^ 64 * (x.get 15#5).toNat = ((x.get 14#5).toNat + 2 ^ 64 * (x.get 15#5).toNat) *
             2 ^ (63 - (x.get 15#5).toNat.log2) := by
         rw [hS0]; simp only [pow_zero, Nat.mul_one]; rw [Nat.mod_eq_of_lt (x.get 14#5).isLt]
       rw [← h0] at hdn
       have hdn63 : 2 ^ 63 ≤ (x.get 15#5).toNat := by rw [hS0] at hS63; simpa using hS63)
  all_goals
    -- The address of the table in the run.
    simp only [hT] at *
    -- The table entry of the top word of the normalized divisor: the low half.
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
    rv_exec_cut 201
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
    rv_exec_cut 201
  -- The top word of the numerator, u[n - 1] with n - 1 = q.size().
  all_goals
    refine Reach.step (by decide) rfl ?_
    simp only [StepGoal, Nat.reduceAdd]
    rv_val
    have hut : x.get 12#5 + x.get 11#5 <<< 3 =
        x.get 12#5 + BitVec.ofNat 64 (8 * (x.get 11#5).toNat) := by
      rw [shl3_ofNat _ hq8]
    rv_fold hut
    rw [hut]
    refine ⟨List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (mem_bufWords (by omega)))), fun wT hwT => ?_⟩
    rv_exec_cut 201
  -- The reciprocal of t1:t0.
  all_goals
    -- For s = 0, d1 >>> 1 is computed for the count of the leading zeros and the reciprocal.
    rv_cse
    obtain ⟨hL, hH⟩ := table_LH hdn63 hwL hwH
    have hv := recip3BV_spec_of h0 _ wL wH hdn63 hL hH
    simp only [recip3BV] at hv
    -- The negation reads x0 as 0#64.
    rw [show (0 : BitVec 64) = 0#64 from rfl] at hv
    rv_fold hv
    rv_fold hv
  -- The paths that test s against 0 twice with different outcomes do not run.
  all_goals first
    | (rv_get hz : BitVec.ofNat 64 (63 - (x.get 15#5).toNat.log2) = 0#64
       rv_get hnz : ¬BitVec.ofNat 64 (63 - (x.get 15#5).toNat.log2) = 0#64
       exact absurd hz hnz)
    | skip
  -- The word u[n - 2]: from n - 2 (u[n - 1] > d1) or from the end of u (u[n - 1] ≤ d1).
  all_goals
    refine Reach.step (by decide) rfl ?_
    simp only [StepGoal, Nat.reduceAdd]
    rv_val
    first
      | (have hua : x.get 12#5 + (x.get 13#5 + 18446744073709551614#64) <<< 3 =
            x.get 12#5 + BitVec.ofNat 64 (8 * ((x.get 13#5).toNat - 2)) := by
           rw [off_sub2 _ (by omega) hn8]
         rv_fold hua
         rw [hua])
      | (have hua : x.get 12#5 + x.get 13#5 <<< 3 + 18446744073709551600#64 =
            x.get 12#5 + BitVec.ofNat 64 (8 * ((x.get 13#5).toNat - 2)) := by
           rw [BitVec.add_assoc, off16 _ (by omega) hn8]
         rv_fold hua
         rw [hua])
    refine ⟨List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (mem_bufWords (by omega)))), fun wA hwA => ?_⟩
    rv_exec_cut 134 169 201
  -- u[n - 1] > d1, s ≠ 0: the word u[n - 3] for the funnel shift of the third digit.
  all_goals first
    | (rv_not_at 123; skip)
    | (refine Reach.step (by decide) rfl ?_
       simp only [StepGoal, Nat.reduceAdd]
       rv_val
       have huc : x.get 12#5 + x.get 13#5 <<< 3 + 18446744073709551592#64 =
           x.get 12#5 + BitVec.ofNat 64 (8 * ((x.get 13#5).toNat - 3)) := by
         rw [BitVec.add_assoc, off24 _ hn3 hn8]
       rv_fold huc
       rw [huc]
       refine ⟨List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
         (mem_bufWords (by omega)))), fun wC hwC => ?_⟩
       rv_exec_cut 134 169 201)
  -- u[n - 1] > d1: the inlined udivrem_3by2() of the top digits.
  all_goals first
    | (rv_not_at 169; skip)
    | (refine Reach.trans (by2_div_top base _ _ ?_ ?_ ?_) ?_
       · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
         omega
       · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
         first
           | (simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_mul, Nat.zero_add]
              have := wT.isLt
              omega)
           | (rv_get hne : ¬BitVec.ofNat 64 (63 - (x.get 15#5).toNat.log2) = 0#64
              have hS0 := ofNat_S_ne (by omega) hne
              have hhi : (wT >>> ((BitVec.signExtend 64 (BitVec.setWidth 32 0#64 -
                  BitVec.setWidth 32 (BitVec.ofNat 64 (63 - (x.get 15#5).toNat.log2)))).toNat %
                    64)).toNat = wT.toNat / 2 ^ (64 - (63 - (x.get 15#5).toNat.log2)) := by
                rw [negw_shift _ (by omega) hS0, BitVec.toNat_ushiftRight,
                  Nat.shiftRight_eq_div_pow]
              rv_fold hhi
              rv_fold hhi
              exact top2_lt (S := 63 - (x.get 15#5).toNat.log2) (by omega)
                (by rw [hhi]; exact shr_lt_pow wT _ (by omega)) (BitVec.isLt _) (by omega))
       · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
         exact hv
       intro x' m' ⟨hm, hq0, hr0, h00, hfr⟩
       subst hm
       rw [regs_eq_sets _ x' _ h00 hfr]
       simp only [setRegs]
       rv_exec_cut 201
       -- The quotient word q[n - 2].
       refine Reach.step (by decide) rfl ?_
       simp only [StepGoal, Nat.reduceAdd]
       rv_val
       -- (n - 2) << 3 is computed for u[n - 2] and again for q[n - 2].
       rv_cse
       have hqa : x.get 10#5 + (x.get 13#5 + 18446744073709551614#64) <<< 3 =
           x.get 10#5 + BitVec.ofNat 64 (8 * ((x.get 13#5).toNat - 2)) := by
         rw [off_sub2 _ (by omega) hn8]
       rv_fold hqa
       rv_fold hqa
       rw [hqa]
       refine ⟨List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
         (mem_bufWords (by omega)))), ?_⟩
       rv_exec_cut 201)
  -- u[n - 1] ≤ d1: d subtracted from the top two words at most once.
  all_goals first
    | (rv_not_at 134; skip)
    | (simp only [zopz0zKzJ_u_eq, decide_eq_true_eq] at *
       refine Reach.trans (by2_sub_top base _ _ ?_ ?_) ?_
       · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
         omega
       · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
         rv_get hle : wT ≤ x.get 15#5
         exact BitVec.le_def.mp hle
       intro x' m' ⟨hm, hq0, hr0, h00, hfr⟩
       subst hm
       rw [regs_eq_sets _ x' _ h00 hfr]
       simp only [setRegs]
       rv_exec_cut 201
       -- The quotient word q[n - 2], 0 or 1.
       refine Reach.step (by decide) rfl ?_
       simp only [StepGoal, Nat.reduceAdd]
       rv_val
       have hqa : x.get 10#5 + x.get 13#5 <<< 3 + 18446744073709551600#64 =
           x.get 10#5 + BitVec.ofNat 64 (8 * ((x.get 13#5).toNat - 2)) := by
         rw [BitVec.add_assoc, off16 _ (by omega) hn8]
       rv_fold hqa
       rv_fold hqa
       rw [hqa]
       refine ⟨List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
         (mem_bufWords (by omega)))), ?_⟩
       rv_exec_cut 201)
  all_goals first
    | (rv_get hz : BitVec.ofNat 64 (63 - (x.get 15#5).toNat.log2) = 0#64
       rv_get hnz : ¬BitVec.ofNat 64 (63 - (x.get 15#5).toNat.log2) = 0#64
       exact absurd hz hnz)
    | skip
  -- u[n - 1] ≤ d1, s ≠ 0: the word u[n - 3] for the funnel shift of the remainder.
  all_goals first
    | (rv_not_at 153; skip)
    | (refine Reach.step (by decide) rfl ?_
       simp only [StepGoal, Nat.reduceAdd]
       rv_val
       have huc : x.get 12#5 + x.get 13#5 <<< 3 + 18446744073709551592#64 =
           x.get 12#5 + BitVec.ofNat 64 (8 * ((x.get 13#5).toNat - 3)) := by
         rw [BitVec.add_assoc, off24 _ hn3 hn8]
       rv_fold huc
       rv_fold huc
       rw [huc]
       refine ⟨List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
         (mem_bufWords (by omega)))), fun wC hwC => ?_⟩
       rv_exec_cut 201)
  -- The end of the division of the top digits.
  all_goals
    have ht3 : (x.get 13#5 <<< 3).toNat = 8 * (x.get 13#5).toNat % 2 ^ 64 := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]
    rv_fold ht3
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte] at hq0 hr0
    -- The words of u in the memory at the start.
    have hwTm : wT.toNat = wordAt m (x.get 12#5) ((x.get 13#5).toNat - 1) := by
      rw [hwT.eq, memWord_stack_u _ _ _ (x.get 13#5).toNat _ _ _ _ (by omega) hun8 hsn hdsu,
        show (x.get 11#5).toNat = (x.get 13#5).toNat - 1 by omega]
    have hwAm : wA.toNat = wordAt m (x.get 12#5) ((x.get 13#5).toNat - 2) := by
      rw [hwA.eq, memWord_stack_u _ _ _ (x.get 13#5).toNat _ _ _ _ (by omega) hun8 hsn hdsu]
    -- The quotient word q[n - 2] and the remainder of the top digits on the four kinds of path.
    first
      | (rv_has LeanRV64D.Functions.zopz0zKzJ_u (x.get 15#5) wT = false
         rv_has BitVec.ofNat 64 (63 - (x.get 15#5).toNat.log2) = 0#64
         rv_get hz : BitVec.ofNat 64 (63 - (x.get 15#5).toNat.log2) = 0#64
         have hS0 := ofNat_S_eq (by omega) hz
         have hU : (0#64).toNat * 2 ^ 128 + wT.toNat * 2 ^ 64 + wA.toNat = words m (x.get 12#5) (x.get 13#5).toNat * 2 ^ (63 - (x.get 15#5).toNat.log2) / 2 ^ (64 * ((x.get 13#5).toNat - 2)) := by
           rw [hS0, pow_zero, Nat.mul_one, by2_top3_s0 _ _ _ hn3, hwTm, hwAm]; simp
         rw [hU, hdn] at hq0 hr0
         have h9 : (x' 7#5).toNat + 2 ^ 64 * (x' 29#5).toNat < ((x.get 14#5).toNat + 2 ^ 64 * (x.get 15#5).toNat) * 2 ^ (63 - (x.get 15#5).toNat.log2) := by
           rw [Regs.eq_get x' (show (7#5 : BitVec 5) ≠ 0 by decide), Regs.eq_get x' (show (29#5 : BitVec 5) ≠ 0 by decide), hr0]; exact Nat.mod_lt _ hDp
         have h10 : (x' 15#5).toNat * (((x.get 14#5).toNat + 2 ^ 64 * (x.get 15#5).toNat) * 2 ^ (63 - (x.get 15#5).toNat.log2)) + ((x' 7#5).toNat + 2 ^ 64 * (x' 29#5).toNat) =
             words m (x.get 12#5) (x.get 13#5).toNat * 2 ^ (63 - (x.get 15#5).toNat.log2) / 2 ^ (64 * ((x.get 13#5).toNat - 2)) := by
           rw [Regs.eq_get x' (show (7#5 : BitVec 5) ≠ 0 by decide), Regs.eq_get x' (show (29#5 : BitVec 5) ≠ 0 by decide), Regs.eq_get x' (show (15#5 : BitVec 5) ≠ 0 by decide), hq0, hr0]; exact Nat.div_add_mod' _ _)
      | (rv_has LeanRV64D.Functions.zopz0zKzJ_u (x.get 15#5) wT = false
         rv_get hne : ¬BitVec.ofNat 64 (63 - (x.get 15#5).toNat.log2) = 0#64
         have hS0 := ofNat_S_ne (by omega) hne
         have hwCm : wC.toNat = wordAt m (x.get 12#5) ((x.get 13#5).toNat - 3) := by
           first
             | rw [hwC.eq, memWord_stack_u _ _ _ (x.get 13#5).toNat _ _ _ _ (by omega) hun8 hsn hdsu]
             | rw [hwC.eq]
         have hhi : (wT >>> ((BitVec.signExtend 64 (BitVec.setWidth 32 0#64 -
             BitVec.setWidth 32 (BitVec.ofNat 64 (63 - (x.get 15#5).toNat.log2)))).toNat % 64)).toNat =
             wT.toNat / 2 ^ (64 - (63 - (x.get 15#5).toNat.log2)) := by
           rw [negw_shift _ (by omega) hS0, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
         rv_fold hhi
         rv_fold hhi
         have hu1 := toNat_fshl_code wT wA (BitVec.ofNat 64 (63 - (x.get 15#5).toNat.log2)) (by rw [hSt]; omega)
         rv_fold hu1
         rv_fold hu1
         have hu0 := toNat_fshl_code wA wC (BitVec.ofNat 64 (63 - (x.get 15#5).toNat.log2)) (by rw [hSt]; omega)
         rv_fold hu0
         rv_fold hu0
         rw [hSt] at hu1 hu0
         rw [hhi, hu1, hu0, hwTm, hwAm, hwCm, ← by2_top3 m (x.get 12#5) (x.get 13#5).toNat _ hS64' hn3,
           hdn] at hq0 hr0
         have h9 : (x' 7#5).toNat + 2 ^ 64 * (x' 29#5).toNat < ((x.get 14#5).toNat + 2 ^ 64 * (x.get 15#5).toNat) * 2 ^ (63 - (x.get 15#5).toNat.log2) := by
           rw [Regs.eq_get x' (show (7#5 : BitVec 5) ≠ 0 by decide), Regs.eq_get x' (show (29#5 : BitVec 5) ≠ 0 by decide), hr0]; exact Nat.mod_lt _ hDp
         have h10 : (x' 15#5).toNat * (((x.get 14#5).toNat + 2 ^ 64 * (x.get 15#5).toNat) * 2 ^ (63 - (x.get 15#5).toNat.log2)) + ((x' 7#5).toNat + 2 ^ 64 * (x' 29#5).toNat) =
             words m (x.get 12#5) (x.get 13#5).toNat * 2 ^ (63 - (x.get 15#5).toNat.log2) / 2 ^ (64 * ((x.get 13#5).toNat - 2)) := by
           rw [Regs.eq_get x' (show (7#5 : BitVec 5) ≠ 0 by decide), Regs.eq_get x' (show (29#5 : BitVec 5) ≠ 0 by decide), Regs.eq_get x' (show (15#5 : BitVec 5) ≠ 0 by decide), hq0, hr0]; exact Nat.div_add_mod' _ _)
      | (rv_has wT ≤ x.get 15#5
         rv_has BitVec.ofNat 64 (63 - (x.get 15#5).toNat.log2) = 0#64
         rv_get hz : BitVec.ofNat 64 (63 - (x.get 15#5).toNat.log2) = 0#64
         have hS0 := ofNat_S_eq (by omega) hz
         have hU : wA.toNat + 2 ^ 64 * wT.toNat = words m (x.get 12#5) (x.get 13#5).toNat * 2 ^ (63 - (x.get 15#5).toNat.log2) / 2 ^ (64 * ((x.get 13#5).toNat - 2)) := by
           rw [hS0, pow_zero, Nat.mul_one, by2_top3_s0 _ _ _ hn3, hwTm, hwAm]; ring
         have hD1 : ((x.get 14#5).toNat + 2 ^ 64 * (x.get 15#5).toNat) * 2 ^ (63 - (x.get 15#5).toNat.log2) = (x.get 14#5).toNat + 2 ^ 64 * (x.get 15#5).toNat := by
           rw [hS0]; simp
         have h9 : (x' 7#5).toNat + 2 ^ 64 * (x' 29#5).toNat < ((x.get 14#5).toNat + 2 ^ 64 * (x.get 15#5).toNat) * 2 ^ (63 - (x.get 15#5).toNat.log2) := by
           rw [Regs.eq_get x' (show (7#5 : BitVec 5) ≠ 0 by decide), Regs.eq_get x' (show (29#5 : BitVec 5) ≠ 0 by decide), hr0, hD1]; exact Nat.mod_lt _ (by omega)
         have h10 : (x' 14#5).toNat * (((x.get 14#5).toNat + 2 ^ 64 * (x.get 15#5).toNat) * 2 ^ (63 - (x.get 15#5).toNat.log2)) + ((x' 7#5).toNat + 2 ^ 64 * (x' 29#5).toNat) =
             words m (x.get 12#5) (x.get 13#5).toNat * 2 ^ (63 - (x.get 15#5).toNat.log2) / 2 ^ (64 * ((x.get 13#5).toNat - 2)) := by
           rw [Regs.eq_get x' (show (7#5 : BitVec 5) ≠ 0 by decide), Regs.eq_get x' (show (29#5 : BitVec 5) ≠ 0 by decide), Regs.eq_get x' (show (14#5 : BitVec 5) ≠ 0 by decide), hq0, hr0, hD1, ← hU]; exact Nat.div_add_mod' _ _)
      | (rv_has wT ≤ x.get 15#5
         rv_get hne : ¬BitVec.ofNat 64 (63 - (x.get 15#5).toNat.log2) = 0#64
         have hS0 := ofNat_S_ne (by omega) hne
         have hwCm : wC.toNat = wordAt m (x.get 12#5) ((x.get 13#5).toNat - 3) := by
           first
             | rw [hwC.eq, memWord_stack_u _ _ _ (x.get 13#5).toNat _ _ _ _ (by omega) hun8 hsn hdsu]
             | rw [hwC.eq]
         have hf0 := toNat_fshl_code (x' 7#5) wC (BitVec.ofNat 64 (63 - (x.get 15#5).toNat.log2)) (by rw [hSt]; omega)
         rv_fold hf0
         rv_fold hf0
         have hf1 := toNat_fshl_code (x' 29#5) (x' 7#5) (BitVec.ofNat 64 (63 - (x.get 15#5).toNat.log2)) (by rw [hSt]; omega)
         rv_fold hf1
         rv_fold hf1
         rw [hSt] at hf0 hf1
         rw [Regs.eq_get x' (show (7#5 : BitVec 5) ≠ 0 by decide)] at hf0
         rw [Regs.eq_get x' (show (7#5 : BitVec 5) ≠ 0 by decide), Regs.eq_get x' (show (29#5 : BitVec 5) ≠ 0 by decide)] at hf1
         have hT : (x'.get 7#5).toNat + 2 ^ 64 * (x'.get 29#5).toNat <
             (x.get 14#5).toNat + 2 ^ 64 * (x.get 15#5).toNat := by
           rw [hr0]; exact Nat.mod_lt _ (by omega)
         have hrem := norm2_low (x'.get 7#5).toNat (x'.get 29#5).toNat wC.toNat _ (BitVec.isLt _)
           (BitVec.isLt _) hS64'
           ((Nat.mul_lt_mul_of_pos_right hT (Nat.two_pow_pos _)).trans (lt_2_128_of_words hdn))
         rw [← hf0, ← hf1, hr0] at hrem
         have hUn : words m (x.get 12#5) (x.get 13#5).toNat * 2 ^ (63 - (x.get 15#5).toNat.log2) / 2 ^ (64 * ((x.get 13#5).toNat - 2)) = (wA.toNat + 2 ^ 64 * wT.toNat) * 2 ^ (63 - (x.get 15#5).toNat.log2) +
             wC.toNat / 2 ^ (64 - (63 - (x.get 15#5).toNat.log2)) := by
           rw [norm3_words _ _ _ _ (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _) hS64', hwTm, hwAm,
             hwCm, by2_top3 m (x.get 12#5) (x.get 13#5).toNat _ hS64' hn3]
         obtain ⟨hdq, hdr⟩ := div_norm_low (T := wA.toNat + 2 ^ 64 * wT.toNat)
           (d := (x.get 14#5).toNat + 2 ^ 64 * (x.get 15#5).toNat)
           (S := 63 - (x.get 15#5).toNat.log2) (by omega) (shr_lt_pow wC _ hS64')
         have h9 : ∀ r, r = (wA.toNat + 2 ^ 64 * wT.toNat) % ((x.get 14#5).toNat +
             2 ^ 64 * (x.get 15#5).toNat) * 2 ^ (63 - (x.get 15#5).toNat.log2) +
             wC.toNat / 2 ^ (64 - (63 - (x.get 15#5).toNat.log2)) → r < ((x.get 14#5).toNat + 2 ^ 64 * (x.get 15#5).toNat) * 2 ^ (63 - (x.get 15#5).toNat.log2) := by
           intro r hr; rw [hr, ← hdr]; exact Nat.mod_lt _ hDp
         have h10 : ∀ r, r = (wA.toNat + 2 ^ 64 * wT.toNat) % ((x.get 14#5).toNat +
             2 ^ 64 * (x.get 15#5).toNat) * 2 ^ (63 - (x.get 15#5).toNat.log2) +
             wC.toNat / 2 ^ (64 - (63 - (x.get 15#5).toNat.log2)) →
             (x' 14#5).toNat * (((x.get 14#5).toNat + 2 ^ 64 * (x.get 15#5).toNat) * 2 ^ (63 - (x.get 15#5).toNat.log2)) + r = words m (x.get 12#5) (x.get 13#5).toNat * 2 ^ (63 - (x.get 15#5).toNat.log2) / 2 ^ (64 * ((x.get 13#5).toNat - 2)) := by
           intro r hr; rw [hr, Regs.eq_get x' (show (14#5 : BitVec 5) ≠ 0 by decide), hq0, ← hdr, ← hdq, hUn]; exact Nat.div_add_mod' _ _)
    refine by2_top_exit base x m hpre0 hr _ _ ?_
    simp only [by2Top, By2Frame]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      (by2_frame_top m _ _ _ _ _ _ _ _ _ (by omega) hqn hsn hdsq rfl).1,
      (by2_frame_top m _ _ _ _ _ _ _ _ _ (by omega) hqn hsn hdsq rfl).2.1,
      (by2_frame_top m _ _ _ _ _ _ _ _ _ (by omega) hqn hsn hdsq rfl).2.2.1,
      (by2_frame_top m _ _ _ _ _ _ _ _ _ (by omega) hqn hsn hdsq rfl).2.2.2, ?_⟩
    · trivial
    · trivial
    · trivial
    · exact ht3
    · exact hSt
    · trivial
    · exact hdn
    · rw [← hdn]; exact hv
    · first | exact h9 | exact h9 _ hrem
    · rw [memWord_memStore_self]; first | exact h10 | exact h10 _ hrem
    · trivial
    · trivial
    · intro r hr h2' h8' h9' h18'
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;>
      first
        | exact absurd rfl h2' | exact absurd rfl h8' | exact absurd rfl h9'
        | exact absurd rfl h18'
        | simp (config := { decide := true }) only [↓reduceIte]


/-- The frame below sp is outside the image: its first and last words are. -/
theorem frame_outside (sp base : BitVec 64) (o1 o2 : Nat)
    (h0 : (sp - 32#64).toNat + 8 ≤ base.toNat ∨ base.toNat + o1 + o2 ≤ (sp - 32#64).toNat)
    (h3 : (sp - 32#64 + BitVec.ofNat 64 (8 * 3)).toNat + 8 ≤ base.toNat ∨
      base.toNat + o1 + o2 ≤ (sp - 32#64 + BitVec.ofNat 64 (8 * 3)).toNat)
    (hs : (sp - 32#64).toNat + 32 ≤ 2 ^ 64) (hoff : 32 ≤ o1 + o2) :
    (sp - 32#64).toNat + 32 ≤ base.toNat ∨ base.toNat + o1 + o2 ≤ (sp - 32#64).toNat := by
  have : (sp - 32#64 + BitVec.ofNat 64 (8 * 3)).toNat = (sp - 32#64).toNat + 24 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  omega

theorem udivrem_by2.proof : udivrem_by2.spec := by
  apply runsI_of_reach udivrem_by2_image_decodes
  intro base ret _ hr _ _ hw x m hx1 hbufs hhold hpre
  rw [show udivrem_by2_image_dataOff = 1256 from rfl] at hw hhold hbufs ⊢
  rw [show udivrem_by2_image_data.length = 256 from rfl] at hw hbufs ⊢
  have hx : x.get 1#5 = ret := by rw [← Regs.eq_get x (by decide)]; exact hx1
  have hpre' := hpre
  simp only [udivrem_by2.pre, Buf] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  have hst := frame_outside (x 2#5) base 1256 (8 * 256)
    (hbufs _ (List.mem_append_right _ (mem_bufWords_zero (by norm_num))))
    (hbufs _ (List.mem_append_right _ (mem_bufWords (by norm_num))))
    (by rw [Regs.eq_get x (by decide)]; exact hpre'.2.2.2.1.2) (by norm_num)
  rw [Regs.eq_get x (by decide)] at hst
  rw [show udivrem_by2_entry = udivrem_by2_image_udivrem_by2_offset from rfl, dataWords, ← hx]
  refine Reach.lift udivrem_by2_image_udivrem_by2_in (by decide) ?_
  have hT : (base + BitVec.ofNat 64 1256).toNat = base.toNat + 1256 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have h := udivrem_by2.reach 0x0#20 0x410#12 (pcAt base udivrem_by2_image_udivrem_by2_offset) _
    x m (by simp only [udivrem_by2_image_udivrem_by2_offset, pcAt, BitVec.reduceAppend,
      BitVec.reduceSignExtend]; bv_omega)
    (by rw [hT]; omega) (hx ▸ hr) (by rw [hT]; omega) hhold hpre
  rwa [pcAt_zero] at h

/-- The registers of the nonvacuous instance: q of 2 words and u of 3 words above the data, the
divisor 2^64 and the frame below sp. -/
theorem udivrem_by2.nonvacuous :
    NonVacuousI udivrem_by2_image_code udivrem_by2_image_data udivrem_by2_image_dataOff
      udivrem_by2.bufs udivrem_by2.pre :=
  nonVacuousI_of (fun i => if i = 10#5 then 0x80000C00#64 else if i = 11#5 then 2#64
      else if i = 12#5 then 0x80000C10#64 else if i = 13#5 then 3#64 else if i = 15#5 then 1#64
      else if i = 2#5 then 0x80000C60#64 else 0)
    (by decide) (by decide) (by decide) (by decide)
    (by simp only [udivrem_by2.bufs, ↓reduceIte, BitVec.reduceEq, BitVec.toNat_ofNat,
          Nat.reducePow, Nat.reduceMod, BitVec.reduceSub, bufWords, List.cons_append,
          List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq]
        decide)
    (fun _ => by simp only [udivrem_by2.pre, Buf, Disjoint]; decide)

end IntxRV.Api
