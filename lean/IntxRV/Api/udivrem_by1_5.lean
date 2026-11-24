import IntxRV.DivBy15
/-!
# `internal::udivrem_by1()` of 5 words

The specification, from `include/intx/intx.hpp`:

```cpp
/// Divides arbitrary long unsigned integer by 64-bit unsigned integer (1 word).
/// @param q  The quotient words. It may be u.
/// @param u  The numerator words.
/// @param d  The divisor.
/// @return   The remainder.
/// @pre 2 <= u.size()
/// @pre q.size() = u.size()
/// @pre 0 < d
/// @post q = u / d
/// @post result = u % d
/// @note FV: not proved for q that overlaps u.
template <size_t W>
constexpr uint64_t udivrem_by1(std::span<uint64_t, W> q,
    std::type_identity_t<std::span<const uint64_t, W>> u, uint64_t d) noexcept
```

`udivrem_by1_5.spec` states it for the RV64 machine code of `udivrem_by1_5` in `IntxRV/Api.cpp`,
the instance for spans of 5 words, which `udivrem<320, 256>()` calls. The function normalizes `d`,
computes the reciprocal with the table of the image as the dynamic instance does
(`IntxRV/Api/udivrem_by1.lean`), divides the top digits of the shifted numerator into q[4] on the
four kinds of path of the shift 0 or not and u[4] below d or not, and runs the unrolled digits 3 to
0 (`IntxRV/DivBy15.lean`). `udivrem_by1_5.reach` is the run for any immediates of the address of
the table, for the functions that call it.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
-- The guards that select the paths do not change the goals.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- The run of `udivrem_by1<5>()` from its start to the return address in ra, for the immediates
`hi` and `lo` of the address `T` of the table of the reciprocal, which differ in each image. -/
theorem udivrem_by1_5.reach (hi : BitVec 20) (lo : BitVec 12) (base T : BitVec 64) (x : Regs)
    (m : Mem) (hT : pcAt base 5 + ((hi ++ 0x000#12).signExtend 64 + lo.signExtend 64) = T)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64) (hr : x.get 1#5 &&& 3 = 0)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hpre : udivrem_by1_5.pre x m) :
    Reach (udivrem_by1_5.bufs x ++ bufWords T 256) (udivrem_by1_5_progAt hi lo) base (pcAt base 0)
      x m (x.get 1#5) (udivrem_by1_5.post x m) := by
  have hpre0 := hpre
  simp only [udivrem_by1_5.pre, udivrem_by1_5.bufs, Buf, Disjoint] at hpre ⊢
  simp (disch := decide) only [Regs.eq_get x] at hpre ⊢
  obtain ⟨⟨hqa, hqn⟩, ⟨hua, hun⟩, hdis, -, -, hdpos⟩ := hpre
  have hd0 : x.get 12#5 ≠ 0 := by
    intro h; rw [h] at hdpos; simp at hdpos
  have hd0' : (x.get 12#5).toNat ≠ 0 := by omega
  rv_exec_cut 84
  obtain ⟨hdn, hdn63⟩ := norm_shift _ hd0
  -- The count of the leading zeros of d and the normalized divisor dn, with the names of the run.
  have hs := clz_ite (x.get 12#5)
  rw [if_neg hd0, swarClz_expand, smear_expand] at hs
  rv_fold hs
  rw [← hs] at hdn
  rv_fold hdn
  rw [← hdn] at hdn63
  -- The address of the table in the run.
  simp only [hT] at *
  -- The table entry of dn: the low half.
  refine Reach.step (by decide) rfl ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  have ha := table_addr_by1 _ T hdn63
  rv_fold ha
  have hix := index_lt_256 hdn63
  rw [ha]
  refine ⟨Or.inl (List.mem_append_right _ (mem_bufWords hix)), fun wL hwL => ?_⟩
  rw [memHalf_lo,
    holdsData_get hhold (by rw [show reciprocal_2by1_image_data.length = 256 from rfl]; exact hix),
    ← List.getD_eq_getElem _ 0, image_data_get _ hix] at hwL
  rv_exec_cut 84
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
  rw [table_entry_add4 T hdn63 hw, memHalf_hi,
    holdsData_get hhold (by rw [show reciprocal_2by1_image_data.length = 256 from rfl]; exact hix),
    ← List.getD_eq_getElem _ 0, image_data_get _ hix] at hwH
  rv_exec_cut 68
  -- The words u[3] and u[4] of the numerator.
  refine Reach.step (by decide) rfl ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  refine ⟨List.mem_append_left _ (List.mem_append_left _ (mem_bufWords (i := 3) (by norm_num))),
    fun wA hwA => ?_⟩
  refine Reach.step (by decide) rfl ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  refine ⟨List.mem_append_left _ (List.mem_append_left _ (mem_bufWords (i := 4) (by norm_num))),
    fun wB hwB => ?_⟩
  rv_exec_cut 84
  -- The reciprocal.
  obtain ⟨hL, hH⟩ := table_LH hdn63 hwL hwH
  have hv := recip2BV_spec _ wL wH hdn63 hL hH
  simp only [recip2BV] at hv
  rv_fold hv
  subst hs
  have hL64 : Nat.log2 (x.get 12#5).toNat < 64 := (Nat.log2_lt hd0').mpr (x.get 12#5).isLt
  have hD : 0 < (x.get 12#5).toNat * 2 ^ (63 - (x.get 12#5).toNat.log2) :=
    Nat.mul_pos (by omega) (Nat.two_pow_pos _)
  have hS64 : 63 - Nat.log2 (x.get 12#5).toNat < 64 := by omega
  rv_exec_cut 131
  all_goals try simp only [zopz0zKzJ_u_eq, zopz0zI_u_eq, decide_eq_true_eq, decide_eq_false_iff_not] at *
  -- The paths that test the shift twice with opposite results.
  all_goals try (rv_get hz : BitVec.ofNat 64 (63 - (x.get 12#5).toNat.log2) = 0#64
                 rv_get hnz : ¬BitVec.ofNat 64 (63 - (x.get 12#5).toNat.log2) = 0#64
                 exact absurd hz hnz)
  -- The top digits of the normalized numerator, and the digit 3.
  all_goals
    have htop := by1_top m (x.get 11#5) 5 (63 - Nat.log2 (x.get 12#5).toNat) (by omega) (by norm_num)
    simp only [wordAt, show 5 - 1 - 1 = 3 from rfl, show 5 - 1 = 4 from rfl, Nat.reduceMul] at htop
    rw [← hwA.eq, ← hwB.eq] at htop
    have hd3 := norm_digit m (x.get 11#5) 5 (63 - Nat.log2 (x.get 12#5).toNat) 3 (by omega)
      (by norm_num) (by norm_num)
    simp only [wordAt, show 3 - 1 = 2 from rfl, Nat.reduceMul] at hd3
    rw [← hwA.eq] at hd3
    rv_fold hd3
  -- s ≠ 0, u[4] ≥ d: the division of the top digits.
  all_goals first
    | (rv_lacks ¬BitVec.ofNat 64 (63 - (x.get 12#5).toNat.log2) = 0#64; skip)
    | (rv_lacks ¬wB < x.get 12#5; skip)
    | (rv_get hne : ¬BitVec.ofNat 64 (63 - (x.get 12#5).toNat.log2) = 0#64
       have hS0 := ofNat_S_ne (by omega) hne
       have hs := div2by1BV_spec (wB >>> ((BitVec.signExtend 64 (BitVec.setWidth 32 0#64 -
         BitVec.setWidth 32 (BitVec.ofNat 64 (63 - (x.get 12#5).toNat.log2)))).toNat % 64))
         ((wB <<< ((BitVec.ofNat 64 (63 - (x.get 12#5).toNat.log2)).toNat % 64)) |||
           ((wA >>> 1) >>> ((BitVec.ofNat 64 (63 - (x.get 12#5).toNat.log2) ^^^
             18446744073709551615#64).toNat % 64))) _ _ hdn63
         (top_hi_lt hdn63 (by omega) hS0) hv
       simp only [div2by1BV] at hs
       rv_fold hs
       rv_fold hs
       try simp (disch := assumption) only [if_pos, if_neg] at hs
       try simp only [BitVec.add_assoc] at hs
       rv_fold hs
       have hhi : (wB >>> ((BitVec.signExtend 64 (BitVec.setWidth 32 0#64 - BitVec.setWidth 32
           (BitVec.ofNat 64 (63 - (x.get 12#5).toNat.log2)))).toNat % 64)).toNat =
           wB.toNat / 2 ^ (64 - (63 - (x.get 12#5).toNat.log2)) := by
         rw [negw_shift _ (by omega) hS0, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
       have hlo := toNat_fshl_code wB wA (BitVec.ofNat 64 (63 - (x.get 12#5).toNat.log2))
         (by rw [ofNat_S_toNat (by omega)]; omega)
       rv_fold hhi
       rv_fold hhi
       rv_fold hlo
       rv_fold hlo
       rw [ofNat_S_toNat (by omega)] at hlo
       rw [← hhi, ← hlo] at htop
       rw [hdn] at hs
       have hT := top_div hD htop hs.1 hs.2
       skip)
  -- s ≠ 0, u[4] < d: the top quotient word 0.
  all_goals first
    | (rv_lacks ¬BitVec.ofNat 64 (63 - (x.get 12#5).toNat.log2) = 0#64; skip)
    | (rv_lacks wB < x.get 12#5; skip)
    | (rv_get hlt : wB < x.get 12#5
       have hlo := toNat_fshl_code wB wA (BitVec.ofNat 64 (63 - (x.get 12#5).toNat.log2))
         (by rw [ofNat_S_toNat (by omega)]; omega)
       rv_fold hlo
       rv_fold hlo
       rw [ofNat_S_toNat (by omega)] at hlo
       rw [← hlo] at htop
       have hT := top_zero (d := (x.get 12#5).toNat) (by omega) (by rw [← hdn]; exact BitVec.isLt _)
         (by simp only [BitVec.lt_def] at hlt; exact hlt) htop hlo wA.isLt
       rw [show (0 : Nat) = (0#64).toNat from rfl] at hT)
  -- s = 0, u[4] ≥ d: the division of 0:u[4].
  all_goals first
    | (rv_lacks BitVec.ofNat 64 (63 - (x.get 12#5).toNat.log2) = 0#64; skip)
    | (rv_lacks x.get 12#5 ≤ wB; skip)
    | (rv_get hz : BitVec.ofNat 64 (63 - (x.get 12#5).toNat.log2) = 0#64
       have hS0 := ofNat_S_eq (by omega) hz
       have hs := div2by1BV_spec 0#64 wB _ _ hdn63 (by rw [BitVec.toNat_ofNat]; omega) hv
       simp only [div2by1BV, BitVec.zero_add] at hs
       rv_fold hs
       rv_fold hs
       try simp (disch := assumption) only [if_pos, if_neg] at hs
       try simp only [BitVec.add_assoc] at hs
       rv_fold hs
       have hU0 : 2 ^ 64 * (wB.toNat / 2 ^ (64 - (63 - (x.get 12#5).toNat.log2))) +
           (wB.toNat * 2 ^ (63 - (x.get 12#5).toNat.log2) +
             wA.toNat / 2 ^ (64 - (63 - (x.get 12#5).toNat.log2))) % 2 ^ 64 =
           2 ^ 64 * (0#64).toNat + wB.toNat := by
         rw [hS0, top_s0 _ _ wB.isLt wA.isLt]; simp
       rw [hdn] at hs
       have hT := top_div hD (htop.trans hU0) hs.1 hs.2)
  -- s = 0, u[4] < d: the top quotient word 0 and the remainder u[4].
  all_goals first
    | (rv_lacks BitVec.ofNat 64 (63 - (x.get 12#5).toNat.log2) = 0#64; skip)
    | (rv_lacks ¬x.get 12#5 ≤ wB; skip)
    | (rv_get hz : BitVec.ofNat 64 (63 - (x.get 12#5).toNat.log2) = 0#64
       rv_get hlt : ¬x.get 12#5 ≤ wB
       have hS0 := ofNat_S_eq (by omega) hz
       have hU0 : 2 ^ 64 * (wB.toNat / 2 ^ (64 - (63 - (x.get 12#5).toNat.log2))) +
           (wB.toNat * 2 ^ (63 - (x.get 12#5).toNat.log2) +
             wA.toNat / 2 ^ (64 - (63 - (x.get 12#5).toNat.log2))) % 2 ^ 64 = wB.toNat := by
         rw [hS0, top_s0 _ _ wB.isLt wA.isLt]
       have hT : (0#64).toNat * ((x.get 12#5).toNat * 2 ^ (63 - (x.get 12#5).toNat.log2)) +
           wB.toNat = words m (x.get 11#5) 5 * 2 ^ (63 - (x.get 12#5).toNat.log2) / 2 ^ 256 ∧
           wB.toNat < (x.get 12#5).toNat * 2 ^ (63 - (x.get 12#5).toNat.log2) := by
         simp only [BitVec.le_def, not_le] at hlt
         rw [htop, hU0, hS0]; simp; exact hlt)
  -- The digit 3 in a7, and the state of the division of the digit 3.
  all_goals
    have hdig3 : True := trivial
    first
      | (rv_has ¬BitVec.ofNat 64 (63 - (x.get 12#5).toNat.log2) = 0#64
         have hlo3 := toNat_fshl_code wA (memWord m (x.get 11#5 + 16#64).toNat)
           (BitVec.ofNat 64 (63 - (x.get 12#5).toNat.log2)) (by rw [ofNat_S_toNat hS64]; exact hS64)
         rv_fold hlo3
         rv_fold hlo3
         rw [ofNat_S_toNat hS64, ← hd3] at hlo3
         clear hdig3
         have hdig3 := hlo3)
      | (rv_get hz : BitVec.ofNat 64 (63 - (x.get 12#5).toNat.log2) = 0#64
         have hS0 := ofNat_S_eq hS64 hz
         rw [hS0] at hd3
         simp only [pow_zero, Nat.mul_one, Nat.sub_zero] at hd3
         rw [Nat.div_eq_of_lt (BitVec.isLt _), Nat.add_zero, Nat.mod_eq_of_lt (BitVec.isLt _)] at hd3
         clear hdig3
         have hdig3 : wA.toNat = words m (x.get 11#5) 5 * 2 ^ (63 - (x.get 12#5).toNat.log2) /
             2 ^ 192 % 2 ^ 64 := by rw [hS0, pow_zero, Nat.mul_one]; exact hd3.symm)
    refine by15_d3 base x m hpre0 hr _ _ ?_ ?_ ?_ ?_
    · simp only [By15St]
      simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      refine ⟨hdn, by rw [hv, hdn], trivial, trivial, trivial, hT.2, by simpa using hdig3, ?_, ?_,
        trivial, ?_⟩
      · simp only [BitVec.reduceSignExtend, Nat.reduceAdd, Nat.reduceMul,
          show 4 - 3 = 1 from rfl]
        rw [words_one_memStore]
        simpa using hT.1
      · simp only [BitVec.reduceSignExtend]
        exact (unchangedExcept_memStore _ _ ⟨by bv_omega, by bv_omega⟩).mpr
          (unchangedExcept_refl _ _ _)
      · intro r hr'
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl <;>
        first | rfl | simp (config := { decide := true }) only [↓reduceIte]
    all_goals simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    all_goals assumption

theorem udivrem_by1_5.proof : udivrem_by1_5.spec := by
  apply runsI_of_reach udivrem_by1_5_image_decodes
  intro base ret _ hr _ _ hw x m hx1 _ hhold hpre
  rw [show udivrem_by1_5_image_dataOff = 976 from rfl] at hw hhold ⊢
  rw [show udivrem_by1_5_image_data.length = 256 from rfl] at hw ⊢
  have hx : x.get 1#5 = ret := by rw [← Regs.eq_get x (by decide)]; exact hx1
  rw [show udivrem_by1_5_entry = udivrem_by1_5_image_udivrem_by1_5_offset from rfl, dataWords, ← hx]
  refine Reach.lift udivrem_by1_5_image_udivrem_by1_5_in (by decide) ?_
  have h := udivrem_by1_5.reach 0x0#20 0x3bc#12 (pcAt base udivrem_by1_5_image_udivrem_by1_5_offset)
    _ x m
    (by simp only [udivrem_by1_5_image_udivrem_by1_5_offset, pcAt, BitVec.reduceAppend,
      BitVec.reduceSignExtend]; bv_omega)
    (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (hx ▸ hr) hhold hpre
  rwa [pcAt_zero] at h

theorem udivrem_by1_5.nonvacuous :
    NonVacuousI udivrem_by1_5_image_code udivrem_by1_5_image_data udivrem_by1_5_image_dataOff
      udivrem_by1_5.bufs udivrem_by1_5.pre :=
  nonVacuousI_of (fun i => if i = 10#5 then 0x80000C00#64 else if i = 11#5 then 0x80000C28#64
      else if i = 12#5 then 1#64 else 0)
    (by decide) (by decide) (by decide) (by decide)
    (by rw [show udivrem_by1_5_image_dataOff = 976 from rfl,
          show udivrem_by1_5_image_data.length = 256 from rfl]
        simp only [udivrem_by1_5.bufs, ↓reduceIte, BitVec.reduceEq, bufWords, List.cons_append,
          List.nil_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        repeat' apply And.intro
        all_goals decide)
    (fun _ => by simp only [udivrem_by1_5.pre, Buf, Disjoint]; decide)

end IntxRV.Api
