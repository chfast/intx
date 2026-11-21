import IntxRV.DivBy1
/-!
# `internal::udivrem_by1()` of a span

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
template <size_t W>
constexpr uint64_t udivrem_by1(std::span<uint64_t, W> q,
    std::type_identity_t<std::span<const uint64_t, W>> u, uint64_t d) noexcept
```

`udivrem_by1.spec` states it for the RV64 machine code of `udivrem_by1` in `IntxRV/Api.cpp`, the
version for spans of dynamic extent (generated in `IntxRV/Gen/Api.lean`, see `IntxRV/README.md`),
for `q` and `u` that do not overlap. The function normalizes `d` with the count of its leading
zeros (`clz_ite`), computes the reciprocal with the table of the image (`recip2BV_spec`), divides
the top digits of the shifted numerator into the top quotient word, runs the loop over the words
below it and divides the last digit (`IntxRV/DivBy1.lean`). `rv_exec_cut` runs the code up to the
head of the loop and its exit, where `by1_loop` and `by1_exit` take over.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
-- The guards that select the paths do not change the goals.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem udivrem_by1.proof : udivrem_by1.spec := by


  apply runsI_of_reach udivrem_by1_image_decodes
  intro base ret hb hr hc hl hw x m hx1 hbufs hhold hpre
  have hpre0 := hpre
  simp only [udivrem_by1.pre, udivrem_by1.bufs, Buf, Disjoint] at hpre ⊢
  simp (disch := decide) only [Regs.eq_get x] at hpre hx1 ⊢
  simp only [udivrem_by1_entry, show udivrem_by1_image_data.length = 256 from rfl,
    show udivrem_by1_image_dataOff = 776 from rfl] at *
  have hd0 : x.get 14#5 ≠ 0 := by
    intro h; rw [h] at hpre; simp at hpre
  have hd0' : (x.get 14#5).toNat ≠ 0 := by omega
  rv_exec_cut 148 167
  obtain ⟨hdn, hdn63⟩ := norm_shift _ hd0
  -- The count of the leading zeros of d and the normalized divisor dn, with the names of the run.
  have hs := clz_ite (x.get 14#5)
  rw [if_neg hd0, swarClz_expand, smear_expand] at hs
  rv_fold hs
  rw [← hs] at hdn
  rv_fold hdn
  rw [← hdn] at hdn63
  -- The table entry of dn: the low half.
  refine Reach.step (by decide) rfl ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  have ha := table_addr_by1 _ base hdn63
  rv_fold ha
  have hi := index_lt_256 hdn63
  rw [ha]
  refine ⟨Or.inl (List.mem_append_right _ (mem_bufWords hi)), fun wL hwL => ?_⟩
  rw [memHalf_lo,
    holdsData_get hhold (by rw [show udivrem_by1_image_data.length = 256 from rfl]; exact hi),
    ← List.getD_eq_getElem _ 0, show udivrem_by1_image_data = reciprocal_2by1_image_data from rfl,
    image_data_get _ hi] at hwL
  rv_exec_cut 148 167
  -- The high half.
  refine Reach.step (by decide) rfl ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  have hah := table_addr_by1_hi _ base hdn63
  rv_fold hah
  rw [hah]
  refine ⟨Or.inr (by
    rw [show ∀ a : BitVec 64, a + 4 - 4#64 = a from fun a => by bv_omega]
    exact List.mem_append_right _ (mem_bufWords hi)), fun wH hwH => ?_⟩
  rw [table_entry_add4 base hdn63 hw, memHalf_hi,
    holdsData_get hhold (by rw [show udivrem_by1_image_data.length = 256 from rfl]; exact hi),
    ← List.getD_eq_getElem _ 0, show udivrem_by1_image_data = reciprocal_2by1_image_data from rfl,
    image_data_get _ hi] at hwH
  rv_exec_cut 148 167
  -- The words u[top - 1] and u[top] of the numerator.
  refine Reach.step (by decide) rfl ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  have hn2 : 2 ≤ (x.get 11#5).toNat := by omega
  have hn8 : 8 * (x.get 11#5).toNat ≤ 2 ^ 64 := by omega
  have hua : x.get 12#5 + (x.get 11#5 + 18446744073709551614#64) <<< 3 =
      x.get 12#5 + BitVec.ofNat 64 (8 * ((x.get 11#5).toNat - 2)) := by rw [off_sub2 _ hn2 hn8]
  rv_fold hua
  rw [hua]
  refine ⟨List.mem_append_left _ (List.mem_append_left _ (mem_bufWords (by omega))),
    fun wA hwA => ?_⟩
  refine Reach.step (by decide) rfl ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  have hub : x.get 12#5 + x.get 11#5 <<< 3 + 18446744073709551608#64 =
      x.get 12#5 + BitVec.ofNat 64 (8 * ((x.get 11#5).toNat - 1)) := by
    rw [BitVec.add_assoc, off_sub1 _ (by omega) hn8]
  rv_fold hub
  rw [hub]
  refine ⟨List.mem_append_left _ (List.mem_append_left _ (mem_bufWords (by omega))),
    fun wB hwB => ?_⟩
  rv_exec_cut 148 167
  -- The top quotient word q[top].
  all_goals
    have hqa : x.get 10#5 + x.get 11#5 <<< 3 + 18446744073709551608#64 =
        x.get 10#5 + BitVec.ofNat 64 (8 * ((x.get 11#5).toNat - 1)) := by
      rw [BitVec.add_assoc, off_sub1 _ (by omega) hn8]
    refine Reach.step (by decide) rfl ?_
    simp only [StepGoal, Nat.reduceAdd]
    rv_val
    rv_fold hqa
    rw [hqa]
    refine ⟨trivial, List.mem_append_left _ (List.mem_append_right _ (mem_bufWords (by omega))), ?_⟩
    rv_exec_cut 148 167
  -- The reciprocal, the shift and the branches of the first quotient word.
  all_goals
    obtain ⟨hL, hH⟩ := table_LH hdn63 hwL hwH
    have hv := recip2BV_spec _ wL wH hdn63 hL hH
    simp only [recip2BV] at hv
    rv_fold hv
    subst hs
    try simp only [zopz0zKzJ_u_eq, zopz0zI_u_eq, decide_eq_true_eq, decide_eq_false_iff_not] at *
  -- The top digits of the normalized numerator.
  have hL64 : Nat.log2 (x.get 14#5).toNat < 64 := (Nat.log2_lt hd0').mpr (x.get 14#5).isLt
  all_goals
    have htop := by1_top m (x.get 12#5) (x.get 11#5).toNat (63 - Nat.log2 (x.get 14#5).toNat)
      (by omega) hn2
    simp only [wordAt, show (x.get 11#5).toNat - 1 - 1 = (x.get 11#5).toNat - 2 by omega] at htop
    rw [← hwA.eq, ← hwB.eq] at htop
  -- The first quotient word and the remainder on the four kinds of path.
  -- s ≠ 0, u[top] ≥ d: the division of the top digits.
  all_goals first
    | (rv_lacks ¬BitVec.ofNat 64 (63 - (x.get 14#5).toNat.log2) = 0#64; skip)
    | (rv_lacks x.get 14#5 ≤ wB; skip)
    | (
       rv_get hne : ¬BitVec.ofNat 64 (63 - (x.get 14#5).toNat.log2) = 0#64
       have hS0 := ofNat_S_ne (by omega) hne
       have hs := div2by1BV_spec (wB >>> ((BitVec.signExtend 64 (BitVec.setWidth 32 0#64 -
         BitVec.setWidth 32 (BitVec.ofNat 64 (63 - (x.get 14#5).toNat.log2)))).toNat % 64))
         ((wB <<< ((BitVec.ofNat 64 (63 - (x.get 14#5).toNat.log2)).toNat % 64)) |||
           ((wA >>> 1) >>> ((BitVec.ofNat 64 (63 - (x.get 14#5).toNat.log2) ^^^
             18446744073709551615#64).toNat % 64))) _ _ hdn63
         (top_hi_lt hdn63 (by omega) hS0) hv
       simp only [div2by1BV] at hs
       rv_fold hs
       rv_fold hs
       try simp (disch := assumption) only [if_pos, if_neg] at hs
       try simp only [BitVec.add_assoc] at hs
       rv_fold hs
       have hhi : (wB >>> ((BitVec.signExtend 64 (BitVec.setWidth 32 0#64 - BitVec.setWidth 32
           (BitVec.ofNat 64 (63 - (x.get 14#5).toNat.log2)))).toNat % 64)).toNat =
           wB.toNat / 2 ^ (64 - (63 - (x.get 14#5).toNat.log2)) := by
         rw [negw_shift _ (by omega) hS0, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
       have hlo := toNat_fshl_code wB wA (BitVec.ofNat 64 (63 - (x.get 14#5).toNat.log2))
         (by rw [ofNat_S_toNat (by omega)]; omega)
       rv_fold hhi
       rv_fold hhi
       rv_fold hlo
       rv_fold hlo
       rw [ofNat_S_toNat (by omega)] at hlo
       rw [← hhi, ← hlo] at htop
       rw [hdn] at hs
       have hT := top_div (D := (x.get 14#5).toNat * 2 ^ (63 - (x.get 14#5).toNat.log2))
         (Nat.mul_pos (by omega) (Nat.two_pow_pos _)) htop hs.1 hs.2
       skip)
  -- s ≠ 0, u[top] < d: the top quotient word 0.
  all_goals first
    | (rv_lacks ¬BitVec.ofNat 64 (63 - (x.get 14#5).toNat.log2) = 0#64; skip)
    | (rv_lacks ¬x.get 14#5 ≤ wB; skip)
    | (rv_get hlt : ¬x.get 14#5 ≤ wB
       have hlo := toNat_fshl_code wB wA (BitVec.ofNat 64 (63 - (x.get 14#5).toNat.log2))
         (by rw [ofNat_S_toNat (by omega)]; omega)
       rv_fold hlo
       rv_fold hlo
       rw [ofNat_S_toNat (by omega)] at hlo
       rw [← hlo] at htop
       have hT := top_zero (d := (x.get 14#5).toNat) (by omega) (by rw [← hdn]; exact BitVec.isLt _)
         (by simp only [BitVec.le_def, not_le] at hlt; exact hlt) htop hlo wA.isLt
       rw [show (0 : Nat) = (0#64).toNat from rfl] at hT)
  -- s = 0, u[top] ≥ d: the division of 0:u[top].
  all_goals first
    | (rv_lacks BitVec.ofNat 64 (63 - (x.get 14#5).toNat.log2) = 0#64; skip)
    | (rv_lacks x.get 14#5 ≤ wB; skip)
    | (rv_get hz : BitVec.ofNat 64 (63 - (x.get 14#5).toNat.log2) = 0#64
       have hS0 := ofNat_S_eq (by omega) hz
       rv_copies
       have hs := div2by1BV_spec 0#64 wB _ _ hdn63 (by rw [BitVec.toNat_ofNat]; omega) hv
       simp only [div2by1BV, BitVec.zero_add] at hs
       rv_fold hs
       rv_fold hs
       try simp (disch := assumption) only [if_pos, if_neg] at hs
       try simp only [BitVec.add_assoc] at hs
       rv_fold hs
       have hU0 : 2 ^ 64 * (wB.toNat / 2 ^ (64 - (63 - (x.get 14#5).toNat.log2))) +
           (wB.toNat * 2 ^ (63 - (x.get 14#5).toNat.log2) +
             wA.toNat / 2 ^ (64 - (63 - (x.get 14#5).toNat.log2))) % 2 ^ 64 =
           2 ^ 64 * (0#64).toNat + wB.toNat := by
         rw [hS0, top_s0 _ _ wB.isLt wA.isLt]; simp
       rw [hdn] at hs
       have hT := top_div (Nat.mul_pos (by omega) (Nat.two_pow_pos _)) (htop.trans hU0) hs.1 hs.2)
  -- s = 0, u[top] < d: the top quotient word 0 and the remainder u[top].
  all_goals first
    | (rv_lacks BitVec.ofNat 64 (63 - (x.get 14#5).toNat.log2) = 0#64; skip)
    | (rv_lacks ¬x.get 14#5 ≤ wB; skip)
    | (rv_get hz : BitVec.ofNat 64 (63 - (x.get 14#5).toNat.log2) = 0#64
       rv_get hlt : ¬x.get 14#5 ≤ wB
       have hS0 := ofNat_S_eq (by omega) hz
       have hU0 : 2 ^ 64 * (wB.toNat / 2 ^ (64 - (63 - (x.get 14#5).toNat.log2))) +
           (wB.toNat * 2 ^ (63 - (x.get 14#5).toNat.log2) +
             wA.toNat / 2 ^ (64 - (63 - (x.get 14#5).toNat.log2))) % 2 ^ 64 = wB.toNat := by
         rw [hS0, top_s0 _ _ wB.isLt wA.isLt]
       have hT : (0#64).toNat * ((x.get 14#5).toNat * 2 ^ (63 - (x.get 14#5).toNat.log2)) +
           wB.toNat = words m (x.get 12#5) (x.get 11#5).toNat *
             2 ^ (63 - (x.get 14#5).toNat.log2) / 2 ^ (64 * ((x.get 11#5).toNat - 1)) ∧
           wB.toNat < (x.get 14#5).toNat * 2 ^ (63 - (x.get 14#5).toNat.log2) := by
         simp only [BitVec.le_def, not_le] at hlt
         rw [htop, hU0, hS0]; simp; exact hlt)
  -- The cut points: the head of the loop before the word n - 2, the exit for n = 2.
  all_goals
    have hr' : x.get 1#5 &&& 3 = 0 := hx1 ▸ hr
    rw [← hx1]
    have hqn : (x.get 10#5 + BitVec.ofNat 64 (8 * ((x.get 11#5).toNat - 1))).toNat =
        (x.get 10#5).toNat + 8 * ((x.get 11#5).toNat - 1) := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have hun : ∀ v : BitVec 64, UnchangedExcept m
        (memStore m (x.get 10#5 + BitVec.ofNat 64 (8 * ((x.get 11#5).toNat - 1))).toNat v)
        (x.get 10#5) (8 * (x.get 11#5).toNat) :=
      fun v => (unchangedExcept_memStore _ v ⟨by omega, by omega⟩).mpr (unchangedExcept_refl _ _ _)
  all_goals first
    | (rv_not_at 148; skip)
    | (rv_get hne : ¬x.get 11#5 + 18446744073709551614#64 = 0#64
       have hn3 : 3 ≤ (x.get 11#5).toNat := by
         by_contra hc; exact hne (cnt_sub2_zero _ (by omega))
       have h16 := ptr_sub16 (x.get 10#5) (x.get 11#5) hn2 hn8
       rv_fold h16
       have h24 := ptr_sub24 (x.get 12#5) (x.get 11#5) hn3 hn8
       rv_fold h24
       refine by1_loop base x m hpre0 hr' ((x.get 11#5).toNat - 2) _ _ ?_
       simp only [by1Head]
       simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
       rw [show (x.get 11#5).toNat - 2 + 1 = (x.get 11#5).toNat - 1 by omega,
         show (x.get 11#5).toNat - 1 - ((x.get 11#5).toNat - 2) = 1 by omega, words_one_memStore]
       refine ⟨by omega, by omega, trivial, ofNat_S_toNat (by omega), trivial, hdn, by rw [hv, hdn],
         cnt_sub2 _ hn2, h16, h24, hwA.eq, hT.2, hT.1, hun _, trivial, trivial, ?_⟩
       intro r hr
       simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
         rfl | rfl <;>
       simp (config := { decide := true }) only [↓reduceIte])
  all_goals first
    | (rv_not_at 167; skip)
    | (rv_get heq : x.get 11#5 + 18446744073709551614#64 = 0#64
       have hn : (x.get 11#5).toNat = 2 := cnt_sub2_eq_zero _ hn2 heq
       refine by1_exit base x m hpre0 hr' _ _ ?_
       simp only [by1Exit]
       simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
       rw [hn] at hT hwA hun ⊢
       simp only [Nat.sub_self, Nat.mul_zero, show 2 - 1 = 1 from rfl, Nat.mul_one]
         at hT hwA hun ⊢
       rw [show x.get 12#5 + BitVec.ofNat 64 0 = x.get 12#5 by simp] at hwA
       rw [show x.get 10#5 + 8#64 = x.get 10#5 + BitVec.ofNat 64 8 from rfl, words_one_memStore]
       refine ⟨trivial, ofNat_S_toNat (by omega), hdn, by rw [hv, hdn], hwA.eq, hT.2, hT.1, hun _,
         trivial, trivial, ?_⟩
       intro r hr
       simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
         rfl | rfl <;>
       simp (config := { decide := true }) only [↓reduceIte])

theorem udivrem_by1.nonvacuous :
    NonVacuousI udivrem_by1_image_code udivrem_by1_image_data udivrem_by1_image_dataOff
      udivrem_by1.bufs udivrem_by1.pre :=
  nonVacuousI_of (fun i => if i = 10#5 then 0x80000000#64 else if i = 11#5 then 2#64
      else if i = 12#5 then 0x80000010#64 else if i = 13#5 then 2#64 else if i = 14#5 then 1#64
      else 0)
    (by decide) (by decide) (by decide) (by decide)
    (by simp only [udivrem_by1.bufs, ↓reduceIte, BitVec.reduceEq, BitVec.toNat_ofNat,
          Nat.reducePow, Nat.reduceMod, bufWords, List.cons_append, List.nil_append,
          List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        decide)
    (fun _ => by simp only [udivrem_by1.pre, Buf, Disjoint]; decide)

end IntxRV.Api
