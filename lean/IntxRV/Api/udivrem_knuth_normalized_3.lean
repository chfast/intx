import IntxRV.Knuth3
import IntxRV.DivTop1
/-!
# `internal::udivrem_knuth_normalized<3>()`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Divides the normalized words u by d with the Knuth algorithm, in place: the low d.size() words
/// of u become the normalized remainder.
/// A fixed size of d (DIVISOR_WORDS) lets the loops over the divisor words unroll. d is not
/// deduced, so spans of non-const words convert to it.
/// @pre 3 ≤ d.size()
/// @pre d.size() < u.size()
/// @pre q.size() = u.size() - d.size()
/// @pre 2^(64 * d.size() - 1) ≤ d
/// @pre u / 2^(64 * (u.size() - d.size())) < d
/// @post q = old(u) / d
/// @post u % 2^(64 * d.size()) = old(u) % d
template <size_t DIVISOR_WORDS = std::dynamic_extent>
constexpr void udivrem_knuth_normalized(uint64_t q[], std::span<uint64_t> u,
    std::type_identity_t<std::span<const uint64_t, DIVISOR_WORDS>> d) noexcept
```

`udivrem_knuth_normalized_3.spec` states it for the RV64 machine code of
`udivrem_knuth_normalized_3` in `IntxRV/Api.cpp` (generated in `IntxRV/Gen/Api/`, see
`IntxRV/README.md`). The prologue saves ra and s0 to s7, loads the top 2 words of d and computes
their reciprocal with the table (`recip3BV`, as in `udivrem_by2()`), and sets the pointers to the
digit `n - 4` of u and q; the loop and its blocks are in `IntxRV/Knuth3.lean`. The proof holds for
any immediates of the address of the table (`udivrem_knuth_normalized_3.reach`), so it runs in the
images of the functions that call it.
-/

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

namespace IntxRV.Api
open IntxRV IntxRV.Gen

/-- The run of `udivrem_knuth_normalized<3>()` from its start, for the immediates `hi` and `lo`
of the address `T` of the table of the reciprocal. -/
theorem udivrem_knuth_normalized_3.reach (hi : BitVec 20) (lo : BitVec 12) (base T : BitVec 64)
    (x : Regs) (m : Mem) (hb : base &&& 3 = 0)
    (hT : pcAt base 12 + ((hi ++ 0x000#12).signExtend 64 + lo.signExtend 64) = T)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64) (hr : x.get 1#5 &&& 3 = 0)
    (hstk : (x.get 2#5 - 80#64).toNat + 80 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 2#5 - 80#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hpre : udivrem_knuth_normalized_3.pre x m) :
    Reach (udivrem_knuth_normalized_3.bufs x ++ bufWords T 256)
      (udivrem_knuth_normalized_3_progAt hi lo) base (pcAt base 0) x m (x.get 1#5)
      (udivrem_knuth_normalized_3.post x m) := by
  have hpre' := hpre
  simp only [udivrem_knuth_normalized_3.pre, Buf, Disjoint] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hqa, hqn⟩, ⟨hua, hun⟩, ⟨hda, hdn⟩, hdqd, hdqu, hdud, ⟨hsa, hsn⟩, hdsd, hdsq, hdsu, -,
    hn3, hD, hU⟩ := hpre'
  suffices h : Reach (bufWords (x.get 13#5) 3 ++ bufWords (x.get 10#5) ((x.get 12#5).toNat - 3) ++
      bufWords (x.get 11#5) (x.get 12#5).toNat ++ bufWords (x.get 2#5 - 80#64) 10 ++ bufWords T 256)
      (udivrem_knuth_normalized_3_progAt hi lo) base (pcAt base 0) x m (x.get 1#5)
      (udivrem_knuth_normalized_3.post x m) by
    simp only [udivrem_knuth_normalized_3.bufs]
    simp (disch := decide) only [Regs.eq_get x]
    exact h
  have hDw0 := words3_eq m (x.get 13#5)
  have hdn63 : 2 ^ 63 ≤ (memWord m (x.get 13#5 + 16#64).toNat).toNat :=
    k3_d2 hD hDw0 (memWord m (x.get 13#5).toNat).isLt (memWord m (x.get 13#5 + 8#64).toNat).isLt
  rv_exec_cut 76
  rename_i wd1 hwd1 wd2 hwd2 wsh hwsh wue hwue w52 hw52 w24 hw24 wa hwa
  have hdn63' : 2 ^ 63 ≤ wd2.toNat := by rw [hwd2.eq]; exact hdn63
  have hix := index_lt_256 hdn63'
  simp only [hT] at *
  -- The table entry of d[2]: the low half.
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  have ha := table_addr_by1 _ T hdn63'
  rv_fold ha
  rw [ha]
  refine ⟨Or.inl (List.mem_append_right _ (mem_bufWords hix)), fun wL hwL => ?_⟩
  try simp (disch := bv_omega) only [memHalf_memStore_of_ne] at hwL
  rw [memHalf_lo, holdsData_get hhold
      (by rw [show reciprocal_2by1_image_data.length = 256 from rfl]; exact hix),
    ← List.getD_eq_getElem _ 0, image_data_get _ hix] at hwL
  rv_exec_cut 76
  -- The high half.
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  have hah := table_addr_by1_hi _ T hdn63'
  rv_fold hah
  rw [hah]
  refine ⟨Or.inr (by
    rw [show ∀ a : BitVec 64, a + 4 - 4#64 = a from fun a => by bv_omega]
    exact List.mem_append_right _ (mem_bufWords hix)), fun wH hwH => ?_⟩
  try simp (disch := bv_omega) only [memHalf_memStore_of_ne] at hwH
  rw [table_entry_add4 T hdn63' hw, memHalf_hi, holdsData_get hhold
      (by rw [show reciprocal_2by1_image_data.length = 256 from rfl]; exact hix),
    ← List.getD_eq_getElem _ 0, image_data_get _ hix] at hwH
  rv_exec_cut 76
  have hn4 : 4 ≤ (x.get 12#5).toNat := by clear * - hn3; omega
  -- The words u[n - 2] and u[n - 1].
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  rw [hwue.eq, hwsh.eq, k3_addr_u2 _ _ hn4]
  refine ⟨List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (mem_bufWords (by clear * - hn4; omega)))), fun wu2 hwu2 => ?_⟩
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  rw [k3_addr_u3 _ _ hn4]
  refine ⟨List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (mem_bufWords (by clear * - hn4; omega)))), fun wu3 hwu3 => ?_⟩
  rv_exec_cut 76
  -- The reciprocal of d[2]:d[1].
  obtain ⟨hL, hH⟩ := table_LH hdn63' hwL hwH
  have hv := recip3BV_spec_of (t0 := wd1) rfl _ wL wH hdn63' hL hH
  simp only [recip3BV] at hv
  rw [show (0 : BitVec 64) = 0#64 from rfl] at hv
  rv_fold hv
  rename_i wq hwq w0 hw0 w1 hw1 w2 hw2 w3 hw3 w4 hw4 w5 hw5 wv hwv ws hws
  -- The head of the loop for the digit n - 4.
  have hfun := k3FrameMem_unchanged x m hsn
  have hfw := k3FrameMem_words x m hsn
  have hmu : ∀ b, b + 8 ≤ (x.get 2#5 - 80#64).toNat ∨ (x.get 2#5 - 80#64).toNat + 80 ≤ b →
      memWord (k3FrameMem x m) b = memWord m b := fun b hb' => memWord_of_unchangedExcept hfun b hb'
  have hsub : ∀ a ∈ udivrem_knuth_normalized_3.bufs x ++ bufWords T 256,
      a ∈ bufWords (x.get 13#5) 3 ++ bufWords (x.get 10#5) ((x.get 12#5).toNat - 3) ++
        bufWords (x.get 11#5) (x.get 12#5).toNat ++ bufWords (x.get 2#5 - 80#64) 10 ++
          bufWords T 256 := by
    intro a ha
    simp only [udivrem_knuth_normalized_3.bufs] at ha
    simp (disch := decide) only [Regs.eq_get x] at ha
    exact ha
  refine Reach.mono_bufs hsub (k3_loop base x m hb hr hpre ((x.get 12#5).toNat - 4) _ _ ?_)
  have hu3 : (x.get 11#5 + BitVec.ofNat 64 (8 * ((x.get 12#5).toNat - 4 + 3))).toNat =
      (x.get 11#5).toNat + 8 * ((x.get 12#5).toNat - 4 + 3) :=
    toNat_add8 _ _ (by clear * - hun hn4; omega) (by clear * - hun hn4; omega)
  refine ⟨by clear * - hn4; omega, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · exact hfw.1
  · exact hfw.2.1
  · exact hfw.2.2.1
  · exact hfw.2.2.2.1
  · exact hfw.2.2.2.2.1
  · exact hfw.2.2.2.2.2.1
  · exact hfw.2.2.2.2.2.2.1
  · exact hfw.2.2.2.2.2.2.2.1
  · exact hfw.2.2.2.2.2.2.2.2
  · exact fun k _ _ hk => hfun k hk
  · intro r hr hnr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> simp (config := { decide := true }) at hnr ⊢
  · rw [hws.eq, k3_addr_end _ _ hn4]
  · rw [hwq.eq, k3_addr_end _ _ hn4]
  · rw [cnt_sub3 _ (by clear * - hn4; omega), show (x.get 12#5).toNat - 4 + 1 =
      (x.get 12#5).toNat - 3 by clear * - hn4; omega]
  · exact hwd1
  · exact hwd2
  · exact hv
  · exact hwu2
  · rw [hwu3.eq]
    exact (hmu _ (by rw [hu3]; clear * - hdsu hn4 hun; omega)).symm
  · intro k hk
    have := toNat_add8 (x.get 11#5) (8 * k) (by clear * - hk hun hn4; omega)
      (by clear * - hk hun hn4; omega)
    exact hmu _ (by rw [this]; clear * - hdsu hn4 hun hk; omega)
  · have hb1 := toNat_add8 (x.get 11#5) (8 * ((x.get 12#5).toNat - 4 + 1))
      (by clear * - hun hn4; omega) (by clear * - hun hn4; omega)
    rw [Nat.sub_self, words, Nat.zero_mul, Nat.zero_add,
      words_of_unchangedExcept hfun _ _ (by rw [hb1]; clear * - hun hn4; omega)
        (by rw [hb1]; clear * - hdsu hn4 hun; omega), k3_top3 _ _ _ hn4]
  · have hb1 := toNat_add8 (x.get 11#5) (8 * ((x.get 12#5).toNat - 4 + 1))
      (by clear * - hun hn4; omega) (by clear * - hun hn4; omega)
    rw [words_of_unchangedExcept hfun _ _ (by rw [hb1]; clear * - hun hn4; omega)
        (by rw [hb1]; clear * - hdsu hn4 hun; omega), ← k3_top3 _ _ _ hn4,
      show (x.get 12#5).toNat - 4 + 1 = (x.get 12#5).toNat - 3 by clear * - hn4; omega]
    exact hU

theorem udivrem_knuth_normalized_3.proof_of_decodes (hdec : udivrem_knuth_normalized_3.decodes) :
    udivrem_knuth_normalized_3.spec := by
  apply runsI_of_reach hdec
  intro base ret hb8 hr _ _ hw x m hx1 hbufs hhold hpre
  rw [show udivrem_knuth_normalized_3_image_dataOff = 792 from rfl] at hw hhold hbufs ⊢
  rw [show udivrem_knuth_normalized_3_image_data.length = 256 from rfl] at hw hbufs ⊢
  have hb : base &&& 3 = 0 := by
    have := congrArg (· &&& 3#64) hb8
    simpa [BitVec.and_assoc] using this
  have hx : x.get 1#5 = ret := by rw [← Regs.eq_get x (by decide)]; exact hx1
  have hpre' := hpre
  simp only [udivrem_knuth_normalized_3.pre, Buf] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  have hst := k3_frame_outside (x 2#5) base (792 + 8 * 256)
    (hbufs _ (List.mem_append_right _ (mem_bufWords_zero (by norm_num))))
    (hbufs _ (List.mem_append_right _ (mem_bufWords (by norm_num))))
    (by rw [Regs.eq_get x (by decide)]; exact hpre'.2.2.2.2.2.2.1.2) (by norm_num)
  rw [Regs.eq_get x (by decide)] at hst
  rw [show udivrem_knuth_normalized_3_entry =
      udivrem_knuth_normalized_3_image_udivrem_knuth_normalized_3_offset from rfl, dataWords, ← hx]
  refine Reach.lift udivrem_knuth_normalized_3_image_udivrem_knuth_normalized_3_in (by decide) ?_
  have hT : (base + BitVec.ofNat 64 792).toNat = base.toNat + 792 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have h := udivrem_knuth_normalized_3.reach 0x0#20 0x2e8#12
    (pcAt base udivrem_knuth_normalized_3_image_udivrem_knuth_normalized_3_offset) _ x m
    (by simp only [udivrem_knuth_normalized_3_image_udivrem_knuth_normalized_3_offset, pcAt]
        exact aligned_add hb (by decide))
    (by simp only [udivrem_knuth_normalized_3_image_udivrem_knuth_normalized_3_offset, pcAt,
      BitVec.reduceAppend, BitVec.reduceSignExtend]; bv_omega)
    (by rw [hT]; omega) (hx ▸ hr) (by rw [hT]; omega) hhold hpre
  rwa [pcAt_zero] at h

/-- The registers of the nonvacuous instance: q of 1 word, u of 4 words 0 and d of 3 words
2^191 above the data, and the frame below sp. -/
theorem udivrem_knuth_normalized_3.nonvacuous :
    NonVacuousI udivrem_knuth_normalized_3_image_code udivrem_knuth_normalized_3_image_data
      udivrem_knuth_normalized_3_image_dataOff udivrem_knuth_normalized_3.bufs
      udivrem_knuth_normalized_3.pre :=
  nonVacuousI_of_args (fun i => if i = 10#5 then 0x80000C00#64 else if i = 11#5 then 0x80000C08#64
      else if i = 12#5 then 4#64 else if i = 13#5 then 0x80000C28#64
      else if i = 2#5 then 0x80000C90#64 else 0)
    0x80000C08 [0, 0, 0, 0, 0, 0, 0x8000000000000000]
    (by decide) (by decide) (by decide) (by decide)
    (by rw [show udivrem_knuth_normalized_3_image_dataOff = 792 from rfl,
          show udivrem_knuth_normalized_3_image_data.length = 256 from rfl]
        simp only [udivrem_knuth_normalized_3.bufs, ↓reduceIte, BitVec.reduceEq, BitVec.reduceSub,
          BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub, bufWords,
          List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq]
        repeat' apply And.intro
        all_goals decide)
    (by decide)
    (fun m => by
      simp only [udivrem_knuth_normalized_3.pre, Buf, Disjoint, words, ↓reduceIte, BitVec.reduceEq,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, BitVec.toNat_ofNat,
        Nat.reducePow, Nat.reduceMod, Nat.reduceSub, Nat.mul_zero, Nat.add_zero]
      simp (disch := decide) only [memWord_storeWords_getD]
      decide)

end IntxRV.Api
