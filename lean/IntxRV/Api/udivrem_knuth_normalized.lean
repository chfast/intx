import IntxRV.KnuthN
/-!
# `internal::udivrem_knuth_normalized()`

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

`udivrem_knuth_normalized.spec` states it for the RV64 machine code of the instance with a
dynamic size of d, `udivrem_knuth_normalized` in `IntxRV/Api.cpp` (generated in
`IntxRV/Gen/Api/`, see `IntxRV/README.md`). The prologue saves ra and s0 to s11, loads the top
2 words of d and computes their reciprocal with the table (`recip3BV`, as in `udivrem_by2()`), and
sets the pointers to the digit `u.size() - d.size() - 1` of u; the loop and its blocks are in
`IntxRV/KnuthN.lean`. The proof holds for any immediates of the address of the table
(`udivrem_knuth_normalized.reach`), so it runs in the images of the functions that call it.
-/

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace IntxRV.Api
open IntxRV IntxRV.Gen

/-- The run of `udivrem_knuth_normalized()` from its start, for the immediates `hi` and `lo` of the
address `T` of the table of the reciprocal. -/
theorem udivrem_knuth_normalized.reach (hi : BitVec 20) (lo : BitVec 12) (base T : BitVec 64)
    (x : Regs) (m : Mem) (hb : base &&& 3 = 0)
    (hT : pcAt base 16 + ((hi ++ 0x000#12).signExtend 64 + lo.signExtend 64) = T)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64) (hr : x.get 1#5 &&& 3 = 0)
    (hstk : (x.get 2#5 - 144#64).toNat + 144 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 144#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hpre : udivrem_knuth_normalized.pre x m) :
    Reach (udivrem_knuth_normalized.bufs x ++ bufWords T 256)
      (udivrem_knuth_normalized_progAt hi lo) base (pcAt base 0) x m (x.get 1#5)
      (udivrem_knuth_normalized.post x m) := by
  have hpre' := hpre
  simp only [udivrem_knuth_normalized.pre, Buf, Disjoint] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hqa, hqn⟩, ⟨hua, hun⟩, ⟨hda, hdn⟩, hdqd, hdqu, hdud, ⟨hsa, hsn⟩, hdsd, hdsq, hdsu,
    hn3, hnu, hD, hU⟩ := hpre'
  have hbufs : udivrem_knuth_normalized.bufs x = bufWords (x.get 13#5) (x.get 14#5).toNat ++
      bufWords (x.get 10#5) ((x.get 12#5).toNat - (x.get 14#5).toNat) ++
      bufWords (x.get 11#5) (x.get 12#5).toNat ++ bufWords (x.get 2#5 - 144#64) 18 := by
    simp only [udivrem_knuth_normalized.bufs]
    simp (disch := decide) only [Regs.eq_get x]
  rw [hbufs]
  -- The top 2 words of the divisor.
  have hDs := words_top2 m (x.get 13#5) ((x.get 14#5).toNat - 2)
  rw [show (x.get 14#5).toNat - 2 + 2 = (x.get 14#5).toNat by omega,
    show (x.get 14#5).toNat - 2 + 1 = (x.get 14#5).toNat - 1 by omega] at hDs
  have hdlo := words_lt m ((x.get 14#5).toNat - 2) (x.get 13#5)
  have hdh := kn_dh rfl hn3 hD hDs hdlo
  have hfun := knFrameMem_unchanged x m hsn
  have hfw := knFrameMem_words x m hsn
  have hmu : ∀ b, b + 8 ≤ (x.get 2#5 - 144#64).toNat ∨ (x.get 2#5 - 144#64).toNat + 144 ≤ b →
      memWord (knFrameMem x m) b = memWord m b := fun b hb' => memWord_of_unchangedExcept hfun b hb'
  have hd0 : (x.get 13#5 + BitVec.ofNat 64 (8 * ((x.get 14#5).toNat - 2))).toNat =
      (x.get 13#5).toNat + 8 * ((x.get 14#5).toNat - 2) := toNat_add8 _ _ (by omega) (by omega)
  have hd1 : (x.get 13#5 + BitVec.ofNat 64 (8 * ((x.get 14#5).toNat - 1))).toNat =
      (x.get 13#5).toNat + 8 * ((x.get 14#5).toNat - 1) := toNat_add8 _ _ (by omega) (by omega)
  have hdn63 : 2 ^ 63 ≤
      (memWord m (x.get 13#5 + BitVec.ofNat 64 (8 * ((x.get 14#5).toNat - 1))).toNat).toNat := by
    have := (memWord m (x.get 13#5 + BitVec.ofNat 64 (8 * ((x.get 14#5).toNat - 2))).toNat).isLt
    omega
  rv_exec_cut 85
  rename_i wsh hwsh wus hwus wde hwde
  refine Reach.step (by decide) rfl ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  rw [hwde.eq, hwsh.eq, kn_addr_dn2 _ _ (by omega) (by omega)]
  refine ⟨List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (mem_bufWords (i := (x.get 14#5).toNat - 2) (by omega))))),
    fun wd0 hwd0 => ?_⟩
  refine Reach.step (by decide) rfl ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  rw [kn_addr_dn1 _ _ (by omega) (by omega)]
  refine ⟨List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (mem_bufWords (i := (x.get 14#5).toNat - 1) (by omega))))),
    fun wd1 hwd1 => ?_⟩
  have ed0 : wd0 = memWord m (x.get 13#5 + BitVec.ofNat 64 (8 * ((x.get 14#5).toNat - 2))).toNat := by
    rw [hwd0.eq]; try exact hmu _ (by rw [hd0]; omega)
  have ed1 : wd1 = memWord m (x.get 13#5 + BitVec.ofNat 64 (8 * ((x.get 14#5).toNat - 1))).toNat := by
    rw [hwd1.eq]; try exact hmu _ (by rw [hd1]; omega)
  have hdn63' : 2 ^ 63 ≤ wd1.toNat := by rw [ed1]; exact hdn63
  have hix := index_lt_256 hdn63'
  have hTi : (T + BitVec.ofNat 64 (8 * (wd1.toNat / 2 ^ 55 - 256))).toNat =
      T.toNat + 8 * (wd1.toNat / 2 ^ 55 - 256) := toNat_add8 _ _ (by omega) (by omega)
  rv_exec_cut 85
  rename_i wj0 hwj0 w52 hw52 w24 hw24 wta hwta
  simp only [hT] at *
  -- The table entry of d[n - 1]: the low half.
  refine Reach.step (by decide) rfl ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  have ha := table_addr_by1 _ T hdn63'
  rv_fold ha
  rw [ha]
  refine ⟨Or.inl (List.mem_append_right _ (mem_bufWords hix)), fun wL hwL => ?_⟩
  try rw [memHalf_of_unchangedExcept hfun _ (by rw [hTi]; omega)] at hwL
  rw [memHalf_lo, holdsData_get hhold
      (by rw [show reciprocal_2by1_image_data.length = 256 from rfl]; exact hix),
    ← List.getD_eq_getElem _ 0, image_data_get _ hix] at hwL
  rv_exec_cut 85
  -- The high half.
  refine Reach.step (by decide) rfl ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  have hah := table_addr_by1_hi _ T hdn63'
  rv_fold hah
  rw [hah]
  refine ⟨Or.inr (by
    rw [show ∀ a : BitVec 64, a + 4 - 4#64 = a from fun a => by bv_omega]
    exact List.mem_append_right _ (mem_bufWords hix)), fun wH hwH => ?_⟩
  try rw [memHalf_of_unchangedExcept hfun _ (by rw [table_entry_add4 T hdn63' hw, hTi]; omega)] at hwH
  rw [table_entry_add4 T hdn63' hw, memHalf_hi, holdsData_get hhold
      (by rw [show reciprocal_2by1_image_data.length = 256 from rfl]; exact hix),
    ← List.getD_eq_getElem _ 0, image_data_get _ hix] at hwH
  rv_exec_cut 85
  rename_i wue hwue wq hwq wv hwv
  -- The words u[us - 2] and u[us - 1].
  have hu2 : (x.get 11#5 + BitVec.ofNat 64 (8 * ((x.get 12#5).toNat - 2))).toNat =
      (x.get 11#5).toNat + 8 * ((x.get 12#5).toNat - 2) := toNat_add8 _ _ (by omega) (by omega)
  have hu1 : (x.get 11#5 + BitVec.ofNat 64 (8 * ((x.get 12#5).toNat - 1))).toNat =
      (x.get 11#5).toNat + 8 * ((x.get 12#5).toNat - 1) := toNat_add8 _ _ (by omega) (by omega)
  refine Reach.step (by decide) rfl ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  rw [hwue.eq, hwus.eq, kn_addr_dn2 _ _ (by omega) (by omega)]
  refine ⟨List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (mem_bufWords (i := (x.get 12#5).toNat - 2) (by omega)))), fun wu2 hwu2 => ?_⟩
  refine Reach.step (by decide) rfl ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  first
    | rw [kn_addr_dn1 _ _ (by omega) (by omega)]
    | rw [kn_addr_dn1b _ _ (by omega) (by omega)]
    | rw [hwue.eq, hwus.eq, kn_addr_dn1b _ _ (by omega) (by omega)]
  refine ⟨List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (mem_bufWords (i := (x.get 12#5).toNat - 1) (by omega)))), fun wu1 hwu1 => ?_⟩
  rv_exec_cut 85
  -- The reciprocal of d[n - 1]:d[n - 2].
  obtain ⟨hL, hH⟩ := table_LH hdn63' hwL hwH
  have hv := recip3BV_spec_of (t0 := wd0) rfl _ wL wH hdn63' hL hH
  simp only [recip3BV] at hv
  rw [show (0 : BitVec 64) = 0#64 from rfl] at hv
  rv_fold hv
  rename_i w22 hw22 wrec hwrec
  -- The head of the loop for the digit us - n - 1.
  have hj : (x.get 14#5).toNat < (x.get 12#5).toNat := hnu
  have hu0 : (x.get 11#5 + BitVec.ofNat 64 (8 * ((x.get 12#5).toNat - (x.get 14#5).toNat))).toNat =
      (x.get 11#5).toNat + 8 * ((x.get 12#5).toNat - (x.get 14#5).toNat) :=
    toNat_add8 _ _ (by omega) (by omega)
  rw [← hbufs]
  refine kn_loop base x m hb hr hpre ((x.get 12#5).toNat - (x.get 14#5).toNat - 1) _ _ ?_
  refine ⟨by omega, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · exact hfw.1
  · exact hfw.2.1
  · exact hfw.2.2.1
  · exact hfw.2.2.2.1
  · exact hfw.2.2.2.2.1
  · exact hfw.2.2.2.2.2.1
  · exact hfw.2.2.2.2.2.2.1
  · exact hfw.2.2.2.2.2.2.2.1
  · exact hfw.2.2.2.2.2.2.2.2.1
  · exact hfw.2.2.2.2.2.2.2.2.2.1
  · exact hfw.2.2.2.2.2.2.2.2.2.2.1
  · exact hfw.2.2.2.2.2.2.2.2.2.2.2.1
  · exact hfw.2.2.2.2.2.2.2.2.2.2.2.2
  · exact fun k _ _ hk => hfun k hk
  · intro r hr hnr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> simp (config := { decide := true }) at hnr ⊢
  · rw [hwj0.eq]; exact kn_j0 _ _ hj
  · rw [hw22.eq, hwq.eq, hwus.eq]; exact kn_u_j0 _ _ _ hj (by omega)
  · rw [show (x.get 12#5).toNat - (x.get 14#5).toNat - 1 -
      ((x.get 12#5).toNat - (x.get 14#5).toNat - 1) = 0 by omega]
    all_goals rfl
  · rw [shl3_ofNat _ (by omega)]
  · exact ed0
  · exact ed1
  · first
      | exact kn_24 _ (by omega) (by omega)
      | (rw [hwus.eq]; exact kn_24 _ (by omega) (by omega))
  · exact hv
  · rw [show (x.get 12#5).toNat - (x.get 14#5).toNat - 1 + (x.get 14#5).toNat - 1 =
      (x.get 12#5).toNat - 2 by omega, hwu2.eq]
    all_goals first | rfl | exact (hmu _ (by rw [hu2]; omega)).symm
  · rw [show (x.get 12#5).toNat - (x.get 14#5).toNat - 1 + (x.get 14#5).toNat =
      (x.get 12#5).toNat - 1 by omega, hwu1.eq]
    all_goals first | rfl | exact (hmu _ (by rw [hu1]; omega)).symm
  · intro k hk
    have := toNat_add8 (x.get 11#5) (8 * k) (by omega) (by omega)
    exact hmu _ (by rw [this]; omega)
  · rw [show (x.get 12#5).toNat - (x.get 14#5).toNat - 1 + 1 =
      (x.get 12#5).toNat - (x.get 14#5).toNat by omega, Nat.sub_self, words, Nat.zero_mul,
      Nat.zero_add, words_of_unchangedExcept hfun _ _ (by rw [hu0]; omega) (by rw [hu0]; omega),
      kn_topn _ _ _ _ hj.le]
  · rw [show (x.get 12#5).toNat - (x.get 14#5).toNat - 1 + 1 =
      (x.get 12#5).toNat - (x.get 14#5).toNat by omega,
      words_of_unchangedExcept hfun _ _ (by rw [hu0]; omega) (by rw [hu0]; omega),
      ← kn_topn _ _ _ _ hj.le]
    exact hU

theorem udivrem_knuth_normalized.proof_of_decodes (hdec : udivrem_knuth_normalized.decodes) :
    udivrem_knuth_normalized.spec := by
  apply runsI_of_reach hdec
  intro base ret hb8 hr _ _ hw x m hx1 hbufs hhold hpre
  rw [show udivrem_knuth_normalized_image_dataOff = 976 from rfl] at hw hhold hbufs ⊢
  rw [show udivrem_knuth_normalized_image_data.length = 256 from rfl] at hw hbufs ⊢
  have hb : base &&& 3 = 0 := by
    have := congrArg (· &&& 3#64) hb8
    simpa [BitVec.and_assoc] using this
  have hx : x.get 1#5 = ret := by rw [← Regs.eq_get x (by decide)]; exact hx1
  have hpre' := hpre
  simp only [udivrem_knuth_normalized.pre, Buf] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  have hst := kn_frame_outside (x 2#5) base (976 + 8 * 256)
    (hbufs _ (List.mem_append_right _ (mem_bufWords_zero (by norm_num))))
    (hbufs _ (List.mem_append_right _ (mem_bufWords (by norm_num))))
    (by rw [Regs.eq_get x (by decide)]; exact hpre'.2.2.2.2.2.2.1.2) (by norm_num)
  rw [Regs.eq_get x (by decide)] at hst
  rw [show udivrem_knuth_normalized_entry =
      udivrem_knuth_normalized_image_udivrem_knuth_normalized_offset from rfl, dataWords, ← hx]
  refine Reach.lift udivrem_knuth_normalized_image_udivrem_knuth_normalized_in (by decide) ?_
  have hT : (base + BitVec.ofNat 64 976).toNat = base.toNat + 976 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have h := udivrem_knuth_normalized.reach 0x0#20 0x390#12
    (pcAt base udivrem_knuth_normalized_image_udivrem_knuth_normalized_offset) _ x m
    (by simp only [udivrem_knuth_normalized_image_udivrem_knuth_normalized_offset, pcAt]
        exact aligned_add hb (by decide))
    (by simp only [udivrem_knuth_normalized_image_udivrem_knuth_normalized_offset, pcAt,
      BitVec.reduceAppend, BitVec.reduceSignExtend]; bv_omega)
    (by rw [hT]; omega) (hx ▸ hr) (by rw [hT]; omega) hhold hpre
  rwa [pcAt_zero] at h

/-- The registers of the nonvacuous instance: q of 1 word, u of 4 words 0 and d of 3 words
2^191 above the data, and the frame below sp. -/
theorem udivrem_knuth_normalized.nonvacuous :
    NonVacuousI udivrem_knuth_normalized_image_code udivrem_knuth_normalized_image_data
      udivrem_knuth_normalized_image_dataOff udivrem_knuth_normalized.bufs
      udivrem_knuth_normalized.pre :=
  nonVacuousI_of_args (fun i => if i = 10#5 then 0x80000C00#64 else if i = 11#5 then 0x80000C08#64
      else if i = 12#5 then 4#64 else if i = 13#5 then 0x80000C28#64
      else if i = 14#5 then 3#64 else if i = 2#5 then 0x80000CD0#64 else 0)
    0x80000C08 [0, 0, 0, 0, 0, 0, 0x8000000000000000]
    (by decide) (by decide) (by decide) (by decide)
    (by rw [show udivrem_knuth_normalized_image_dataOff = 976 from rfl,
          show udivrem_knuth_normalized_image_data.length = 256 from rfl]
        simp only [udivrem_knuth_normalized.bufs, ↓reduceIte, BitVec.reduceEq, BitVec.reduceSub,
          BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub, bufWords,
          List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq]
        repeat' apply And.intro
        all_goals decide)
    (by decide)
    (fun m => by
      simp only [udivrem_knuth_normalized.pre, Buf, Disjoint, words, ↓reduceIte, BitVec.reduceEq,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, BitVec.toNat_ofNat,
        Nat.reducePow, Nat.reduceMod, Nat.reduceSub, Nat.mul_zero, Nat.add_zero]
      simp (disch := decide) only [memWord_storeWords_getD]
      decide)

end IntxRV.Api
