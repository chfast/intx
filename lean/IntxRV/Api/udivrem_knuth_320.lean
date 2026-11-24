import IntxRV.Knuth320
/-!
# `internal::udivrem_knuth<320, 256>()` with a dynamic size of d

The specification, from `include/intx/intx.hpp`:

```cpp
/// Divides the words u by d into the result of udivrem<M, N>(), built in the return slot.
/// @pre 3 ≤ d.size()
/// @pre d.size() ≤ N / 64
/// @pre 2^(64 * (d.size() - 1)) ≤ d
/// @pre m ≤ u.size()
/// @pre u < 2^(64 * m)
/// @pre 2^(64 * (m - 1)) ≤ u
/// @pre d / 2^(64 * (d.size() - 1)) ≤ u / 2^(64 * (d.size() - 1))
/// @post result.quot = u / d
/// @post result.rem = u % d
template <unsigned M, unsigned N, size_t D>
constexpr div_result<uint<M>, uint<N>> udivrem_knuth(
    std::span<const uint64_t, uint<M>::num_words> u, size_t m,
    std::span<const uint64_t, D> d) noexcept
```

`udivrem_knuth_320.spec` states it for the RV64 machine code of the instance that
`udivrem<320, 256>()` calls, `udivrem_knuth_320` in `IntxRV/Api.cpp` (generated in
`IntxRV/Gen/Api.lean`, see `IntxRV/README.md`). The code clears the result by `memset()`, shifts
d left by the count of the leading zeros of its top word into the stack in a loop
(`k320_dn_loop`), shifts the 5 words of u into 6 words (two paths, for a zero shift and for the
others), counts the words to divide, calls `udivrem_knuth_normalized()` (`k320_tail`), and shifts
the remainder back in a loop (`k320_r_loop`). The blocks are in `IntxRV/Knuth320.lean`. The proof
holds for any immediates of the address of the table of the reciprocal in the callee
(`udivrem_knuth_320.reach`), so it runs in the images of the functions that call it.
-/

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option hygiene false in
/-- The run from 120, after the words of u were shifted in either path, to the call at 133. -/
local macro "k320_join" : tactic => `(tactic| (
  rv_exec_cut 126
  rename_i wun0 hwun0 wum hwum wsm hwsm
  -- u[m - 1]
  refine Reach.step (by decide) rfl ?_
  simp only [StepGoal, Nat.reduceAdd, BitVec.reduceSignExtend, BitVec.add_zero]
  rv_val
  rw [hwsm.eq, hwum.eq, kn_addr_dn1b _ _ (by omega) (by omega)]
  refine ⟨List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (mem_bufWords (i := (x.get 12#5).toNat - 1) (by omega))))),
    fun wtop hwtop => ?_⟩
  rv_exec_cut 133
  rename_i wmn hwmn wsh3 hwsh3 wq hwq wlt hwlt wul hwul
  have hwtop' : wtop = memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * ((x.get 12#5).toNat - 1))).toNat := by
    rw [hwtop.eq]
    rw [memWord_of_unchangedExcept (k320_chain m80 (x.get 2#5) hsn _ _ _ _ _ _ _).1 _
      (by rw [hut, t112]; omega), memWord_memStore_of_ne _ _ _ _ (by rw [hut, t144]; omega)]
    exact hmu80 _ (by rw [hut]; omega) (by rw [hut]; omega)
  have hun0v : (wun0).toNat = (memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * 0)).toNat).toNat *
      2 ^ s % 2 ^ 64 := by
    rw [hwun0.eq, hu0, BitVec.toNat_shiftLeft, hsN, Nat.mod_eq_of_lt hs64, Nat.shiftLeft_eq]
  refine k320_tail base T x m hb hT hw hr hstk hrT hhold hpre s hs64 ?_ hnorm' _ _ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← hed]; exact hns.2
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    have hnum := num_toNat (x.get 12#5).toNat (by omega) wtop wd
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hnum
    rw [hwul.eq, hwlt.eq, hnum, hwtop', ← hed]
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    rw [hwq.eq, hwsh3.eq, hwmn.eq]
    exact k320_q_addr _ _ _ (by omega) (by omega)
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
      rw [hcl80 _ (by decide)]
      simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
      rw [hcs2 _ (by decide)]
      simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
  · exact (k320_at133 x m hpre s hs64 hnorm' m80 _ hdun hdw _ hv0
      (k320_chain m80 (x.get 2#5) hsn _ _ _ _ _ _ _).1).1
  · exact (k320_at133 x m hpre s hs64 hnorm' m80 _ hdun hdw _ hv0
      (k320_chain m80 (x.get 2#5) hsn _ _ _ _ _ _ _).1).2.1
  · exact (k320_at133 x m hpre s hs64 hnorm' m80 _ hdun hdw _ hv0
      (k320_chain m80 (x.get 2#5) hsn _ _ _ _ _ _ _).1).2.2.1
  · exact (k320_at133 x m hpre s hs64 hnorm' m80 _ hdun hdw _ hv0
      (k320_chain m80 (x.get 2#5) hsn _ _ _ _ _ _ _).1).2.2.2
  · obtain ⟨-, c0, c1, c2, c3, c4, c5⟩ := k320_chain m80 (x.get 2#5) hsn wdn0 wun5 _ _ _ wun0 _
    refine k320_unw m _ (x.get 11#5) _ s hs64 ?_ ?_
    · intro i hi
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
      · rw [c0, hun0v]; simp
      · rw [c1, hun1v]; simp
      · rw [c2, hun2v]; simp
      · rw [c3, hun3v]; simp
      · rw [c4, hun4v]; simp
    · rw [c5, hun5v]))

/-- The run of `udivrem_knuth<320, 256>()` from its start, for the immediates `hi` and `lo` of the
address `T` of the table of the reciprocal in `udivrem_knuth_normalized()`. -/
theorem udivrem_knuth_320.reach (hi : BitVec 20) (lo : BitVec 12) (base T : BitVec 64)
    (x : Regs) (m : Mem) (hb : base &&& 3 = 0)
    (hT : pcAt base 184 + ((hi ++ 0x000#12).signExtend 64 + lo.signExtend 64) = T)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64) (hr : x.get 1#5 &&& 3 = 0)
    (hstk : (x.get 2#5 - 288#64).toNat + 288 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 288#64).toNat)
    (hrT : (x.get 10#5).toNat + 72 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hpre : udivrem_knuth_320.pre x m) :
    Reach (udivrem_knuth_320.bufs x ++ bufWords T 256)
      (udivrem_knuth_320_progAt hi lo) base (pcAt base 0) x m (x.get 1#5)
      (udivrem_knuth_320.post x m) := by
  have hpre' := hpre
  simp only [udivrem_knuth_320.pre, Buf, Disjoint] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hda, hdn⟩, hdru, hdrd, ⟨hsa, hsn⟩, hdsu, hdsd, hdsr, hn3, hn4,
    hD, hmm, hU, -, htop⟩ := hpre'
  have hbufs : udivrem_knuth_320.bufs x = bufWords (x.get 11#5) 5 ++
      bufWords (x.get 13#5) (x.get 14#5).toNat ++ bufWords (x.get 10#5) 9 ++
      bufWords (x.get 2#5 - 288#64) 36 := by
    simp only [udivrem_knuth_320.bufs]
    simp (disch := decide) only [Regs.eq_get x]
  rw [hbufs]
  rv_exec_cut 411
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.reduceSignExtend]
  rw [show pcAt base 16 + 1580#64 = pcAt base 411 by simp only [pcAt]; bv_omega,
    update_aligned (pcAt_aligned hb 411)]
  -- The call of memset() of the result.
  refine Reach.call_sub (r := 18) udivrem_knuth_320_progAt_memset_in
    (by rw [udivrem_knuth_320_progAt_length]; decide)
    (memset.reach (A := bufWords (x.get 10#5) 9) (pcAt base 411) _ _ ?_ ?_ ?_) ?_ ?_ ?_
  all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · exact pcAt_aligned hb 18
  · simp only [BitVec.toNat_ofNat]; omega
  · intro i hi
    exact and_not7_mem_bufWords hra (by simpa using hi)
  · intro a ha
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ha))
  intro x2 m2 ⟨hm2, hx10, hcs2⟩
  rw [show BitVec.setWidth 8 0#64 = 0#8 from rfl, show (72#64).toNat = 72 from rfl] at hm2
  subst hm2
  have hfun := k320FrameMem_unchanged x m hsn
  have hfw := k320FrameMem_words x m hsn
  have hmu : ∀ b, b + 8 ≤ (x.get 10#5).toNat ∨ (x.get 10#5).toNat + 72 ≤ b →
      b + 8 ≤ (x.get 2#5 - 288#64).toNat ∨ (x.get 2#5 - 288#64).toNat + 288 ≤ b →
      memWord (memFill (k320FrameMem x m) (x.get 10#5).toNat 0#8 72) b = memWord m b := by
    intro b h1 h2
    rw [memWord_memFill_of_disjoint _ _ _ _ _ h1]
    exact memWord_of_unchangedExcept hfun b h2
  have h2' := get_of_calleeSaved hcs2 (i := 2#5) (by decide)
  have h8' := get_of_calleeSaved hcs2 (i := 8#5) (by decide)
  have h9' := get_of_calleeSaved hcs2 (i := 9#5) (by decide)
  have h18' := get_of_calleeSaved hcs2 (i := 18#5) (by decide)
  have h19' := get_of_calleeSaved hcs2 (i := 19#5) (by decide)
  have h20' := get_of_calleeSaved hcs2 (i := 20#5) (by decide)
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte] at h2' h8' h9' h18' h19' h20'
  rw [← regs_set_of_get' (by decide) h2', ← regs_set_of_get' (by decide) h8',
    ← regs_set_of_get' (by decide) h9', ← regs_set_of_get' (by decide) h18',
    ← regs_set_of_get' (by decide) h19', ← regs_set_of_get' (by decide) h20']
  rv_exec_cut 71
  rename_i wsh hwsh wde hwde
  -- The top word of d.
  have hdt : (x.get 13#5 + BitVec.ofNat 64 (8 * ((x.get 14#5).toNat - 1))).toNat =
      (x.get 13#5).toNat + 8 * ((x.get 14#5).toNat - 1) := toNat_add8 _ _ (by omega) (by omega)
  refine Reach.step (by decide) rfl ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  rw [hwde.eq, hwsh.eq, kn_addr_dn1b _ _ (by omega) (by omega)]
  refine ⟨List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (mem_bufWords (i := (x.get 14#5).toNat - 1) (by omega))))),
    fun wd hwd => ?_⟩
  -- The top word of d and its count of leading zeros: the shift.
  have hed : wd = memWord m (x.get 13#5 + BitVec.ofNat 64 (8 * ((x.get 14#5).toNat - 1))).toNat := by
    rw [hwd.eq]; exact hmu _ (by rw [hdt]; omega) (by rw [hdt]; omega)
  have hDs := words_succ_top m ((x.get 14#5).toNat - 1) (x.get 13#5)
  rw [show (x.get 14#5).toNat - 1 + 1 = (x.get 14#5).toNat by omega] at hDs
  have hd0 : wd ≠ 0 := by
    intro h0
    have hl := words_lt m ((x.get 14#5).toNat - 1) (x.get 13#5)
    rw [hed] at h0
    rw [h0] at hDs
    simp at hDs
    omega
  rv_exec_cut 71
  rv_subst
  have hs := clz_ite wd
  rw [if_neg hd0, swarClz_expand, smear_expand] at hs
  rw [hs]
  clear hs
  have hns := norm_shift wd hd0
  generalize hsd : 63 - Nat.log2 wd.toNat = s at hns
  have hs64 : s < 64 := by omega
  have hsN : (BitVec.ofNat 64 s).toNat = s := by rw [BitVec.toNat_ofNat]; omega
  have hsp' : (x.get 2#5 + 18446744073709551472#64).toNat = (x.get 2#5 - 288#64).toNat + 144 := by
    bv_omega
  -- The shift loop of the divisor into the words at sp - 144.
  refine k320_dn_start (A := bufWords (x.get 11#5) 5 ++ bufWords (x.get 13#5) (x.get 14#5).toNat ++
      bufWords (x.get 10#5) 9 ++ bufWords (x.get 2#5 - 288#64) 36 ++ bufWords T 256) _ _
    (x.get 13#5) (x.get 2#5 + 18446744073709551472#64) (x.get 14#5).toNat (BitVec.ofNat 64 s)
    ?_ (by omega) ?_ ?_ ?_ ?_ (by rw [hsN]; exact hs64) (by omega) hdn (by rw [hsp']; omega)
    (by rw [hsp']; omega) ?_ ?_ ?_
  all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · exact off_sub1 _ (by omega) (by omega)
  · intro i hi
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (mem_bufWords hi))))
  · intro i hi
    rw [k320_sp144 _ hsn]
    exact List.mem_append_left _ (List.mem_append_right _
      (mem_bufWords_of_offset (by omega) (mem_bufWords hi)))
  -- The end of the shift loop of the divisor at 80.
  intro x80 m80 ⟨hdw, hdun, h80z, hcl80⟩
  have e2 := get_of_cl hcl80 (r := 2#5) (by decide) (by decide)
  have e8 := get_of_cl hcl80 (r := 8#5) (by decide) (by decide)
  have e9 := get_of_cl hcl80 (r := 9#5) (by decide) (by decide)
  have e10 := get_of_cl hcl80 (r := 10#5) (by decide) (by decide)
  have e14 := get_of_cl hcl80 (r := 14#5) (by decide) (by decide)
  have e18 := get_of_cl hcl80 (r := 18#5) (by decide) (by decide)
  have e19 := get_of_cl hcl80 (r := 19#5) (by decide) (by decide)
  have e20 := get_of_cl hcl80 (r := 20#5) (by decide) (by decide)
  have e21 := get_of_cl hcl80 (r := 21#5) (by decide) (by decide)
  have e22 := get_of_cl hcl80 (r := 22#5) (by decide) (by decide)
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte] at e2 e8 e9 e10 e14
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte] at e18 e19 e20 e21 e22
  rw [← regs_set_of_get' (by decide) e2, ← regs_set_of_get' (by decide) e8,
    ← regs_set_of_get' (by decide) e9, ← regs_set_of_get' (by decide) e10,
    ← regs_set_of_get' (by decide) e14, ← regs_set_of_get' (by decide) e18,
    ← regs_set_of_get' (by decide) e19, ← regs_set_of_get' (by decide) e20,
    ← regs_set_of_get' (by decide) e21, ← regs_set_of_get' (by decide) e22]
  have hsp0 : (x.get 2#5 + 18446744073709551472#64).toNat = (x.get 2#5 - 288#64).toNat + 144 := hsp'
  -- The memory of u and d after the shift loop of the divisor.
  have hmu80 : ∀ b, b + 8 ≤ (x.get 10#5).toNat ∨ (x.get 10#5).toNat + 72 ≤ b →
      b + 8 ≤ (x.get 2#5 - 288#64).toNat ∨ (x.get 2#5 - 288#64).toNat + 288 ≤ b →
      memWord m80 b = memWord m b := by
    intro b h1 h2
    rw [memWord_of_unchangedExcept hdun b (by rw [hsp0]; omega)]
    exact hmu b h1 h2
  -- d[0]
  refine Reach.step (by decide) rfl ?_
  simp only [StepGoal, Nat.reduceAdd, BitVec.reduceSignExtend, BitVec.add_zero]
  rv_val
  refine ⟨List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (mem_bufWords_zero (by omega))))), fun wd0 hwd0 => ?_⟩
  have hnm := k320_n_le_mm hD hU htop
  obtain ⟨t144, t72, t80, t88, t96, t104, t112⟩ := k320_stack_toNat (x.get 2#5) hsn
  -- The words of u: unchanged since the start.
  have hum : ∀ k, k < 5 → memWord m80 (x.get 11#5 + BitVec.ofNat 64 (8 * k)).toNat =
      memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * k)).toNat := by
    intro k hk
    have hk8 := toNat_add8 (x.get 11#5) (8 * k) (by omega) (by omega)
    exact hmu80 _ (by rw [hk8]; omega) (by rw [hk8]; omega)
  have hum0 : memWord m80 (x.get 11#5).toNat = memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * 0)).toNat := by
    have := hum 0 (by omega); simpa using this
  have hum1 : memWord m80 (x.get 11#5 + 8#64).toNat = memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * 1)).toNat :=
    hum 1 (by omega)
  have hum2 : memWord m80 (x.get 11#5 + 16#64).toNat = memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * 2)).toNat :=
    hum 2 (by omega)
  have hum3 : memWord m80 (x.get 11#5 + 24#64).toNat = memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * 3)).toNat :=
    hum 3 (by omega)
  have hum4 : memWord m80 (x.get 11#5 + 32#64).toNat = memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * 4)).toNat :=
    hum 4 (by omega)
  have hd0m : wd0 = memWord m (x.get 13#5).toNat := by
    rw [hwd0.eq]; exact hmu80 _ (by omega) (by omega)
  rv_exec_cut 90
  rename_i wu4 hwu4 wdn0 hwdn0 wsx hwsx wsh5 hwsh5 wun5 hwun5
  have hv0 : wdn0 = memWord m (x.get 13#5).toNat <<< ((BitVec.ofNat 64 s).toNat % 64) := by
    rw [hwdn0.eq, hd0m]
  have hun5v : wun5.toNat = (memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * 4)).toNat).toNat /
      2 ^ (64 - s) := by
    rw [hwun5.eq, hwsh5.eq, hwsx.eq, hwu4.eq, hum4]; exact k320_un5_val _ s hs64
  have hsN : (BitVec.ofNat 64 s).toNat = s := by rw [BitVec.toNat_ofNat]; omega
  have hnorm' : (memWord m (x.get 13#5 + BitVec.ofNat 64 (8 * ((x.get 14#5).toNat - 1))).toNat).toNat *
      2 ^ s < 2 ^ 64 := by rw [← hed, ← hns.1]; exact BitVec.isLt _
  have hut : (x.get 11#5 + BitVec.ofNat 64 (8 * ((x.get 12#5).toNat - 1))).toNat =
      (x.get 11#5).toNat + 8 * ((x.get 12#5).toNat - 1) := toNat_add8 _ _ (by omega) (by omega)
  rv_exec_cut 91 113
  all_goals first
    | (rv_get hS0 : BitVec.ofNat 64 s = 0#64
       have hs0 : s = 0 := by
         have := congrArg BitVec.toNat hS0; rw [BitVec.toNat_ofNat] at this; simp at this; omega
       rv_exec_cut 120
       rename_i wu3 hwu3 wu2 hwu2 wu0 hwu0 wu1 hwu1
       have hun4v : wu4.toNat = (memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * 4)).toNat).toNat * 2 ^ s %
           2 ^ 64 + (memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * 3)).toNat).toNat / 2 ^ (64 - s) := by
         rw [hwu4.eq, hum4, hs0]; have := (memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * 3)).toNat).isLt
         have := (memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * 4)).toNat).isLt; simp; omega
       have hun3v : wu3.toNat = (memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * 3)).toNat).toNat * 2 ^ s %
           2 ^ 64 + (memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * 2)).toNat).toNat / 2 ^ (64 - s) := by
         rw [hwu3.eq, hum3, hs0]; have := (memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * 3)).toNat).isLt
         have := (memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * 2)).toNat).isLt; simp; omega
       have hun2v : wu2.toNat = (memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * 2)).toNat).toNat * 2 ^ s %
           2 ^ 64 + (memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * 1)).toNat).toNat / 2 ^ (64 - s) := by
         rw [hwu2.eq, hum2, hs0]; have := (memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * 2)).toNat).isLt
         have := (memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * 1)).toNat).isLt; simp; omega
       have hun1v : wu1.toNat = (memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * 1)).toNat).toNat * 2 ^ s %
           2 ^ 64 + (memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * 0)).toNat).toNat / 2 ^ (64 - s) := by
         rw [hwu1.eq, hum1, hs0]; have := (memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * 1)).toNat).isLt
         have := (memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * 0)).toNat).isLt; simp; omega
       have hu0 : wu0 = memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * 0)).toNat := by
         rw [hwu0.eq, hum0]
       k320_join)
    | (rv_get hS0 : ¬BitVec.ofNat 64 s = 0#64
       have hs0 : 0 < s := by
         rcases Nat.eq_zero_or_pos s with h | h
         · subst h; exact absurd rfl hS0
         · exact h
       rv_exec_cut 120
       rename_i wu3 hwu3 w64 hw64 a4 ha4 b3 hb3 un4 hun4 wu2 hwu2 a3 ha3 b2 hb2 un3 hun3 wu1 hwu1 a2 ha2
         b1 hb1 un2 hun2 wu0 hwu0 a1 ha1 b0 hb0 un1 hun1
       have hun4v : un4.toNat = (memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * 4)).toNat).toNat * 2 ^ s %
           2 ^ 64 + (memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * 3)).toNat).toNat / 2 ^ (64 - s) := by
         rw [hun4.eq, hb3.eq, ha4.eq, hw64.eq, hwu3.eq, hwu4.eq, hum3, hum4]
         exact k320_funnel_val _ _ s hs0 hs64
       have hun3v : un3.toNat = (memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * 3)).toNat).toNat * 2 ^ s %
           2 ^ 64 + (memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * 2)).toNat).toNat / 2 ^ (64 - s) := by
         rw [hun3.eq, hb2.eq, ha3.eq, hw64.eq, hwu2.eq, hwu3.eq, hum2, hum3]
         exact k320_funnel_val _ _ s hs0 hs64
       have hun2v : un2.toNat = (memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * 2)).toNat).toNat * 2 ^ s %
           2 ^ 64 + (memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * 1)).toNat).toNat / 2 ^ (64 - s) := by
         rw [hun2.eq, hb1.eq, ha2.eq, hw64.eq, hwu1.eq, hwu2.eq, hum1, hum2]
         exact k320_funnel_val _ _ s hs0 hs64
       have hun1v : un1.toNat = (memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * 1)).toNat).toNat * 2 ^ s %
           2 ^ 64 + (memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * 0)).toNat).toNat / 2 ^ (64 - s) := by
         rw [hun1.eq, hb0.eq, ha1.eq, hw64.eq, hwu0.eq, hwu1.eq, hum0, hum1]
         exact k320_funnel_val _ _ s hs0 hs64
       have hu0 : wu0 = memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * 0)).toNat := by
         rw [hwu0.eq, hum0]
       k320_join)

/-- A buffer is outside the image if its first and last words are. -/
theorem k320_buf_outside (a base : BitVec 64) (k o : Nat)
    (h0 : a.toNat + 8 ≤ base.toNat ∨ base.toNat + o ≤ a.toNat)
    (hk : (a + BitVec.ofNat 64 (8 * k)).toNat + 8 ≤ base.toNat ∨
      base.toNat + o ≤ (a + BitVec.ofNat 64 (8 * k)).toNat)
    (ha : a.toNat + 8 * (k + 1) ≤ 2 ^ 64) (ho : 8 * (k + 1) ≤ o) :
    a.toNat + 8 * (k + 1) ≤ base.toNat ∨ base.toNat + o ≤ a.toNat := by
  have : (a + BitVec.ofNat 64 (8 * k)).toNat = a.toNat + 8 * k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  omega

theorem udivrem_knuth_320.proof : udivrem_knuth_320.spec := by
  apply runsI_of_reach udivrem_knuth_320_image_decodes
  intro base ret hb8 hr _ _ hw x m hx1 hbufs hhold hpre
  rw [show udivrem_knuth_320_image_dataOff = 1672 from rfl] at hw hhold hbufs ⊢
  rw [show udivrem_knuth_320_image_data.length = 256 from rfl] at hw hbufs ⊢
  have hb : base &&& 3 = 0 := by
    have := congrArg (· &&& 3#64) hb8
    simpa [BitVec.and_assoc] using this
  have hx : x.get 1#5 = ret := by rw [← Regs.eq_get x (by decide)]; exact hx1
  have hpre' := hpre
  simp only [udivrem_knuth_320.pre, Buf] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  have hst := k320_buf_outside (x 2#5 - 288#64) base 35 (1672 + 8 * 256)
    (hbufs _ (List.mem_append_right _ (mem_bufWords_zero (by norm_num))))
    (hbufs _ (List.mem_append_right _ (mem_bufWords (by norm_num))))
    (by rw [Regs.eq_get x (by decide)]; exact hpre'.2.2.2.2.2.1.2) (by norm_num)
  have hres := k320_buf_outside (x 10#5) base 8 (1672 + 8 * 256)
    (hbufs _ (List.mem_append_left _ (List.mem_append_right _ (mem_bufWords_zero (by norm_num)))))
    (hbufs _ (List.mem_append_left _ (List.mem_append_right _ (mem_bufWords (by norm_num)))))
    (by rw [Regs.eq_get x (by decide)]; exact hpre'.1.2) (by norm_num)
  rw [Regs.eq_get x (by decide)] at hst hres
  rw [show udivrem_knuth_320_entry =
      udivrem_knuth_320_image_udivrem_knuth_320_offset from rfl, dataWords, ← hx]
  refine Reach.lift udivrem_knuth_320_image_udivrem_knuth_320_in (by decide) ?_
  have hT : (base + BitVec.ofNat 64 1672).toNat = base.toNat + 1672 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have h := udivrem_knuth_320.reach 0x0#20 0x3a8#12
    (pcAt base udivrem_knuth_320_image_udivrem_knuth_320_offset) _ x m
    (by simp only [udivrem_knuth_320_image_udivrem_knuth_320_offset, pcAt]
        exact aligned_add hb (by decide))
    (by simp only [udivrem_knuth_320_image_udivrem_knuth_320_offset, pcAt,
      BitVec.reduceAppend, BitVec.reduceSignExtend]; bv_omega)
    (by rw [hT]; omega) (hx ▸ hr) (by rw [hT]; omega) (by rw [hT]; omega) hhold hpre
  rwa [pcAt_zero] at h

/-- The registers of the nonvacuous instance: the result of 9 words, u = 2^192 of 5 words with
m = 4 and d = 2^128 of 3 words above the data, and the stack below sp. -/
theorem udivrem_knuth_320.nonvacuous :
    NonVacuousI udivrem_knuth_320_image_code udivrem_knuth_320_image_data
      udivrem_knuth_320_image_dataOff udivrem_knuth_320.bufs udivrem_knuth_320.pre :=
  nonVacuousI_of_args (fun i => if i = 10#5 then 0x80000C00#64 else if i = 11#5 then 0x80000C48#64
      else if i = 12#5 then 4#64 else if i = 13#5 then 0x80000C70#64
      else if i = 14#5 then 3#64 else if i = 2#5 then 0x80000DA8#64 else 0)
    0x80000C48 [0, 0, 0, 1, 0, 0, 0, 1]
    (by decide) (by decide) (by decide) (by decide)
    (by rw [show udivrem_knuth_320_image_dataOff = 1672 from rfl,
          show udivrem_knuth_320_image_data.length = 256 from rfl]
        simp only [udivrem_knuth_320.bufs, ↓reduceIte, BitVec.reduceEq, BitVec.reduceSub,
          BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub, bufWords,
          List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq]
        repeat' apply And.intro
        all_goals decide)
    (by decide)
    (fun m => by
      simp only [udivrem_knuth_320.pre, Buf, Disjoint, words, ↓reduceIte, BitVec.reduceEq,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, BitVec.toNat_ofNat,
        Nat.reducePow, Nat.reduceMod, Nat.reduceSub, Nat.mul_zero, Nat.add_zero]
      simp (disch := decide) only [memWord_storeWords_getD]
      decide)

end IntxRV.Api
