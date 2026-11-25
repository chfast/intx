import IntxRV.Div512
import IntxRV.Api.shl_9_8
import IntxRV.Api.udivrem_knuth_normalized_3
/-!
# The path of `udivrem<512, 256>()` for a divisor of 3 words

For 2^128 ≤ v < 2^192 (`u512_k3`): the result is zeroed by `memset()`, the divisor is normalized
inline by the count of the leading zeros of v[2], u by `shl<9, 8>()`; the code counts the words to
divide, stores 0 to the top quotient word and calls `udivrem_knuth_normalized<3>()`
(`u512_k3_div`), and shifts the remainder back inline. See `IntxRV/Div512.lean`.
-/


namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

variable {hi0 hi1 hi2 hi3 : BitVec 20} {lo0 lo1 lo2 lo3 : BitVec 12} {T : BitVec 64}

set_option hygiene false in
local notation "P512" => udivrem_512_256_progAt hi0 lo0 hi1 lo1 hi2 lo2 hi3 lo3


/-- The path of the 3-word Knuth division in `udivrem<512, 256>()` from 192, after `shl<9, 8>()`
of u: the words to divide, the call of `udivrem_knuth_normalized<3>()` and the shift right of the
remainder. -/
theorem u512_k3_div {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hb3 : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0) (hpre : udivrem_512_256.pre x m)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64)
    (hTr : (x.get 10#5).toNat + 96 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hTs : (x.get 2#5 - 240#64).toNat + 240 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 240#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hD : ∀ a ∈ bufWords T 256, a ∈ D)
    (hT2 : pcAt (pcAt base 916) 12 + ((hi2 ++ 0x000#12).signExtend 64 + lo2.signExtend 64) = T)
    (m' : Mem) (x5 : Regs) (m5 : Mem) (hF : U512Frame x m x5 m5)
    (hm5 : UnchangedExcept (IntxRV.memFill m' (x.get 10#5).toNat 0#8 96) m5
      (x.get 2#5 + 18446744073709551456#64) 104)
    (h8 : x5.get 8#5 = x.get 11#5) (h18 : x5.get 18#5 = x.get 10#5)
    (h20 : x5.get 20#5 = x.get 12#5) (mm : Nat) (hmm1 : 1 ≤ mm) (hmm8 : mm ≤ 8)
    (h9 : x5.get 9#5 = BitVec.ofNat 64 mm) (hum : words m (x.get 11#5) 8 < 2 ^ (64 * mm))
    (s : Nat) (hs : s < 64) (h19 : x5.get 19#5 = BitVec.ofNat 64 s)
    (h21 : x5.get 21#5 = BitVec.ofNat 64 s ^^^ 18446744073709551615#64)
    (hv3 : memWord m (x.get 12#5 + 24#64).toNat = 0#64)
    (hv2 : memWord m (x.get 12#5 + 16#64).toNat ≠ 0)
    (hdn : words m5 (x.get 2#5 + 18446744073709551456#64) 3 = words m (x.get 12#5) 3 * 2 ^ s)
    (hdn63 : 2 ^ 191 ≤ words m (x.get 12#5) 3 * 2 ^ s)
    (hdn64 : (memWord m (x.get 12#5 + 16#64).toNat).toNat * 2 ^ s < 2 ^ 64)
    (hshl : words m5 (x.get 2#5 + 18446744073709551488#64) 9 = words m (x.get 11#5) 8 * 2 ^ s)
    (hnum : 3 < mm + if (memWord m (x.get 12#5 + 16#64).toNat).toNat ≤
      (memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * (mm - 1))).toNat).toNat then 1 else 0) :
    Reach (u512Bufs x D) P512 base (pcAt base 192) x5 m5 (x.get 1#5)
      (udivrem_512_256.post x m) := by
  -- `omega` and `subst_vars` do not see the address of the table.
  replace hT2 := PLift.up hT2
  have hpre0 := hpre
  simp only [udivrem_512_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr⟩ := hpre
  have h2 : x5.get 2#5 = x.get 2#5 + 18446744073709551456#64 := hF.1
  have hmn : (BitVec.ofNat 64 mm).toNat = mm := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hv2' := hF.memWord_v hpre0 16#64 (by decide)
  have hu' := hF.memWord_u hpre0 (BitVec.ofNat 64 (8 * (mm - 1)))
    (by rw [BitVec.toNat_ofNat]; omega)
  have hua' : x.get 11#5 + (BitVec.ofNat 64 mm <<< 3 + 18446744073709551608#64) =
      x.get 11#5 + BitVec.ofNat 64 (8 * (mm - 1)) := by bv_omega
  rw [← regs_set_of_get' (by decide) h2, ← regs_set_of_get' (by decide) h8,
    ← regs_set_of_get' (by decide) h9, ← regs_set_of_get' (by decide) h18,
    ← regs_set_of_get' (by decide) h19, ← regs_set_of_get' (by decide) h20,
    ← regs_set_of_get' (by decide) h21]
  rv_exec_cut 195
  rv_subst
  -- The top word u[mm - 1] of u.
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  rw [hua']
  refine ⟨by simp only [u512Bufs, List.mem_append]
             exact Or.inl (Or.inl (Or.inl (Or.inl (mem_bufWords (by omega))))), fun wa hwa => ?_⟩
  rw [hu'] at hwa
  rv_subst
  rv_exec_cut 200
  rv_subst
  -- The store of 0 to q[mm - 3].
  have hmm3 : 3 ≤ mm := by split_ifs at hnum <;> omega
  have hqa : x.get 10#5 + (BitVec.ofNat 64 mm <<< 3 + 18446744073709551592#64) =
      x.get 10#5 + BitVec.ofNat 64 (8 * (mm - 3)) := by bv_omega
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  rw [hqa]
  refine ⟨by simp only [u512Bufs, List.mem_append]
             exact Or.inl (Or.inl (Or.inr (mem_bufWords (by omega)))), ?_⟩
  rv_exec_cut 916
  try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.reduceSignExtend]
  rw [show pcAt base 204 + 4096#64 + 18446744073709550368#64 = pcAt base 916 by
      simp only [pcAt]; bv_omega,
    update_aligned (pcAt_aligned hb3 916), hv2']
  -- The words to divide.
  generalize hL : BitVec.ofNat 64 mm + ((if memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * (mm - 1))).toNat <
      memWord m (x.get 12#5 + 16#64).toNat then 1#64 else 0#64) ^^^ 1#64) = L
  have hLn : L.toNat = mm + if (memWord m (x.get 12#5 + 16#64).toNat).toNat ≤
      (memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * (mm - 1))).toNat).toNat then 1 else 0 := by
    subst hL
    by_cases hab : memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * (mm - 1))).toNat <
        memWord m (x.get 12#5 + 16#64).toNat
    · rw [if_pos hab, if_neg (by rw [BitVec.lt_def] at hab; omega),
        show (1#64 ^^^ 1#64 : BitVec 64) = 0#64 from rfl, BitVec.add_zero, hmn, Nat.add_zero]
    · rw [if_neg hab, if_pos (by rw [BitVec.lt_def] at hab; omega),
        show (0#64 ^^^ 1#64 : BitVec 64) = 1#64 from rfl, BitVec.toNat_add, hmn]
      simp only [BitVec.toNat_ofNat]; omega
  generalize hul : (mm + if (memWord m (x.get 12#5 + 16#64).toNat).toNat ≤
      (memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * (mm - 1))).toNat).toNat then 1 else 0) = ulen
    at hLn hnum
  have hl9 : ulen ≤ 9 := by rw [← hul]; split_ifs <;> omega
  -- The normalized numerator and divisor in the memory of the call.
  have hm7 := unchangedExcept_memFill_memStore_zero hm5
    (x.get 10#5 + BitVec.ofNat 64 (8 * (mm - 3))).toNat (by bv_omega)
  generalize hM7 : memStore m5 (x.get 10#5 + BitVec.ofNat 64 (8 * (mm - 3))).toNat 0#64 = M7
    at hm7 ⊢
  have hdn7 : words M7 (x.get 2#5 + 18446744073709551456#64) 3 = words m (x.get 12#5) 3 * 2 ^ s := by
    rw [← hM7, words_memStore_of_disjoint _ _ _ _ _ (by bv_omega) (by bv_omega), hdn]
  have hU := words_lt m 8 (x.get 11#5)
  have hun7 : words M7 (x.get 2#5 + 18446744073709551488#64) 9 = words m (x.get 11#5) 8 * 2 ^ s := by
    rw [← hM7, words_memStore_of_disjoint _ _ _ _ _ (by bv_omega) (by bv_omega), hshl]
  have hw3 : words m (x.get 12#5) 3 = (memWord m (x.get 12#5).toNat).toNat + 2 ^ 64 *
      ((memWord m (x.get 12#5 + 8#64).toNat).toNat + 2 ^ 64 *
        (memWord m (x.get 12#5 + 16#64).toNat).toNat) := by
    simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
      Nat.add_zero]
  have hv0l := (memWord m (x.get 12#5).toNat).isLt
  have hv1l := (memWord m (x.get 12#5 + 8#64).toNat).isLt
  have hb0 : 0 < (memWord m (x.get 12#5 + 16#64).toNat).toNat := by
    rcases Nat.eq_zero_or_pos (memWord m (x.get 12#5 + 16#64).toNat).toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hv2
    · exact h
  have hVb : (memWord m (x.get 12#5 + 16#64).toNat).toNat * 2 ^ (64 * (3 - 1)) ≤
      words m (x.get 12#5) 3 := by rw [hw3]; norm_num; omega
  have hVs : words m (x.get 12#5) 3 * 2 ^ s < 2 ^ (64 * 3) :=
    norm_top_lt (k := 2) (by rw [hw3]; omega) hdn64 hs
  obtain ⟨hUs, hUq⟩ := knuth_ulen (n := 3) hmm1 (by norm_num) (BitVec.isLt _)
    (words_top_bound m _ mm hmm1 hmm8 hum) hVb hVs hs hb0 hul.symm hnum
  have hunl : words M7 (x.get 2#5 + 18446744073709551488#64) ulen =
      words m (x.get 11#5) 8 * 2 ^ s := by
    have hs9 := words_split M7 ulen (9 - ulen) (x.get 2#5 + 18446744073709551488#64)
    rw [show ulen + (9 - ulen) = 9 by omega, hun7] at hs9
    exact lo_of_lt hs9 hUs
  have hFM : U512Frame x m x5 M7 := by
    refine U512Frame.mem hF hpre0 ?_
    rw [← hM7]
    simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
    exact unchangedExcept2_refl _ _ _ _ _
  refine Reach.call_sub (r := 206) udivrem_512_256_progAt_udivrem_knuth_normalized_3_in
    (by rw [udivrem_512_256_progAt_length]; decide)
    (udivrem_knuth_normalized_3.reach hi2 lo2 (pcAt base 916) T _ M7 (pcAt_aligned hb3 916)
      hT2.down hw ?_ ?_ ?_ ?_) ?_ ?_ ?_
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    exact pcAt_aligned hb3 206
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    rw [show x.get 2#5 + 18446744073709551456#64 - 80#64 = x.get 2#5 - 240#64 by bv_omega]
    omega
  · exact hFM.holdsData hw hTr hTs hhold
  · simp only [udivrem_knuth_normalized_3.pre, Buf, Disjoint]
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    rw [hLn, hdn7, hunl]
    rw [show x.get 2#5 + 18446744073709551456#64 - 80#64 = x.get 2#5 - 240#64 by bv_omega]
    refine ⟨⟨by bv_omega, by bv_omega⟩, ⟨by bv_omega, by bv_omega⟩, ⟨by bv_omega, by bv_omega⟩,
      by bv_omega, by bv_omega, by bv_omega, ⟨hsa, by omega⟩, by bv_omega, by bv_omega,
      by bv_omega, trivial, hnum, ?_, hUq⟩
    rw [show 64 * 3 - 1 = 191 from rfl]; exact hdn63
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · intro a ha
    simp only [udivrem_knuth_normalized_3.bufs] at ha
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at ha
    rw [hLn] at ha
    rw [show x.get 2#5 + 18446744073709551456#64 - 80#64 = x.get 2#5 - 240#64 by bv_omega] at ha
    simp only [List.mem_append] at ha ⊢
    rcases ha with (((h | h) | h) | h) | h
    · rw [show x.get 2#5 + 18446744073709551456#64 = x.get 2#5 - 240#64 +
        BitVec.ofNat 64 (8 * 10) by bv_omega] at h
      exact Or.inl (Or.inr (mem_bufWords_of_offset (by norm_num) h))
    · exact Or.inl (Or.inl (Or.inr (mem_bufWords_of_le (by omega) h)))
    · rw [show x.get 2#5 + 18446744073709551488#64 = x.get 2#5 - 240#64 +
        BitVec.ofNat 64 (8 * 14) by bv_omega] at h
      exact Or.inl (Or.inr (mem_bufWords_of_offset (by omega) h))
    · exact Or.inl (Or.inr (mem_bufWords_of_le (by norm_num) h))
    · exact Or.inr (hD _ h)
  · intro x7 m7 hpost
    obtain ⟨hq, hrm, hunc, hsaved⟩ := hpost
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at hq hrm hunc
    rw [hLn] at hq hrm hunc
    rw [hunl, hdn7, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos s)] at hq
    rw [hunl, hdn7, Nat.mul_mod_mul_right] at hrm
    have hF7 : U512Frame x m x7 m7 := by
      refine U512Frame.regs (x' := x5) (U512Frame.mem hFM hpre0 ?_) ?_ ?_
      · intro k hka hkb
        exact hunc k (by omega) (by bv_omega) (by bv_omega)
      · rw [get_of_calleeSaved hsaved (by decide)]
        simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
        exact h2.symm
      · u512_cs' hsaved
    have h27 : x7.get 2#5 = x.get 2#5 + 18446744073709551456#64 := hF7.1
    have h187 : x7.get 18#5 = x.get 10#5 := by
      rw [get_of_calleeSaved hsaved (by decide)]
      simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    have h197 : x7.get 19#5 = BitVec.ofNat 64 s := by
      rw [get_of_calleeSaved hsaved (by decide)]
      simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    have h217 : x7.get 21#5 = BitVec.ofNat 64 s ^^^ 18446744073709551615#64 := by
      rw [get_of_calleeSaved hsaved (by decide)]
      simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    -- The memory outside q, u and the frame: the zero result of `memset()`.
    have hres7 : UnchangedExcept2 (IntxRV.memFill m' (x.get 10#5).toNat 0#8 96) m7 (x.get 10#5)
        (8 * (ulen - 3)) (x.get 2#5 - 240#64) 240 :=
      unchangedExcept2_comp hm7 (by bv_omega)
        (unchangedExcept2_of_3 _ _ hunc (by bv_omega) (by bv_omega))
    have hb : (x.get 10#5).toNat + 96 ≤ (x.get 2#5 - 240#64).toNat ∨
        (x.get 2#5 - 240#64).toNat + 240 ≤ (x.get 10#5).toNat := by omega
    -- The 3 words of the normalized remainder.
    have hr3 : words m7 (x.get 2#5 + 18446744073709551488#64) 3 =
        words m (x.get 11#5) 8 % words m (x.get 12#5) 3 * 2 ^ s := by
      have hs3 := words_split m7 3 (ulen - 3) (x.get 2#5 + 18446744073709551488#64)
      rw [show 3 + (ulen - 3) = ulen by omega] at hs3
      rw [← hrm, hs3, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (words_lt _ _ _)]
    rw [← regs_set_of_get' (by decide) h27, ← regs_set_of_get' (by decide) h187,
      ← regs_set_of_get' (by decide) h197, ← regs_set_of_get' (by decide) h217]
    rv_exec_cut 327
    rv_subst
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.reduceSignExtend]
    have hv4 : words m (x.get 12#5) 4 = words m (x.get 12#5) 3 := by
      have h := words_split m 3 1 (x.get 12#5)
      rw [show 3 + 1 = 4 from rfl] at h
      have h1 : words m (x.get 12#5 + 24#64) 1 = 0 := by
        simp only [words, hv3, BitVec.toNat_zero, Nat.mul_zero, Nat.add_zero]
      rw [h, show BitVec.ofNat 64 (8 * 3) = 24#64 from rfl, h1, Nat.mul_zero, Nat.add_zero]
    have hV0 : words m (x.get 12#5) 4 ≠ 0 := by
      rw [hv4, hw3]; omega
    refine u512_epi base x m hr _ _ (U512Frame.regs (U512Frame.mem hF7 hpre0 ?_) ?_ ?_) ?_ ?_
    · simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
      exact unchangedExcept2_refl _ _ _ _ _
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      exact h27.symm
    · u512_cs
    · rw [words_memStore_of_disjoint _ _ _ _ _ (by omega) (by bv_omega),
        words_memStore_of_disjoint _ _ _ _ _ (by omega) (by bv_omega),
        words_memStore_of_disjoint _ _ _ _ _ (by omega) (by bv_omega),
        u512_quot_words m' m7 hpre0 (ulen - 3) (by omega) hres7 hb, hq, hv4]
    · have hz := u512_res_zero m' m7 hpre0 (ulen - 3) hres7 hb 11 1 (by omega) (by omega)
      rw [show BitVec.ofNat 64 (8 * 11) = 88#64 from rfl] at hz
      simp only [words, Nat.mul_zero, Nat.add_zero] at hz
      have hu3 : words m7 (x.get 2#5 + 18446744073709551488#64) 3 =
          (memWord m7 (x.get 2#5 + 18446744073709551488#64).toNat).toNat + 2 ^ 64 *
            ((memWord m7 (x.get 2#5 + 18446744073709551496#64).toNat).toNat + 2 ^ 64 *
              (memWord m7 (x.get 2#5 + 18446744073709551504#64).toNat).toNat) := by
        simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
          Nat.add_zero]
      have e := shr_val3 (memWord m7 (x.get 2#5 + 18446744073709551488#64).toNat).toNat
        (memWord m7 (x.get 2#5 + 18446744073709551496#64).toNat).toNat
        (memWord m7 (x.get 2#5 + 18446744073709551504#64).toNat).toNat s hs
      rw [← hu3, hr3, Nat.mul_div_cancel _ (Nat.two_pow_pos s)] at e
      rw [if_neg hV0, hv4, ← e]
      simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
        Nat.add_zero]
      simp (disch := first | bv_omega | fail) only [memWord_memStore_self, memWord_memStore_of_ne]
      have hsv : (BitVec.ofNat 64 s).toNat = s := by rw [BitVec.toNat_ofNat]; omega
      rw [funnel_shr_val _ _ _ (by rw [hsv]; exact hs), funnel_shr_val _ _ _ (by rw [hsv]; exact hs),
        toNat_ushiftRight', hsv, Nat.mod_eq_of_lt hs, hz]
      omega

theorem u512_k3 {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hb3 : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0) (hpre : udivrem_512_256.pre x m)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64)
    (hTr : (x.get 10#5).toNat + 96 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hTs : (x.get 2#5 - 240#64).toNat + 240 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 240#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hD : ∀ a ∈ bufWords T 256, a ∈ D)
    (hT2 : pcAt (pcAt base 916) 12 + ((hi2 ++ 0x000#12).signExtend 64 + lo2.signExtend 64) = T)
    (x' : Regs) (m' : Mem) (hF : U512Frame x m x' m') (h8 : x'.get 8#5 = x.get 11#5)
    (h10 : x'.get 10#5 = x.get 10#5) (h12 : x'.get 12#5 = 96#64) (h18 : x'.get 18#5 = x.get 10#5)
    (h19 : x'.get 19#5 = x.get 12#5) (mm : Nat) (hmm1 : 1 ≤ mm) (hmm8 : mm ≤ 8)
    (h9 : x'.get 9#5 = BitVec.ofNat 64 mm) (hum : words m (x.get 11#5) 8 < 2 ^ (64 * mm))
    (hv3 : memWord m (x.get 12#5 + 24#64).toNat = 0#64)
    (hv2 : memWord m (x.get 12#5 + 16#64).toNat ≠ 0)
    (hnum : 3 < mm + if (memWord m (x.get 12#5 + 16#64).toNat).toNat ≤
      (memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * (mm - 1))).toNat).toNat then 1 else 0) :
    Reach (u512Bufs x D) P512 base (pcAt base 126) x' m' (x.get 1#5)
      (udivrem_512_256.post x m) := by
  -- `omega` and `subst_vars` do not see the address of the table.
  replace hT2 := PLift.up hT2
  have hpre0 := hpre
  simp only [udivrem_512_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr⟩ := hpre
  rw [← regs_set_of_get' (by decide) h10, ← regs_set_of_get' (by decide) h12]
  rv_exec_cut 1308
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.reduceSignExtend]
  rw [show pcAt base 127 + 4096#64 + 628#64 = pcAt base 1308 by simp only [pcAt]; bv_omega,
    update_aligned (pcAt_aligned hb3 1308)]
  have hF1 := U512Frame.regs (x'' := ((((((x'.set (12#5) 96#64).set (10#5) (x.get 10#5)).set 11#5
      0#64).set (1#5) (pcAt base 127 + 4096#64)).set (1#5) (pcAt base 129))))
    hF (by simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]) (by u512_cs)
  refine u512_memset base x m hb3 hpre0 _ m' ?_ ?_ ?_ 129 ?_ ?_
  all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  intro x2 m2 hm2 hx10 hcs
  subst hm2
  have hF2 := (hF1.memFill hpre0).callee hcs
  have h22 : x2.get 2#5 = x.get 2#5 + 18446744073709551456#64 := hF2.1
  have h82 : x2.get 8#5 = x.get 11#5 := by
    rw [get_of_calleeSaved hcs (by decide)]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h8
  have h92 : x2.get 9#5 = BitVec.ofNat 64 mm := by
    rw [get_of_calleeSaved hcs (by decide)]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h9
  have h182 : x2.get 18#5 = x.get 10#5 := by
    rw [get_of_calleeSaved hcs (by decide)]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h18
  have h192 : x2.get 19#5 = x.get 12#5 := by
    rw [get_of_calleeSaved hcs (by decide)]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h19
  have hw0 := hF2.memWord_v hpre0 0#64 (by decide)
  rw [BitVec.add_zero] at hw0
  have hw1 := hF2.memWord_v hpre0 8#64 (by decide)
  have hw2 := hF2.memWord_v hpre0 16#64 (by decide)
  rw [← regs_set_of_get' (by decide) h22, ← regs_set_of_get' (by decide) h82,
    ← regs_set_of_get' (by decide) h92, ← regs_set_of_get' (by decide) h182,
    ← regs_set_of_get' (by decide) h192]
  rv_exec_cut 341
  rv_subst
  rw [hw0, hw1, hw2]
  have hs := clz_ite (memWord m (x.get 12#5 + 16#64).toNat)
  rw [if_neg hv2, swarClz_expand, smear_expand] at hs
  rw [hs]
  clear hs
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.reduceSignExtend]
  obtain ⟨hdn, hdn63⟩ := norm_shift _ hv2
  generalize hsd : 63 - Nat.log2 (memWord m (x.get 12#5 + 16#64).toNat).toNat = s at hdn hdn63
  have hs64 : s < 64 := by omega
  have hsn : (BitVec.ofNat 64 s).toNat = s := by rw [BitVec.toNat_ofNat]; omega
  rw [hsn, Nat.mod_eq_of_lt hs64] at hdn
  rw [show pcAt base 190 + 604#64 = pcAt base 341 by simp only [pcAt]; bv_omega,
    update_aligned (pcAt_aligned hb3 341)]
  refine Reach.call_sub (r := 192) udivrem_512_256_progAt_shl_9_8_in
    (by rw [udivrem_512_256_progAt_length]; decide)
    (shl_9_8.reach (pcAt base 341) _ _ ?_ ?_) ?_ ?_ ?_
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    exact pcAt_aligned hb3 192
  · simp only [shl_9_8.pre, Buf, Disjoint]
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    rw [hsn]
    exact ⟨⟨by bv_omega, by bv_omega⟩, ⟨hua, hun⟩, signExtend_setWidth_of_lt (by rw [hsn]; omega),
      by bv_omega, by omega⟩
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · intro a ha
    simp only [shl_9_8.bufs] at ha
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at ha
    simp only [List.mem_append] at ha ⊢
    rcases ha with h | h
    · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
    · rw [show x.get 2#5 + 18446744073709551488#64 = x.get 2#5 - 240#64 + BitVec.ofNat 64 (8 * 14)
        by bv_omega] at h
      exact Or.inl (Or.inr (mem_bufWords_of_offset (by norm_num) h))
  · intro x5 m5 hpost
    obtain ⟨hres, hunc, hsaved⟩ := hpost
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at hres hunc
    generalize hM : memStore (memStore (memStore (IntxRV.memFill m' (x.get 10#5).toNat 0#8 96)
      (x.get 2#5 + 18446744073709551456#64).toNat
      (memWord m (x.get 12#5).toNat <<< ((BitVec.ofNat 64 s).toNat % 64)))
      (x.get 2#5 + 18446744073709551464#64).toNat
      (memWord m (x.get 12#5 + 8#64).toNat <<< ((BitVec.ofNat 64 s).toNat % 64) |||
        memWord m (x.get 12#5).toNat >>> 1 >>>
          ((BitVec.ofNat 64 s ^^^ 18446744073709551615#64).toNat % 64)))
      (x.get 2#5 + 18446744073709551472#64).toNat
      (memWord m (x.get 12#5 + 16#64).toNat <<< ((BitVec.ofNat 64 s).toNat % 64) |||
        memWord m (x.get 12#5 + 8#64).toNat >>> 1 >>>
          ((BitVec.ofNat 64 s ^^^ 18446744073709551615#64).toNat % 64)) = M at hres hunc
    rw [hsn, Nat.mod_eq_of_lt (by omega : s < 2 ^ 32)] at hres
    -- The memory of the frame: the stores of the normalized divisor and the shifted numerator.
    have hFM : U512Frame x m x2 M := by
      refine U512Frame.mem hF2 hpre0 ?_
      rw [← hM]
      simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
      exact unchangedExcept2_refl _ _ _ _ _
    have hF5 : U512Frame x m x5 m5 := by
      refine U512Frame.regs (x' := x2) (U512Frame.mem hFM hpre0 ?_) ?_ ?_
      · intro k hka hkb
        exact hunc k (by bv_omega)
      · rw [get_of_calleeSaved hsaved (by decide)]
        simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
        exact h22.symm
      · u512_cs' hsaved
    have hm5 : UnchangedExcept (IntxRV.memFill m' (x.get 10#5).toNat 0#8 96) m5
        (x.get 2#5 + 18446744073709551456#64) 104 := by
      intro k hk
      rw [hunc k (by bv_omega), ← hM, getElem?_memStore_of_ne _ _ _ _ (by bv_omega),
        getElem?_memStore_of_ne _ _ _ _ (by bv_omega), getElem?_memStore_of_ne _ _ _ _ (by bv_omega)]
    have hu8 : words M (x.get 11#5) 8 = words m (x.get 11#5) 8 := hFM.words_u hpre0 8 le_rfl
    rw [hu8, Nat.mod_eq_of_lt] at hres
    swap
    · calc words m (x.get 11#5) 8 * 2 ^ s < 2 ^ (64 * 8) * 2 ^ 64 :=
            Nat.mul_lt_mul_of_lt_of_le (words_lt _ _ _) (Nat.pow_le_pow_right (by norm_num) hs64.le)
              (by positivity)
        _ = 2 ^ 576 := by rw [← pow_add]
    have hv2n : (memWord m (x.get 12#5 + 16#64).toNat).toNat * 2 ^ s < 2 ^ 64 :=
      hdn ▸ BitVec.isLt _
    have hw3 : words m (x.get 12#5) 3 = (memWord m (x.get 12#5).toNat).toNat + 2 ^ 64 *
        ((memWord m (x.get 12#5 + 8#64).toNat).toNat + 2 ^ 64 *
          (memWord m (x.get 12#5 + 16#64).toNat).toNat) := by
      simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
        Nat.add_zero]
    refine u512_k3_div base x m hb3 hr hpre0 hw hTr hTs hhold hD hT2.down m' x5 m5 hF5 hm5 ?_ ?_ ?_ mm
      hmm1 hmm8 ?_ hum s hs64 ?_ ?_ hv3 hv2 ?_ ?_ hv2n hres hnum
    all_goals try (rw [get_of_calleeSaved hsaved (by decide)]
                   simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte])
    · rw [words_of_unchangedExcept hunc 3 _ (by bv_omega) (by bv_omega), ← hM, hw3]
      simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
        Nat.add_zero]
      simp (disch := first | bv_omega | fail) only [memWord_memStore_self, memWord_memStore_of_ne]
      rw [toNat_shl, funnel_shl_val _ _ _ (by rw [hsn]; exact hs64),
        funnel_shl_val _ _ _ (by rw [hsn]; exact hs64), hsn, Nat.mod_eq_of_lt hs64]
      exact norm3_val _ _ _ s hs64 hv2n
    · rw [hw3]
      calc 2 ^ 191 = 2 ^ 128 * 2 ^ 63 := by norm_num
        _ ≤ 2 ^ 128 * ((memWord m (x.get 12#5 + 16#64).toNat).toNat * 2 ^ s) :=
          Nat.mul_le_mul_left _ hdn63
        _ = (2 ^ 64 * (2 ^ 64 * (memWord m (x.get 12#5 + 16#64).toNat).toNat)) * 2 ^ s := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ (by omega)

end IntxRV.Api
