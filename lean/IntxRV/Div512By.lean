import IntxRV.Div512
import IntxRV.Api.udivrem_by1
import IntxRV.Api.udivrem_by2
/-!
# The paths of `udivrem<512, 256>()` that call `udivrem_by1()` and `udivrem_by2()`

For v < 2^64 (`u512_by1`) and 2^64 ≤ v < 2^128 (`u512_by2`): the result is zeroed by `memset()`,
and the call passes max(m, 2) or max(m, 3) words of u (`u512_by1_call`, `u512_by2_call`). The
quotient words above the ones that the callee writes stay 0. See `IntxRV/Div512.lean`.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

variable {hi0 hi1 hi2 hi3 : BitVec 20} {lo0 lo1 lo2 lo3 : BitVec 12} {T : BitVec 64}

set_option hygiene false in
local notation "P512" => udivrem_512_256_progAt hi0 lo0 hi1 lo1 hi2 lo2 hi3 lo3

/-- The call of `udivrem_by1()` in `udivrem<512, 256>()` from 70 with U words of u. -/
theorem u512_by1_call {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hb3 : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0) (hpre : udivrem_512_256.pre x m)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64)
    (hTr : (x.get 10#5).toNat + 96 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hTs : (x.get 2#5 - 240#64).toNat + 240 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 240#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hD : ∀ a ∈ bufWords T 256, a ∈ D)
    (hT0 : pcAt (pcAt base 409) 5 + ((hi0 ++ 0x000#12).signExtend 64 + lo0.signExtend 64) = T)
    (x' : Regs) (m' : Mem) (hF : U512Frame x m x' m') (h8 : x'.get 8#5 = x.get 11#5)
    (h10 : x'.get 10#5 = x.get 10#5) (U : Nat) (hU2 : 2 ≤ U) (hU8 : U ≤ 8)
    (h9 : x'.get 9#5 = BitVec.ofNat 64 U) (hu : words m (x.get 11#5) U = words m (x.get 11#5) 8)
    (h18 : x'.get 18#5 = memWord m (x.get 12#5).toNat) (hv0 : memWord m (x.get 12#5).toNat ≠ 0)
    (hv : words m (x.get 12#5) 4 = (memWord m (x.get 12#5).toNat).toNat) :
    Reach (u512Bufs x D) P512 base (pcAt base 70) x' m' (x.get 1#5)
      (udivrem_512_256.post x m) := by
  -- `omega` and `subst_vars` do not see the address of the table.
  replace hT0 := PLift.up hT0
  have hpre0 := hpre
  simp only [udivrem_512_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr⟩ := hpre
  have hUn : (BitVec.ofNat 64 U).toNat = U := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [← regs_set_of_get' (by decide) h10]
  rv_exec_cut 1308
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  rw [show pcAt base 73 + 4096#64 + BitVec.signExtend 64 844#12 = pcAt base 1308 by
      simp only [pcAt, BitVec.reduceSignExtend]; bv_omega,
    update_aligned (pcAt_aligned hb3 1308)]
  have hF1 := U512Frame.regs (x'' := (((((x'.set (10#5) (x.get 10#5)).set 12#5 96#64).set (19#5)
      (x.get 10#5)).set 11#5 0#64).set (1#5) (pcAt base 73 + 4096#64)).set (1#5) (pcAt base 75))
    hF (by simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]) (by u512_cs)
  refine u512_memset base x m hb3 hpre0 _ m' ?_ ?_ ?_ 75 ?_ ?_
  all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  intro x2 m2 hm2 hx10 hcs
  subst hm2
  have hF2 := (hF1.memFill hpre0).callee hcs
  have h82 : x2.get 8#5 = x.get 11#5 := by
    rw [get_of_calleeSaved hcs (by decide)]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h8
  have h92 : x2.get 9#5 = BitVec.ofNat 64 U := by
    rw [get_of_calleeSaved hcs (by decide)]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h9
  have h182 : x2.get 18#5 = memWord m (x.get 12#5).toNat := by
    rw [get_of_calleeSaved hcs (by decide)]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h18
  have h192 : x2.get 19#5 = x.get 10#5 := by
    rw [get_of_calleeSaved hcs (by decide)]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  rw [← regs_set_of_get' (by decide) h82, ← regs_set_of_get' (by decide) h92,
    ← regs_set_of_get' (by decide) h182, ← regs_set_of_get' (by decide) h192]
  rv_exec_cut 409
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  rw [show pcAt base 80 + BitVec.signExtend 64 1316#12 = pcAt base 409 by
      simp only [pcAt, BitVec.reduceSignExtend]; bv_omega,
    update_aligned (pcAt_aligned hb3 409)]
  have hz : ∀ c : BitVec 64, c.toNat + 8 ≤ 96 →
      memWord (IntxRV.memFill m' (x.get 10#5).toNat 0#8 96) (x.get 10#5 + c).toNat = 0#64 :=
    u512_memFill_zero m' hpre0
  have hu2 := hF2.words_u hpre0 U hU8
  refine Reach.call_sub (r := 82) udivrem_512_256_progAt_udivrem_by1_in
    (by rw [udivrem_512_256_progAt_length]; decide)
    (udivrem_by1.reach hi0 lo0 (pcAt base 409) T _ _ hT0.down hw ?_ ?_ ?_) ?_ ?_ ?_
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    exact pcAt_aligned hb3 82
  · exact hF2.holdsData hw hTr hTs hhold
  · simp only [udivrem_by1.pre, Buf, Disjoint]
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    rw [hUn]
    have hv0n : 0 < (memWord m (x.get 12#5).toNat).toNat := by
      rcases Nat.eq_zero_or_pos (memWord m (x.get 12#5).toNat).toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hv0
      · exact h
    exact ⟨⟨hra, by omega⟩, ⟨hua, by omega⟩, by omega, hU2, trivial, hv0n⟩
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · intro a ha
    simp only [udivrem_by1.bufs] at ha
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at ha
    rw [hUn] at ha
    simp only [List.mem_append] at ha ⊢
    rcases ha with (h | h) | h
    · exact Or.inl (Or.inl (Or.inl (Or.inl (mem_bufWords_of_le hU8 h))))
    · exact Or.inl (Or.inl (Or.inr (mem_bufWords_of_le (by omega) h)))
    · exact Or.inr (hD _ h)
  · intro x4 m4 hpost
    obtain ⟨hq, hrem, hunc, hsaved⟩ := hpost
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at hq hrem hunc
    rw [hUn, hu2, hu, ← hv] at hq hrem
    rw [hUn] at hunc
    have hunc2 := unchangedExcept2_of (x.get 2#5 - 240#64) 240 hunc
    have hb : (x.get 10#5).toNat + 96 ≤ (x.get 2#5 - 240#64).toNat ∨
        (x.get 2#5 - 240#64).toNat + 240 ≤ (x.get 10#5).toNat := by omega
    have hF4 : U512Frame x m x4 m4 := by
      refine U512Frame.regs (x' := x2) (U512Frame.mem hF2 hpre0 ?_) ?_ ?_
      · exact unchangedExcept2_of _ _ (fun k hk => hunc k (by omega))
      · rw [get_of_calleeSaved hsaved (by decide)]
        simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      · u512_cs' hsaved
    have h194 : x4.get 19#5 = x.get 10#5 := by
      rw [get_of_calleeSaved hsaved (by decide)]
      simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    rw [← regs_set_of_get' (by decide) h194]
    rv_exec_cut 327
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.reduceSignExtend] at *
    refine u512_epi base x m hr _ _ (U512Frame.regs (U512Frame.mem hF4 hpre0 ?_) ?_ ?_) ?_ ?_
    · simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
      exact unchangedExcept2_refl _ _ _ _ _
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · u512_cs
    · rw [words_memStore_of_disjoint _ _ _ _ _ (by omega) (by bv_omega),
        u512_quot_words m' m4 hpre0 U hU8 hunc2 hb, hq]
    · have hV : words m (x.get 12#5) 4 ≠ 0 := by
        rw [hv]; intro h; exact hv0 (BitVec.eq_of_toNat_eq (by simpa using h))
      rw [if_neg hV, ← hrem, words, memWord_memStore_self, BitVec.add_assoc,
        words_memStore_of_disjoint _ _ _ _ _ (by bv_omega) (by bv_omega),
        show (64#64 + 8 : BitVec 64) = BitVec.ofNat 64 (8 * 9) from rfl,
        u512_res_zero m' m4 hpre0 U hunc2 hb 9 3 (by omega) (by omega)]
      simp

/-- The path of `udivrem<512, 256>()` for v < 2^64 and v ≠ 0 from 67: the call of
`udivrem_by1()` with max(m, 2) words of u. -/
theorem u512_by1 {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hb3 : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0) (hpre : udivrem_512_256.pre x m)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64)
    (hTr : (x.get 10#5).toNat + 96 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hTs : (x.get 2#5 - 240#64).toNat + 240 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 240#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hD : ∀ a ∈ bufWords T 256, a ∈ D)
    (hT0 : pcAt (pcAt base 409) 5 + ((hi0 ++ 0x000#12).signExtend 64 + lo0.signExtend 64) = T)
    (x' : Regs) (m' : Mem) (hF : U512Frame x m x' m') (h8 : x'.get 8#5 = x.get 11#5)
    (h10 : x'.get 10#5 = x.get 10#5) (mm : Nat) (hmm1 : 1 ≤ mm) (hmm8 : mm ≤ 8)
    (h9 : x'.get 9#5 = BitVec.ofNat 64 mm) (hum : words m (x.get 11#5) 8 < 2 ^ (64 * mm))
    (h18 : x'.get 18#5 = memWord m (x.get 12#5).toNat) (hv0 : memWord m (x.get 12#5).toNat ≠ 0)
    (hv : words m (x.get 12#5) 4 = (memWord m (x.get 12#5).toNat).toNat) :
    Reach (u512Bufs x D) P512 base (pcAt base 67) x' m' (x.get 1#5)
      (udivrem_512_256.post x m) := by
  replace hT0 := PLift.up hT0
  have hmn : (BitVec.ofNat 64 mm).toNat = mm := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [← regs_set_of_get' (by decide) h9]
  rv_exec_cut 70
  all_goals simp only [zopz0zI_u_eq, decide_eq_true_eq, decide_eq_false_iff_not] at *
  · rename_i hb
    have hlt : 2 < mm := by rw [BitVec.lt_def, hmn] at hb; simpa using hb
    refine u512_by1_call base x m hb3 hr hpre hw hTr hTs hhold hD hT0.down _ m'
      (U512Frame.regs hF ?_ ?_) ?_ ?_ mm (by omega) hmm8 ?_
      (u512_words_u m _ mm mm le_rfl hmm8 hum) ?_ hv0 hv
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    all_goals first | assumption | u512_cs
  · rename_i hb
    have hle : mm ≤ 2 := by rw [BitVec.lt_def, hmn] at hb; simp at hb; omega
    refine u512_by1_call base x m hb3 hr hpre hw hTr hTs hhold hD hT0.down _ m'
      (U512Frame.regs hF ?_ ?_) ?_ ?_ 2 le_rfl (by norm_num) ?_
      (u512_words_u m _ mm 2 hle (by norm_num) hum) ?_ hv0 hv
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    all_goals first | assumption | rfl | u512_cs

/-- The call of `udivrem_by2()` in `udivrem<512, 256>()` from 104 with U words of u. -/
theorem u512_by2_call {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hb3 : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0) (hpre : udivrem_512_256.pre x m)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64)
    (hTr : (x.get 10#5).toNat + 96 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hTs : (x.get 2#5 - 240#64).toNat + 240 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 240#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hD : ∀ a ∈ bufWords T 256, a ∈ D)
    (hT1 : pcAt (pcAt base 602) 54 + ((hi1 ++ 0x000#12).signExtend 64 + lo1.signExtend 64) = T)
    (x' : Regs) (m' : Mem) (hF : U512Frame x m x' m') (h8 : x'.get 8#5 = x.get 11#5)
    (h10 : x'.get 10#5 = x.get 10#5) (h12 : x'.get 12#5 = x.get 12#5) (U : Nat) (hU3 : 3 ≤ U)
    (hU8 : U ≤ 8) (h9 : x'.get 9#5 = BitVec.ofNat 64 U)
    (hu : words m (x.get 11#5) U = words m (x.get 11#5) 8)
    (hv1 : memWord m (x.get 12#5 + 8#64).toNat ≠ 0)
    (hv : words m (x.get 12#5) 4 = (memWord m (x.get 12#5).toNat).toNat +
      2 ^ 64 * (memWord m (x.get 12#5 + 8#64).toNat).toNat) :
    Reach (u512Bufs x D) P512 base (pcAt base 104) x' m' (x.get 1#5)
      (udivrem_512_256.post x m) := by
  -- `omega` and `subst_vars` do not see the address of the table.
  replace hT1 := PLift.up hT1
  have hpre0 := hpre
  simp only [udivrem_512_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr⟩ := hpre
  have hUn : (BitVec.ofNat 64 U).toNat = U := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hv0' := hF.memWord_v hpre0 0#64 (by decide)
  rw [BitVec.add_zero] at hv0'
  have hv1' := hF.memWord_v hpre0 8#64 (by decide)
  rw [← regs_set_of_get' (by decide) h10, ← regs_set_of_get' (by decide) h12]
  rv_exec_cut 1308
  rename_i w0 hw0 w1 hw1
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.reduceSignExtend]
    at hw0 hw1 ⊢
  simp only [Defn] at hw0 hw1
  rw [hv0'] at hw0
  rw [hv1'] at hw1
  subst hw0 hw1
  rw [show pcAt base 109 + 4096#64 + 700#64 = pcAt base 1308 by simp only [pcAt]; bv_omega,
    update_aligned (pcAt_aligned hb3 1308)]
  have hF1 := U512Frame.regs (x'' := (((((((((x'.set (12#5) (x.get 12#5)).set (10#5)
      (x.get 10#5)).set (18#5) (memWord m (x.get 12#5).toNat)).set (19#5)
      (memWord m (x.get 12#5 + 8#64).toNat)).set 12#5 96#64).set (20#5) (x.get 10#5)).set
      11#5 0#64).set (1#5) (pcAt base 109 + 4096#64)).set (1#5) (pcAt base 111)))
    hF (by simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]) (by u512_cs)
  refine u512_memset base x m hb3 hpre0 _ m' ?_ ?_ ?_ 111 ?_ ?_
  all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  intro x2 m2 hm2 hx10 hcs
  subst hm2
  have hF2 := (hF1.memFill hpre0).callee hcs
  have h22 : x2.get 2#5 = x.get 2#5 + 18446744073709551456#64 := hF2.1
  have h82 : x2.get 8#5 = x.get 11#5 := by
    rw [get_of_calleeSaved hcs (by decide)]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h8
  have h92 : x2.get 9#5 = BitVec.ofNat 64 U := by
    rw [get_of_calleeSaved hcs (by decide)]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h9
  have h182 : x2.get 18#5 = memWord m (x.get 12#5).toNat := by
    rw [get_of_calleeSaved hcs (by decide)]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  have h192 : x2.get 19#5 = memWord m (x.get 12#5 + 8#64).toNat := by
    rw [get_of_calleeSaved hcs (by decide)]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  have h202 : x2.get 20#5 = x.get 10#5 := by
    rw [get_of_calleeSaved hcs (by decide)]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  rw [← regs_set_of_get' (by decide) h22, ← regs_set_of_get' (by decide) h82,
    ← regs_set_of_get' (by decide) h92, ← regs_set_of_get' (by decide) h182,
    ← regs_set_of_get' (by decide) h192, ← regs_set_of_get' (by decide) h202]
  rv_exec_cut 602
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.reduceSignExtend]
  rw [show pcAt base 117 + 1940#64 = pcAt base 602 by simp only [pcAt]; bv_omega,
    update_aligned (pcAt_aligned hb3 602)]
  have hu2 := hF2.words_u hpre0 U hU8
  have hU1 : (BitVec.ofNat 64 U + 18446744073709551615#64).toNat = U - 1 := by bv_omega
  refine Reach.call_sub (r := 119) udivrem_512_256_progAt_udivrem_by2_in
    (by rw [udivrem_512_256_progAt_length]; decide)
    (udivrem_by2.reach hi1 lo1 (pcAt base 602) T _ _ hT1.down hw ?_ ?_ ?_ ?_) ?_ ?_ ?_
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    exact pcAt_aligned hb3 119
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    rw [show x.get 2#5 + 18446744073709551456#64 - 32#64 = x.get 2#5 - 240#64 + 48#64 by
      bv_omega]
    bv_omega
  · exact hF2.holdsData hw hTr hTs hhold
  · simp only [udivrem_by2.pre, Buf, Disjoint]
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    rw [hUn, hU1]
    rw [show x.get 2#5 + 18446744073709551456#64 - 32#64 = x.get 2#5 - 240#64 + 48#64 by
      bv_omega]
    have hv1n : 0 < (memWord m (x.get 12#5 + 8#64).toNat).toNat := by
      rcases Nat.eq_zero_or_pos (memWord m (x.get 12#5 + 8#64).toNat).toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hv1
      · exact h
    refine ⟨⟨hra, by omega⟩, ⟨hua, by omega⟩, by omega, ⟨by bv_omega, by bv_omega⟩, by bv_omega,
      by bv_omega, hU3, by omega, ?_⟩
    have := (memWord m (x.get 12#5).toNat).isLt
    nlinarith
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · intro a ha
    simp only [udivrem_by2.bufs] at ha
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at ha
    rw [hUn, hU1] at ha
    rw [show x.get 2#5 + 18446744073709551456#64 - 32#64 = x.get 2#5 - 240#64 +
      BitVec.ofNat 64 (8 * 6) by bv_omega] at ha
    simp only [List.mem_append] at ha ⊢
    rcases ha with ((h | h) | h) | h
    · exact Or.inl (Or.inl (Or.inl (Or.inl (mem_bufWords_of_le hU8 h))))
    · exact Or.inl (Or.inl (Or.inr (mem_bufWords_of_le (by omega) h)))
    · exact Or.inl (Or.inr (mem_bufWords_of_offset (by norm_num) h))
    · exact Or.inr (hD _ h)
  · intro x4 m4 hpost
    obtain ⟨hq, hrem, hunc, hsaved⟩ := hpost
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at hq hrem hunc
    simp only [hUn, hU1] at hq hrem hunc
    rw [hu2, hu, ← hv] at hq hrem
    have hb : (x.get 10#5).toNat + 96 ≤ (x.get 2#5 + 18446744073709551456#64 - 32#64).toNat ∨
        (x.get 2#5 + 18446744073709551456#64 - 32#64).toNat + 32 ≤ (x.get 10#5).toNat := by
      bv_omega
    have hF4 : U512Frame x m x4 m4 := by
      refine U512Frame.regs (x' := x2) (U512Frame.mem hF2 hpre0 ?_) ?_ ?_
      · intro k hka hkb
        exact hunc k (by omega) (by bv_omega)
      · rw [get_of_calleeSaved hsaved (by decide)]
        simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
        exact h22.symm
      · u512_cs' hsaved
    have h204 : x4.get 20#5 = x.get 10#5 := by
      rw [get_of_calleeSaved hsaved (by decide)]
      simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    rw [← regs_set_of_get' (by decide) h204]
    rv_exec_cut 327
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.reduceSignExtend] at *
    refine u512_epi base x m hr _ _ (U512Frame.regs (U512Frame.mem hF4 hpre0 ?_) ?_ ?_) ?_ ?_
    · simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
      exact unchangedExcept2_refl _ _ _ _ _
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · u512_cs
    · rw [words_memStore_of_disjoint _ _ _ _ _ (by omega) (by bv_omega),
        words_memStore_of_disjoint _ _ _ _ _ (by omega) (by bv_omega),
        u512_quot_words m' m4 hpre0 (U - 1) (by omega) hunc hb, hq]
    · have hV : words m (x.get 12#5) 4 ≠ 0 := by
        rw [hv]; intro h
        have : (memWord m (x.get 12#5 + 8#64).toNat).toNat = 0 := by omega
        exact hv1 (BitVec.eq_of_toNat_eq (by simpa using this))
      rw [if_neg hV, ← hrem, words, words]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [words_memStore_of_disjoint _ _ _ _ _ (by bv_omega) (by bv_omega),
        words_memStore_of_disjoint _ _ _ _ _ (by bv_omega) (by bv_omega),
        show (80#64 : BitVec 64) = BitVec.ofNat 64 (8 * 10) from rfl,
        u512_res_zero m' m4 hpre0 (U - 1) hunc hb 10 2 (by omega) (by omega),
        memWord_memStore_self, memWord_memStore_of_ne _ _ _ _ (by bv_omega), memWord_memStore_self]
      ring

/-- The path of `udivrem<512, 256>()` for 2^64 ≤ v < 2^128 from 101: the call of `udivrem_by2()`
with max(m, 3) words of u. -/
theorem u512_by2 {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hb3 : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0) (hpre : udivrem_512_256.pre x m)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64)
    (hTr : (x.get 10#5).toNat + 96 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hTs : (x.get 2#5 - 240#64).toNat + 240 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 240#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hD : ∀ a ∈ bufWords T 256, a ∈ D)
    (hT1 : pcAt (pcAt base 602) 54 + ((hi1 ++ 0x000#12).signExtend 64 + lo1.signExtend 64) = T)
    (x' : Regs) (m' : Mem) (hF : U512Frame x m x' m') (h8 : x'.get 8#5 = x.get 11#5)
    (h10 : x'.get 10#5 = x.get 10#5) (h12 : x'.get 12#5 = x.get 12#5) (mm : Nat) (hmm1 : 1 ≤ mm)
    (hmm8 : mm ≤ 8) (h9 : x'.get 9#5 = BitVec.ofNat 64 mm)
    (hum : words m (x.get 11#5) 8 < 2 ^ (64 * mm))
    (hv1 : memWord m (x.get 12#5 + 8#64).toNat ≠ 0)
    (hv : words m (x.get 12#5) 4 = (memWord m (x.get 12#5).toNat).toNat +
      2 ^ 64 * (memWord m (x.get 12#5 + 8#64).toNat).toNat) :
    Reach (u512Bufs x D) P512 base (pcAt base 101) x' m' (x.get 1#5)
      (udivrem_512_256.post x m) := by
  replace hT1 := PLift.up hT1
  have hmn : (BitVec.ofNat 64 mm).toNat = mm := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [← regs_set_of_get' (by decide) h9]
  rv_exec_cut 104
  all_goals simp only [zopz0zI_u_eq, decide_eq_true_eq, decide_eq_false_iff_not] at *
  · rename_i hb
    have hlt : 3 < mm := by rw [BitVec.lt_def, hmn] at hb; simpa using hb
    refine u512_by2_call base x m hb3 hr hpre hw hTr hTs hhold hD hT1.down _ m'
      (U512Frame.regs hF ?_ ?_) ?_ ?_ ?_ mm (by omega) hmm8 ?_
      (u512_words_u m _ mm mm le_rfl hmm8 hum) hv1 hv
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    all_goals first | assumption | u512_cs
  · rename_i hb
    have hle : mm ≤ 3 := by rw [BitVec.lt_def, hmn] at hb; simp at hb; omega
    refine u512_by2_call base x m hb3 hr hpre hw hTr hTs hhold hD hT1.down _ m'
      (U512Frame.regs hF ?_ ?_) ?_ ?_ ?_ 3 le_rfl (by norm_num) ?_
      (u512_words_u m _ mm 3 hle (by norm_num) hum) hv1 hv
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    all_goals first | assumption | rfl | u512_cs

end IntxRV.Api
