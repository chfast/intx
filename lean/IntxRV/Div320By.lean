import IntxRV.Div320
import IntxRV.Api.udivrem_by1_5
import IntxRV.Api.udivrem_by2_4
import IntxRV.Api.udivrem_by1
import IntxRV.Api.udivrem_by2

/-!
# The paths of `udivrem<320, 256>()` that call `udivrem_by1()` and `udivrem_by2()`

For v[3] = v[2] = 0 and u ≥ 2^192 the calls of `udivrem_by2()` of 4 quotient words (`u320_by24`)
and of `udivrem_by1()` of 5 words (`u320_by15`); for the smaller u the calls of the dynamic
`udivrem_by1()` with max(m, 2) words (`u320_by1`) and `udivrem_by2()` with max(m, 3) words
(`u320_by2`) of u. Each path zeroes the result with `memset()` first (`u320_memset`), so that the
words that the callee does not write are 0, and stores the remainder that the callee returns. See
`IntxRV/Api/udivrem_320_256.lean`.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {hi0 hi1 hi2 hi3 hi4 hi5 hi6 hi7 hi8 hi9 : BitVec 20}
  {lo0 lo1 lo2 lo3 lo4 lo5 lo6 lo7 lo8 lo9 : BitVec 12} {T : BitVec 64}

set_option hygiene false in
local notation "R320" => udivrem_by1_progAt hi0 lo0 ++ (udivrem_by1_5_progAt hi1 lo1 ++
  (udivrem_by2_progAt hi2 lo2 ++ (udivrem_by2_4_progAt hi3 lo3 ++
  (udivrem_top1_2_320_progAt hi4 lo4 ++ (udivrem_top1_3_320_progAt hi5 lo5 ++
  (udivrem_top2_3_320_progAt hi6 lo6 ++ (udivrem_top2_3_equal_320_progAt hi7 lo7 ++
  (udivrem_top2_4_320_progAt hi8 lo8 ++ (udivrem_knuth_320_progOwn ++
  (udivrem_knuth_normalized_progOwn hi9 lo9 ++ (submul_prog ++ memset_prog)))))))))))

set_option hygiene false in
local notation "P320" => udivrem_320_256_progOwn ++ R320

/-- The words of the result from the word `k` after `memset()` and a callee that writes its first
`U ≤ k` words. -/
theorem u320_res_zero {x : Regs} {m : Mem} (m' m4 : Mem) (hpre : udivrem_320_256.pre x m)
    (U : Nat) (hunc : UnchangedExcept (IntxRV.memFill m' (x.get 10#5).toNat 0#8 72) m4 (x.get 10#5)
      (8 * U)) (k j : Nat) (hk : U ≤ k) (hkj : k + j ≤ 9) :
    words m4 (x.get 10#5 + BitVec.ofNat 64 (8 * k)) j = 0 := by
  have hpre' := hpre
  simp only [udivrem_320_256.pre, Buf, Disjoint] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hra, hrn⟩, -⟩ := hpre'
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rfl
  have ha : (x.get 10#5 + BitVec.ofNat 64 (8 * k)).toNat = (x.get 10#5).toNat + 8 * k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [words_of_unchangedExcept2 (unchangedExcept2_of (x.get 10#5) 0 hunc) j _ (by omega)
    (by omega) (by omega)]
  exact u320_memFill_words m' hpre j k (by omega)

/-- The words of the result from the word `k` after `memset()` and a callee that writes its first
`U ≤ k` words and the `lb` bytes at `b` outside the result. -/
theorem u320_res_zero2 {x : Regs} {m : Mem} (m' m4 : Mem) (hpre : udivrem_320_256.pre x m)
    (U : Nat) {b : BitVec 64} {lb : Nat}
    (hunc : UnchangedExcept2 (IntxRV.memFill m' (x.get 10#5).toNat 0#8 72) m4 (x.get 10#5)
      (8 * U) b lb)
    (hb : (x.get 10#5).toNat + 72 ≤ b.toNat ∨ b.toNat + lb ≤ (x.get 10#5).toNat)
    (k j : Nat) (hk : U ≤ k) (hkj : k + j ≤ 9) :
    words m4 (x.get 10#5 + BitVec.ofNat 64 (8 * k)) j = 0 := by
  have hpre' := hpre
  simp only [udivrem_320_256.pre, Buf, Disjoint] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hra, hrn⟩, -⟩ := hpre'
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rfl
  have ha : (x.get 10#5 + BitVec.ofNat 64 (8 * k)).toNat = (x.get 10#5).toNat + 8 * k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [words_of_unchangedExcept2 hunc j _ (by omega) (by omega) (by omega)]
  exact u320_memFill_words m' hpre j k (by omega)

/-- The 5 words of the quotient after `memset()` and a callee that writes its first `U` words and
the `lb` bytes at `b` outside the result. -/
theorem u320_quot_words {x : Regs} {m : Mem} (m' m4 : Mem) (hpre : udivrem_320_256.pre x m)
    (U : Nat) (hU5 : U ≤ 5) {b : BitVec 64} {lb : Nat}
    (hunc : UnchangedExcept2 (IntxRV.memFill m' (x.get 10#5).toNat 0#8 72) m4 (x.get 10#5)
      (8 * U) b lb)
    (hb : (x.get 10#5).toNat + 72 ≤ b.toNat ∨ b.toNat + lb ≤ (x.get 10#5).toNat) :
    words m4 (x.get 10#5) 5 = words m4 (x.get 10#5) U := by
  have hs := words_split m4 U (5 - U) (x.get 10#5)
  rw [show U + (5 - U) = 5 by omega,
    u320_res_zero2 m' m4 hpre U hunc hb U (5 - U) le_rfl (by omega), Nat.mul_zero,
    Nat.add_zero] at hs
  exact hs

/-- The `U` words of u that hold its `mm` significant words. -/
theorem u320_words_u (m : Mem) (u : BitVec 64) (mm U : Nat) (hU : mm ≤ U) (hU5 : U ≤ 5)
    (hum : words m u 5 < 2 ^ (64 * mm)) : words m u U = words m u 5 := by
  have hs := words_split m U (5 - U) u
  rw [show U + (5 - U) = 5 by omega] at hs
  exact lo_of_lt hs (lt_of_lt_of_le hum (Nat.pow_le_pow_right (by norm_num) (by omega)))

/-- The path of `udivrem<320, 256>()` for v < 2^64, v ≠ 0 and u ≥ 2^192 from 79: `memset()` of the
result and the call of `udivrem_by1()` of 5 words. -/
theorem u320_by15 {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hb3 : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0) (hpre : udivrem_320_256.pre x m)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64)
    (hTr : (x.get 10#5).toNat + 72 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hTs : (x.get 2#5 - 336#64).toNat + 336 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 336#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hD : ∀ a ∈ bufWords T 256, a ∈ D)
    (hT1 : pcAt (pcAt base 375) 5 + ((hi1 ++ 0x000#12).signExtend 64 + lo1.signExtend 64) = T)
    (x' : Regs) (m' : Mem) (hF : U320Frame x m x' m') (h10 : x'.get 10#5 = x.get 10#5)
    (h11 : x'.get 11#5 = x.get 11#5) (h8 : x'.get 8#5 = memWord m (x.get 12#5).toNat)
    (hv0 : memWord m (x.get 12#5).toNat ≠ 0#64)
    (hv : words m (x.get 12#5) 4 = (memWord m (x.get 12#5).toNat).toNat) :
    Reach (u320Bufs x D) P320 base (pcAt base 79) x' m' (x.get 1#5)
      (udivrem_320_256.post x m) := by
  -- `omega` and `subst_vars` do not see the address of the table.
  replace hT1 := PLift.up hT1
  have hpre0 := hpre
  simp only [udivrem_320_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr⟩ := hpre
  rw [← regs_set_of_get' (by decide) h10, ← regs_set_of_get' (by decide) h11,
    ← regs_set_of_get' (by decide) h8]
  rv_exec_cut 2996
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  rw [show pcAt base 83 + 12288#64 + BitVec.signExtend 64 3460#12 = pcAt base 2996 by
      simp only [pcAt, BitVec.reduceSignExtend]; bv_omega,
    update_aligned (pcAt_aligned hb3 2996)]
  have hF1 := U320Frame.regs (x'' := ((((((((x'.set (8#5) (memWord m (x.get 12#5).toNat)).set
      (11#5) (x.get 11#5)).set (10#5) (x.get 10#5)).set (9#5) (x.get 11#5)).set 12#5 72#64).set
      (18#5) (x.get 10#5)).set 11#5 0#64).set (1#5) (pcAt base 83 + 12288#64)).set (1#5)
      (pcAt base 85)) hF (by simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte])
    (by u320_cs)
  refine u320_memset base x m hb3 hpre0 _ m' ?_ ?_ ?_ 85 ?_ ?_
  all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  intro x2 m2 hm2 hx10 hcs
  subst hm2
  have hF2 := (hF1.memFill hpre0).callee hcs
  have h82 : x2.get 8#5 = memWord m (x.get 12#5).toNat := by
    rw [get_of_calleeSaved hcs (by decide)]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  have h92 : x2.get 9#5 = x.get 11#5 := by
    rw [get_of_calleeSaved hcs (by decide)]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  have h182 : x2.get 18#5 = x.get 10#5 := by
    rw [get_of_calleeSaved hcs (by decide)]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  rw [← regs_set_of_get' (by decide) h82, ← regs_set_of_get' (by decide) h92,
    ← regs_set_of_get' (by decide) h182]
  rv_exec_cut 375
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  rw [show pcAt base 88 + BitVec.signExtend 64 1148#12 = pcAt base 375 by
      simp only [pcAt, BitVec.reduceSignExtend]; bv_omega,
    update_aligned (pcAt_aligned hb3 375)]
  have hu2 := hF2.words_u hpre0 5 le_rfl
  have hv0n : 0 < (memWord m (x.get 12#5).toNat).toNat := by
    rcases Nat.eq_zero_or_pos (memWord m (x.get 12#5).toNat).toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hv0
    · exact h
  refine Reach.call_sub (r := 90) (p320_eq ▸ udivrem_320_256_progAt_udivrem_by1_5_in) p320_length
    (udivrem_by1_5.reach hi1 lo1 (pcAt base 375) T _ _ hT1.down hw ?_ ?_ ?_) ?_ ?_ ?_
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    exact pcAt_aligned hb3 90
  · exact hF2.holdsData hw hTr hTs hhold
  · simp only [udivrem_by1_5.pre, Buf, Disjoint]
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    try simp (disch := decide) only [Regs.eq_get x2]
    try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    exact ⟨⟨hra, by omega⟩, ⟨hua, by omega⟩, by omega, trivial, trivial, hv0n⟩
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · intro a ha
    simp only [udivrem_by1_5.bufs] at ha
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at ha
    try simp (disch := decide) only [Regs.eq_get x2] at ha
    try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte] at ha
    simp only [List.mem_append] at ha ⊢
    rcases ha with (h | h) | h
    · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
    · exact Or.inl (Or.inl (Or.inr (mem_bufWords_of_le (by norm_num) h)))
    · exact Or.inr (hD _ h)
  · intro x4 m4 hpost
    obtain ⟨hq, hrem, hunc, hsaved⟩ := hpost
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at hq hrem hunc
    try simp (disch := decide) only [Regs.eq_get x2] at hq hrem hunc
    try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte] at hq hrem hunc
    rw [hu2, ← hv] at hq hrem
    have hF4 : U320Frame x m x4 m4 := by
      refine U320Frame.regs (x' := x2) (U320Frame.mem hF2 hpre0 ?_) ?_ ?_
      · exact unchangedExcept2_of _ _ (fun k hk => hunc k (by omega))
      · rw [get_of_calleeSaved hsaved (by decide)]
        simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      · intro r hr' hn
        rw [get_of_calleeSaved hsaved hr']
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl <;> simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte] at hn ⊢
    have h184 : x4.get 18#5 = x.get 10#5 := by
      rw [get_of_calleeSaved hsaved (by decide)]
      simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    rw [← regs_set_of_get' (by decide) h184]
    rv_exec_cut 142
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.reduceSignExtend] at *
    refine u320_epi base x m hr _ _ (U320Frame.regs (U320Frame.mem hF4 hpre0 ?_) ?_ ?_) ?_ ?_
    · simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
      exact unchangedExcept2_refl _ _ _ _ _
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · u320_cs
    · rw [words_memStore_of_disjoint _ _ _ _ _ (by omega) (by bv_omega), hq]
    · have hV : words m (x.get 12#5) 4 ≠ 0 := by
        rw [hv]; intro h; exact hv0 (BitVec.eq_of_toNat_eq (by simpa using h))
      rw [if_neg hV, ← hrem, words, memWord_memStore_self, BitVec.add_assoc,
        words_memStore_of_disjoint _ _ _ _ _ (by bv_omega) (by bv_omega),
        show (40#64 + 8 : BitVec 64) = BitVec.ofNat 64 (8 * 6) from rfl,
        u320_res_zero m' m4 hpre0 5 hunc 6 3 (by omega) (by omega)]
      simp

/-- The path of `udivrem<320, 256>()` for 2^64 ≤ v < 2^128 and u ≥ 2^192 from 57: `memset()` of the
result and the call of `udivrem_by2()` of 4 quotient words. -/
theorem u320_by24 {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hb3 : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0) (hpre : udivrem_320_256.pre x m)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64)
    (hTr : (x.get 10#5).toNat + 72 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hTs : (x.get 2#5 - 336#64).toNat + 336 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 336#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hD : ∀ a ∈ bufWords T 256, a ∈ D)
    (hT3 : pcAt (pcAt base 932) 50 + ((hi3 ++ 0x000#12).signExtend 64 + lo3.signExtend 64) = T)
    (x' : Regs) (m' : Mem) (hF : U320Frame x m x' m') (h10 : x'.get 10#5 = x.get 10#5)
    (h11 : x'.get 11#5 = x.get 11#5) (h13 : x'.get 13#5 = x.get 12#5)
    (h8 : x'.get 8#5 = memWord m (x.get 12#5 + 8#64).toNat)
    (hv1 : memWord m (x.get 12#5 + 8#64).toNat ≠ 0#64)
    (hv : words m (x.get 12#5) 4 = (memWord m (x.get 12#5).toNat).toNat +
      2 ^ 64 * (memWord m (x.get 12#5 + 8#64).toNat).toNat) :
    Reach (u320Bufs x D) P320 base (pcAt base 57) x' m' (x.get 1#5)
      (udivrem_320_256.post x m) := by
  -- `omega` and `subst_vars` do not see the address of the table.
  replace hT3 := PLift.up hT3
  have hpre0 := hpre
  simp only [udivrem_320_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr⟩ := hpre
  have hv0m : memWord m' (x.get 12#5).toNat = memWord m (x.get 12#5).toNat := by
    have := hF.memWord_v hpre0 0#64 (by decide)
    rwa [BitVec.add_zero] at this
  rw [← regs_set_of_get' (by decide) h10, ← regs_set_of_get' (by decide) h11,
    ← regs_set_of_get' (by decide) h13, ← regs_set_of_get' (by decide) h8]
  rv_exec_cut 2996
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  rw [show pcAt base 62 + 12288#64 + BitVec.signExtend 64 3544#12 = pcAt base 2996 by
      simp only [pcAt, BitVec.reduceSignExtend]; bv_omega,
    update_aligned (pcAt_aligned hb3 2996)]
  rename_i w0 hw0
  rw [hv0m] at hw0
  simp only [Defn] at hw0
  subst hw0
  have hF1 := U320Frame.regs (x'' := ((((((((((x'.set (8#5) (memWord m (x.get 12#5 + 8#64).toNat)).set
      (13#5) (x.get 12#5)).set (11#5) (x.get 11#5)).set (10#5) (x.get 10#5)).set (9#5)
      (memWord m (x.get 12#5).toNat)).set 12#5 72#64).set (18#5) (x.get 10#5)).set (19#5)
      (x.get 11#5)).set 11#5 0#64).set (1#5) (pcAt base 62 + 12288#64)).set (1#5) (pcAt base 64))
    hF (by simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]) (by u320_cs)
  refine u320_memset base x m hb3 hpre0 _ m' ?_ ?_ ?_ 64 ?_ ?_
  all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  intro x2 m2 hm2 hx10 hcs
  subst hm2
  have hF2 := (hF1.memFill hpre0).callee hcs
  have h82 : x2.get 8#5 = memWord m (x.get 12#5 + 8#64).toNat := by
    rw [get_of_calleeSaved hcs (by decide)]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  have h92 : x2.get 9#5 = memWord m (x.get 12#5).toNat := by
    rw [get_of_calleeSaved hcs (by decide)]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  have h182 : x2.get 18#5 = x.get 10#5 := by
    rw [get_of_calleeSaved hcs (by decide)]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  have h192 : x2.get 19#5 = x.get 11#5 := by
    rw [get_of_calleeSaved hcs (by decide)]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  rw [← regs_set_of_get' (by decide) h82, ← regs_set_of_get' (by decide) h92,
    ← regs_set_of_get' (by decide) h182, ← regs_set_of_get' (by decide) h192]
  rv_exec_cut 932
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  rw [show pcAt base 68 + 4096#64 + BitVec.signExtend 64 3456#12 = pcAt base 932 by
      simp only [pcAt, BitVec.reduceSignExtend]; bv_omega,
    update_aligned (pcAt_aligned hb3 932)]
  have hu2 := hF2.words_u hpre0 5 le_rfl
  have hv1n : 0 < (memWord m (x.get 12#5 + 8#64).toNat).toNat := by
    rcases Nat.eq_zero_or_pos (memWord m (x.get 12#5 + 8#64).toNat).toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hv1
    · exact h
  refine Reach.call_sub (r := 70) (p320_eq ▸ udivrem_320_256_progAt_udivrem_by2_4_in) p320_length
    (udivrem_by2_4.reach hi3 lo3 (pcAt base 932) T _ _ hT3.down hw ?_ ?_ ?_) ?_ ?_ ?_
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    exact pcAt_aligned hb3 70
  · exact hF2.holdsData hw hTr hTs hhold
  · simp only [udivrem_by2_4.pre, Buf, Disjoint]
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    try simp (disch := decide) only [Regs.eq_get x2]
    try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    refine ⟨⟨hra, by omega⟩, ⟨hua, by omega⟩, by omega, trivial, trivial, ?_⟩
    have := (memWord m (x.get 12#5).toNat).isLt
    omega
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · intro a ha
    simp only [udivrem_by2_4.bufs] at ha
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at ha
    try simp (disch := decide) only [Regs.eq_get x2] at ha
    try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte] at ha
    simp only [List.mem_append] at ha ⊢
    rcases ha with (h | h) | h
    · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
    · exact Or.inl (Or.inl (Or.inr (mem_bufWords_of_le (by norm_num) h)))
    · exact Or.inr (hD _ h)
  · intro x4 m4 hpost
    obtain ⟨hq, hrem, hunc, hsaved⟩ := hpost
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at hq hrem hunc
    try simp (disch := decide) only [Regs.eq_get x2] at hq hrem hunc
    try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte] at hq hrem hunc
    rw [hu2, ← hv] at hq hrem
    have hF4 : U320Frame x m x4 m4 := by
      refine U320Frame.regs (x' := x2) (U320Frame.mem hF2 hpre0 ?_) ?_ ?_
      · exact unchangedExcept2_of _ _ (fun k hk => hunc k (by omega))
      · rw [get_of_calleeSaved hsaved (by decide)]
        simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      · intro r hr' hn
        rw [get_of_calleeSaved hsaved hr']
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl <;> simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte] at hn ⊢
    have h184 : x4.get 18#5 = x.get 10#5 := by
      rw [get_of_calleeSaved hsaved (by decide)]
      simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    rw [← regs_set_of_get' (by decide) h184]
    rv_exec_cut 142
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.reduceSignExtend] at *
    refine u320_epi base x m hr _ _ (U320Frame.regs (U320Frame.mem hF4 hpre0 ?_) ?_ ?_) ?_ ?_
    · simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
      exact unchangedExcept2_refl _ _ _ _ _
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · u320_cs
    · have hs := words_split m4 4 1 (x.get 10#5)
      rw [show 4 + 1 = 5 from rfl, u320_res_zero m' m4 hpre0 4 hunc 4 1 le_rfl (by omega),
        Nat.mul_zero, Nat.add_zero] at hs
      rw [words_memStore_of_disjoint _ _ _ _ _ (by omega) (by bv_omega),
        words_memStore_of_disjoint _ _ _ _ _ (by omega) (by bv_omega), hs, hq]
    · have hV : words m (x.get 12#5) 4 ≠ 0 := by omega
      rw [if_neg hV, ← hrem]
      have hz := u320_res_zero m' m4 hpre0 4 hunc 7 2 (by omega) (by omega)
      simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul,
        Nat.mul_zero, Nat.add_zero] at hz
      simp (disch := first | bv_omega | fail) only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
        BitVec.reduceAdd, memWord_memStore_self, memWord_memStore_of_ne, Nat.mul_zero, Nat.add_zero]
      omega

/-- The call of `udivrem_by1()` in `udivrem<320, 256>()` from 115 with U words of u. -/
theorem u320_by1_call {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hb3 : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0) (hpre : udivrem_320_256.pre x m)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64)
    (hTr : (x.get 10#5).toNat + 72 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hTs : (x.get 2#5 - 336#64).toNat + 336 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 336#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hD : ∀ a ∈ bufWords T 256, a ∈ D)
    (hT0 : pcAt (pcAt base 182) 5 + ((hi0 ++ 0x000#12).signExtend 64 + lo0.signExtend 64) = T)
    (x' : Regs) (m' : Mem) (hF : U320Frame x m x' m') (h18 : x'.get 18#5 = x.get 11#5)
    (h10 : x'.get 10#5 = x.get 10#5) (U : Nat) (hU2 : 2 ≤ U) (hU5 : U ≤ 5)
    (h8 : x'.get 8#5 = BitVec.ofNat 64 U) (hu : words m (x.get 11#5) U = words m (x.get 11#5) 5)
    (h9 : x'.get 9#5 = memWord m (x.get 12#5).toNat) (hv0 : memWord m (x.get 12#5).toNat ≠ 0)
    (hv : words m (x.get 12#5) 4 = (memWord m (x.get 12#5).toNat).toNat) :
    Reach (u320Bufs x D) P320 base (pcAt base 115) x' m' (x.get 1#5)
      (udivrem_320_256.post x m) := by
  -- `omega` and `subst_vars` do not see the address of the table.
  replace hT0 := PLift.up hT0
  have hpre0 := hpre
  simp only [udivrem_320_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr⟩ := hpre
  have hUn : (BitVec.ofNat 64 U).toNat = U := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [← regs_set_of_get' (by decide) h10]
  rv_exec_cut 2996
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  rw [show pcAt base 118 + 12288#64 + BitVec.signExtend 64 3320#12 = pcAt base 2996 by
      simp only [pcAt, BitVec.reduceSignExtend]; bv_omega,
    update_aligned (pcAt_aligned hb3 2996)]
  have hF1 := U320Frame.regs (x'' := (((((x'.set (10#5) (x.get 10#5)).set 12#5 72#64).set (19#5)
      (x.get 10#5)).set 11#5 0#64).set (1#5) (pcAt base 118 + 12288#64)).set (1#5) (pcAt base 120))
    hF (by simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]) (by u320_cs)
  refine u320_memset base x m hb3 hpre0 _ m' ?_ ?_ ?_ 120 ?_ ?_
  all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  intro x2 m2 hm2 hx10 hcs
  subst hm2
  have hF2 := (hF1.memFill hpre0).callee hcs
  have h82 : x2.get 8#5 = BitVec.ofNat 64 U := by
    rw [get_of_calleeSaved hcs (by decide)]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h8
  have h92 : x2.get 9#5 = memWord m (x.get 12#5).toNat := by
    rw [get_of_calleeSaved hcs (by decide)]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h9
  have h182 : x2.get 18#5 = x.get 11#5 := by
    rw [get_of_calleeSaved hcs (by decide)]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h18
  have h192 : x2.get 19#5 = x.get 10#5 := by
    rw [get_of_calleeSaved hcs (by decide)]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  rw [← regs_set_of_get' (by decide) h82, ← regs_set_of_get' (by decide) h92,
    ← regs_set_of_get' (by decide) h182, ← regs_set_of_get' (by decide) h192]
  rv_exec_cut 182
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  rw [show pcAt base 125 + BitVec.signExtend 64 228#12 = pcAt base 182 by
      simp only [pcAt, BitVec.reduceSignExtend]; bv_omega,
    update_aligned (pcAt_aligned hb3 182)]
  have hu2 := hF2.words_u hpre0 U hU5
  refine Reach.call_sub (r := 127) (p320_eq ▸ udivrem_320_256_progAt_udivrem_by1_in) p320_length
    (udivrem_by1.reach hi0 lo0 (pcAt base 182) T _ _ hT0.down hw ?_ ?_ ?_) ?_ ?_ ?_
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    exact pcAt_aligned hb3 127
  · exact hF2.holdsData hw hTr hTs hhold
  · simp only [udivrem_by1.pre, Buf, Disjoint]
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    try simp (disch := decide) only [Regs.eq_get x2]
    try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
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
    try simp (disch := decide) only [Regs.eq_get x2] at ha
    try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte] at ha
    rw [hUn] at ha
    simp only [List.mem_append] at ha ⊢
    rcases ha with (h | h) | h
    · exact Or.inl (Or.inl (Or.inl (Or.inl (mem_bufWords_of_le hU5 h))))
    · exact Or.inl (Or.inl (Or.inr (mem_bufWords_of_le (by omega) h)))
    · exact Or.inr (hD _ h)
  · intro x4 m4 hpost
    obtain ⟨hq, hrem, hunc, hsaved⟩ := hpost
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at hq hrem hunc
    try simp (disch := decide) only [Regs.eq_get x2] at hq hrem hunc
    try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte] at hq hrem hunc
    rw [hUn, hu2, hu, ← hv] at hq hrem
    rw [hUn] at hunc
    have hunc2 := unchangedExcept2_of (x.get 2#5 - 336#64) 336 hunc
    have hb : (x.get 10#5).toNat + 72 ≤ (x.get 2#5 - 336#64).toNat ∨
        (x.get 2#5 - 336#64).toNat + 336 ≤ (x.get 10#5).toNat := by omega
    have hF4 : U320Frame x m x4 m4 := by
      refine U320Frame.regs (x' := x2) (U320Frame.mem hF2 hpre0 ?_) ?_ ?_
      · exact unchangedExcept2_of _ _ (fun k hk => hunc k (by omega))
      · rw [get_of_calleeSaved hsaved (by decide)]
        simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      · intro r hr' hn
        rw [get_of_calleeSaved hsaved hr']
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl <;> simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte] at hn ⊢
    have h194 : x4.get 19#5 = x.get 10#5 := by
      rw [get_of_calleeSaved hsaved (by decide)]
      simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    rw [← regs_set_of_get' (by decide) h194]
    rv_exec_cut 142
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.reduceSignExtend] at *
    refine u320_epi base x m hr _ _ (U320Frame.regs (U320Frame.mem hF4 hpre0 ?_) ?_ ?_) ?_ ?_
    · simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
      exact unchangedExcept2_refl _ _ _ _ _
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · u320_cs
    · rw [words_memStore_of_disjoint _ _ _ _ _ (by omega) (by bv_omega),
        u320_quot_words m' m4 hpre0 U hU5 hunc2 hb, hq]
    · have hV : words m (x.get 12#5) 4 ≠ 0 := by
        rw [hv]; intro h; exact hv0 (BitVec.eq_of_toNat_eq (by simpa using h))
      rw [if_neg hV, ← hrem, words, memWord_memStore_self, BitVec.add_assoc,
        words_memStore_of_disjoint _ _ _ _ _ (by bv_omega) (by bv_omega),
        show (40#64 + 8 : BitVec 64) = BitVec.ofNat 64 (8 * 6) from rfl,
        u320_res_zero2 m' m4 hpre0 U hunc2 hb 6 3 (by omega) (by omega)]
      simp

/-- The path of `udivrem<320, 256>()` for v < 2^64 and v ≠ 0 from 111: the call of `udivrem_by1()`
with max(m, 2) words of u. -/
theorem u320_by1 {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hb3 : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0) (hpre : udivrem_320_256.pre x m)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64)
    (hTr : (x.get 10#5).toNat + 72 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hTs : (x.get 2#5 - 336#64).toNat + 336 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 336#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hD : ∀ a ∈ bufWords T 256, a ∈ D)
    (hT0 : pcAt (pcAt base 182) 5 + ((hi0 ++ 0x000#12).signExtend 64 + lo0.signExtend 64) = T)
    (x' : Regs) (m' : Mem) (hF : U320Frame x m x' m') (h11 : x'.get 11#5 = x.get 11#5)
    (h10 : x'.get 10#5 = x.get 10#5) (mm : Nat) (hmm1 : 1 ≤ mm) (hmm5 : mm ≤ 5)
    (h8 : x'.get 8#5 = BitVec.ofNat 64 mm) (hum : words m (x.get 11#5) 5 < 2 ^ (64 * mm))
    (h9 : x'.get 9#5 = memWord m (x.get 12#5).toNat) (hv0 : memWord m (x.get 12#5).toNat ≠ 0)
    (hv : words m (x.get 12#5) 4 = (memWord m (x.get 12#5).toNat).toNat) :
    Reach (u320Bufs x D) P320 base (pcAt base 111) x' m' (x.get 1#5)
      (udivrem_320_256.post x m) := by
  replace hT0 := PLift.up hT0
  have hmn : (BitVec.ofNat 64 mm).toNat = mm := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [← regs_set_of_get' (by decide) h8, ← regs_set_of_get' (by decide) h11]
  rv_exec_cut 115
  all_goals simp only [zopz0zI_u_eq, decide_eq_true_eq, decide_eq_false_iff_not] at *
  · rename_i hb
    have hlt : 2 < mm := by rw [BitVec.lt_def, hmn] at hb; simpa using hb
    refine u320_by1_call base x m hb3 hr hpre hw hTr hTs hhold hD hT0.down _ m'
      (U320Frame.regs hF ?_ ?_) ?_ ?_ mm (by omega) hmm5 ?_
      (u320_words_u m _ mm mm le_rfl hmm5 hum) ?_ hv0 hv
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    all_goals first | assumption | u320_cs
  · rename_i hb
    have hle : mm ≤ 2 := by rw [BitVec.lt_def, hmn] at hb; simp at hb; omega
    refine u320_by1_call base x m hb3 hr hpre hw hTr hTs hhold hD hT0.down _ m'
      (U320Frame.regs hF ?_ ?_) ?_ ?_ 2 le_rfl (by norm_num) ?_
      (u320_words_u m _ mm 2 hle (by norm_num) hum) ?_ hv0 hv
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    all_goals first | assumption | rfl | u320_cs

/-- The call of `udivrem_by2()` in `udivrem<320, 256>()` from 154 with U words of u. -/
theorem u320_by2_call {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hb3 : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0) (hpre : udivrem_320_256.pre x m)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64)
    (hTr : (x.get 10#5).toNat + 72 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hTs : (x.get 2#5 - 336#64).toNat + 336 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 336#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hD : ∀ a ∈ bufWords T 256, a ∈ D)
    (hT2 : pcAt (pcAt base 618) 54 + ((hi2 ++ 0x000#12).signExtend 64 + lo2.signExtend 64) = T)
    (x' : Regs) (m' : Mem) (hF : U320Frame x m x' m') (h9 : x'.get 9#5 = x.get 11#5)
    (h10 : x'.get 10#5 = x.get 10#5) (h13 : x'.get 13#5 = x.get 12#5) (U : Nat) (hU3 : 3 ≤ U)
    (hU5 : U ≤ 5) (h8 : x'.get 8#5 = BitVec.ofNat 64 U)
    (hu : words m (x.get 11#5) U = words m (x.get 11#5) 5)
    (hv1 : memWord m (x.get 12#5 + 8#64).toNat ≠ 0)
    (hv : words m (x.get 12#5) 4 = (memWord m (x.get 12#5).toNat).toNat +
      2 ^ 64 * (memWord m (x.get 12#5 + 8#64).toNat).toNat) :
    Reach (u320Bufs x D) P320 base (pcAt base 154) x' m' (x.get 1#5)
      (udivrem_320_256.post x m) := by
  -- `omega` and `subst_vars` do not see the address of the table.
  replace hT2 := PLift.up hT2
  have hpre0 := hpre
  simp only [udivrem_320_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr⟩ := hpre
  have hUn : (BitVec.ofNat 64 U).toNat = U := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hv0' := hF.memWord_v hpre0 0#64 (by decide)
  rw [BitVec.add_zero] at hv0'
  have hv1' := hF.memWord_v hpre0 8#64 (by decide)
  rw [← regs_set_of_get' (by decide) h10, ← regs_set_of_get' (by decide) h13]
  rv_exec_cut 2996
  rename_i w0 hw0 w1 hw1
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.reduceSignExtend]
    at hw0 hw1 ⊢
  simp only [Defn] at hw0 hw1
  rw [hv0'] at hw0
  rw [hv1'] at hw1
  subst hw0 hw1
  rw [show pcAt base 159 + 12288#64 + 18446744073709550676#64 = pcAt base 2996 by
      simp only [pcAt]; bv_omega,
    update_aligned (pcAt_aligned hb3 2996)]
  have hF1 := U320Frame.regs (x'' := (((((((((x'.set (13#5) (x.get 12#5)).set (10#5)
      (x.get 10#5)).set (18#5) (memWord m (x.get 12#5).toNat)).set (19#5)
      (memWord m (x.get 12#5 + 8#64).toNat)).set 12#5 72#64).set (20#5) (x.get 10#5)).set
      11#5 0#64).set (1#5) (pcAt base 159 + 12288#64)).set (1#5) (pcAt base 161)))
    hF (by simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]) (by u320_cs)
  refine u320_memset base x m hb3 hpre0 _ m' ?_ ?_ ?_ 161 ?_ ?_
  all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  intro x2 m2 hm2 hx10 hcs
  subst hm2
  have hF2 := (hF1.memFill hpre0).callee hcs
  have h22 : x2.get 2#5 = x.get 2#5 + 18446744073709551568#64 := hF2.1
  have h82 : x2.get 8#5 = BitVec.ofNat 64 U := by
    rw [get_of_calleeSaved hcs (by decide)]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h8
  have h92 : x2.get 9#5 = x.get 11#5 := by
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
  rv_exec_cut 618
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.reduceSignExtend]
  rw [show pcAt base 167 + 1804#64 = pcAt base 618 by simp only [pcAt]; bv_omega,
    update_aligned (pcAt_aligned hb3 618)]
  have hu2 := hF2.words_u hpre0 U hU5
  have hU1 : (BitVec.ofNat 64 U + 18446744073709551615#64).toNat = U - 1 := by bv_omega
  refine Reach.call_sub (r := 169) (p320_eq ▸ udivrem_320_256_progAt_udivrem_by2_in) p320_length
    (udivrem_by2.reach hi2 lo2 (pcAt base 618) T _ _ hT2.down hw ?_ ?_ ?_ ?_) ?_ ?_ ?_
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    exact pcAt_aligned hb3 169
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    rw [show x.get 2#5 + 18446744073709551568#64 - 32#64 = x.get 2#5 - 336#64 + 256#64 by
      bv_omega]
    bv_omega
  · exact hF2.holdsData hw hTr hTs hhold
  · simp only [udivrem_by2.pre, Buf, Disjoint]
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    rw [hUn, hU1]
    rw [show x.get 2#5 + 18446744073709551568#64 - 32#64 = x.get 2#5 - 336#64 + 256#64 by
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
    rw [show x.get 2#5 + 18446744073709551568#64 - 32#64 = x.get 2#5 - 336#64 +
      BitVec.ofNat 64 (8 * 32) by bv_omega] at ha
    simp only [List.mem_append] at ha ⊢
    rcases ha with ((h | h) | h) | h
    · exact Or.inl (Or.inl (Or.inl (Or.inl (mem_bufWords_of_le hU5 h))))
    · exact Or.inl (Or.inl (Or.inr (mem_bufWords_of_le (by omega) h)))
    · exact Or.inl (Or.inr (mem_bufWords_of_offset (by norm_num) h))
    · exact Or.inr (hD _ h)
  · intro x4 m4 hpost
    obtain ⟨hq, hrem, hunc, hsaved⟩ := hpost
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at hq hrem hunc
    simp only [hUn, hU1] at hq hrem hunc
    rw [hu2, hu, ← hv] at hq hrem
    have hb : (x.get 10#5).toNat + 72 ≤ (x.get 2#5 + 18446744073709551568#64 - 32#64).toNat ∨
        (x.get 2#5 + 18446744073709551568#64 - 32#64).toNat + 32 ≤ (x.get 10#5).toNat := by
      bv_omega
    have hF4 : U320Frame x m x4 m4 := by
      refine U320Frame.regs (x' := x2) (U320Frame.mem hF2 hpre0 ?_) ?_ ?_
      · intro k hka hkb
        exact hunc k (by omega) (by bv_omega)
      · rw [get_of_calleeSaved hsaved (by decide)]
        simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
        exact h22.symm
      · intro r hr' hn
        rw [get_of_calleeSaved hsaved hr']
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl <;> simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte] at hn ⊢
    have h204 : x4.get 20#5 = x.get 10#5 := by
      rw [get_of_calleeSaved hsaved (by decide)]
      simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    rw [← regs_set_of_get' (by decide) h204]
    rv_exec_cut 142
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.reduceSignExtend] at *
    refine u320_epi base x m hr _ _ (U320Frame.regs (U320Frame.mem hF4 hpre0 ?_) ?_ ?_) ?_ ?_
    · simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
      exact unchangedExcept2_refl _ _ _ _ _
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · u320_cs
    · rw [words_memStore_of_disjoint _ _ _ _ _ (by omega) (by bv_omega),
        words_memStore_of_disjoint _ _ _ _ _ (by omega) (by bv_omega),
        u320_quot_words m' m4 hpre0 (U - 1) (by omega) hunc hb, hq]
    · have hV : words m (x.get 12#5) 4 ≠ 0 := by
        rw [hv]; intro h
        have : (memWord m (x.get 12#5 + 8#64).toNat).toNat = 0 := by omega
        exact hv1 (BitVec.eq_of_toNat_eq (by simpa using this))
      rw [if_neg hV, ← hrem, words, words]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [words_memStore_of_disjoint _ _ _ _ _ (by bv_omega) (by bv_omega),
        words_memStore_of_disjoint _ _ _ _ _ (by bv_omega) (by bv_omega),
        show (56#64 : BitVec 64) = BitVec.ofNat 64 (8 * 7) from rfl,
        u320_res_zero2 m' m4 hpre0 (U - 1) hunc hb 7 2 (by omega) (by omega),
        memWord_memStore_self, memWord_memStore_of_ne _ _ _ _ (by bv_omega), memWord_memStore_self]
      ring

/-- The path of `udivrem<320, 256>()` for 2^64 ≤ v < 2^128 from 150: the call of `udivrem_by2()`
with max(m, 3) words of u. -/
theorem u320_by2 {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hb3 : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0) (hpre : udivrem_320_256.pre x m)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64)
    (hTr : (x.get 10#5).toNat + 72 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hTs : (x.get 2#5 - 336#64).toNat + 336 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 336#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hD : ∀ a ∈ bufWords T 256, a ∈ D)
    (hT2 : pcAt (pcAt base 618) 54 + ((hi2 ++ 0x000#12).signExtend 64 + lo2.signExtend 64) = T)
    (x' : Regs) (m' : Mem) (hF : U320Frame x m x' m') (h11 : x'.get 11#5 = x.get 11#5)
    (h10 : x'.get 10#5 = x.get 10#5) (h13 : x'.get 13#5 = x.get 12#5) (mm : Nat) (hmm1 : 1 ≤ mm)
    (hmm5 : mm ≤ 5) (h8 : x'.get 8#5 = BitVec.ofNat 64 mm)
    (hum : words m (x.get 11#5) 5 < 2 ^ (64 * mm))
    (hv1 : memWord m (x.get 12#5 + 8#64).toNat ≠ 0)
    (hv : words m (x.get 12#5) 4 = (memWord m (x.get 12#5).toNat).toNat +
      2 ^ 64 * (memWord m (x.get 12#5 + 8#64).toNat).toNat) :
    Reach (u320Bufs x D) P320 base (pcAt base 150) x' m' (x.get 1#5)
      (udivrem_320_256.post x m) := by
  replace hT2 := PLift.up hT2
  have hmn : (BitVec.ofNat 64 mm).toNat = mm := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [← regs_set_of_get' (by decide) h8, ← regs_set_of_get' (by decide) h11]
  rv_exec_cut 154
  all_goals simp only [zopz0zI_u_eq, decide_eq_true_eq, decide_eq_false_iff_not] at *
  · rename_i hb
    have hlt : 3 < mm := by rw [BitVec.lt_def, hmn] at hb; simpa using hb
    refine u320_by2_call base x m hb3 hr hpre hw hTr hTs hhold hD hT2.down _ m'
      (U320Frame.regs hF ?_ ?_) ?_ ?_ ?_ mm (by omega) hmm5 ?_
      (u320_words_u m _ mm mm le_rfl hmm5 hum) hv1 hv
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    all_goals first | assumption | u320_cs
  · rename_i hb
    have hle : mm ≤ 3 := by rw [BitVec.lt_def, hmn] at hb; simp at hb; omega
    refine u320_by2_call base x m hb3 hr hpre hw hTr hTs hhold hD hT2.down _ m'
      (U320Frame.regs hF ?_ ?_) ?_ ?_ ?_ 3 le_rfl (by norm_num) ?_
      (u320_words_u m _ mm 3 hle (by norm_num) hum) hv1 hv
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    all_goals first | assumption | rfl | u320_cs

end IntxRV.Api
