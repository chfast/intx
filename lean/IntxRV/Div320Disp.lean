import IntxRV.Div320By
import IntxRV.Div320K

/-!
# The dispatch of `udivrem<320, 256>()`

From 7, after the prologue, the dispatch on the top words of u and v (`u320_main`): the calls of
`udivrem_top1()` and `udivrem_top2()` (`IntxRV/Div320Top.lean`), of `udivrem_by2()` of 4 quotient
words and `udivrem_by1()` of 5 words (`IntxRV/Div320By.lean`), and v = 0 (`u320_vzero`). Otherwise
the count of the significant words m of u from 52 (`u320_scan`) for u[4] = 0, and the dispatch at 95
on the counts n of v and m of u (`u320_dispatch`): u < v (`u320_ult`) if the words of u to divide,
m and the word with the bits shifted out of the top, are at most n (`ult_of_count`), and otherwise
v = 0, the division by 1 word (`u320_by1`), 2 words (`u320_by2`) or 3 words (`u320_knuth`). See
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

/-- The top word `a` of the `mm` significant words of u bounds u. -/
theorem words5_top_bound (m : Mem) (u : BitVec 64) (mm : Nat) (h1 : 1 ≤ mm) (h5 : mm ≤ 5)
    (hum : words m u 5 < 2 ^ (64 * mm)) :
    words m u 5 < ((memWord m (u + BitVec.ofNat 64 (8 * (mm - 1))).toNat).toNat + 1) *
      2 ^ (64 * (mm - 1)) := by
  have hs := words_split m (mm - 1) (5 - (mm - 1)) u
  rw [show mm - 1 + (5 - (mm - 1)) = 5 by omega] at hs
  obtain ⟨k, hk⟩ : ∃ k, 5 - (mm - 1) = k + 1 := ⟨4 - (mm - 1), by omega⟩
  have hW : words m (u + BitVec.ofNat 64 (8 * (mm - 1))) (k + 1) =
      (memWord m (u + BitVec.ofNat 64 (8 * (mm - 1))).toNat).toNat +
        2 ^ 64 * words m (u + BitVec.ofNat 64 (8 * (mm - 1)) + 8) k := rfl
  rw [hk, hW] at hs
  have hlo := words_lt m (mm - 1) u
  have hP : 2 ^ (64 * mm) = 2 ^ (64 * (mm - 1)) * 2 ^ 64 := by
    rw [← pow_add]; congr 1; omega
  generalize words m (u + BitVec.ofNat 64 (8 * (mm - 1)) + 8) k = R at hs
  generalize (memWord m (u + BitVec.ofNat 64 (8 * (mm - 1))).toNat).toNat = a at hs ⊢
  generalize 2 ^ (64 * (mm - 1)) = P at hs hlo hP ⊢
  rcases Nat.eq_zero_or_pos R with rfl | hR
  · rw [hs]; nlinarith
  · have : P * 2 ^ 64 ≤ P * (a + 2 ^ 64 * R) := Nat.mul_le_mul_left _ (by nlinarith)
    omega

/-- The top word `a` of the `mm` words of u times `2^(64 (mm - 1))` is at most u. -/
theorem words5_ge_top (m : Mem) (u : BitVec 64) (mm : Nat) (h1 : 1 ≤ mm) (h5 : mm ≤ 5) :
    (memWord m (u + BitVec.ofNat 64 (8 * (mm - 1))).toNat).toNat * 2 ^ (64 * (mm - 1)) ≤
      words m u 5 := by
  have hs := words_split m (mm - 1) (5 - (mm - 1)) u
  rw [show mm - 1 + (5 - (mm - 1)) = 5 by omega] at hs
  obtain ⟨k, hk⟩ : ∃ k, 5 - (mm - 1) = k + 1 := ⟨4 - (mm - 1), by omega⟩
  rw [hk] at hs
  have hW : words m (u + BitVec.ofNat 64 (8 * (mm - 1))) (k + 1) =
      (memWord m (u + BitVec.ofNat 64 (8 * (mm - 1))).toNat).toNat +
        2 ^ 64 * words m (u + BitVec.ofNat 64 (8 * (mm - 1)) + 8) k := rfl
  rw [hs, hW]
  generalize (memWord m (u + BitVec.ofNat 64 (8 * (mm - 1))).toNat).toNat = b
  generalize 2 ^ (64 * (mm - 1)) = P
  calc b * P = P * b := Nat.mul_comm _ _
    _ ≤ P * (b + 2 ^ 64 * words m (u + BitVec.ofNat 64 (8 * (mm - 1)) + 8) k) :=
      Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
    _ ≤ _ := Nat.le_add_left _ _

/-- The top digits of u are not less than those of v of 3 words when the count of the words of u
to divide is more than 3. -/
theorem u320_knuth_top {U V a b mm : Nat} (hmm : mm ≤ 5) (hlo : a * 2 ^ (64 * (mm - 1)) ≤ U)
    (ha1 : 1 ≤ a) (hVb : b * 2 ^ 128 ≤ V) (hVb2 : V < (b + 1) * 2 ^ 128) (hb : b < 2 ^ 64)
    (hl : 3 < mm + if b ≤ a then 1 else 0) : V / 2 ^ (64 * 2) ≤ U / 2 ^ (64 * 2) := by
  have hVq : V / 2 ^ 128 = b := Nat.div_eq_of_lt_le hVb hVb2
  rw [show 64 * 2 = 128 from rfl, hVq]
  by_cases h4 : 4 ≤ mm
  · have hP : 2 ^ 192 ≤ 2 ^ (64 * (mm - 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h1 : 2 ^ 192 ≤ U := le_trans hP (le_trans (Nat.le_mul_of_pos_left _ ha1) hlo)
    have h2 : 2 ^ 192 / 2 ^ 128 ≤ U / 2 ^ 128 := Nat.div_le_div_right h1
    have e : (2 : Nat) ^ 192 / 2 ^ 128 = 2 ^ 64 := by norm_num
    omega
  · have h3 : mm = 3 := by split_ifs at hl <;> omega
    have hba : b ≤ a := by
      split_ifs at hl with h
      · exact h
      · omega
    subst h3
    have h1 : a * 2 ^ 128 ≤ U := by simpa using hlo
    have h2 : a ≤ U / 2 ^ 128 := (Nat.le_div_iff_mul_le (by positivity)).mpr h1
    omega

/-- The dispatch of `udivrem<320, 256>()` at 95 on the counts `n` of the words of v and `mm` of
the words of u. -/
theorem u320_dispatch {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hb3 : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0) (hpre : udivrem_320_256.pre x m)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64)
    (hTr : (x.get 10#5).toNat + 72 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hTs : (x.get 2#5 - 336#64).toNat + 336 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 336#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hD : ∀ a ∈ bufWords T 256, a ∈ D)
    (hT0 : pcAt (pcAt base 182) 5 + ((hi0 ++ 0x000#12).signExtend 64 + lo0.signExtend 64) = T)
    (hT2 : pcAt (pcAt base 618) 54 + ((hi2 ++ 0x000#12).signExtend 64 + lo2.signExtend 64) = T)
    (hT9 : pcAt (pcAt base 2585) 184 + ((hi9 ++ 0x000#12).signExtend 64 + lo9.signExtend 64) = T)
    (x' : Regs) (m' : Mem) (hF : U320Frame x m x' m') (h10 : x'.get 10#5 = x.get 10#5)
    (h11 : x'.get 11#5 = x.get 11#5) (h13 : x'.get 13#5 = x.get 12#5)
    (n : Nat) (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (h12 : x'.get 12#5 = BitVec.ofNat 64 n)
    (hvn : words m (x.get 12#5) 4 < 2 ^ (64 * n))
    (hvt : n = 1 ∨ memWord m (x.get 12#5 + BitVec.ofNat 64 (8 * (n - 1))).toNat ≠ 0)
    (mm : Nat) (hmm1 : 1 ≤ mm) (hmm5 : mm ≤ 5) (h8 : x'.get 8#5 = BitVec.ofNat 64 mm)
    (hum : words m (x.get 11#5) 5 < 2 ^ (64 * mm))
    (hut : mm = 1 ∨ memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * (mm - 1))).toNat ≠ 0) :
    Reach (u320Bufs x D) P320 base (pcAt base 95) x' m' (x.get 1#5)
      (udivrem_320_256.post x m) := by
  have hpre0 := hpre
  simp only [udivrem_320_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn'⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr⟩ := hpre
  have hU := words5_top_bound m _ mm hmm1 hmm5 hum
  have hUlo := words5_ge_top m (x.get 11#5) mm hmm1 hmm5
  have hVb := words4_ge_top m (x.get 12#5) n hn1 (by omega)
  have huw := hF.memWord_u hpre0 (BitVec.ofNat 64 (8 * (mm - 1))) (by rw [BitVec.toNat_ofNat]; omega)
  have hvw := hF.memWord_v hpre0 (BitVec.ofNat 64 (8 * (n - 1))) (by rw [BitVec.toNat_ofNat]; omega)
  rw [← regs_set_of_get' (by decide) h8, ← regs_set_of_get' (by decide) h10,
    ← regs_set_of_get' (by decide) h11, ← regs_set_of_get' (by decide) h12,
    ← regs_set_of_get' (by decide) h13]
  have hua' : BitVec.ofNat 64 mm <<< 3 + (x.get 11#5 + 18446744073709551608#64) =
      x.get 11#5 + BitVec.ofNat 64 (8 * (mm - 1)) := by bv_omega
  have hva' : BitVec.ofNat 64 n <<< 3 + (x.get 12#5 + 18446744073709551608#64) =
      x.get 12#5 + BitVec.ofNat 64 (8 * (n - 1)) := by bv_omega
  rv_exec_cut 99
  rv_subst
  -- The top word u[mm - 1] of u.
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  rw [hua']
  refine ⟨by simp only [u320Bufs, List.mem_append]
             exact Or.inl (Or.inl (Or.inl (Or.inl (mem_bufWords (by omega))))), fun wa hwa => ?_⟩
  rw [huw] at hwa
  rv_subst
  -- The top word v[n - 1] of v.
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  rw [hva']
  refine ⟨by simp only [u320Bufs, List.mem_append]
             exact Or.inl (Or.inl (Or.inl (Or.inr (mem_bufWords (by omega))))), fun wb hwb => ?_⟩
  rw [hvw] at hwb
  rv_subst
  have hmn : (BitVec.ofNat 64 mm).toNat = mm := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hw4 : words m (x.get 12#5) 4 = (memWord m (x.get 12#5).toNat).toNat + 2 ^ 64 *
      ((memWord m (x.get 12#5 + 8#64).toNat).toNat + 2 ^ 64 *
        ((memWord m (x.get 12#5 + 16#64).toNat).toNat + 2 ^ 64 *
          (memWord m (x.get 12#5 + 24#64).toNat).toNat)) := words4_unfold m _
  have hv0l := (memWord m (x.get 12#5).toNat).isLt
  have hv1l := (memWord m (x.get 12#5 + 8#64).toNat).isLt
  have hv2l := (memWord m (x.get 12#5 + 16#64).toNat).isLt
  have hv3l := (memWord m (x.get 12#5 + 24#64).toNat).isLt
  have hv0' := hF.memWord_v hpre0 0#64 (by decide)
  rw [BitVec.add_zero] at hv0'
  generalize hua : memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * (mm - 1))).toNat = ua at *
  interval_cases n
  · -- v < 2^64.
    simp only [show 8 * (1 - 1) = 0 from rfl, BitVec.add_zero, pow_zero, Nat.mul_one,
      show 64 * 1 = 64 from rfl] at hVb hvn ⊢
    rv_exec_cut 129 177 111
    all_goals rv_subst
    all_goals try simp only [zopz0zKzJ_u_eq, decide_eq_true_eq, decide_eq_false_iff_not] at *
    · rename_i hb
      rw [BitVec.le_def, num_toNat mm (by omega)] at hb
      refine u320_ult base x m hr hpre0 _ _ (U320Frame.regs hF ?_ ?_) ?_ ?_
        (ult_of_count (n := 1) hmm1 (BitVec.isLt _) hU (by simpa using hVb) (Or.inl rfl)
          (by simpa using hb))
      all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      all_goals first | rfl | u320_cs
    · rename_i hv0 hb
      rw [hv0'] at hv0
      refine u320_vzero base x m hb3 hr hpre0 _ _ (U320Frame.regs hF ?_ ?_) ?_ ?_
      all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      all_goals first | rfl | u320_cs | skip
      rw [hv0] at hw4; rw [hw4] at hvn ⊢; simp at hvn ⊢; omega
    · rename_i hv0 hb
      rw [hv0'] at hv0
      refine u320_by1 base x m hb3 hr hpre0 hw hTr hTs hhold hD hT0 _ m'
        (U320Frame.regs hF ?_ ?_) ?_ ?_ mm hmm1 hmm5 ?_ hum ?_ hv0 ?_
      all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      all_goals first | rfl | u320_cs | exact hv0' | skip
      rw [hw4] at hvn ⊢; omega
  · -- 2^64 ≤ v < 2^128.
    simp only [show 8 * (2 - 1) = 8 from rfl, show 64 * (2 - 1) = 64 from rfl,
      show 64 * 2 = 128 from rfl] at hVb hvn hvt ⊢
    have hv1 : memWord m (x.get 12#5 + 8#64).toNat ≠ 0 := by simpa using hvt
    rv_exec_cut 129 150
    all_goals rv_subst
    all_goals try simp only [zopz0zKzJ_u_eq, decide_eq_true_eq, decide_eq_false_iff_not] at *
    · rename_i hb
      rw [BitVec.le_def, num_toNat mm (by omega)] at hb
      refine u320_ult base x m hr hpre0 _ _ (U320Frame.regs hF ?_ ?_) ?_ ?_
        (ult_of_count (n := 2) hmm1 (BitVec.isLt _) hU (by simpa using hVb) (Or.inr ?_)
          (by simpa using hb))
      all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      all_goals first | rfl | u320_cs | skip
      rcases Nat.eq_zero_or_pos (memWord m (x.get 12#5 + 8#64).toNat).toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hv1
      · exact h
    · refine u320_by2 base x m hb3 hr hpre0 hw hTr hTs hhold hD hT2 _ m'
        (U320Frame.regs hF ?_ ?_) ?_ ?_ ?_ mm hmm1 hmm5 ?_ hum hv1 ?_
      all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      all_goals first | rfl | u320_cs | skip
      rw [hw4] at hvn ⊢; omega
  · -- 2^128 ≤ v < 2^192.
    simp only [show 8 * (3 - 1) = 16 from rfl, show 64 * (3 - 1) = 128 from rfl,
      show 64 * 3 = 192 from rfl] at hVb hvn hvt ⊢
    have hv2 : memWord m (x.get 12#5 + 16#64).toNat ≠ 0 := by simpa using hvt
    have hv3 : memWord m (x.get 12#5 + 24#64).toNat = 0#64 := by
      apply BitVec.eq_of_toNat_eq; rw [hw4] at hvn; rw [BitVec.toNat_zero]; omega
    rv_exec_cut 129 172
    all_goals rv_subst
    all_goals try simp only [zopz0zKzJ_u_eq, decide_eq_true_eq, decide_eq_false_iff_not] at *
    · rename_i hb
      rw [BitVec.le_def, num_toNat mm (by omega)] at hb
      refine u320_ult base x m hr hpre0 _ _ (U320Frame.regs hF ?_ ?_) ?_ ?_
        (ult_of_count (n := 3) hmm1 (BitVec.isLt _) hU (by simpa using hVb) (Or.inr ?_)
          (by simpa using hb))
      all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      all_goals first | rfl | u320_cs | skip
      rcases Nat.eq_zero_or_pos (memWord m (x.get 12#5 + 16#64).toNat).toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hv2
      · exact h
    · rename_i hb
      rw [BitVec.le_def, num_toNat mm (by omega)] at hb
      simp only [show (3#64 : BitVec 64).toNat = 3 from rfl] at hb
      have hl : 3 < mm + if (memWord m (x.get 12#5 + 16#64).toNat).toNat ≤ ua.toNat then 1 else 0 :=
        by omega
      have hmm3 : 3 ≤ mm := by split_ifs at hl <;> omega
      have hua1 : 1 ≤ ua.toNat := by
        rcases hut with h | h
        · omega
        · rcases Nat.eq_zero_or_pos ua.toNat with h0 | h0
          · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) h
          · exact h0
      have hw3 : words m (x.get 12#5) 3 = (memWord m (x.get 12#5).toNat).toNat + 2 ^ 64 *
          ((memWord m (x.get 12#5 + 8#64).toNat).toNat + 2 ^ 64 *
            (memWord m (x.get 12#5 + 16#64).toNat).toNat) := by
        simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
          Nat.add_zero]
      have hv2n : 0 < (memWord m (x.get 12#5 + 16#64).toNat).toNat := by
        rcases Nat.eq_zero_or_pos (memWord m (x.get 12#5 + 16#64).toNat).toNat with h | h
        · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hv2
        · exact h
      refine u320_knuth base x m hb3 hr hpre0 hw hTr hTs hhold hD hT9 _ m'
        (U320Frame.regs hF ?_ ?_) ?_ ?_ ?_ mm ?_ hmm1 hmm5 hum ?_ hv3 ?_ ?_
      all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      all_goals first | rfl | u320_cs | skip
      · exact le_trans (Nat.le_mul_of_pos_left _ hua1) hUlo
      · rw [hw3]; omega
      · exact u320_knuth_top hmm5 hUlo hua1 (by rw [hw3]; omega) (by rw [hw3]; omega) hv2l hl

theorem words5_lt_of_zero (m : Mem) (u : BitVec 64) (mm : Nat) (hmm : mm ≤ 5)
    (h : ∀ i, mm ≤ i → i < 5 → memWord m (u + BitVec.ofNat 64 (8 * i)).toNat = 0#64) :
    words m u 5 < 2 ^ (64 * mm) := by
  have hs := words_split m mm (5 - mm) u
  rw [show mm + (5 - mm) = 5 by omega] at hs
  rw [hs, words_eq_zero m (5 - mm) _ fun i hi => by
    rw [BitVec.add_assoc, show BitVec.ofNat 64 (8 * mm) + BitVec.ofNat 64 (8 * i) =
      BitVec.ofNat 64 (8 * (mm + i)) by apply BitVec.eq_of_toNat_eq; simp; omega]
    exact h (mm + i) (by omega) (by omega), Nat.mul_zero, Nat.add_zero]
  exact words_lt _ _ _

/-- The number `s + 1` of the significant words of u when u[2..4] = 0: 2 for u[1] ≠ 0. -/
theorem u320_sltu_add_one (w : BitVec 64) :
    (if 0#64 < w then 1#64 else 0#64) + 1#64 = if w = 0#64 then 1#64 else 2#64 := by
  by_cases h : w = 0#64
  · subst h; rfl
  · rw [if_pos (by rw [BitVec.lt_def]; have : w.toNat ≠ 0 := fun h0 => h (BitVec.eq_of_toNat_eq
      (by simpa using h0)); simp; omega), if_neg h]; rfl

set_option hygiene false in
/-- The exit of the count of the words of u at 95 with `k` words: the dispatch. -/
local macro "u320_exit" k:num : tactic => `(tactic| (
  refine u320_dispatch base x m hb3 hr hpre0 hw hTr hTs hhold hD hT0 hT2 hT9 _ m'
    (U320Frame.regs hF ?_ ?_) ?_ ?_ ?_ n hn1 hn3 ?_ hvn hvt $k (by norm_num) (by norm_num) ?_ ?_ ?_
  all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte,
    u320_sltu_add_one]
  all_goals first
    | done
    | rfl
    | u320_cs
    | exact h10
    | exact h11
    | exact h13
    | exact h12
    | (rw [if_neg]; assumption)
    | (rw [if_pos]; assumption)
    | (refine words5_lt_of_zero m _ $k (by norm_num) fun i h1 h2 => ?_
       interval_cases i <;> simp only [Nat.reduceMul] <;> first | assumption | exact hu4)
    | (left; first | rfl | trivial)
    | (right; simp only [Nat.reduceSub, Nat.reduceMul]; assumption)))

/-- The count of the significant words of u from 52 for u[4] = 0, and the dispatch at 95. -/
theorem u320_scan {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hb3 : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0) (hpre : udivrem_320_256.pre x m)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64)
    (hTr : (x.get 10#5).toNat + 72 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hTs : (x.get 2#5 - 336#64).toNat + 336 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 336#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hD : ∀ a ∈ bufWords T 256, a ∈ D)
    (hT0 : pcAt (pcAt base 182) 5 + ((hi0 ++ 0x000#12).signExtend 64 + lo0.signExtend 64) = T)
    (hT2 : pcAt (pcAt base 618) 54 + ((hi2 ++ 0x000#12).signExtend 64 + lo2.signExtend 64) = T)
    (hT9 : pcAt (pcAt base 2585) 184 + ((hi9 ++ 0x000#12).signExtend 64 + lo9.signExtend 64) = T)
    (x' : Regs) (m' : Mem) (hF : U320Frame x m x' m') (h10 : x'.get 10#5 = x.get 10#5)
    (h11 : x'.get 11#5 = x.get 11#5) (h13 : x'.get 13#5 = x.get 12#5)
    (n : Nat) (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (h12 : x'.get 12#5 = BitVec.ofNat 64 n)
    (hvn : words m (x.get 12#5) 4 < 2 ^ (64 * n))
    (hvt : n = 1 ∨ memWord m (x.get 12#5 + BitVec.ofNat 64 (8 * (n - 1))).toNat ≠ 0)
    (hu4 : memWord m (x.get 11#5 + 32#64).toNat = 0#64) :
    Reach (u320Bufs x D) P320 base (pcAt base 52) x' m' (x.get 1#5)
      (udivrem_320_256.post x m) := by
  have hpre0 := hpre
  have hu : ∀ c : BitVec 64, c.toNat + 8 ≤ 40 →
      memWord m' (x.get 11#5 + c).toNat = memWord m (x.get 11#5 + c).toNat :=
    hF.memWord_u hpre0
  rw [← regs_set_of_get' (by decide) h11]
  rv_exec_cut 95
  all_goals rv_subst
  all_goals simp only [hu 8#64 (by decide), hu 16#64 (by decide), hu 24#64 (by decide)] at *
  all_goals by_cases hu1 : memWord m (x.get 11#5 + 8#64).toNat = 0#64
  all_goals first
    | u320_exit 4 | u320_exit 3 | u320_exit 2 | u320_exit 1

/-- A word greater than another is not 0. -/
theorem bv_ne_zero_of_lt {a b : BitVec 64} (h : a.toNat < b.toNat) : b ≠ 0#64 := by
  intro h0; rw [h0] at h; simp at h

/-- The dispatch of `udivrem<320, 256>()` from 7, after the prologue, on the top words of u and
v. -/
theorem u320_main {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hb3 : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0) (hpre : udivrem_320_256.pre x m)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64)
    (hTr : (x.get 10#5).toNat + 72 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hTs : (x.get 2#5 - 336#64).toNat + 336 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 336#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hD : ∀ a ∈ bufWords T 256, a ∈ D)
    (hT0 : pcAt (pcAt base 182) 5 + ((hi0 ++ 0x000#12).signExtend 64 + lo0.signExtend 64) = T)
    (hT1 : pcAt (pcAt base 375) 5 + ((hi1 ++ 0x000#12).signExtend 64 + lo1.signExtend 64) = T)
    (hT2 : pcAt (pcAt base 618) 54 + ((hi2 ++ 0x000#12).signExtend 64 + lo2.signExtend 64) = T)
    (hT3 : pcAt (pcAt base 932) 50 + ((hi3 ++ 0x000#12).signExtend 64 + lo3.signExtend 64) = T)
    (hT4 : pcAt (pcAt base 1275) 65 + ((hi4 ++ 0x000#12).signExtend 64 + lo4.signExtend 64) = T)
    (hT5 : pcAt (pcAt base 1457) 64 + ((hi5 ++ 0x000#12).signExtend 64 + lo5.signExtend 64) = T)
    (hT6 : pcAt (pcAt base 1661) 87 + ((hi6 ++ 0x000#12).signExtend 64 + lo6.signExtend 64) = T)
    (hT7 : pcAt (pcAt base 1948) 107 + ((hi7 ++ 0x000#12).signExtend 64 + lo7.signExtend 64) = T)
    (hT8 : pcAt (pcAt base 2273) 84 + ((hi8 ++ 0x000#12).signExtend 64 + lo8.signExtend 64) = T)
    (hT9 : pcAt (pcAt base 2585) 184 + ((hi9 ++ 0x000#12).signExtend 64 + lo9.signExtend 64) = T)
    (x' : Regs) (m' : Mem) (hF : U320Frame x m x' m') (h10 : x'.get 10#5 = x.get 10#5)
    (h11 : x'.get 11#5 = x.get 11#5) (h12 : x'.get 12#5 = x.get 12#5) :
    Reach (u320Bufs x D) P320 base (pcAt base 7) x' m' (x.get 1#5)
      (udivrem_320_256.post x m) := by
  have hpre0 := hpre
  have hu : ∀ c : BitVec 64, c.toNat + 8 ≤ 40 →
      memWord m' (x.get 11#5 + c).toNat = memWord m (x.get 11#5 + c).toNat :=
    hF.memWord_u hpre0
  have hv : ∀ c : BitVec 64, c.toNat + 8 ≤ 32 →
      memWord m' (x.get 12#5 + c).toNat = memWord m (x.get 12#5 + c).toNat :=
    hF.memWord_v hpre0
  have hv0 := hv 0#64 (by decide)
  rw [BitVec.add_zero] at hv0
  rw [← regs_set_of_get' (by decide) h10, ← regs_set_of_get' (by decide) h11,
    ← regs_set_of_get' (by decide) h12]
  have hw4 := words4_unfold m (x.get 12#5)
  have hw5 := words5_unfold m (x.get 11#5)
  have hv0l := (memWord m (x.get 12#5).toNat).isLt
  have hv1l := (memWord m (x.get 12#5 + 8#64).toNat).isLt
  have hv2l := (memWord m (x.get 12#5 + 16#64).toNat).isLt
  have hv3l := (memWord m (x.get 12#5 + 24#64).toNat).isLt
  have hu0l := (memWord m (x.get 11#5).toNat).isLt
  have hu1l := (memWord m (x.get 11#5 + 8#64).toNat).isLt
  have hu2l := (memWord m (x.get 11#5 + 16#64).toNat).isLt
  have hu3l := (memWord m (x.get 11#5 + 24#64).toNat).isLt
  have hu4l := (memWord m (x.get 11#5 + 32#64).toNat).isLt
  rv_exec_cut 12 25 21 129 37 31 52 95 57 177 79
  all_goals rv_subst
  all_goals simp only [hu 16#64 (by decide), hu 24#64 (by decide), hu 32#64 (by decide),
    hv 8#64 (by decide), hv 16#64 (by decide), hv 24#64 (by decide), hv0] at *
  all_goals try simp only [zopz0zKzJ_u_eq, zopz0zI_u_eq, decide_eq_true_eq,
    decide_eq_false_iff_not, BitVec.or_eq_zero_iff, BitVec.le_def, BitVec.lt_def] at *
  -- v ≥ 2^192 and u[4] < v[3]: `udivrem_top1<3>()`.
  all_goals first
    | (rv_not_at 12; skip)
    | (refine u320_top13 base x m hb3 hr hpre0 hw hTr hTs hhold hD hT5 _ m'
         (U320Frame.regs hF ?_ ?_) ?_ ?_ ?_ (by assumption) (by omega)
       all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
       all_goals first | rfl | u320_cs)
  -- v ≥ 2^192 and u[4] ≥ v[3]: `udivrem_top2<4>()`.
  all_goals first
    | (rv_not_at 25; skip)
    | (refine u320_top24 base x m hb3 hr hpre0 hw hTr hTs hhold hD hT8 _ m'
         (U320Frame.regs hF ?_ ?_) ?_ ?_ ?_ (by assumption)
       all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
       all_goals first | rfl | u320_cs)
  -- v[3] = 0, u[4] < v[2] and u[4] or u[3] not 0: `udivrem_top2<3>()`.
  all_goals first
    | (rv_not_at 21; skip)
    | (refine u320_top23 base x m hb3 hr hpre0 hw hTr hTs hhold hD hT6 _ m'
         (U320Frame.regs hF ?_ ?_) ?_ ?_ ?_ (by assumption)
         (bv_ne_zero_of_lt (a := memWord m (x.get 11#5 + 32#64).toNat) (by omega)) (by omega)
       all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
       all_goals first | rfl | u320_cs)
  -- v[3] = 0, u[4] < v[2], u[4] = u[3] = 0 and u[2] < v[2]: u < v.
  all_goals first
    | (rv_not_at 129; skip)
    | (refine u320_ult base x m hr hpre0 _ _ (U320Frame.regs hF ?_ ?_) ?_ ?_ ?_
       all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
       all_goals first | rfl | u320_cs | skip
       rw [hw4, hw5]
       simp only [*, BitVec.toNat_ofNat, Nat.zero_mod] at *
       omega)
  -- v[3] = 0, u[4] < v[2], u[4] = u[3] = 0 and u[2] ≥ v[2]: `udivrem_top1<2>()`.
  all_goals first
    | (rv_not_at 37; skip)
    | (refine u320_top12 base x m hb3 hr hpre0 hw hTr hTs hhold hD hT4 _ m'
         (U320Frame.regs hF ?_ ?_) ?_ ?_ ?_ (by assumption)
         (bv_ne_zero_of_lt (a := memWord m (x.get 11#5 + 32#64).toNat) (by omega)) (by tauto)
         (by tauto)
       all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
       all_goals first | rfl | u320_cs)
  -- v[3] = 0, v[2] ≠ 0 and u[4] = v[2]: `udivrem_top2<3, true>()`.
  all_goals first
    | (rv_not_at 31; skip)
    | (refine u320_topE base x m hb3 hr hpre0 hw hTr hTs hhold hD hT7 _ m'
         (U320Frame.regs hF ?_ ?_) ?_ ?_ ?_ (by assumption) (by assumption) (by assumption)
       all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
       all_goals first | rfl | u320_cs)
  -- v[3] = 0, v[2] ≠ 0 and u[4] > v[2]: the count of the words of u, 5, and the dispatch.
  all_goals first
    | (rv_not_at 95; skip)
    | (refine u320_dispatch base x m hb3 hr hpre0 hw hTr hTs hhold hD hT0 hT2 hT9 _ m'
         (U320Frame.regs hF ?_ ?_) ?_ ?_ ?_ 3 (by norm_num) (by norm_num) ?_ ?_ ?_ 5 (by norm_num)
         (by norm_num) ?_ (words_lt m 5 _) ?_
       all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
       all_goals first
         | rfl
         | u320_cs
         | (rw [hw4, ‹memWord m (x.get 12#5 + 24#64).toNat = 0#64›]; simp only [BitVec.toNat_ofNat,
             Nat.zero_mod, Nat.mul_zero, Nat.add_zero]; omega)
         | (right; simp only [Nat.reduceSub, Nat.reduceMul]; assumption))
  -- The two words u[4] and u[3] not 0, v[3] = v[2] = 0 and v[1] ≠ 0: `udivrem_by2()` of 4 words.
  all_goals first
    | (rv_not_at 57; skip)
    | (refine u320_by24 base x m hb3 hr hpre0 hw hTr hTs hhold hD hT3 _ m'
         (U320Frame.regs hF ?_ ?_) ?_ ?_ ?_ ?_ (by assumption) ?_
       all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
       all_goals first
         | rfl
         | u320_cs
         | (rw [hw4, ‹memWord m (x.get 12#5 + 24#64).toNat = 0#64›,
             ‹memWord m (x.get 12#5 + 16#64).toNat = 0#64›]
            simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.mul_zero, Nat.add_zero]))
  -- v[3] = v[2] = v[1] = 0 and v[0] ≠ 0: `udivrem_by1()` of 5 words.
  all_goals first
    | (rv_not_at 79; skip)
    | (refine u320_by15 base x m hb3 hr hpre0 hw hTr hTs hhold hD hT1 _ m'
         (U320Frame.regs hF ?_ ?_) ?_ ?_ ?_ (by assumption) ?_
       all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
       all_goals first
         | rfl
         | u320_cs
         | (rw [hw4, ‹memWord m (x.get 12#5 + 24#64).toNat = 0#64›,
             ‹memWord m (x.get 12#5 + 16#64).toNat = 0#64›,
             ‹memWord m (x.get 12#5 + 8#64).toNat = 0#64›]
            simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.mul_zero, Nat.add_zero]))
  -- v = 0.
  all_goals first
    | (rv_not_at 177; skip)
    | (refine u320_vzero base x m hb3 hr hpre0 _ _ (U320Frame.regs hF ?_ ?_) ?_ ?_
       all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
       all_goals first
         | rfl
         | u320_cs
         | (rw [hw4, ‹memWord m (x.get 12#5 + 24#64).toNat = 0#64›,
             ‹memWord m (x.get 12#5 + 16#64).toNat = 0#64›,
             ‹memWord m (x.get 12#5 + 8#64).toNat = 0#64›, ‹memWord m (x.get 12#5).toNat = 0#64›]
            rfl))
  -- The count of the words of u from 52: not from 49, where u[4] ≥ v[2] > 0.
  all_goals first
    | (exfalso
       have hz := ‹memWord m (x.get 11#5 + 32#64).toNat = 0#64›
       have hle := ‹(memWord m (x.get 12#5 + 16#64).toNat).toNat ≤
         (memWord m (x.get 11#5 + 32#64).toNat).toNat›
       have hne := ‹¬memWord m (x.get 12#5 + 16#64).toNat = 0#64›
       rw [hz] at hle
       exact hne (BitVec.eq_of_toNat_eq (by simpa using hle)))
    | skip
  -- v[3] = v[2] = 0 and u[4] = u[3] = 0: n by v[1].
  all_goals
    have hu4 : memWord m (x.get 11#5 + 32#64).toNat = 0#64 := by tauto
    by_cases hv1 : memWord m (x.get 12#5 + 8#64).toNat = 0#64
    · refine u320_scan base x m hb3 hr hpre0 hw hTr hTs hhold hD hT0 hT2 hT9 _ m'
        (U320Frame.regs hF ?_ ?_) ?_ ?_ ?_ 1 (by norm_num) (by norm_num) ?_ ?_ (Or.inl rfl) hu4
      all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      all_goals first
        | rfl
        | u320_cs
        | (rw [hv1]; rfl)
        | (rw [hw4, ‹memWord m (x.get 12#5 + 24#64).toNat = 0#64›,
            ‹memWord m (x.get 12#5 + 16#64).toNat = 0#64›, hv1]
           simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.mul_zero, Nat.add_zero]; omega)
    · refine u320_scan base x m hb3 hr hpre0 hw hTr hTs hhold hD hT0 hT2 hT9 _ m'
        (U320Frame.regs hF ?_ ?_) ?_ ?_ ?_ 2 (by norm_num) (by norm_num) ?_ ?_
        (Or.inr (by simpa using hv1)) hu4
      all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      all_goals first
        | rfl
        | u320_cs
        | (have h0 : (0#64).toNat < (memWord m (x.get 12#5 + 8#64).toNat).toNat :=
             Nat.pos_of_ne_zero fun h => hv1 (BitVec.eq_of_toNat_eq (by simpa using h))
           rw [if_pos h0]; rfl)
        | (rw [hw4, ‹memWord m (x.get 12#5 + 24#64).toNat = 0#64›,
            ‹memWord m (x.get 12#5 + 16#64).toNat = 0#64›]
           simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.mul_zero, Nat.add_zero]; omega)

end IntxRV.Api
