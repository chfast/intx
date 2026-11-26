import IntxRV.Div512By
import IntxRV.Div512K3
import IntxRV.Div512K4
/-!
# The dispatch of `udivrem<512, 256>()`

The count of the significant words of u from 29 (`u512_scan`), for u[7] = 0, and the dispatch at
54 on the counts n of v and m of u (`u512_dispatch`): u < v (`u512_ult`) if the words of u to
divide, m and the word with the bits shifted out of the top, are at most n (`ult_of_count`), and
otherwise v = 0 (`u512_vzero`), the division by 1 word (`u512_by1`), 2 words (`u512_by2`), 3 words
(`u512_k3`) or 4 words (`u512_k4`). See `IntxRV/Api/udivrem_512_256.lean`.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

variable {hi0 hi1 hi2 hi3 : BitVec 20} {lo0 lo1 lo2 lo3 : BitVec 12} {T : BitVec 64}

set_option hygiene false in
local notation "P512" => udivrem_512_256_progAt hi0 lo0 hi1 lo1 hi2 lo2 hi3 lo3

/-- The dispatch of `udivrem<512, 256>()` at 54 on the counts `n` of the words of v and `mm` of
the words of u. -/
theorem u512_dispatch {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hb3 : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0) (hpre : udivrem_512_256.pre x m)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64)
    (hTr : (x.get 10#5).toNat + 96 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hTs : (x.get 2#5 - 240#64).toNat + 240 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 240#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hD : ∀ a ∈ bufWords T 256, a ∈ D)
    (hT0 : pcAt (pcAt base 409) 5 + ((hi0 ++ 0x000#12).signExtend 64 + lo0.signExtend 64) = T)
    (hT1 : pcAt (pcAt base 602) 54 + ((hi1 ++ 0x000#12).signExtend 64 + lo1.signExtend 64) = T)
    (hT2 : pcAt (pcAt base 916) 12 + ((hi2 ++ 0x000#12).signExtend 64 + lo2.signExtend 64) = T)
    (hT3 : pcAt (pcAt base 1091) 34 + ((hi3 ++ 0x000#12).signExtend 64 + lo3.signExtend 64) = T)
    (x' : Regs) (m' : Mem) (hF : U512Frame x m x' m') (h8 : x'.get 8#5 = x.get 11#5)
    (h10 : x'.get 10#5 = x.get 10#5) (h12 : x'.get 12#5 = x.get 12#5)
    (n : Nat) (hn1 : 1 ≤ n) (hn4 : n ≤ 4) (h13 : x'.get 13#5 = BitVec.ofNat 64 n)
    (hvn : words m (x.get 12#5) 4 < 2 ^ (64 * n))
    (hvt : n = 1 ∨ memWord m (x.get 12#5 + BitVec.ofNat 64 (8 * (n - 1))).toNat ≠ 0)
    (h20 : n = 4 → x'.get 20#5 = memWord m (x.get 12#5 + 24#64).toNat)
    (h11a : n = 4 → x'.get 11#5 = 0#64) (h11b : n = 3 → x'.get 11#5 ≠ 0#64)
    (mm : Nat) (hmm1 : 1 ≤ mm) (hmm8 : mm ≤ 8) (h9 : x'.get 9#5 = BitVec.ofNat 64 mm)
    (h14 : x'.get 14#5 = memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * (mm - 1))).toNat)
    (hum : words m (x.get 11#5) 8 < 2 ^ (64 * mm)) :
    Reach (u512Bufs x D) P512 base (pcAt base 54) x' m' (x.get 1#5)
      (udivrem_512_256.post x m) := by
  have hpre0 := hpre
  simp only [udivrem_512_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn'⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr⟩ := hpre
  have hU := words_top_bound m _ mm hmm1 hmm8 hum
  have hVb := words4_ge_top m (x.get 12#5) n hn1 hn4
  have hvw := hF.memWord_v hpre0 (BitVec.ofNat 64 (8 * (n - 1))) (by rw [BitVec.toNat_ofNat]; omega)
  have hva' : BitVec.ofNat 64 n <<< 3 + (x.get 12#5 + 18446744073709551608#64) =
      x.get 12#5 + BitVec.ofNat 64 (8 * (n - 1)) := by bv_omega
  rw [← regs_set_of_get' (by decide) h8, ← regs_set_of_get' (by decide) h9,
    ← regs_set_of_get' (by decide) h10, ← regs_set_of_get' (by decide) h12,
    ← regs_set_of_get' (by decide) h13, ← regs_set_of_get' (by decide) h14]
  rv_exec_cut 56
  rv_subst
  -- The top word v[n - 1] of v.
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  rw [hva']
  refine ⟨by simp only [u512Bufs, List.mem_append]
             exact Or.inl (Or.inl (Or.inl (Or.inr (mem_bufWords (by omega))))), fun wb hwb => ?_⟩
  rw [hvw] at hwb
  rv_subst
  have hmn : (BitVec.ofNat 64 mm).toNat = mm := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hw4 : words m (x.get 12#5) 4 = (memWord m (x.get 12#5).toNat).toNat + 2 ^ 64 *
      ((memWord m (x.get 12#5 + 8#64).toNat).toNat + 2 ^ 64 *
        ((memWord m (x.get 12#5 + 16#64).toNat).toNat + 2 ^ 64 *
          (memWord m (x.get 12#5 + 24#64).toNat).toNat)) := by
    simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
      Nat.add_zero]
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
    rv_exec_cut 84 336 67
    all_goals rv_subst
    all_goals try simp only [zopz0zKzJ_u_eq, decide_eq_true_eq, decide_eq_false_iff_not] at *
    · rename_i hb
      rw [BitVec.le_def, num_toNat mm (by omega)] at hb
      refine u512_ult base x m hr hpre0 _ _ (U512Frame.regs hF ?_ ?_) ?_ ?_
        (ult_of_count (n := 1) hmm1 (BitVec.isLt _) hU (by simpa using hVb) (Or.inl rfl)
          (by simpa using hb))
      all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      all_goals first | rfl | u512_cs
    · rename_i hv0 hb
      rw [hv0'] at hv0
      refine u512_vzero base x m hb3 hr hpre0 _ _ (U512Frame.regs hF ?_ ?_) ?_ ?_
      all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      all_goals first | rfl | u512_cs | skip
      rw [hv0] at hw4; rw [hw4] at hvn ⊢; simp at hvn ⊢; omega
    · rename_i hv0 hb
      rw [hv0'] at hv0
      refine u512_by1 base x m hb3 hr hpre0 hw hTr hTs hhold hD hT0 _ m'
        (U512Frame.regs hF ?_ ?_) ?_ ?_ mm hmm1 hmm8 ?_ hum ?_ hv0 ?_
      all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      all_goals first | rfl | u512_cs | exact hv0' | skip
      rw [hw4] at hvn ⊢; omega
  · -- 2^64 ≤ v < 2^128.
    simp only [show 8 * (2 - 1) = 8 from rfl, show 64 * (2 - 1) = 64 from rfl,
      show 64 * 2 = 128 from rfl] at hVb hvn hvt ⊢
    have hv1 : memWord m (x.get 12#5 + 8#64).toNat ≠ 0 := by simpa using hvt
    rv_exec_cut 84 101
    all_goals rv_subst
    all_goals try simp only [zopz0zKzJ_u_eq, decide_eq_true_eq, decide_eq_false_iff_not] at *
    · rename_i hb
      rw [BitVec.le_def, num_toNat mm (by omega)] at hb
      refine u512_ult base x m hr hpre0 _ _ (U512Frame.regs hF ?_ ?_) ?_ ?_
        (ult_of_count (n := 2) hmm1 (BitVec.isLt _) hU (by simpa using hVb) (Or.inr ?_)
          (by simpa using hb))
      all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      all_goals first | rfl | u512_cs | skip
      rcases Nat.eq_zero_or_pos (memWord m (x.get 12#5 + 8#64).toNat).toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hv1
      · exact h
    · refine u512_by2 base x m hb3 hr hpre0 hw hTr hTs hhold hD hT1 _ m'
        (U512Frame.regs hF ?_ ?_) ?_ ?_ ?_ mm hmm1 hmm8 ?_ hum hv1 ?_
      all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      all_goals first | rfl | u512_cs | skip
      rw [hw4] at hvn ⊢; omega
  · -- 2^128 ≤ v < 2^192.
    simp only [show 8 * (3 - 1) = 16 from rfl, show 64 * (3 - 1) = 128 from rfl,
      show 64 * 3 = 192 from rfl] at hVb hvn hvt ⊢
    have hv2 : memWord m (x.get 12#5 + 16#64).toNat ≠ 0 := by simpa using hvt
    have hv3 : memWord m (x.get 12#5 + 24#64).toNat = 0#64 := by
      apply BitVec.eq_of_toNat_eq; rw [hw4] at hvn; rw [BitVec.toNat_zero]; omega
    have h11 := h11b rfl
    rv_exec_cut 84 126 222
    all_goals rv_subst
    all_goals try simp only [zopz0zKzJ_u_eq, decide_eq_true_eq, decide_eq_false_iff_not] at *
    · rename_i hb
      rw [BitVec.le_def, num_toNat mm (by omega)] at hb
      refine u512_ult base x m hr hpre0 _ _ (U512Frame.regs hF ?_ ?_) ?_ ?_
        (ult_of_count (n := 3) hmm1 (BitVec.isLt _) hU (by simpa using hVb) (Or.inr ?_)
          (by simpa using hb))
      all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      all_goals first | rfl | u512_cs | skip
      rcases Nat.eq_zero_or_pos (memWord m (x.get 12#5 + 16#64).toNat).toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hv2
      · exact h
    · rename_i ha1 hb
      exact absurd ha1 h11
    · rename_i ha1 hb
      rw [BitVec.le_def, num_toNat mm (by omega)] at hb
      refine u512_k3 base x m hb3 hr hpre0 hw hTr hTs hhold hD hT2 _ m'
        (U512Frame.regs hF ?_ ?_) ?_ ?_ ?_ ?_ ?_ mm hmm1 hmm8 ?_ hum hv3 hv2 ?_
      all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      all_goals first | rfl | u512_cs | skip
      rw [hua]; simpa using hb
  · -- 2^192 ≤ v.
    simp only [show 8 * (4 - 1) = 24 from rfl, show 64 * (4 - 1) = 192 from rfl] at hVb hvt ⊢
    have hv3 : memWord m (x.get 12#5 + 24#64).toNat ≠ 0 := by simpa using hvt
    have h11 := h11a rfl
    have h20' := h20 rfl
    rv_exec_cut 84 126 222
    all_goals rv_subst
    all_goals try simp only [zopz0zKzJ_u_eq, decide_eq_true_eq, decide_eq_false_iff_not] at *
    · rename_i hb
      rw [BitVec.le_def, num_toNat mm (by omega)] at hb
      refine u512_ult base x m hr hpre0 _ _ (U512Frame.regs hF ?_ ?_) ?_ ?_
        (ult_of_count (n := 4) hmm1 (BitVec.isLt _) hU (by simpa using hVb) (Or.inr ?_)
          (by simpa using hb))
      all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      all_goals first | rfl | u512_cs | skip
      rcases Nat.eq_zero_or_pos (memWord m (x.get 12#5 + 24#64).toNat).toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hv3
      · exact h
    · rename_i ha1 hb
      rw [BitVec.le_def, num_toNat mm (by omega)] at hb
      refine u512_k4 base x m hb3 hr hpre0 hw hTr hTs hhold hD hT3 _ m'
        (U512Frame.regs hF ?_ ?_) ?_ ?_ ?_ ?_ ?_ ?_ ?_ mm hmm1 hmm8 ?_ hum hv3 ?_
      all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      all_goals first | rfl | u512_cs | exact h20' | exact h11 | skip
      rw [hua]; simpa using hb
    · rename_i ha1 hb
      exact absurd h11 ha1

/-- The number `s1 + 1` of the significant words of u when u[2..7] = 0: 2 for u[1] ≠ 0. -/
theorem sltu_zero_add_one (w : BitVec 64) :
    (if 0#64 < w then 1#64 else 0#64) + 1#64 = if w = 0#64 then 1#64 else 2#64 := by
  by_cases h : w = 0#64
  · subst h; rfl
  · rw [if_pos (by rw [BitVec.lt_def]; have : w.toNat ≠ 0 := fun h0 => h (BitVec.eq_of_toNat_eq
      (by simpa using h0)); simp; omega), if_neg h]; rfl

set_option hygiene false in
/-- The exit of the count of the words of u at 54 with `k` words: the dispatch. -/
local macro "u512_exit" k:num : tactic => `(tactic| (
  refine u512_dispatch base x m hb3 hr hpre0 hw hTr hTs hhold hD hT0 hT1 hT2 hT3 _ m'
    (U512Frame.regs hF ?_ ?_) ?_ ?_ ?_ n hn1 hn4 ?_ hvn hvt ?_ ?_ ?_ $k (by norm_num) (by norm_num)
    ?_ ?_ ?_
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · u512_cs
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h10
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h12
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h13
  · intro h; simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h20 h
  · intro h; simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h11a h
  · intro h; simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h11b h
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, sltu_zero_add_one]
    first | done | rfl | (rw [if_neg]; assumption) | (rw [if_pos]; assumption)
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    first | done | rfl | rw [show BitVec.ofNat 64 (8 * (1 - 1)) = 0#64 from rfl, BitVec.add_zero]
  · refine words8_lt_of_zero m _ $k (by norm_num) fun i h1 h2 => ?_
    interval_cases i <;> first | assumption | exact hu7))

/-- The count of the significant words of u in `udivrem<512, 256>()` from 29, for u[7] = 0. -/
theorem u512_scan {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hb3 : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0) (hpre : udivrem_512_256.pre x m)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64)
    (hTr : (x.get 10#5).toNat + 96 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hTs : (x.get 2#5 - 240#64).toNat + 240 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 240#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hD : ∀ a ∈ bufWords T 256, a ∈ D)
    (hT0 : pcAt (pcAt base 409) 5 + ((hi0 ++ 0x000#12).signExtend 64 + lo0.signExtend 64) = T)
    (hT1 : pcAt (pcAt base 602) 54 + ((hi1 ++ 0x000#12).signExtend 64 + lo1.signExtend 64) = T)
    (hT2 : pcAt (pcAt base 916) 12 + ((hi2 ++ 0x000#12).signExtend 64 + lo2.signExtend 64) = T)
    (hT3 : pcAt (pcAt base 1091) 34 + ((hi3 ++ 0x000#12).signExtend 64 + lo3.signExtend 64) = T)
    (x' : Regs) (m' : Mem) (hF : U512Frame x m x' m') (h8 : x'.get 8#5 = x.get 11#5)
    (h10 : x'.get 10#5 = x.get 10#5) (h12 : x'.get 12#5 = x.get 12#5)
    (n : Nat) (hn1 : 1 ≤ n) (hn4 : n ≤ 4) (h13 : x'.get 13#5 = BitVec.ofNat 64 n)
    (hvn : words m (x.get 12#5) 4 < 2 ^ (64 * n))
    (hvt : n = 1 ∨ memWord m (x.get 12#5 + BitVec.ofNat 64 (8 * (n - 1))).toNat ≠ 0)
    (h20 : n = 4 → x'.get 20#5 = memWord m (x.get 12#5 + 24#64).toNat)
    (h11a : n = 4 → x'.get 11#5 = 0#64) (h11b : n = 3 → x'.get 11#5 ≠ 0#64)
    (hu7 : memWord m (x.get 11#5 + 56#64).toNat = 0#64) :
    Reach (u512Bufs x D) P512 base (pcAt base 29) x' m' (x.get 1#5)
      (udivrem_512_256.post x m) := by
  have hpre0 := hpre
  have hu : ∀ c : BitVec 64, c.toNat + 8 ≤ 64 →
      memWord m' (x.get 11#5 + c).toNat = memWord m (x.get 11#5 + c).toNat :=
    hF.memWord_u hpre0
  have hu0 := hu 0#64 (by decide)
  rw [BitVec.add_zero] at hu0
  rw [← regs_set_of_get' (by decide) h8]
  rv_exec_cut 54
  all_goals rv_subst
  all_goals simp only [hu 8#64 (by decide), hu 16#64 (by decide), hu 24#64 (by decide),
    hu 32#64 (by decide), hu 40#64 (by decide), hu 48#64 (by decide), hu0] at *
  all_goals first
    | u512_exit 7 | u512_exit 6 | u512_exit 5 | u512_exit 4 | u512_exit 3 | u512_exit 2
    | u512_exit 1

end IntxRV.Api
