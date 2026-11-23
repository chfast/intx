import IntxRV.Div320Top
import IntxRV.Api.udivrem_knuth_320

/-!
# The path of `udivrem<320, 256>()` that calls `udivrem_knuth<320, 256>()`

For a divisor of 3 words and a quotient of more than 2 words: the call of the Knuth division with
the count m of the significant words of u (`u320_knuth`), which writes the whole result. See
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

/-- The path of `udivrem<320, 256>()` for a divisor of 3 words from 172: the call of
`udivrem_knuth<320, 256>()` with the `mm` significant words of u. -/
theorem u320_knuth {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hb3 : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0) (hpre : udivrem_320_256.pre x m)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64)
    (hTr : (x.get 10#5).toNat + 72 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hTs : (x.get 2#5 - 336#64).toNat + 336 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 336#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hD : ∀ a ∈ bufWords T 256, a ∈ D)
    (hT9 : pcAt (pcAt base 2585) 184 + ((hi9 ++ 0x000#12).signExtend 64 + lo9.signExtend 64) = T)
    (x' : Regs) (m' : Mem) (hF : U320Frame x m x' m') (h10 : x'.get 10#5 = x.get 10#5)
    (h11 : x'.get 11#5 = x.get 11#5) (h13 : x'.get 13#5 = x.get 12#5) (mm : Nat)
    (h8 : x'.get 8#5 = BitVec.ofNat 64 mm) (hmm1 : 1 ≤ mm) (hmm5 : mm ≤ 5)
    (hum : words m (x.get 11#5) 5 < 2 ^ (64 * mm))
    (hum1 : 2 ^ (64 * (mm - 1)) ≤ words m (x.get 11#5) 5)
    (hv3 : memWord m (x.get 12#5 + 24#64).toNat = 0#64)
    (hd2 : 2 ^ (64 * 2) ≤ words m (x.get 12#5) 3)
    (htop : words m (x.get 12#5) 3 / 2 ^ (64 * 2) ≤ words m (x.get 11#5) 5 / 2 ^ (64 * 2)) :
    Reach (u320Bufs x D) P320 base (pcAt base 172) x' m' (x.get 1#5)
      (udivrem_320_256.post x m) := by
  -- `omega` and `subst_vars` do not see the address of the table.
  replace hT9 := PLift.up hT9
  have hpre0 := hpre
  simp only [udivrem_320_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr⟩ := hpre
  have hmn : (BitVec.ofNat 64 mm).toNat = mm := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hV3 : words m (x.get 12#5) 4 = words m (x.get 12#5) 3 := by
    have hs := words_split m 3 1 (x.get 12#5)
    rw [show 3 + 1 = 4 from rfl] at hs
    have hw1 : words m (x.get 12#5 + BitVec.ofNat 64 (8 * 3)) 1 = 0 := by
      rw [show (BitVec.ofNat 64 (8 * 3) : BitVec 64) = 24#64 from rfl]
      simp only [words, hv3, BitVec.toNat_ofNat, Nat.zero_mod, Nat.mul_zero, Nat.add_zero]
    rw [hs, hw1, Nat.mul_zero, Nat.add_zero]
  have hvne : words m (x.get 12#5) 4 ≠ 0 := by
    rw [hV3]; intro h0; rw [h0] at hd2; exact absurd hd2 (by norm_num)
  have hsp := hF.1
  have hu5 := hF.words_u hpre0 5 le_rfl
  have hv3w := hF.words_v hpre0 3 (by norm_num)
  have hsub : x.get 2#5 + 18446744073709551568#64 - 288#64 = x.get 2#5 - 336#64 := by bv_omega
  rw [← regs_set_of_get' (by decide) h13, ← regs_set_of_get' (by decide) h8]
  rv_exec_cut 2585
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  rw [show pcAt base 174 + 8192#64 + BitVec.signExtend 64 1452#12 = pcAt base 2585 by
      simp only [pcAt, BitVec.reduceSignExtend]; bv_omega,
    update_aligned (pcAt_aligned hb3 2585)]
  refine Reach.call_sub (r := 176) (p320_eq ▸ udivrem_320_256_progAt_udivrem_knuth_320_in)
    p320_length
    (udivrem_knuth_320.reach hi9 lo9 (pcAt base 2585) T _ _ (pcAt_aligned hb3 2585) hT9.down hw
      ?_ ?_ ?_ ?_ ?_) ?_ ?_ ?_
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    exact pcAt_aligned hb3 176
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    rw [hsp, hsub]
    rcases hTs with h | h
    · exact Or.inl (by omega)
    · exact Or.inr h
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    rw [h10]; exact hTr
  · exact hF.holdsData hw hTr hTs hhold
  · simp only [udivrem_knuth_320.pre, Buf, Disjoint]
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    simp (disch := decide) only [Regs.eq_get x']
    have hmn' : mm % 18446744073709551616 = mm := Nat.mod_eq_of_lt (by omega)
    simp only [h10, h11, hsp, hsub, hu5, hv3w, BitVec.toNat_ofNat, hmn']
    repeat' apply And.intro
    all_goals first
      | exact hd2 | exact htop | exact hmm5 | exact hum | exact hum1 | decide | omega | bv_omega
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · intro a ha
    simp only [udivrem_knuth_320.bufs] at ha
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at ha
    simp (disch := decide) only [Regs.eq_get x'] at ha
    simp only [h10, h11, hsp, hsub, List.mem_append] at ha
    simp only [List.mem_append]
    rcases ha with ((((h | h) | h) | h) | h)
    · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr (mem_bufWords_of_le (by decide) h))))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr (mem_bufWords_of_le (by decide) h))
    · exact Or.inr (hD _ h)
  · intro x3 m3 hpost
    obtain ⟨hq, hrem, hunc, hsaved⟩ := hpost
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at hq hrem hunc
    simp (disch := decide) only [Regs.eq_get x'] at hq hrem hunc
    simp only [h10, h11, hsp, hsub, hu5, hv3w, BitVec.toNat_ofNat] at hq hrem hunc
    have hF3 : U320Frame x m x3 m3 := by
      refine (U320Frame.mem hF hpre0 hunc).callee ?_
      intro i hi
      rw [hsaved i hi]
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
      rw [Regs.eq_get x' (by decide)]
      exact h8.symm
    rv_exec_cut 142
    refine u320_epi base x m hr x3 m3 hF3 ?_ ?_
    · rw [hV3]; exact hq
    · rw [if_neg hvne, hV3]; exact hrem

end IntxRV.Api
