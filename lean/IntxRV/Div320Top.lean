import IntxRV.Div320
import IntxRV.Api.udivrem_top1_3_320
import IntxRV.Api.udivrem_top2_3_equal_320
import IntxRV.Api.udivrem_top1_2_320
import IntxRV.Api.udivrem_top2_3_320
import IntxRV.Api.udivrem_top2_4_320

/-!
# The paths of `udivrem<320, 256>()` that call `udivrem_top1()` and `udivrem_top2()`

For v ≥ 2^192 the calls of `udivrem_top1<3>()` (`u320_top13`) and `udivrem_top2<4>()`
(`u320_top24`) by u[4] < v[3]; for v[3] = 0 and v[2] ≠ 0 the calls of `udivrem_top2<3>()`
(`u320_top23`), `udivrem_top1<2>()` (`u320_top12`) and `udivrem_top2<3, true>()` (`u320_topE`).
Each callee runs by its proof (`Reach.call_sub`) and the path ends in the epilogue (`u320_epi`).
See `IntxRV/Api/udivrem_320_256.lean`.
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

/-- The words of u of 5 words and of v of 4 words. -/
theorem words5_unfold (m : Mem) (a : BitVec 64) :
    words m a 5 = (memWord m a.toNat).toNat + 2 ^ 64 * ((memWord m (a + 8#64).toNat).toNat +
      2 ^ 64 * ((memWord m (a + 16#64).toNat).toNat + 2 ^ 64 * ((memWord m (a + 24#64).toNat).toNat +
      2 ^ 64 * (memWord m (a + 32#64).toNat).toNat))) := by
  simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
    Nat.add_zero]

/-- The values of the arguments of `udivrem_top1<3>()` in `udivrem<320, 256>()`. -/
theorem u320_top13_vals (m : Mem) (u v : BitVec 64) (hv3 : memWord m (v + 24#64).toNat ≠ 0#64)
    (hu4 : (memWord m (u + 32#64).toNat).toNat < (memWord m (v + 24#64).toNat).toNat) :
    2 ^ (64 * 3) ≤ words m v 4 ∧ words m v 4 < 2 ^ (64 * (3 + 1)) ∧
      words m u 5 / 2 ^ (64 * (3 + 1)) < words m v 4 / 2 ^ (64 * 3) := by
  have h3 : 0 < (memWord m (v + 24#64).toNat).toNat := by
    rcases Nat.eq_zero_or_pos (memWord m (v + 24#64).toNat).toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hv3
    · exact h
  rw [words4_unfold, words5_unfold]
  have := (memWord m u.toNat).isLt
  have := (memWord m (u + 8#64).toNat).isLt
  have := (memWord m (u + 16#64).toNat).isLt
  have := (memWord m (u + 24#64).toNat).isLt
  have := (memWord m (u + 32#64).toNat).isLt
  have := (memWord m v.toNat).isLt
  have := (memWord m (v + 8#64).toNat).isLt
  have := (memWord m (v + 16#64).toNat).isLt
  have := (memWord m (v + 24#64).toNat).isLt
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd] at *
  omega

set_option exponentiation.threshold 320 in
/-- The values of the arguments of `udivrem_top2<4>()` in `udivrem<320, 256>()`. -/
theorem u320_top24_vals (m : Mem) (u v : BitVec 64) (hv3 : memWord m (v + 24#64).toNat ≠ 0#64) :
    2 ^ (64 * (4 - 1)) ≤ words m v 4 ∧ words m v 4 < 2 ^ (64 * 4) ∧
      words m u 5 / 2 ^ (64 * (4 + 1)) < words m v 4 / 2 ^ (64 * (4 - 1)) + 0 := by
  have h3 : 0 < (memWord m (v + 24#64).toNat).toNat := by
    rcases Nat.eq_zero_or_pos (memWord m (v + 24#64).toNat).toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hv3
    · exact h
  rw [words4_unfold, words5_unfold]
  have := (memWord m u.toNat).isLt
  have := (memWord m (u + 8#64).toNat).isLt
  have := (memWord m (u + 16#64).toNat).isLt
  have := (memWord m (u + 24#64).toNat).isLt
  have := (memWord m (u + 32#64).toNat).isLt
  have := (memWord m v.toNat).isLt
  have := (memWord m (v + 8#64).toNat).isLt
  have := (memWord m (v + 16#64).toNat).isLt
  have := (memWord m (v + 24#64).toNat).isLt
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub] at *
  omega

/-- The values of the arguments of `udivrem_top2<3>()` and `udivrem_top2<3, true>()` in
`udivrem<320, 256>()`: v[3] = 0 and u[4] less than v[2] plus `E`. -/
theorem u320_top23_vals (m : Mem) (u v : BitVec 64) (E : Nat) (hv3 : memWord m (v + 24#64).toNat = 0#64)
    (hv2 : memWord m (v + 16#64).toNat ≠ 0#64)
    (hu4 : (memWord m (u + 32#64).toNat).toNat < (memWord m (v + 16#64).toNat).toNat + E) :
    2 ^ (64 * (3 - 1)) ≤ words m v 4 ∧ words m v 4 < 2 ^ (64 * 3) ∧
      words m u 5 / 2 ^ (64 * (3 + 1)) < words m v 4 / 2 ^ (64 * (3 - 1)) + E := by
  have h2 : 0 < (memWord m (v + 16#64).toNat).toNat := by
    rcases Nat.eq_zero_or_pos (memWord m (v + 16#64).toNat).toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hv2
    · exact h
  rw [words4_unfold, words5_unfold, hv3]
  have := (memWord m u.toNat).isLt
  have := (memWord m (u + 8#64).toNat).isLt
  have := (memWord m (u + 16#64).toNat).isLt
  have := (memWord m (u + 24#64).toNat).isLt
  have := (memWord m (u + 32#64).toNat).isLt
  have := (memWord m v.toNat).isLt
  have := (memWord m (v + 8#64).toNat).isLt
  have := (memWord m (v + 16#64).toNat).isLt
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd,
    Nat.reduceSub] at *
  omega

/-- The values of the arguments of `udivrem_top1<2>()` in `udivrem<320, 256>()`: v[3] = 0,
v[2] ≠ 0 and u[4] = u[3] = 0. -/
theorem u320_top12_vals (m : Mem) (u v : BitVec 64) (hv3 : memWord m (v + 24#64).toNat = 0#64)
    (hv2 : memWord m (v + 16#64).toNat ≠ 0#64) (hu4 : memWord m (u + 32#64).toNat = 0#64)
    (hu3 : memWord m (u + 24#64).toNat = 0#64) :
    2 ^ (64 * 2) ≤ words m v 4 ∧ words m v 4 < 2 ^ (64 * (2 + 1)) ∧
      words m u 5 / 2 ^ (64 * (2 + 1)) < words m v 4 / 2 ^ (64 * 2) := by
  have h2 : 0 < (memWord m (v + 16#64).toNat).toNat := by
    rcases Nat.eq_zero_or_pos (memWord m (v + 16#64).toNat).toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hv2
    · exact h
  rw [words4_unfold, words5_unfold, hv3, hu4, hu3]
  have := (memWord m u.toNat).isLt
  have := (memWord m (u + 8#64).toNat).isLt
  have := (memWord m (u + 16#64).toNat).isLt
  have := (memWord m v.toNat).isLt
  have := (memWord m (v + 8#64).toNat).isLt
  have := (memWord m (v + 16#64).toNat).isLt
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd] at *
  omega

/-- The path of `udivrem<320, 256>()` for v ≥ 2^192 and u[4] < v[3] from 12: the call of
`udivrem_top1<3>()`. -/
theorem u320_top13 {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hb3 : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0) (hpre : udivrem_320_256.pre x m)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64)
    (hTr : (x.get 10#5).toNat + 72 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hTs : (x.get 2#5 - 336#64).toNat + 336 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 336#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hD : ∀ a ∈ bufWords T 256, a ∈ D)
    (hT5 : pcAt (pcAt base 1457) 64 + ((hi5 ++ 0x000#12).signExtend 64 + lo5.signExtend 64) = T)
    (x' : Regs) (m' : Mem) (hF : U320Frame x m x' m') (h10 : x'.get 10#5 = x.get 10#5)
    (h11 : x'.get 11#5 = x.get 11#5) (h13 : x'.get 13#5 = x.get 12#5)
    (hv3 : memWord m (x.get 12#5 + 24#64).toNat ≠ 0#64)
    (hu4 : (memWord m (x.get 11#5 + 32#64).toNat).toNat <
      (memWord m (x.get 12#5 + 24#64).toNat).toNat) :
    Reach (u320Bufs x D) P320 base (pcAt base 12) x' m' (x.get 1#5)
      (udivrem_320_256.post x m) := by
  -- `omega` and `subst_vars` do not see the address of the table.
  replace hT5 := PLift.up hT5
  have hpre0 := hpre
  simp only [udivrem_320_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr⟩ := hpre
  have hv := u320_top13_vals m (x.get 11#5) (x.get 12#5) hv3 hu4
  have hvne : words m (x.get 12#5) 4 ≠ 0 := by
    have h := hv.1; intro h0; rw [h0] at h; exact absurd h (by norm_num)
  have hsp := hF.1
  rw [← regs_set_of_get' (by decide) h13]
  rv_exec_cut 1457
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  rw [show pcAt base 13 + 4096#64 + BitVec.signExtend 64 1680#12 = pcAt base 1457 by
      simp only [pcAt, BitVec.reduceSignExtend]; bv_omega,
    update_aligned (pcAt_aligned hb3 1457)]
  have hu5 := hF.words_u hpre0 5 le_rfl
  have hv4 := hF.words_v hpre0 4 le_rfl
  have hsub : x.get 2#5 + 18446744073709551568#64 - 16#64 = x.get 2#5 - 64#64 := by bv_omega
  refine Reach.call_sub (r := 15) (p320_eq ▸ udivrem_320_256_progAt_udivrem_top1_3_320_in)
    p320_length
    (udivrem_top1_3_320.reach hi5 lo5 (pcAt base 1457) T _ _ hT5.down hw ?_ ?_ ?_) ?_ ?_ ?_
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    exact pcAt_aligned hb3 15
  · exact hF.holdsData hw hTr hTs hhold
  · simp only [udivrem_top1_3_320.pre, Buf, Disjoint]
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    simp (disch := decide) only [Regs.eq_get x']
    simp only [h10, h11, hsp, hsub, hu5, hv4]
    repeat' apply And.intro
    all_goals first | exact hv.1 | exact hv.2.1 | exact hv.2.2 | omega | bv_omega
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · intro a ha
    simp only [udivrem_top1_3_320.bufs] at ha
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at ha
    simp (disch := decide) only [Regs.eq_get x'] at ha
    simp only [h10, h11, hsp, hsub, List.mem_append] at ha
    simp only [List.mem_append]
    rcases ha with ((((h | h) | h) | h) | h)
    · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    · exact Or.inl (Or.inl (Or.inr h))
    · rw [show x.get 2#5 - 64#64 = x.get 2#5 - 336#64 + BitVec.ofNat 64 (8 * 34) by bv_omega] at h
      exact Or.inl (Or.inr (mem_bufWords_of_offset (by decide) h))
    · exact Or.inr (hD _ h)
  · intro x3 m3 hpost
    obtain ⟨hq, hrem, hunc, hsaved⟩ := hpost
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at hq hrem hunc
    simp (disch := decide) only [Regs.eq_get x'] at hq hrem hunc
    simp only [h10, h11, hsp, hsub, hu5, hv4] at hq hrem hunc
    have e64 : (x.get 2#5 - 64#64).toNat = (x.get 2#5 - 336#64).toNat + 272 := by bv_omega
    have hF3 : U320Frame x m x3 m3 := by
      refine (U320Frame.mem hF hpre0 (fun k hk1 hk2 => hunc k hk1 (by omega))).callee ?_
      intro i hi
      rw [hsaved i hi]
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    rv_exec_cut 142
    exact u320_epi base x m hr x3 m3 hF3 hq (by rw [if_neg hvne]; exact hrem)

/-- The path of `udivrem<320, 256>()` for v ≥ 2^192 and u[4] ≥ v[3] from 25: the call of
`udivrem_top2<4>()`. -/
theorem u320_top24 {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hb3 : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0) (hpre : udivrem_320_256.pre x m)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64)
    (hTr : (x.get 10#5).toNat + 72 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hTs : (x.get 2#5 - 336#64).toNat + 336 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 336#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hD : ∀ a ∈ bufWords T 256, a ∈ D)
    (hT8 : pcAt (pcAt base 2273) 84 + ((hi8 ++ 0x000#12).signExtend 64 + lo8.signExtend 64) = T)
    (x' : Regs) (m' : Mem) (hF : U320Frame x m x' m') (h10 : x'.get 10#5 = x.get 10#5)
    (h11 : x'.get 11#5 = x.get 11#5) (h13 : x'.get 13#5 = x.get 12#5)
    (hv3 : memWord m (x.get 12#5 + 24#64).toNat ≠ 0#64) :
    Reach (u320Bufs x D) P320 base (pcAt base 25) x' m' (x.get 1#5)
      (udivrem_320_256.post x m) := by
  -- `omega` and `subst_vars` do not see the address of the table.
  replace hT8 := PLift.up hT8
  have hpre0 := hpre
  simp only [udivrem_320_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr⟩ := hpre
  have hv := u320_top24_vals m (x.get 11#5) (x.get 12#5) hv3
  have hvne : words m (x.get 12#5) 4 ≠ 0 := by
    have h := hv.1; intro h0; rw [h0] at h; exact absurd h (by norm_num)
  have hsp := hF.1
  rw [← regs_set_of_get' (by decide) h13]
  rv_exec_cut 2273
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  rw [show pcAt base 26 + 8192#64 + BitVec.signExtend 64 796#12 = pcAt base 2273 by
      simp only [pcAt, BitVec.reduceSignExtend]; bv_omega,
    update_aligned (pcAt_aligned hb3 2273)]
  have hu5 := hF.words_u hpre0 5 le_rfl
  have hv4 := hF.words_v hpre0 4 le_rfl
  have hsub : x.get 2#5 + 18446744073709551568#64 - 32#64 = x.get 2#5 - 80#64 := by bv_omega
  refine Reach.call_sub (r := 28) (p320_eq ▸ udivrem_320_256_progAt_udivrem_top2_4_320_in)
    p320_length
    (udivrem_top2_4_320.reach hi8 lo8 (pcAt base 2273) T _ _ hT8.down hw ?_ ?_ ?_ ?_) ?_ ?_ ?_
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    exact pcAt_aligned hb3 28
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    rw [hsp, hsub]
    bv_omega
  · exact hF.holdsData hw hTr hTs hhold
  · simp only [udivrem_top2_4_320.pre, Buf, Disjoint]
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    simp (disch := decide) only [Regs.eq_get x']
    simp only [h10, h11, hsp, hsub, hu5, hv4]
    repeat' apply And.intro
    all_goals first | exact hv.1 | exact hv.2.1 | exact hv.2.2 | omega | bv_omega
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · intro a ha
    simp only [udivrem_top2_4_320.bufs] at ha
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at ha
    simp (disch := decide) only [Regs.eq_get x'] at ha
    simp only [h10, h11, hsp, hsub, List.mem_append] at ha
    simp only [List.mem_append]
    rcases ha with ((((h | h) | h) | h) | h)
    · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    · exact Or.inl (Or.inl (Or.inr h))
    · rw [show x.get 2#5 - 80#64 = x.get 2#5 - 336#64 + BitVec.ofNat 64 (8 * 32) by bv_omega] at h
      exact Or.inl (Or.inr (mem_bufWords_of_offset (by decide) h))
    · exact Or.inr (hD _ h)
  · intro x3 m3 hpost
    obtain ⟨hq, hrem, hunc, hsaved⟩ := hpost
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at hq hrem hunc
    simp (disch := decide) only [Regs.eq_get x'] at hq hrem hunc
    simp only [h10, h11, hsp, hsub, hu5, hv4] at hq hrem hunc
    have e64 : (x.get 2#5 - 80#64).toNat = (x.get 2#5 - 336#64).toNat + 256 := by bv_omega
    have hF3 : U320Frame x m x3 m3 := by
      refine (U320Frame.mem hF hpre0 (fun k hk1 hk2 => hunc k hk1 (by omega))).callee ?_
      intro i hi
      rw [hsaved i hi]
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    rv_exec_cut 142
    exact u320_epi base x m hr x3 m3 hF3 hq (by rw [if_neg hvne]; exact hrem)

/-- The path of `udivrem<320, 256>()` for v[3] = 0, u[4] < v[2] and u[4] or u[3] not 0 from 21:
the call of `udivrem_top2<3>()`. -/
theorem u320_top23 {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hb3 : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0) (hpre : udivrem_320_256.pre x m)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64)
    (hTr : (x.get 10#5).toNat + 72 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hTs : (x.get 2#5 - 336#64).toNat + 336 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 336#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hD : ∀ a ∈ bufWords T 256, a ∈ D)
    (hT6 : pcAt (pcAt base 1661) 87 + ((hi6 ++ 0x000#12).signExtend 64 + lo6.signExtend 64) = T)
    (x' : Regs) (m' : Mem) (hF : U320Frame x m x' m') (h10 : x'.get 10#5 = x.get 10#5)
    (h11 : x'.get 11#5 = x.get 11#5) (h13 : x'.get 13#5 = x.get 12#5)
    (hv3 : memWord m (x.get 12#5 + 24#64).toNat = 0#64)
    (hv2 : memWord m (x.get 12#5 + 16#64).toNat ≠ 0#64)
    (hu4 : (memWord m (x.get 11#5 + 32#64).toNat).toNat <
      (memWord m (x.get 12#5 + 16#64).toNat).toNat) :
    Reach (u320Bufs x D) P320 base (pcAt base 21) x' m' (x.get 1#5)
      (udivrem_320_256.post x m) := by
  -- `omega` and `subst_vars` do not see the address of the table.
  replace hT6 := PLift.up hT6
  have hpre0 := hpre
  simp only [udivrem_320_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr⟩ := hpre
  have hv := u320_top23_vals m (x.get 11#5) (x.get 12#5) 0 hv3 hv2 (by omega)
  have hvne : words m (x.get 12#5) 4 ≠ 0 := by
    have h := hv.1; intro h0; rw [h0] at h; exact absurd h (by norm_num)
  have hsp := hF.1
  rw [← regs_set_of_get' (by decide) h13]
  rv_exec_cut 1661
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  rw [show pcAt base 22 + 8192#64 + BitVec.signExtend 64 2460#12 = pcAt base 1661 by
      simp only [pcAt, BitVec.reduceSignExtend]; bv_omega,
    update_aligned (pcAt_aligned hb3 1661)]
  have hu5 := hF.words_u hpre0 5 le_rfl
  have hv4 := hF.words_v hpre0 4 le_rfl
  have hsub : x.get 2#5 + 18446744073709551568#64 - 32#64 = x.get 2#5 - 80#64 := by bv_omega
  refine Reach.call_sub (r := 24) (p320_eq ▸ udivrem_320_256_progAt_udivrem_top2_3_320_in)
    p320_length
    (udivrem_top2_3_320.reach hi6 lo6 (pcAt base 1661) T _ _ hT6.down hw ?_ ?_ ?_ ?_) ?_ ?_ ?_
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    exact pcAt_aligned hb3 24
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    rw [hsp, hsub]
    bv_omega
  · exact hF.holdsData hw hTr hTs hhold
  · simp only [udivrem_top2_3_320.pre, Buf, Disjoint]
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    simp (disch := decide) only [Regs.eq_get x']
    simp only [h10, h11, hsp, hsub, hu5, hv4]
    repeat' apply And.intro
    all_goals first | exact hv.1 | exact hv.2.1 | exact hv.2.2 | omega | bv_omega
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · intro a ha
    simp only [udivrem_top2_3_320.bufs] at ha
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at ha
    simp (disch := decide) only [Regs.eq_get x'] at ha
    simp only [h10, h11, hsp, hsub, List.mem_append] at ha
    simp only [List.mem_append]
    rcases ha with ((((h | h) | h) | h) | h)
    · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    · exact Or.inl (Or.inl (Or.inr h))
    · rw [show x.get 2#5 - 80#64 = x.get 2#5 - 336#64 + BitVec.ofNat 64 (8 * 32) by bv_omega] at h
      exact Or.inl (Or.inr (mem_bufWords_of_offset (by decide) h))
    · exact Or.inr (hD _ h)
  · intro x3 m3 hpost
    obtain ⟨hq, hrem, hunc, hsaved⟩ := hpost
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at hq hrem hunc
    simp (disch := decide) only [Regs.eq_get x'] at hq hrem hunc
    simp only [h10, h11, hsp, hsub, hu5, hv4] at hq hrem hunc
    have e64 : (x.get 2#5 - 80#64).toNat = (x.get 2#5 - 336#64).toNat + 256 := by bv_omega
    have hF3 : U320Frame x m x3 m3 := by
      refine (U320Frame.mem hF hpre0 (fun k hk1 hk2 => hunc k hk1 (by omega))).callee ?_
      intro i hi
      rw [hsaved i hi]
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    rv_exec_cut 142
    exact u320_epi base x m hr x3 m3 hF3 hq (by rw [if_neg hvne]; exact hrem)

/-- The path of `udivrem<320, 256>()` for v[3] = 0, v[2] ≠ 0, u[4] = u[3] = 0 and u[2] ≥ v[2] from
37: the call of `udivrem_top1<2>()`. -/
theorem u320_top12 {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hb3 : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0) (hpre : udivrem_320_256.pre x m)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64)
    (hTr : (x.get 10#5).toNat + 72 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hTs : (x.get 2#5 - 336#64).toNat + 336 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 336#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hD : ∀ a ∈ bufWords T 256, a ∈ D)
    (hT4 : pcAt (pcAt base 1275) 65 + ((hi4 ++ 0x000#12).signExtend 64 + lo4.signExtend 64) = T)
    (x' : Regs) (m' : Mem) (hF : U320Frame x m x' m') (h10 : x'.get 10#5 = x.get 10#5)
    (h11 : x'.get 11#5 = x.get 11#5) (h13 : x'.get 13#5 = x.get 12#5)
    (hv3 : memWord m (x.get 12#5 + 24#64).toNat = 0#64)
    (hv2 : memWord m (x.get 12#5 + 16#64).toNat ≠ 0#64)
    (hu4 : memWord m (x.get 11#5 + 32#64).toNat = 0#64)
    (hu3 : memWord m (x.get 11#5 + 24#64).toNat = 0#64) :
    Reach (u320Bufs x D) P320 base (pcAt base 37) x' m' (x.get 1#5)
      (udivrem_320_256.post x m) := by
  -- `omega` and `subst_vars` do not see the address of the table.
  replace hT4 := PLift.up hT4
  have hpre0 := hpre
  simp only [udivrem_320_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr⟩ := hpre
  have hv := u320_top12_vals m (x.get 11#5) (x.get 12#5) hv3 hv2 hu4 hu3
  have hvne : words m (x.get 12#5) 4 ≠ 0 := by
    have h := hv.1; intro h0; rw [h0] at h; exact absurd h (by norm_num)
  have hsp := hF.1
  rw [← regs_set_of_get' (by decide) h13]
  rv_exec_cut 1275
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  rw [show pcAt base 38 + 4096#64 + BitVec.signExtend 64 852#12 = pcAt base 1275 by
      simp only [pcAt, BitVec.reduceSignExtend]; bv_omega,
    update_aligned (pcAt_aligned hb3 1275)]
  have hu5 := hF.words_u hpre0 5 le_rfl
  have hv4 := hF.words_v hpre0 4 le_rfl
  refine Reach.call_sub (r := 40) (p320_eq ▸ udivrem_320_256_progAt_udivrem_top1_2_320_in)
    p320_length
    (udivrem_top1_2_320.reach hi4 lo4 (pcAt base 1275) T _ _ hT4.down hw ?_ ?_ ?_) ?_ ?_ ?_
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    exact pcAt_aligned hb3 40
  · exact hF.holdsData hw hTr hTs hhold
  · simp only [udivrem_top1_2_320.pre, Buf, Disjoint]
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    simp (disch := decide) only [Regs.eq_get x']
    simp only [h10, h11, hu5, hv4]
    repeat' apply And.intro
    all_goals first | exact hv.1 | exact hv.2.1 | exact hv.2.2 | omega | bv_omega
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · intro a ha
    simp only [udivrem_top1_2_320.bufs] at ha
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at ha
    simp (disch := decide) only [Regs.eq_get x'] at ha
    simp only [h10, h11, List.mem_append] at ha
    simp only [List.mem_append]
    rcases ha with (((h | h) | h) | h)
    · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inr (hD _ h)
  · intro x3 m3 hpost
    obtain ⟨hq, hrem, hunc, hsaved⟩ := hpost
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at hq hrem hunc
    simp (disch := decide) only [Regs.eq_get x'] at hq hrem hunc
    simp only [h10, h11, hu5, hv4] at hq hrem hunc
    have hF3 : U320Frame x m x3 m3 := by
      refine (U320Frame.mem hF hpre0 (fun k hk1 _ => hunc k hk1)).callee ?_
      intro i hi
      rw [hsaved i hi]
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    rv_exec_cut 142
    exact u320_epi base x m hr x3 m3 hF3 hq (by rw [if_neg hvne]; exact hrem)

/-- The path of `udivrem<320, 256>()` for v[3] = 0, v[2] ≠ 0 and u[4] = v[2] from 31: the call
of `udivrem_top2<3, true>()`. -/
theorem u320_topE {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hb3 : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0) (hpre : udivrem_320_256.pre x m)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64)
    (hTr : (x.get 10#5).toNat + 72 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hTs : (x.get 2#5 - 336#64).toNat + 336 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 336#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hD : ∀ a ∈ bufWords T 256, a ∈ D)
    (hT7 : pcAt (pcAt base 1948) 107 + ((hi7 ++ 0x000#12).signExtend 64 + lo7.signExtend 64) = T)
    (x' : Regs) (m' : Mem) (hF : U320Frame x m x' m') (h10 : x'.get 10#5 = x.get 10#5)
    (h11 : x'.get 11#5 = x.get 11#5) (h13 : x'.get 13#5 = x.get 12#5)
    (hv3 : memWord m (x.get 12#5 + 24#64).toNat = 0#64)
    (hv2 : memWord m (x.get 12#5 + 16#64).toNat ≠ 0#64)
    (hu4 : memWord m (x.get 11#5 + 32#64).toNat = memWord m (x.get 12#5 + 16#64).toNat) :
    Reach (u320Bufs x D) P320 base (pcAt base 31) x' m' (x.get 1#5)
      (udivrem_320_256.post x m) := by
  -- `omega` and `subst_vars` do not see the address of the table.
  replace hT7 := PLift.up hT7
  have hpre0 := hpre
  simp only [udivrem_320_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr⟩ := hpre
  have hv := u320_top23_vals m (x.get 11#5) (x.get 12#5) 1 hv3 hv2 (by rw [hu4]; omega)
  have hvne : words m (x.get 12#5) 4 ≠ 0 := by
    have h := hv.1; intro h0; rw [h0] at h; exact absurd h (by norm_num)
  have hsp := hF.1
  rw [← regs_set_of_get' (by decide) h13]
  rv_exec_cut 1948
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  rw [show pcAt base 32 + 8192#64 + BitVec.signExtend 64 3568#12 = pcAt base 1948 by
      simp only [pcAt, BitVec.reduceSignExtend]; bv_omega,
    update_aligned (pcAt_aligned hb3 1948)]
  have hu5 := hF.words_u hpre0 5 le_rfl
  have hv4 := hF.words_v hpre0 4 le_rfl
  have hsub : x.get 2#5 + 18446744073709551568#64 - 48#64 = x.get 2#5 - 96#64 := by bv_omega
  refine Reach.call_sub (r := 34) (p320_eq ▸ udivrem_320_256_progAt_udivrem_top2_3_equal_320_in)
    p320_length
    (udivrem_top2_3_equal_320.reach hi7 lo7 (pcAt base 1948) T _ _ hT7.down hw ?_ ?_ ?_ ?_) ?_ ?_ ?_
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    exact pcAt_aligned hb3 34
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    rw [hsp, hsub]
    bv_omega
  · exact hF.holdsData hw hTr hTs hhold
  · simp only [udivrem_top2_3_equal_320.pre, Buf, Disjoint]
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    simp (disch := decide) only [Regs.eq_get x']
    simp only [h10, h11, hsp, hsub, hu5, hv4]
    repeat' apply And.intro
    all_goals first | exact hv.1 | exact hv.2.1 | exact hv.2.2 | omega | bv_omega
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · intro a ha
    simp only [udivrem_top2_3_equal_320.bufs] at ha
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at ha
    simp (disch := decide) only [Regs.eq_get x'] at ha
    simp only [h10, h11, hsp, hsub, List.mem_append] at ha
    simp only [List.mem_append]
    rcases ha with ((((h | h) | h) | h) | h)
    · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    · exact Or.inl (Or.inl (Or.inr h))
    · rw [show x.get 2#5 - 96#64 = x.get 2#5 - 336#64 + BitVec.ofNat 64 (8 * 30) by bv_omega] at h
      exact Or.inl (Or.inr (mem_bufWords_of_offset (by decide) h))
    · exact Or.inr (hD _ h)
  · intro x3 m3 hpost
    obtain ⟨hq, hrem, hunc, hsaved⟩ := hpost
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at hq hrem hunc
    simp (disch := decide) only [Regs.eq_get x'] at hq hrem hunc
    simp only [h10, h11, hsp, hsub, hu5, hv4] at hq hrem hunc
    have e64 : (x.get 2#5 - 96#64).toNat = (x.get 2#5 - 336#64).toNat + 240 := by bv_omega
    have hF3 : U320Frame x m x3 m3 := by
      refine (U320Frame.mem hF hpre0 (fun k hk1 hk2 => hunc k hk1 (by omega))).callee ?_
      intro i hi
      rw [hsaved i hi]
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    rv_exec_cut 142
    exact u320_epi base x m hr x3 m3 hF3 hq (by rw [if_neg hvne]; exact hrem)

end IntxRV.Api
