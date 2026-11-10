import Intx.Proofs.Uint
import Intx.Proofs.DivMath
import Intx.Model.Div
set_option warningAsError true
/-!
# Proofs: the divisions

What `div_wide_x86()`, `reciprocal_2by1()` and `udivrem_2by1()` of `Intx.Model` compute, on
both code paths of `Platform`. Without the `div` instruction, `internal::reciprocal()` computes
the reciprocal `floor((2^128 - 1) / d) - 2^64` exactly and `udivrem_2by1(u, d, v)` divides with it
(Möller and Granlund, Theorems 1 and 2, in `Intx.Proofs.DivMath`).
-/

namespace Intx.Model

theorem div_wide_x86_spec (hi lo d : Word) (h : hi < d) :
    ∃ q r, div_wide_x86 hi lo d = some (q, r) ∧
      q.toNat = (hi.toNat * 2 ^ 64 + lo.toNat) / d.toNat ∧
      r.toNat = (hi.toNat * 2 ^ 64 + lo.toNat) % d.toNat := by
  have hlt := UInt64.lt_iff_toNat_lt.mp h
  have hl := lo.toNat_lt
  have hdl := d.toNat_lt
  have hd : 0 < d.toNat := by omega
  refine ⟨UInt64.ofNat ((hi.toNat * 2 ^ 64 + lo.toNat) / d.toNat),
    UInt64.ofNat ((hi.toNat * 2 ^ 64 + lo.toNat) % d.toNat), ?_, ?_, ?_⟩
  · simp only [div_wide_x86, require_pos h]
    rfl
  · rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt]
    rw [Nat.div_lt_iff_lt_mul hd]
    nlinarith
  · rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ hd) hdl)]

/-- The entry `i` of `RECIPROCAL_TABLE`. -/
theorem RECIPROCAL_TABLE_getElem (i : Nat) (hi : i < 256) :
    RECIPROCAL_TABLE[i] = ((523520 / (i + 256)).toUInt32 * (523520 / (i + 256)).toUInt32,
      ((523520 / (i + 256)).toUInt32 <<< 11) - 1) := by
  unfold RECIPROCAL_TABLE
  apply forIn'_rco0_id (P := fun t : Vector (UInt32 × UInt32) 256 => t[i] = _)
    (I := fun k t => ∀ j (hj : j < 256), j < k → t[j] = ((523520 / (j + 256)).toUInt32 *
      (523520 / (j + 256)).toUInt32, ((523520 / (j + 256)).toUInt32 <<< 11) - 1))
  · intro j hj h; omega
  · intro j b hj hm hI
    refine ⟨_, rfl, ?_⟩
    intro j' hj' hlt
    rw [Vector.getElem_set]
    split_ifs with h
    · subst h; rfl
    · exact hI j' hj' (by omega)
  · intro b hb; exact hb i hi hi

/-- The table entry `i`: `v0 = floor(523520 / (i + 256))` in `[1024, 2045]`, `v0 * v0` and
`2^11 * v0 - 1`. -/
theorem reciprocal_table_entry (i : Nat) (hi : i < 256) :
    1024 ≤ 523520 / (i + 256) ∧ 523520 / (i + 256) ≤ 2045 ∧
      RECIPROCAL_TABLE[i].1.toNat = 523520 / (i + 256) * (523520 / (i + 256)) ∧
      RECIPROCAL_TABLE[i].2.toNat = 2 ^ 11 * (523520 / (i + 256)) - 1 := by
  have h1 : 523520 / 511 ≤ 523520 / (i + 256) := Nat.div_le_div_left (by omega) (by omega)
  have h2 : 523520 / (i + 256) ≤ 523520 / 256 := Nat.div_le_div_left (by omega) (by omega)
  rw [RECIPROCAL_TABLE_getElem i hi]
  generalize 523520 / (i + 256) = v0 at h1 h2 ⊢
  norm_num at h1 h2
  have hv : v0.toUInt32.toNat = v0 := by rw [UInt32.toNat_ofNat']; omega
  have hsq : v0 * v0 ≤ 2045 * 2045 := Nat.mul_le_mul h2 h2
  have hs : (v0.toUInt32 <<< 11).toNat = 2 ^ 11 * v0 := by
    rw [UInt32.toNat_shiftLeft, hv, Nat.shiftLeft_eq, show (11 : UInt32).toNat % 32 = 11 from rfl]
    omega
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [UInt32.toNat_mul, hv]; omega
  · rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by rw [hs]; show 1 ≤ _; omega)), hs]
    rfl

theorem and_top_ne_zero (d : Word) (hd : 2 ^ 63 ≤ d.toNat) : d &&& 0x8000000000000000 ≠ 0 := by
  intro h
  have h1 := congrArg UInt64.toNat h
  have := d.toNat_lt
  rw [UInt64.toNat_and, show (0x8000000000000000 : Word).toNat = 2 ^ 63 from rfl, Nat.and_two_pow,
    Nat.testBit_eq_decide_div_mod_eq, decide_eq_true (by omega)] at h1
  simp at h1

theorem reciprocal_approx_spec (d : Word) (hd : 2 ^ 63 ≤ d.toNat) :
    ∃ v2, reciprocal_approx d = some v2 ∧ v2.toNat * d.toNat < 2 ^ 97 ∧
      2 ^ 97 < v2.toNat * d.toNat + 873 * 2 ^ 53 + d.toNat + 2 ^ 24 := by
  have hdl := d.toNat_lt
  have h9 : (d >>> 55).toNat = d.toNat / 2 ^ 55 := by
    rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; rfl
  obtain ⟨k, hk⟩ : ∃ k, d.toNat / 2 ^ 55 = k + 256 := ⟨d.toNat / 2 ^ 55 - 256, by omega⟩
  have hi : k < 256 := by omega
  have h9i : ((d >>> 55) - 256).toNat = k := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [h9]; show 256 ≤ _; omega)),
      h9, hk]
    show k + 256 - 256 = k
    omega
  obtain ⟨hv0a, hv0b, he1, he2⟩ := reciprocal_table_entry k hi
  have hidx : RECIPROCAL_TABLE[((d >>> 55) - 256).toNat]? = some RECIPROCAL_TABLE[k] := by
    rw [h9i]; exact Vector.getElem?_eq_getElem hi
  rw [← hk] at hv0a hv0b he1 he2
  generalize RECIPROCAL_TABLE[k] = t at hidx he1 he2
  obtain ⟨v0v0, v0s⟩ := t
  unfold reciprocal_approx
  simp only [require_pos (and_top_ne_zero d hd), Option.bind_eq_bind, Option.bind_some, hidx]
  refine ⟨_, rfl, ?_⟩
  simp only at he1 he2
  -- d40 = floor(d / 2^24) + 1 and the table entry v0 = floor(523520 / d9) with d9 = floor(d / 2^55).
  have h24 : (d >>> 24 + 1).toNat = d.toNat / 2 ^ 24 + 1 := by
    rw [UInt64.toNat_add, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    show (d.toNat / 2 ^ 24 + 1) % 2 ^ 64 = _
    omega
  generalize d >>> 24 + 1 = d40 at h24 ⊢
  generalize hv0 : 523520 / (d.toNat / 2 ^ 55) = v0 at hv0a hv0b he1 he2
  obtain ⟨h0a, h0b⟩ := recip_e0 (d.toNat / 2 ^ 55) (d.toNat / 2 ^ 24 % 2 ^ 31 + 1) (by omega)
    (by omega) (by omega) (by omega)
  rw [hv0, show 2 ^ 31 * (d.toNat / 2 ^ 55) + (d.toNat / 2 ^ 24 % 2 ^ 31 + 1) =
    d.toNat / 2 ^ 24 + 1 by omega, ← h24] at h0a h0b
  obtain ⟨h1a, h1b, h1c⟩ := recip_e1 v0 d40.toNat h0a h0b (by omega) (by omega)
  -- v1.
  have hm : (v0v0.toUInt64 * d40).toNat = v0 ^ 2 * d40.toNat := by
    rw [UInt64.toNat_mul, UInt32.toNat_toUInt64, he1, ← sq]
    apply Nat.mod_eq_of_lt
    have : v0 ^ 2 ≤ 2045 ^ 2 := Nat.pow_le_pow_left hv0b 2
    have : v0 ^ 2 * d40.toNat ≤ 2045 ^ 2 * 2 ^ 40 := Nat.mul_le_mul this (by omega)
    omega
  have hsh : ((v0v0.toUInt64 * d40) >>> 40).toNat = v0 ^ 2 * d40.toNat / 2 ^ 40 := by
    rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, hm]; rfl
  have hv1 : (v0s.toUInt64 - (v0v0.toUInt64 * d40) >>> 40).toNat =
      2 ^ 11 * v0 - 1 - v0 ^ 2 * d40.toNat / 2 ^ 40 := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr
      (by rw [hsh, UInt32.toNat_toUInt64, he2]; omega)), hsh, UInt32.toNat_toUInt64, he2]
  generalize v0s.toUInt64 - (v0v0.toUInt64 * d40) >>> 40 = v1 at hv1 ⊢
  generalize 2 ^ 11 * v0 - 1 - v0 ^ 2 * d40.toNat / 2 ^ 40 = V1 at hv1 h1b h1c
  obtain ⟨h2a, h2b⟩ := recip_e2 V1 d40.toNat d.toNat h1b h1c (by omega) hd hdl
  -- v2.
  have hV1 : V1 < 2 ^ 21 := by
    by_contra h
    have : 2 ^ 21 * d40.toNat ≤ V1 * d40.toNat := Nat.mul_le_mul_right _ (by omega)
    omega
  have hm1 : (v1 * d40).toNat = V1 * d40.toNat := by
    rw [UInt64.toNat_mul, hv1]; apply Nat.mod_eq_of_lt; omega
  have hs1 : (1152921504606846976 - v1 * d40).toNat = 2 ^ 60 - V1 * d40.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr
      (by rw [hm1]; show _ ≤ 2 ^ 60; omega)), hm1]
    rfl
  have hm2 : (v1 * (1152921504606846976 - v1 * d40)).toNat = V1 * (2 ^ 60 - V1 * d40.toNat) := by
    rw [UInt64.toNat_mul, hv1, hs1]; apply Nat.mod_eq_of_lt
    have : V1 * (2 ^ 60 - V1 * d40.toNat) ≤ 2 ^ 21 * (29 * 2 ^ 38) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have hv2 : (v1 <<< 13 + (v1 * (1152921504606846976 - v1 * d40)) >>> 47).toNat =
      2 ^ 13 * V1 + V1 * (2 ^ 60 - V1 * d40.toNat) / 2 ^ 47 := by
    have : V1 * (2 ^ 60 - V1 * d40.toNat) ≤ 2 ^ 21 * (29 * 2 ^ 38) :=
      Nat.mul_le_mul (by omega) (by omega)
    rw [UInt64.toNat_add, UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight, hm2, hv1,
      Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    show (V1 * 2 ^ 13 % 2 ^ 64 + V1 * (2 ^ 60 - V1 * d40.toNat) / 2 ^ 47) % 2 ^ 64 = _
    omega
  rw [hv2]
  exact ⟨h2a, h2b⟩

theorem reciprocal_spec (d : Word) (hd : 2 ^ 63 ≤ d.toNat) :
    ∃ v, reciprocal d = some v ∧ (2 ^ 64 + v.toNat) * d.toNat < 2 ^ 128 ∧
      2 ^ 128 ≤ (2 ^ 64 + v.toNat + 1) * d.toNat := by
  have hdl := d.toNat_lt
  obtain ⟨v2, hv2, h2a, h2b⟩ := reciprocal_approx_spec d hd
  unfold reciprocal
  simp (config := { zeta := false }) only [Option.bind_eq_bind]
  lift_lets
  intro d1 d1_odd d63
  simp (config := { zeta := false }) only [show reciprocal_approx d1 = some v2 from hv2,
    Option.bind_some]
  lift_lets
  intro e v3 p1
  refine ⟨_, rfl, ?_⟩
  have hd1 : d = d1 := rfl
  clear_value d1
  subst hd1
  have hV2 : v2.toNat < 2 ^ 34 := by
    by_contra h
    have : 2 ^ 34 * d.toNat ≤ v2.toNat * d.toNat := Nat.mul_le_mul_right _ (by omega)
    omega
  -- e = floor(e2 / 2) with e2 = 2^97 - v2 * d.
  have hodd : d1_odd.toNat = d.toNat % 2 := by
    show (d &&& 1).toNat = _
    rw [UInt64.toNat_and, show (1 : Word).toNat = 1 from rfl, Nat.and_one_is_mod]
  have hd63 : d63.toNat = d.toNat / 2 + d.toNat % 2 := by
    show (d >>> 1 + d1_odd).toNat = _
    rw [UInt64.toNat_add, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, hodd,
      show (1 : Word).toNat % 64 = 1 from rfl]
    omega
  clear_value d1_odd d63
  have hmask : (v2 >>> 1 &&& 0 - d1_odd).toNat = v2.toNat / 2 * (d.toNat % 2) := by
    rcases Nat.mod_two_eq_zero_or_one d.toNat with h | h
    · have : d1_odd = 0 := UInt64.toNat_inj.mp (by rw [hodd, h]; rfl)
      rw [this, h, UInt64.sub_self, UInt64.and_zero]
      rfl
    · have : d1_odd = 1 := UInt64.toNat_inj.mp (by rw [hodd, h]; rfl)
      rw [this, h, UInt64.toNat_and, show ((0 : Word) - 1).toNat = 2 ^ 64 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow,
        show (1 : Word).toNat % 64 = 1 from rfl]
      omega
  have hXY : 2 * (v2.toNat * (d.toNat / 2 + d.toNat % 2)) =
      v2.toNat * d.toNat + v2.toNat * (d.toNat % 2) := by
    have : 2 * (d.toNat / 2 + d.toNat % 2) = d.toNat + d.toNat % 2 := by omega
    calc 2 * (v2.toNat * (d.toNat / 2 + d.toNat % 2)) =
        v2.toNat * (2 * (d.toNat / 2 + d.toNat % 2)) := by ring
      _ = _ := by rw [this, Nat.mul_add]
  have he : e.toNat = (2 ^ 97 - v2.toNat * d.toNat) / 2 := by
    show ((v2 >>> 1 &&& 0 - d1_odd) - v2 * d63).toNat = _
    rw [UInt64.toNat_sub, UInt64.toNat_mul, hmask, hd63]
    rcases Nat.mod_two_eq_zero_or_one d.toNat with h | h <;> rw [h] at hXY ⊢ <;>
      simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero] at hXY ⊢ <;> omega
  clear_value e
  -- v3 = 2^31 * v2 + floor(v2 * e / 2^65) - 2^64.
  obtain ⟨h3a, h3b, h3c, h3d⟩ := recip_e3 v2.toNat d.toNat h2a h2b hd hdl
  rw [← he] at h3a h3b h3c h3d
  have hv3 : v3.toNat = 2 ^ 31 * v2.toNat + v2.toNat * e.toNat / 2 ^ 65 - 2 ^ 64 := by
    show ((umul v2 e)[1] >>> 1 + v2 <<< 31).toNat = _
    have hu := umul_spec v2 e
    have := (umul v2 e).lo.toNat_lt
    rw [U128.getElem_one, UInt64.toNat_add, UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft,
      Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, show (1 : Word).toNat % 64 = 1 from rfl,
      show (31 : Word).toNat % 64 = 31 from rfl]
    omega
  clear_value v3
  have hsum : 2 ^ 64 + v3.toNat = 2 ^ 31 * v2.toNat + v2.toNat * e.toNat / 2 ^ 65 := by omega
  have h3c' : (2 ^ 64 + v3.toNat) * d.toNat < 2 ^ 128 := by rw [hsum]; exact h3c
  have h3d' : 2 ^ 128 < (2 ^ 64 + v3.toNat) * d.toNat + 2 * d.toNat := by rw [hsum]; exact h3d
  -- The final adjustment: v3 - floor((v3 * d + d) / 2^64) - d.
  have hp : p1.lo.toNat + 2 ^ 64 * p1.hi.toNat = v3.toNat * d.toNat := umul_spec v3 d
  clear_value p1
  have hplo := p1.lo.toNat_lt
  have hphi := p1.hi.toNat_lt
  have hc : (if p1.lo + d < d then (1 : Word) else 0).toNat =
      (v3.toNat * d.toNat + d.toNat) / 2 ^ 64 - p1.hi.toNat := by
    by_cases h : p1.lo + d < d
    · rw [if_pos h]
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at h
      show 1 = _
      omega
    · rw [if_neg h]
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at h
      show 0 = _
      omega
  have hcl : (if p1.lo + d < d then (1 : Word) else 0).toNat ≤ 1 := by
    split_ifs <;> decide
  have hr : ((v3 - p1.hi - if p1.lo + d < d then 1 else 0) - d).toNat =
      (v3.toNat + 2 ^ 65 - (v3.toNat * d.toNat + d.toNat) / 2 ^ 64 - d.toNat) % 2 ^ 64 := by
    have hQ : (v3.toNat * d.toNat + d.toNat) / 2 ^ 64 =
        p1.hi.toNat + (if p1.lo + d < d then (1 : Word) else 0).toNat := by omega
    rw [UInt64.toNat_sub, UInt64.toNat_sub, UInt64.toNat_sub, hQ]
    have hv3l := v3.toNat_lt
    generalize (if p1.lo + d < d then (1 : Word) else 0).toNat = c at hcl ⊢
    clear * - hv3l hphi hcl hdl
    omega
  have h4 := recip_e4 v3.toNat d.toNat v3.toNat_lt h3c' h3d' hd hdl
  rw [← hr] at h4
  exact h4

theorem reciprocal_2by1_spec (P : Platform) (d : Word) (hd : 2 ^ 63 ≤ d.toNat) :
    ∃ v, reciprocal_2by1 P d = some v ∧ (2 ^ 64 + v.toNat) * d.toNat < 2 ^ 128 ∧
      2 ^ 128 ≤ (2 ^ 64 + v.toNat + 1) * d.toNat := by
  have hdl := d.toNat_lt
  unfold reciprocal_2by1
  simp only [require_pos (and_top_ne_zero d hd), Option.bind_eq_bind, Option.bind_some]
  split
  · have hn : (~~~d).toNat = 2 ^ 64 - 1 - d.toNat := by rw [UInt64.toNat_not]; rfl
    obtain ⟨q, r, h1, h2, -⟩ := div_wide_x86_spec (~~~d) (~~~0) d
      (UInt64.lt_iff_toNat_lt.mpr (by rw [hn]; omega))
    rw [h1, hn, show (~~~(0 : Word)).toNat = 2 ^ 64 - 1 from rfl] at *
    refine ⟨q, rfl, ?_⟩
    have hD : 0 < d.toNat := by omega
    have hq := Nat.div_mul_le_self ((2 ^ 64 - 1 - d.toNat) * 2 ^ 64 + (2 ^ 64 - 1)) d.toNat
    have hq' := Nat.lt_mul_div_succ ((2 ^ 64 - 1 - d.toNat) * 2 ^ 64 + (2 ^ 64 - 1)) hD
    rw [← h2] at hq hq'
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm d.toNat q.toNat] at hq'
    constructor
    · rw [Nat.add_mul]; omega
    · rw [Nat.add_mul, Nat.add_mul]; omega
  · exact reciprocal_spec d hd

theorem and_zero_sub_one (d : Word) : d &&& (0 - 1) = d := by
  apply UInt64.toBitVec_inj.mp; simp

theorem and_zero_sub_zero (d : Word) : d &&& (0 - 0) = 0 := by
  apply UInt64.toBitVec_inj.mp; simp

theorem udivrem_2by1_v_spec (u : U128) (d v : Word) (hd : 2 ^ 63 ≤ d.toNat)
    (hu : u.hi.toNat < d.toNat) (hv1 : (2 ^ 64 + v.toNat) * d.toNat < 2 ^ 128)
    (hv2 : 2 ^ 128 ≤ (2 ^ 64 + v.toNat + 1) * d.toNat) :
    (udivrem_2by1_v u d v).1.toNat = u.toNat / d.toNat ∧
      (udivrem_2by1_v u d v).2.toNat = u.toNat % d.toNat := by
  have hsim : ((udivrem_2by1_v u d v).1.toNat, (udivrem_2by1_v u d v).2.toNat) =
      div2by1N u.lo.toNat u.hi.toNat d.toNat v.toNat := by
    have hQl : v.toNat * u.hi.toNat + (2 ^ 64 * u.hi.toNat + u.lo.toNat) < 2 ^ 128 := by
      have : (2 ^ 64 + v.toNat) * u.hi.toNat + (2 ^ 64 + v.toNat) ≤ (2 ^ 64 + v.toNat) * d.toNat := by
        rw [← Nat.mul_add_one]; exact Nat.mul_le_mul_left _ hu
      have := u.lo.toNat_lt
      nlinarith
    obtain ⟨s, hs⟩ : ∃ s, umul v u.hi + u = s := ⟨_, rfl⟩
    have hsn : s.lo.toNat + 2 ^ 64 * s.hi.toNat =
        v.toNat * u.hi.toNat + (2 ^ 64 * u.hi.toNat + u.lo.toNat) := by
      have h := U128.toNat_add (umul v u.hi) u
      rw [hs, umul_toNat] at h
      simp only [U128.toNat] at h ⊢
      omega
    have hsl := s.lo.toNat_lt
    unfold udivrem_2by1_v div2by1N
    simp only [U128.getElem_zero, U128.getElem_one, Id.run, hs]
    rw [show (v.toNat * u.hi.toNat + (2 ^ 64 * u.hi.toNat + u.lo.toNat)) % 2 ^ 64 = s.lo.toNat by
        omega,
      show (v.toNat * u.hi.toNat + (2 ^ 64 * u.hi.toNat + u.lo.toNat)) / 2 ^ 64 = s.hi.toNat by
        omega,
      show (s.hi.toNat + 1) % 2 ^ 64 = (s.hi + 1).toNat by rw [UInt64.toNat_add]; rfl]
    generalize s.hi + 1 = qt
    generalize s.lo = q0
    rw [show (u.lo.toNat + 2 ^ 64 - qt.toNat * d.toNat % 2 ^ 64) % 2 ^ 64 = (u.lo - qt * d).toNat by
      rw [UInt64.toNat_sub, UInt64.toNat_mul]; omega]
    generalize u.lo - qt * d = r0
    have hdl := d.toNat_lt
    have hr0 := r0.toNat_lt
    have hq0 := q0.toNat_lt
    have hqt := qt.toNat_lt
    split_ifs <;>
      simp only [and_zero_sub_one, and_zero_sub_zero, UInt64.add_zero] at * <;>
      simp only [pure, gt_iff_lt, ge_iff_le, UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le,
        UInt64.toNat_add, UInt64.toNat_sub, UInt64.toNat_one, Prod.mk.injEq, and_true,
        true_and] at * <;>
      omega
  rw [div2by1N_spec u.lo.toNat u.hi.toNat d.toNat v.toNat u.lo.toNat_lt hu hd d.toNat_lt hv1 hv2,
    Prod.mk.injEq] at hsim
  rw [show u.toNat = 2 ^ 64 * u.hi.toNat + u.lo.toNat by simp only [U128.toNat]; omega]
  exact hsim

/-- `udivrem_2by1(u, d)` on both code paths, for a normalized `d`. -/
theorem udivrem_2by1_spec (P : Platform) (u : U128) (d : Word) (hd : 2 ^ 63 ≤ d.toNat)
    (h : u.hi < d) :
    ∃ q r, udivrem_2by1 P u d = some (q, r) ∧ q.toNat = u.toNat / d.toNat ∧
      r.toNat = u.toNat % d.toNat := by
  unfold udivrem_2by1
  split
  · obtain ⟨q, r, h1, h2, h3⟩ := div_wide_x86_spec u.hi u.lo d h
    refine ⟨q, r, by simpa using h1, ?_, ?_⟩ <;> simp only [U128.toNat] <;>
      rw [Nat.add_comm, Nat.mul_comm] <;> assumption
  · obtain ⟨v, hv, hv1, hv2⟩ := reciprocal_2by1_spec P d hd
    simp only [hv, Option.bind_eq_bind, Option.bind_some]
    exact ⟨_, _, rfl, udivrem_2by1_v_spec u d v hd (UInt64.lt_iff_toNat_lt.mp h) hv1 hv2⟩

end Intx.Model
