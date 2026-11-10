import Mathlib
set_option warningAsError true
/-!
# Proofs: the arithmetic of the reciprocal division

The number theory of `internal::reciprocal()` and `udivrem_2by1(u, d, v)`, apart from the model
(Möller and Granlund, "Improved division by invariant integers", IEEE Transactions on Computers 60,
2011). For a normalized `d` (`2^63 ≤ d < 2^64`):

* Theorem 1: the table entry `v0` and the Newton steps `v1`, `v2`, `v3` of Algorithm 2 have the
  errors `e0 = 2^50 - v0 * d40`, `e1 = 2^60 - v1 * d40`, `e2 = 2^97 - v2 * d` and
  `e3 = 2^128 - (2^64 + v3) * d` with `d40 = floor(d / 2^24) + 1`, and the final adjustment gives the
  reciprocal `v = floor((2^128 - 1) / d) - 2^64`, that is `0 < 2^128 - (2^64 + v) * d ≤ d`;
* Theorem 2: with the reciprocal, Algorithm 4 computes the quotient and the remainder of a two-word
  number `u < 2^64 * d` by `d`.
-/

namespace Intx

/-- The table approximation `v0 = floor((2^19 - 3 * 2^8) / d9)`: its error `e0 = 2^50 - v0 * d40`
is less than `5 * 2^39` in magnitude (Möller and Granlund, Theorem 1, (6)). -/
theorem recip_e0 (d9 dd : ℕ) (h9 : 256 ≤ d9) (h9' : d9 < 512) (hdd : 1 ≤ dd) (hdd' : dd ≤ 2 ^ 31) :
    2 ^ 50 < 523520 / d9 * (2 ^ 31 * d9 + dd) + 5 * 2 ^ 39 ∧
      523520 / d9 * (2 ^ 31 * d9 + dd) < 2 ^ 50 + 5 * 2 ^ 39 := by
  have hv1 : 523520 / d9 * d9 ≤ 523520 := Nat.div_mul_le_self _ _
  have hv2 : 523520 < (523520 / d9 + 1) * d9 := by
    rw [Nat.mul_comm]; exact Nat.lt_mul_div_succ _ (by omega)
  have hv0 : 523520 / d9 ≤ 2045 := by
    calc 523520 / d9 ≤ 523520 / 256 := Nat.div_le_div_left h9 (by norm_num)
      _ = 2045 := by norm_num
  generalize 523520 / d9 = v0 at hv1 hv2 hv0 ⊢
  have hq : v0 * dd ≤ 2045 * 2 ^ 31 := Nat.mul_le_mul hv0 hdd'
  have hq' : v0 ≤ v0 * dd := Nat.le_mul_of_pos_right _ hdd
  rw [Nat.add_mul] at hv2
  rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm v0 (2 ^ 31), Nat.mul_assoc]
  omega

/-- The first Newton step `v1 = 2^11 * v0 - 1 - floor(v0^2 * d40 / 2^40)`: its error
`e1 = 2^60 - v1 * d40` is in `(0, 29 * 2^38)`, as `2^40 * e1 = e0^2 + (2^40 - f1) * d40` with the
truncated `f1 < 2^40` (Theorem 1, (7)). -/
theorem recip_e1 (v0 d40 : ℕ) (hlo : 2 ^ 50 < v0 * d40 + 5 * 2 ^ 39)
    (hhi : v0 * d40 < 2 ^ 50 + 5 * 2 ^ 39) (hd40 : 2 ^ 39 < d40) (hd40' : d40 ≤ 2 ^ 40) :
    v0 ^ 2 * d40 / 2 ^ 40 + 1 ≤ 2 ^ 11 * v0 ∧
      (2 ^ 11 * v0 - 1 - v0 ^ 2 * d40 / 2 ^ 40) * d40 < 2 ^ 60 ∧
      2 ^ 60 < (2 ^ 11 * v0 - 1 - v0 ^ 2 * d40 / 2 ^ 40) * d40 + 29 * 2 ^ 38 := by
  have hF := Nat.div_add_mod (v0 ^ 2 * d40) (2 ^ 40)
  have hf := Nat.mod_lt (v0 ^ 2 * d40) (show 0 < 2 ^ 40 by positivity)
  generalize v0 ^ 2 * d40 / 2 ^ 40 = F at hF ⊢
  generalize v0 ^ 2 * d40 % 2 ^ 40 = f at hF hf
  -- In integers: 2^40 * e1 = e0^2 + (2^40 - f) * d40 with v1 = 2^11 * v0 - 1 - F.
  have key : (2 ^ 40 : ℤ) * (2 ^ 60 - (2 ^ 11 * v0 - 1 - F) * d40) =
      (2 ^ 50 - v0 * d40) ^ 2 + (2 ^ 40 - f) * d40 := by
    have hFz : (2 ^ 40 * F + f : ℤ) = v0 ^ 2 * d40 := by exact_mod_cast hF
    linear_combination (d40 : ℤ) * hFz
  have he0 : ((2 : ℤ) ^ 50 - v0 * d40) ^ 2 < 25 * 2 ^ 78 := by
    have h1 : (2 : ℤ) ^ 50 - v0 * d40 < 5 * 2 ^ 39 := by
      have : (2 : ℤ) ^ 50 < v0 * d40 + 5 * 2 ^ 39 := by exact_mod_cast hlo
      linarith
    have h2 : -(5 * 2 ^ 39 : ℤ) < 2 ^ 50 - v0 * d40 := by
      have : (v0 * d40 : ℤ) < 2 ^ 50 + 5 * 2 ^ 39 := by exact_mod_cast hhi
      linarith
    nlinarith
  have hf1 : (0 : ℤ) < (2 ^ 40 - f) * d40 := by
    have : (f : ℤ) < 2 ^ 40 := by exact_mod_cast hf
    have : (0 : ℤ) < d40 := by exact_mod_cast (show 0 < d40 by omega)
    positivity
  have hf2 : ((2 : ℤ) ^ 40 - f) * d40 ≤ 2 ^ 80 := by
    have : (0 : ℤ) ≤ f := by positivity
    have : (d40 : ℤ) ≤ 2 ^ 40 := by exact_mod_cast hd40'
    nlinarith
  have hsq : (0 : ℤ) ≤ (2 ^ 50 - v0 * d40) ^ 2 := sq_nonneg _
  -- e1 in (0, 29 * 2^38).
  have he1a : (0 : ℤ) < 2 ^ 60 - (2 ^ 11 * v0 - 1 - F) * d40 := by nlinarith
  have he1b : (2 : ℤ) ^ 60 - (2 ^ 11 * v0 - 1 - F) * d40 < 29 * 2 ^ 38 := by nlinarith
  -- v1 >= 1, so the Nat subtractions do not truncate.
  have hv1 : (1 : ℤ) ≤ 2 ^ 11 * v0 - 1 - F := by
    by_contra h
    have : (2 ^ 11 * v0 - 1 - F : ℤ) ≤ 0 := by linarith
    have : (2 ^ 11 * v0 - 1 - F : ℤ) * d40 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg this (by positivity)
    linarith
  have hle : F + 1 ≤ 2 ^ 11 * v0 := by
    have : (F + 1 : ℤ) ≤ 2 ^ 11 * v0 := by linarith
    exact_mod_cast this
  refine ⟨hle, ?_, ?_⟩
  · have e : ((2 ^ 11 * v0 - 1 - F : ℕ) : ℤ) = 2 ^ 11 * v0 - 1 - F := by
      omega
    have : (((2 ^ 11 * v0 - 1 - F : ℕ) : ℤ) * d40) < 2 ^ 60 := by rw [e]; linarith
    exact_mod_cast this
  · have e : ((2 ^ 11 * v0 - 1 - F : ℕ) : ℤ) = 2 ^ 11 * v0 - 1 - F := by
      omega
    have : (2 : ℤ) ^ 60 < ((2 ^ 11 * v0 - 1 - F : ℕ) : ℤ) * d40 + 29 * 2 ^ 38 := by rw [e]; linarith
    exact_mod_cast this

/-- The second Newton step `v2 = 2^13 * v1 + floor(v1 * e1 / 2^47)`: its error `e2 = 2^97 - v2 * d`
is in `(0, 873 * 2^53 + d + 2^24)`, as
`2^47 * e2 = 2^24 * (e1^2 + d40 * f2) + 2^47 * v2 * (2^24 * d40 - d)` with the truncated
`f2 < 2^47` (Theorem 1, (8)). -/
theorem recip_e2 (v1 d40 D : ℕ) (h1 : v1 * d40 < 2 ^ 60) (h2 : 2 ^ 60 < v1 * d40 + 29 * 2 ^ 38)
    (hD : D / 2 ^ 24 + 1 = d40) (hD1 : 2 ^ 63 ≤ D) (hD2 : D < 2 ^ 64) :
    (2 ^ 13 * v1 + v1 * (2 ^ 60 - v1 * d40) / 2 ^ 47) * D < 2 ^ 97 ∧
      2 ^ 97 < (2 ^ 13 * v1 + v1 * (2 ^ 60 - v1 * d40) / 2 ^ 47) * D + 873 * 2 ^ 53 + D + 2 ^ 24 := by
  -- e1 = 2^60 - v1 * d40 and d = 2^24 * d40 - dd.
  obtain ⟨e1, he1⟩ : ∃ e1, e1 + v1 * d40 = 2 ^ 60 := ⟨2 ^ 60 - v1 * d40, by omega⟩
  have he1' : 2 ^ 60 - v1 * d40 = e1 := by omega
  rw [he1']
  have he1l : e1 < 29 * 2 ^ 38 := by omega
  have he1p : 0 < e1 := by omega
  have hF2 := Nat.div_add_mod (v1 * e1) (2 ^ 47)
  have hf2 := Nat.mod_lt (v1 * e1) (show 0 < 2 ^ 47 by positivity)
  generalize v1 * e1 / 2 ^ 47 = F2 at hF2 ⊢
  generalize v1 * e1 % 2 ^ 47 = f2 at hF2 hf2
  have hg := Nat.mod_lt D (show 0 < 2 ^ 24 by positivity)
  have hDg := Nat.div_add_mod D (2 ^ 24)
  obtain ⟨dd, hdd⟩ : ∃ dd, D + dd = 2 ^ 24 * d40 := ⟨2 ^ 24 - D % 2 ^ 24, by omega⟩
  have hdd1 : 1 ≤ dd := by omega
  have hdd2 : dd ≤ 2 ^ 24 := by omega
  have hv1 : 1 ≤ v1 := by
    rcases Nat.eq_zero_or_pos v1 with h | h
    · subst h; omega
    · exact h
  -- The identity, in integers.
  have key : (2 ^ 47 : ℤ) * (2 ^ 97 - (2 ^ 13 * v1 + F2) * D) =
      2 ^ 24 * e1 ^ 2 + 2 ^ 24 * d40 * f2 + 2 ^ 47 * (2 ^ 13 * v1 + F2) * dd := by
    have hdd' : (D + dd : ℤ) = 2 ^ 24 * d40 := by exact_mod_cast hdd
    have hF2' : (2 ^ 47 * F2 + f2 : ℤ) = v1 * e1 := by exact_mod_cast hF2
    have he1'' : (e1 + v1 * d40 : ℤ) = 2 ^ 60 := by exact_mod_cast he1
    linear_combination (-(2 : ℤ) ^ 47 * (2 ^ 13 * v1 + F2)) * hdd' + (-(2 : ℤ) ^ 24 * d40) * hF2' +
      (-(2 : ℤ) ^ 84 - 2 ^ 24 * e1) * he1''
  have hpos : (0 : ℤ) < 2 ^ 97 - (2 ^ 13 * v1 + F2) * D := by
    have : (0 : ℤ) < 2 ^ 47 * (2 ^ 13 * v1 + F2) * dd := by
      have : (1 : ℤ) ≤ v1 := by exact_mod_cast hv1
      have : (1 : ℤ) ≤ dd := by exact_mod_cast hdd1
      positivity
    have : (0 : ℤ) ≤ 2 ^ 24 * e1 ^ 2 + 2 ^ 24 * d40 * f2 := by positivity
    nlinarith
  have hlt : (2 ^ 13 * v1 + F2) * D < 2 ^ 97 := by
    have : ((2 ^ 13 * v1 + F2) * D : ℤ) < 2 ^ 97 := by linarith
    exact_mod_cast this
  refine ⟨hlt, ?_⟩
  -- v2 < 2^34, so v2 * dd <= 2^58.
  have hv2 : 2 ^ 13 * v1 + F2 < 2 ^ 34 := by
    by_contra h
    have : 2 ^ 34 * D ≤ (2 ^ 13 * v1 + F2) * D := Nat.mul_le_mul_right _ (by omega)
    have : 2 ^ 34 * 2 ^ 63 ≤ 2 ^ 34 * D := Nat.mul_le_mul_left _ hD1
    omega
  have hb1 : (2 ^ 24 * e1 ^ 2 : ℤ) < 2 ^ 24 * (841 * 2 ^ 76) := by
    have : (e1 : ℤ) < 29 * 2 ^ 38 := by exact_mod_cast he1l
    have : (0 : ℤ) ≤ e1 := by positivity
    nlinarith
  have hb2 : (2 ^ 24 * d40 * f2 : ℤ) ≤ 2 ^ 47 * (D + dd) := by
    have : (f2 : ℤ) ≤ 2 ^ 47 := by exact_mod_cast hf2.le
    have hdd' : (D + dd : ℤ) = 2 ^ 24 * d40 := by exact_mod_cast hdd
    rw [hdd']
    have : (0 : ℤ) ≤ d40 := by positivity
    nlinarith
  have hb3n : (2 ^ 13 * v1 + F2) * dd ≤ 2 ^ 34 * 2 ^ 24 := Nat.mul_le_mul hv2.le hdd2
  have hb3 : ((2 ^ 13 * v1 + F2) * dd : ℤ) ≤ 2 ^ 34 * 2 ^ 24 := by exact_mod_cast hb3n
  have hdd2' : (dd : ℤ) ≤ 2 ^ 24 := by exact_mod_cast hdd2
  have : (2 : ℤ) ^ 97 < (2 ^ 13 * v1 + F2) * D + 873 * 2 ^ 53 + D + 2 ^ 24 := by
    linarith
  exact_mod_cast this

/-- The third Newton step `v3 = 2^31 * v2 + floor(v2 * e / 2^65)` with `e = floor(e2 / 2)`: its
error `e3 = 2^128 - v3 * d` is in `(0, 2 * d)`, as `2^65 * e3 = 2^96 * (e2 - 2 * e) + e * e2 + f3 * d`
with the truncated `f3 < 2^65`, and so `2^64 <= v3 < 2^65` (Theorem 1, (9)). -/
theorem recip_e3 (v2 D : ℕ) (h1 : v2 * D < 2 ^ 97) (h2 : 2 ^ 97 < v2 * D + 873 * 2 ^ 53 + D + 2 ^ 24)
    (hD1 : 2 ^ 63 ≤ D) (hD2 : D < 2 ^ 64) :
    2 ^ 64 ≤ 2 ^ 31 * v2 + v2 * ((2 ^ 97 - v2 * D) / 2) / 2 ^ 65 ∧
      2 ^ 31 * v2 + v2 * ((2 ^ 97 - v2 * D) / 2) / 2 ^ 65 < 2 ^ 65 ∧
      (2 ^ 31 * v2 + v2 * ((2 ^ 97 - v2 * D) / 2) / 2 ^ 65) * D < 2 ^ 128 ∧
      2 ^ 128 < (2 ^ 31 * v2 + v2 * ((2 ^ 97 - v2 * D) / 2) / 2 ^ 65) * D + 2 * D := by
  obtain ⟨e2, he2⟩ : ∃ e2, e2 + v2 * D = 2 ^ 97 := ⟨2 ^ 97 - v2 * D, by omega⟩
  rw [show 2 ^ 97 - v2 * D = e2 by omega]
  have he2p : 0 < e2 := by omega
  have he2l : e2 < 873 * 2 ^ 53 + D + 2 ^ 24 := by omega
  have hε := Nat.div_add_mod e2 2
  have hεl := Nat.mod_lt e2 (show 0 < 2 by norm_num)
  generalize e2 / 2 = e at hε ⊢
  generalize e2 % 2 = ε at hε hεl
  have hF3 := Nat.div_add_mod (v2 * e) (2 ^ 65)
  have hf3 := Nat.mod_lt (v2 * e) (show 0 < 2 ^ 65 by positivity)
  generalize v2 * e / 2 ^ 65 = F3 at hF3 ⊢
  generalize v2 * e % 2 ^ 65 = f3 at hF3 hf3
  -- The identity, in integers.
  have key : (2 ^ 65 : ℤ) * (2 ^ 128 - (2 ^ 31 * v2 + F3) * D) = 2 ^ 96 * ε + e * e2 + f3 * D := by
    have h3 : (2 ^ 65 * F3 + f3 : ℤ) = v2 * e := by exact_mod_cast hF3
    have h4 : (e2 + v2 * D : ℤ) = 2 ^ 97 := by exact_mod_cast he2
    have h5 : (2 * e + ε : ℤ) = e2 := by exact_mod_cast hε
    linear_combination (-(D : ℤ)) * h3 + (-(2 : ℤ) ^ 96 - e) * h4 + (-(2 : ℤ) ^ 96) * h5
  have he2z : (0 : ℤ) < e2 := by exact_mod_cast he2p
  have he2lz : (e2 : ℤ) < 873 * 2 ^ 53 + D + 2 ^ 24 := by exact_mod_cast he2l
  have hDz1 : (2 : ℤ) ^ 63 ≤ D := by exact_mod_cast hD1
  have hDz2 : (D : ℤ) < 2 ^ 64 := by exact_mod_cast hD2
  have hεz : (ε : ℤ) ≤ 1 := by exact_mod_cast (show ε ≤ 1 by omega)
  have h2e : (2 * e : ℤ) ≤ e2 := by exact_mod_cast (show 2 * e ≤ e2 by omega)
  have hf3z : (f3 : ℤ) < 2 ^ 65 := by exact_mod_cast hf3
  have hez : (0 : ℤ) ≤ e := by positivity
  -- e3 > 0.
  have hpos : (0 : ℤ) < 2 ^ 128 - (2 ^ 31 * v2 + F3) * D := by
    have : (0 : ℤ) < 2 ^ 96 * ε + e * e2 + f3 * D := by
      rcases Nat.eq_zero_or_pos e with h0 | h0
      · have : ε = 1 := by omega
        subst this; positivity
      · have : (1 : ℤ) ≤ e := by exact_mod_cast h0
        have : (0 : ℤ) ≤ ε := by positivity
        have : (0 : ℤ) ≤ f3 * D := by positivity
        nlinarith
    linarith
  -- e3 < 2 * d: e2^2 + 2^97 <= 2^66 * d on 2^63 <= d < 2^64.
  have hsq : (e2 : ℤ) ^ 2 + 2 ^ 97 ≤ 2 ^ 66 * D := by
    have hq : ((D : ℤ) - 2 ^ 63) * (2 ^ 64 - D) ≥ 0 := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hlt : (2 : ℤ) ^ 128 - (2 ^ 31 * v2 + F3) * D < 2 * D := by
    have : (2 * e * e2 : ℤ) ≤ e2 ^ 2 := by nlinarith
    have : (f3 * D : ℤ) < 2 ^ 65 * D := by nlinarith
    nlinarith
  have hv3a : (2 ^ 31 * v2 + F3) * D < 2 ^ 128 := by
    have : ((2 ^ 31 * v2 + F3) * D : ℤ) < 2 ^ 128 := by linarith
    exact_mod_cast this
  have hv3b : 2 ^ 128 < (2 ^ 31 * v2 + F3) * D + 2 * D := by
    have : (2 : ℤ) ^ 128 < (2 ^ 31 * v2 + F3) * D + 2 * D := by linarith
    exact_mod_cast this
  refine ⟨?_, ?_, hv3a, hv3b⟩
  · by_contra h
    have : (2 ^ 31 * v2 + F3) * D ≤ (2 ^ 64 - 1) * D := Nat.mul_le_mul_right _ (by omega)
    have : (2 ^ 64 + 1) * D ≤ (2 ^ 64 + 1) * (2 ^ 64 - 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  · by_contra h
    have : 2 ^ 65 * D ≤ (2 ^ 31 * v2 + F3) * D := Nat.mul_le_mul_right _ (by omega)
    have : 2 ^ 65 * 2 ^ 63 ≤ 2 ^ 65 * D := Nat.mul_le_mul_left _ hD1
    omega

/-- The final adjustment `v4 = v3 - floor((v3 + 2^64 + 1) * d / 2^64) mod 2^64` adds 1 to `v3` if
and only if its error `e3` exceeds `d`: then `v4` is the reciprocal, `0 < 2^128 - (2^64 + v4) * d <= d`
(Theorem 1, (10)). -/
theorem recip_e4 (v3 D : ℕ) (hv3 : v3 < 2 ^ 64) (h1 : (2 ^ 64 + v3) * D < 2 ^ 128)
    (h2 : 2 ^ 128 < (2 ^ 64 + v3) * D + 2 * D) (hD1 : 2 ^ 63 ≤ D) (hD2 : D < 2 ^ 64) :
    (2 ^ 64 + (v3 + 2 ^ 65 - (v3 * D + D) / 2 ^ 64 - D) % 2 ^ 64) * D < 2 ^ 128 ∧
      2 ^ 128 ≤ (2 ^ 64 + (v3 + 2 ^ 65 - (v3 * D + D) / 2 ^ 64 - D) % 2 ^ 64 + 1) * D := by
  have hP : (2 ^ 64 + v3) * D = 2 ^ 64 * D + v3 * D := by ring
  rw [hP] at h1 h2
  have hP1 : (2 ^ 64 + v3 + 1) * D = 2 ^ 64 * D + v3 * D + D := by ring
  by_cases he : 2 ^ 128 ≤ 2 ^ 64 * D + v3 * D + D
  · -- e3 <= d: the floor is 2^64 - d, and v4 = v3.
    have hH : (v3 * D + D) / 2 ^ 64 = 2 ^ 64 - D := by
      rw [Nat.div_eq_iff (by positivity)]
      constructor <;> omega
    rw [hH, show v3 + 2 ^ 65 - (2 ^ 64 - D) - D = v3 + 2 ^ 64 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hv3, hP, hP1]
    exact ⟨h1, he⟩
  · -- e3 > d: the floor is 2^64 - d - 1, and v4 = v3 + 1.
    have hH : (v3 * D + D) / 2 ^ 64 = 2 ^ 64 - D - 1 := by
      rw [Nat.div_eq_iff (by positivity)]
      constructor <;> omega
    have hv31 : v3 + 1 < 2 ^ 64 := by
      by_contra h
      have : 2 ^ 64 * D ≤ v3 * D + D := by
        have := Nat.mul_le_mul_right D (show 2 ^ 64 ≤ v3 + 1 by omega)
        rw [Nat.add_mul, Nat.one_mul] at this; exact this
      have : 2 ^ 64 * 2 ^ 63 ≤ 2 ^ 64 * D := Nat.mul_le_mul_left _ hD1
      omega
    rw [hH, show v3 + 2 ^ 65 - (2 ^ 64 - D - 1) - D = v3 + 1 + 2 ^ 64 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hv31]
    have e1 : (2 ^ 64 + (v3 + 1)) * D = 2 ^ 64 * D + v3 * D + D := by ring
    have e2 : (2 ^ 64 + (v3 + 1) + 1) * D = 2 ^ 64 * D + v3 * D + 2 * D := by ring
    rw [e1, e2]
    omega

/-- `udivrem_2by1(u, d, v)` (Algorithm 4) on the numbers of the words: the quotient and the
remainder. -/
def div2by1N (u0 u1 D V : ℕ) : ℕ × ℕ :=
  let Q := V * u1 + (2 ^ 64 * u1 + u0)
  let q0 := Q % 2 ^ 64
  let qt := (Q / 2 ^ 64 + 1) % 2 ^ 64
  let r0 := (u0 + 2 ^ 64 - qt * D % 2 ^ 64) % 2 ^ 64
  let q1 := if q0 < r0 then (qt + 2 ^ 64 - 1) % 2 ^ 64 else qt
  let r1 := if q0 < r0 then (r0 + D) % 2 ^ 64 else r0
  if D ≤ r1 then ((q1 + 1) % 2 ^ 64, r1 - D) else (q1, r1)

theorem pair_div_mod {U D q x y : ℕ} (hD : 0 < D) (j : ℕ) (hx : x = q + j)
    (h1 : y + D * (q + j) = U) (h2 : y < D) : (x, y) = (U / D, U % D) := by
  obtain ⟨a, b⟩ := (Nat.div_mod_unique hD).mpr ⟨h1, h2⟩
  rw [a, b, hx]

/-- Möller and Granlund, Theorem 2: with the candidate quotient `q1 + 1` of `(2^64 + v) * u1 + u0`,
the candidate remainder `r = u - (q1 + 1) * d` is in `[max(2^64 - d, q0 + 1) - 2^64, max(2^64 - d, q0))`,
so Algorithm 4 finds the quotient and the remainder with two conditional adjustments. -/
theorem div2by1N_spec (u0 u1 D V : ℕ) (hu0 : u0 < 2 ^ 64) (hu1 : u1 < D) (hD1 : 2 ^ 63 ≤ D)
    (hD2 : D < 2 ^ 64) (hv1 : (2 ^ 64 + V) * D < 2 ^ 128) (hv2 : 2 ^ 128 ≤ (2 ^ 64 + V + 1) * D) :
    div2by1N u0 u1 D V = ((2 ^ 64 * u1 + u0) / D, (2 ^ 64 * u1 + u0) % D) := by
  have hDp : 0 < D := by omega
  -- Q = (2^64 + v) * u1 + u0 = q1 * 2^64 + q0.
  have hQl : V * u1 + (2 ^ 64 * u1 + u0) < 2 ^ 128 := by
    have : (2 ^ 64 + V) * u1 + (2 ^ 64 + V) ≤ (2 ^ 64 + V) * D := by
      rw [← Nat.mul_add_one]; exact Nat.mul_le_mul_left _ hu1
    nlinarith
  have hQ := Nat.div_add_mod (V * u1 + (2 ^ 64 * u1 + u0)) (2 ^ 64)
  have hq0 := Nat.mod_lt (V * u1 + (2 ^ 64 * u1 + u0)) (show 0 < 2 ^ 64 by positivity)
  have hq1 : (V * u1 + (2 ^ 64 * u1 + u0)) / 2 ^ 64 < 2 ^ 64 := Nat.div_lt_of_lt_mul (by simpa using hQl)
  unfold div2by1N
  simp only []
  generalize hq1d : (V * u1 + (2 ^ 64 * u1 + u0)) / 2 ^ 64 = q1 at hQ hq1 ⊢
  generalize hq0d : (V * u1 + (2 ^ 64 * u1 + u0)) % 2 ^ 64 = q0 at hQ hq0 ⊢
  -- The candidate remainder rt = u - (q1 + 1) * d and the identity
  -- 2^64 * rt = k * u1 + (2^64 - d) * u0 + q0 * d - 2^64 * d with k = 2^128 - (2^64 + v) * d.
  have hk1 : (1 : ℤ) ≤ 2 ^ 128 - (2 ^ 64 + V) * D := by
    have : ((2 ^ 64 + V) * D : ℤ) < 2 ^ 128 := by exact_mod_cast hv1
    linarith
  have hk2 : (2 : ℤ) ^ 128 - (2 ^ 64 + V) * D ≤ D := by
    have : (2 : ℤ) ^ 128 ≤ (2 ^ 64 + V + 1) * D := by exact_mod_cast hv2
    linarith
  have key : (2 ^ 64 : ℤ) * (2 ^ 64 * u1 + u0 - (q1 + 1) * D) =
      (2 ^ 128 - (2 ^ 64 + V) * D) * u1 + (2 ^ 64 - D) * u0 + q0 * D - 2 ^ 64 * D := by
    have hQz : ((2 ^ 64 * q1 + q0 : ℕ) : ℤ) = (V * u1 + (2 ^ 64 * u1 + u0) : ℕ) := by
      exact_mod_cast hQ
    push_cast at hQz
    linear_combination (-(D : ℤ)) * hQz
  have hu0z : (0 : ℤ) ≤ u0 := by positivity
  have hu0z' : (u0 : ℤ) ≤ 2 ^ 64 - 1 := by have : (u0 : ℤ) < 2 ^ 64 := (by exact_mod_cast hu0); linarith
  have hu1z : (u1 : ℤ) ≤ D - 1 := by have : (u1 : ℤ) < D := (by exact_mod_cast hu1); linarith
  have hq0z : (q0 : ℤ) ≤ 2 ^ 64 - 1 := by have : (q0 : ℤ) < 2 ^ 64 := (by exact_mod_cast hq0); linarith
  have hDz : (D : ℤ) ≤ 2 ^ 64 - 1 := by have : (D : ℤ) < 2 ^ 64 := (by exact_mod_cast hD2); linarith
  have hDz' : (2 : ℤ) ^ 63 ≤ D := by exact_mod_cast hD1
  have hku : (0 : ℤ) ≤ (2 ^ 128 - (2 ^ 64 + V) * D) * u1 := mul_nonneg (by linarith) (by positivity)
  have hdu : (0 : ℤ) ≤ (2 ^ 64 - D) * u0 := mul_nonneg (by linarith) hu0z
  have hqd : (0 : ℤ) ≤ q0 * D := by positivity
  -- The bounds of Theorem 2.
  have hlo1 : -(D : ℤ) ≤ 2 ^ 64 * u1 + u0 - (q1 + 1) * D := by
    have : (2 ^ 64 : ℤ) * (2 ^ 64 * u1 + u0 - (q1 + 1) * D) ≥ 2 ^ 64 * (-(D : ℤ)) := by linarith
    exact le_of_mul_le_mul_left this (by positivity)
  have hlo2 : (q0 : ℤ) + 1 - 2 ^ 64 ≤ 2 ^ 64 * u1 + u0 - (q1 + 1) * D := by
    have h1 : (0 : ℤ) < (2 ^ 64 - q0) * (2 ^ 64 - D) := mul_pos (by linarith) (by linarith)
    have : (2 ^ 64 : ℤ) * (q0 - 2 ^ 64) < 2 ^ 64 * (2 ^ 64 * u1 + u0 - (q1 + 1) * D) := by
      linarith
    have := lt_of_mul_lt_mul_left this (by positivity)
    linarith
  have hhi : 2 ^ 64 * u1 + u0 - (q1 + 1) * D < (2 ^ 64 - D : ℤ) ∨
      2 ^ 64 * u1 + u0 - (q1 + 1) * D < (q0 : ℤ) := by
    have h1 : (0 : ℤ) ≤ (D - (2 ^ 128 - (2 ^ 64 + V) * D)) * u1 := mul_nonneg (by linarith) (by positivity)
    have h2 : (0 : ℤ) ≤ D * (D - 1 - u1) := mul_nonneg (by positivity) (by linarith)
    have h3 : (0 : ℤ) ≤ (2 ^ 64 - D) * (2 ^ 64 - 1 - u0) := mul_nonneg (by linarith) (by linarith)
    by_cases hc : (q0 : ℤ) ≤ 2 ^ 64 - D
    · left
      have h4 : (0 : ℤ) ≤ (2 ^ 64 - D - q0) * D := mul_nonneg (by linarith) (by positivity)
      have : (2 ^ 64 : ℤ) * (2 ^ 64 * u1 + u0 - (q1 + 1) * D) < 2 ^ 64 * (2 ^ 64 - D) := by linarith
      exact lt_of_mul_lt_mul_left this (by positivity)
    · right
      have h4 : (0 : ℤ) < (2 ^ 64 - D) * (q0 - (2 ^ 64 - D)) := mul_pos (by linarith) (by linarith)
      have : (2 ^ 64 : ℤ) * (2 ^ 64 * u1 + u0 - (q1 + 1) * D) < 2 ^ 64 * q0 := by linarith
      exact lt_of_mul_lt_mul_left this (by positivity)
  -- The same in natural numbers, with P = q1 * d.
  have hP1 : (q1 + 1) * D = q1 * D + D := by ring
  have hlo1n : q1 * D + D ≤ 2 ^ 64 * u1 + u0 + D := by zify; linarith
  have hlo2n : q0 + 1 + (q1 * D + D) ≤ 2 ^ 64 * u1 + u0 + 2 ^ 64 := by zify; linarith
  have hhin : 2 ^ 64 * u1 + u0 + D < q1 * D + D + 2 ^ 64 ∨ 2 ^ 64 * u1 + u0 < q1 * D + D + q0 := by
    rcases hhi with h | h
    · left; zify; linarith
    · right; zify; linarith
  have hUD : 2 ^ 64 * u1 + u0 < 2 ^ 64 * D := by
    have := Nat.mul_le_mul_left (2 ^ 64) (show u1 + 1 ≤ D by omega)
    rw [Nat.mul_add, Nat.mul_one] at this; omega
  -- q1 + 1 <= 2^64, and q1 + 1 = 2^64 only if u1 = d - 1.
  generalize hP : q1 * D = P at hlo1n hlo2n hhin
  have hqt : (q1 + 1) % 2 ^ 64 * D % 2 ^ 64 = (if q1 + 1 < 2 ^ 64 then (P + D) % 2 ^ 64 else 0) := by
    split_ifs with h
    · rw [Nat.mod_eq_of_lt h, hP1, hP]
    · rw [show q1 + 1 = 2 ^ 64 by omega, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
  rw [hqt]
  have hPq : q1 + 1 < 2 ^ 64 ∨ P + D = 2 ^ 64 * D := by
    rcases Nat.lt_or_ge (q1 + 1) (2 ^ 64) with h | h
    · exact Or.inl h
    · right; rw [← hP, ← hP1, show q1 + 1 = 2 ^ 64 by omega]
  have hPq2 : q1 + 2 < 2 ^ 64 ∨ 2 ^ 64 * D ≤ P + 2 * D := by
    rcases Nat.lt_or_ge (q1 + 2) (2 ^ 64) with h | h
    · exact Or.inl h
    · right; rw [← hP, show q1 * D + 2 * D = (q1 + 2) * D by ring]; exact Nat.mul_le_mul_right D h
  have hDq : ∀ j, D * (q1 + j) = P + j * D := by intro j; rw [← hP]; ring
  clear key hlo1 hlo2 hhi hku hdu hqd hk1 hk2 hQ hq1d hq0d hQl hv1 hv2 hu0z hu0z' hu1z hq0z hDz hDz'
    hP hP1 hqt
  split_ifs <;> first
    | (exfalso; omega)
    | exact pair_div_mod (q := q1) hDp 0 (by omega) (by rw [hDq]; omega) (by omega)
    | exact pair_div_mod (q := q1) hDp 1 (by omega) (by rw [hDq]; omega) (by omega)
    | exact pair_div_mod (q := q1) hDp 2 (by omega) (by rw [hDq]; omega) (by omega)

end Intx
