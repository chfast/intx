import Mathlib
set_option warningAsError true
/-!
# Proofs: the arithmetic of the fold

The number theory of `internal::mulmod_fold<N>()`, apart from the model. With `B = 2 ^ 64`,
`P = B ^ (N - 1)`, the normalized modulus `D` (`B ^ N ≤ 2 * D`, `D < B ^ N`), `C0 = B ^ N - D` and
`B * C0 = q * D + C1` (`C1 < D`):

* one fold of the `(N + 1)`-word `R = t * B ^ N + u * P + low` and the next word `a` gives
  `R' = a + B * low + u * C0 + t * C1`, which is `R * B + a` modulo `D` and less than `B ^ (N + 1)`;
* if `q ≥ 1`, the deficit `B ^ (N + 1) - R` at least halves with each fold; if `q = 0`, the top
  word of `R` grows by at most 1; so after the folds `R ≤ B ^ (N + 1) - 2 * B ^ N`;
* then the Barrett estimate `floor(floor(R / P) * (B + q) / B ^ 2)` is `floor(R / D)` or 1 less.
-/

namespace Intx

/-- One fold: `R * B + a = R' + (t * (B + q) + u) * D`. -/
theorem fold_congr (B P D C0 C1 q a low u t : Nat) (hD : D + C0 = B * P)
    (hq : B * C0 = q * D + C1) :
    (t * (B * P) + u * P + low) * B + a =
      (a + B * low + u * C0 + t * C1) + (t * (B + q) + u) * D := by
  zify at hD hq ⊢
  linear_combination (-(u : ℤ) - t * B) * hD + t * hq

/-- One fold stays below `B ^ (N + 1)`. -/
theorem fold_lt (B P D C0 C1 a low u t : Nat) (hD : D + C0 = B * P) (hC1 : C1 < D)
    (ha : a < B) (hlow : low < P) (hu : u < B) (ht : t < B) :
    a + B * low + u * C0 + t * C1 < B * (B * P) := by
  have hB : 1 ≤ B := by omega
  have h1 : u * C0 + t * C1 ≤ (B - 1) * (C0 + C1) := by
    have := Nat.mul_le_mul_right C0 (show u ≤ B - 1 by omega)
    have := Nat.mul_le_mul_right C1 (show t ≤ B - 1 by omega)
    rw [Nat.mul_add]; omega
  have h3 : a + B * low + 1 ≤ B * P := by
    have := Nat.mul_le_mul_left B (show low + 1 ≤ P by omega)
    rw [Nat.mul_add, Nat.mul_one] at this; omega
  have h4 : (B - 1) * (C0 + C1) + (B - 1) ≤ (B - 1) * (B * P) := by
    rw [← Nat.mul_add_one]; exact Nat.mul_le_mul_left _ (by omega)
  have h5 : (B - 1) * (B * P) + B * P = B * (B * P) := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hB]
  omega

/-- One fold with `q ≥ 1`: `D * (B ^ (N + 1) - R) ≤ B ^ N * (B ^ (N + 1) - R')`. -/
theorem fold_deficit (B P D C0 C1 q a low u t : Nat) (hD : D + C0 = B * P)
    (hq : B * C0 = q * D + C1) (hC1 : C1 < D) (hq1 : 1 ≤ q) (ha : a < B) (hlow : low < P)
    (hu : u < B) (ht : t < B) :
    D * (B * (B * P) - (t * (B * P) + u * P + low)) ≤
      B * P * (B * (B * P) - (a + B * low + u * C0 + t * C1)) := by
  have hR' := fold_lt B P D C0 C1 a low u t hD hC1 ha hlow hu ht
  have hR : t * (B * P) + u * P + low < B * (B * P) := by
    have := Nat.mul_le_mul_right (B * P) (show t + 1 ≤ B by omega)
    have := Nat.mul_le_mul_right P (show u + 1 ≤ B by omega)
    rw [Nat.add_mul, Nat.one_mul] at *
    nlinarith
  have hBC : D ≤ B * C0 := by
    have := Nat.mul_le_mul_right D hq1
    omega
  zify [hR.le, hR'.le] at *
  have key : ((B : ℤ) * P) * (B * (B * P) - (a + B * low + u * C0 + t * C1)) -
      D * (B * (B * P) - (t * (B * P) + u * P + low)) =
      (B - 1 - a) * (B * P) + (P - 1 - low) * (B * (B * P) - D) + t * (B * P) * (D - C1) +
        (B - 1 - u) * P * (B * C0 - D) + C0 := by
    linear_combination (-((B : ℤ) * B * P) + B * P - 1) * hD
  have h1 : (0 : ℤ) ≤ (B - 1 - a) * (B * P) := mul_nonneg (by omega) (by positivity)
  have h2 : (0 : ℤ) ≤ (P - 1 - low) * (B * (B * P) - D) := mul_nonneg (by omega) (by nlinarith)
  have h3 : (0 : ℤ) ≤ t * (B * P) * (D - C1) := mul_nonneg (by positivity) (by omega)
  have h4 : (0 : ℤ) ≤ (B - 1 - u) * P * (B * C0 - D) :=
    mul_nonneg (mul_nonneg (by omega) (by positivity)) (by omega)
  have h5 : (0 : ℤ) ≤ C0 := by positivity
  linarith

/-- One fold with `q = 0`: the top word grows by at most 1, `R' < B ^ N * (t + 2)`. -/
theorem fold_q0 (B P D C0 C1 a low u t : Nat) (hD : D + C0 = B * P) (hq : B * C0 = C1)
    (hC1 : C1 < D) (ha : a < B) (hlow : low < P) (hu : u < B) :
    a + B * low + u * C0 + t * C1 < B * P * (t + 2) := by
  have h3 : a + B * low + 1 ≤ B * P := by
    have := Nat.mul_le_mul_left B (show low + 1 ≤ P by omega)
    rw [Nat.mul_add, Nat.mul_one] at this; omega
  have h1 : u * C0 ≤ B * C0 := Nat.mul_le_mul_right _ hu.le
  have h2 : t * C1 + C1 ≤ t * (B * P) + B * P := by
    have := Nat.mul_le_mul_left t (show C1 ≤ B * P by omega)
    omega
  rw [Nat.mul_add]
  nlinarith

/-- The Barrett estimate: with `B ^ (N + 1) = (B + q) * D + C1` and `R ≤ B ^ (N + 1) - 2 * B ^ N`,
`Qh = floor(floor(R / P) * (B + q) / B ^ 2)` has `Qh * D ≤ R < (Qh + 2) * D`. -/
theorem barrett (B P D C1 q R : Nat) (hB : 0 < B) (hP : 0 < P)
    (hmu : B * (B * P) = (B + q) * D + C1) (hC1 : C1 < D) (hD2 : B * P ≤ 2 * D)
    (hR : R + 2 * (B * P) ≤ B * (B * P)) :
    R / P * (B + q) / (B * B) * D ≤ R ∧ R < (R / P * (B + q) / (B * B) + 2) * D := by
  have hBB : 0 < B * B := Nat.mul_pos hB hB
  set Rt := R / P with hRt
  set Qh := Rt * (B + q) / (B * B) with hQh
  have hQ1 : Qh * (B * B) ≤ Rt * (B + q) := Nat.div_mul_le_self _ _
  have hQ2 : Rt * (B + q) < (Qh + 1) * (B * B) := by
    rw [hQh, Nat.mul_comm (_ + 1)]; exact Nat.lt_mul_div_succ _ hBB
  have hR1 : Rt * P ≤ R := Nat.div_mul_le_self _ _
  have hR2 : R < (Rt + 1) * P := by rw [hRt, Nat.mul_comm (_ + 1)]; exact Nat.lt_mul_div_succ _ hP
  constructor
  · -- Qh * B^2 * D ≤ Rt * (B + q) * D ≤ Rt * B^(N+1) = Rt * P * B^2 ≤ R * B^2.
    have h1 : Qh * (B * B) * D ≤ Rt * (B + q) * D := Nat.mul_le_mul_right _ hQ1
    have h2 : Rt * ((B + q) * D) ≤ Rt * (B * (B * P)) := Nat.mul_le_mul_left _ (by omega)
    have h3 : Rt * P * (B * B) ≤ R * (B * B) := Nat.mul_le_mul_right _ hR1
    have h4 : Qh * D * (B * B) ≤ R * (B * B) := by nlinarith
    exact Nat.le_of_mul_le_mul_right h4 hBB
  · have hD0 : 0 < D := by omega
    have hDP : D < B * (B * P) := by nlinarith
    zify at hQ2 hR2 hmu hC1 hD2 hR hB hP hD0 hDP
    have hA : (R - P : ℤ) * (B * (B * P) - D) ≤ (Rt : ℤ) * P * ((B + q) * D) := by
      rcases le_or_gt (R : ℤ) P with h | h
      · have : (R - P : ℤ) * (B * (B * P) - D) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
        have : (0 : ℤ) ≤ (Rt : ℤ) * P * ((B + q) * D) := by positivity
        linarith
      · exact mul_le_mul (by nlinarith) (by linarith) (by linarith) (by positivity)
    have hB' : (Rt : ℤ) * (B + q) * (D * P) < (Qh + 1) * (B * B) * (D * P) :=
      mul_lt_mul_of_pos_right hQ2 (by positivity)
    have hC : (D : ℤ) * (2 * (B * P)) ≤ D * (B * (B * P) - R) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hE : (B * P : ℤ) * (B * P) ≤ (2 * D) * (B * P) :=
      mul_le_mul_of_nonneg_right hD2 (by positivity)
    have hPD : (0 : ℤ) ≤ P * D := by positivity
    have hF : (R : ℤ) * (B * (B * P)) < (Qh + 2) * D * (B * (B * P)) := by nlinarith
    exact_mod_cast lt_of_mul_lt_mul_right hF (by positivity)

end Intx
