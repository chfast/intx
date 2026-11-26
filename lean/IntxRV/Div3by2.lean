import IntxRV.Values
import Intx.Proofs.DivMath
/-!
# The division of three words by two

`div3by2BV` is what the RV64 code of `udivrem_3by2()` computes, as operations on the words: the
quotient approximation from the reciprocal, the remainders of the quotients `q1` and `q1 + 1`, the
selection by the high word of the remainder and the rare correction. `div3by2BV_spec` gives the
quotient and the remainder from Möller and Granlund, Theorem 3 (`Intx.div3by2_bounds`).
-/

-- omega reduces the powers of 2 in the bounds.
set_option maxRecDepth 100000

namespace IntxRV

/-- The quotient and the two words of the remainder of `u2:u1:u0` by `d1:d0` with the reciprocal
`v`, as the RV64 code of `udivrem_3by2()` computes them. -/
def div3by2BV (u2 u1 u0 d0 d1 v : BitVec 64) : BitVec 64 × BitVec 64 × BitVec 64 :=
  let p0 := v * u2
  let p1 := mulhu v u2
  let q0 := p0 + u1
  let q1 := u2 + p1 + (if q0 < p0 then 1#64 else 0#64)
  let rd0 := u0 - q1 * d0
  let rd1 := u1 - (q1 * d1 + mulhu q1 d0) - (if u0 < rd0 then 1#64 else 0#64)
  let r0 := rd0 - d0
  let r1 := rd1 - d1 - (if rd0 < r0 then 1#64 else 0#64)
  let s0 := if r1 < q0 then r0 else rd0
  let s1 := if r1 < q0 then r1 else rd1
  let q := q1 + (if r1 < q0 then 1#64 else 0#64)
  if (if s1 = d1 then s0 < d0 else s1 < d1) then (q, s0, s1)
  else (q + 1, s0 - d0, s1 - d1 - (if s0 < s0 - d0 then 1#64 else 0#64))

theorem toNat_mulhu (a b : BitVec 64) : (mulhu a b).toNat = a.toNat * b.toNat / 2 ^ 64 := by
  rw [mulhu, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  exact Nat.div_lt_of_lt_mul (Nat.mul_lt_mul'' a.isLt b.isLt)

theorem toNat_ite_lt (a b : BitVec 64) :
    (if a < b then 1#64 else 0#64).toNat = if a.toNat < b.toNat then 1 else 0 := by
  split <;> rename_i h <;> simp only [BitVec.lt_def] at h <;> simp [h]

/-- The two-word subtraction `x1:x0 - y1:y0` with the borrow of the low words. -/
theorem toNat_sub2 (x0 x1 y0 y1 : BitVec 64) :
    (x0 - y0).toNat + 2 ^ 64 * (x1 - y1 - if x0 < x0 - y0 then 1#64 else 0#64).toNat =
      (x0.toNat + 2 ^ 64 * x1.toNat + 2 ^ 128 - (y0.toNat + 2 ^ 64 * y1.toNat)) % 2 ^ 128 := by
  have := x0.isLt
  have := x1.isLt
  have := y0.isLt
  have := y1.isLt
  simp only [BitVec.toNat_sub, toNat_ite_lt]
  split <;> omega

/-- The two-word comparison `s1:s0 < d1:d0`. -/
theorem lt2_iff (s0 s1 d0 d1 : BitVec 64) :
    (if s1 = d1 then s0 < d0 else s1 < d1) ↔
      s0.toNat + 2 ^ 64 * s1.toNat < d0.toNat + 2 ^ 64 * d1.toNat := by
  have := s0.isLt
  have := s1.isLt
  have := d0.isLt
  have := d1.isLt
  split <;> rename_i h <;> simp only [BitVec.lt_def, ← BitVec.toNat_inj] at h ⊢ <;> omega

theorem div_mod_of {U D q x y : ℕ} (hD : 0 < D) (j : ℕ) (hx : x = q + j)
    (h1 : y + D * (q + j) = U) (h2 : y < D) : x = U / D ∧ y = U % D := by
  obtain ⟨a, b⟩ := (Nat.div_mod_unique hD).mpr ⟨h1, h2⟩
  exact ⟨hx.trans a.symm, b.symm⟩

set_option maxHeartbeats 1000000 in
theorem div3by2BV_spec (u2 u1 u0 d0 d1 v : BitVec 64)
    (hD1 : 2 ^ 127 ≤ d0.toNat + 2 ^ 64 * d1.toNat)
    (hX : u2.toNat * 2 ^ 64 + u1.toNat < d0.toNat + 2 ^ 64 * d1.toNat)
    (hv : v.toNat = (2 ^ 192 - 1) / (d0.toNat + 2 ^ 64 * d1.toNat) - 2 ^ 64) :
    (div3by2BV u2 u1 u0 d0 d1 v).1.toNat =
        (u2.toNat * 2 ^ 128 + u1.toNat * 2 ^ 64 + u0.toNat) / (d0.toNat + 2 ^ 64 * d1.toNat) ∧
      (div3by2BV u2 u1 u0 d0 d1 v).2.1.toNat + 2 ^ 64 * (div3by2BV u2 u1 u0 d0 d1 v).2.2.toNat =
        (u2.toNat * 2 ^ 128 + u1.toNat * 2 ^ 64 + u0.toNat) % (d0.toNat + 2 ^ 64 * d1.toNat) := by
  -- omega takes the products with the power of 2 first.
  rw [show u2.toNat * 2 ^ 128 + u1.toNat * 2 ^ 64 + u0.toNat =
    2 ^ 128 * u2.toNat + 2 ^ 64 * u1.toNat + u0.toNat by ring]
  rw [Nat.mul_comm u2.toNat] at hX
  have hd0 := d0.isLt
  have hd1 := d1.isLt
  have hu0 := u0.isLt
  have hu1 := u1.isLt
  have hu2 := u2.isLt
  have hvl := v.isLt
  -- The reciprocal: (2^64 + v) * D < 2^192 ≤ (2^64 + v + 1) * D.
  generalize hD : d0.toNat + 2 ^ 64 * d1.toNat = D at hD1 hX hv ⊢
  have hDl : D < 2 ^ 128 := by omega
  have hUD : 2 ^ 128 * u2.toNat + 2 ^ 64 * u1.toNat + u0.toNat < 2 ^ 64 * D := by
    clear hv; omega
  have hq : 2 ^ 64 ≤ (2 ^ 192 - 1) / D := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hv1 : (2 ^ 64 + v.toNat) * D < 2 ^ 192 := by
    have := Nat.div_mul_le_self (2 ^ 192 - 1) D
    rw [show 2 ^ 64 + v.toNat = (2 ^ 192 - 1) / D by omega]
    omega
  have hv2 : 2 ^ 192 ≤ (2 ^ 64 + v.toNat + 1) * D := by
    have := Nat.lt_mul_div_succ (2 ^ 192 - 1) (show 0 < D by omega)
    rw [show 2 ^ 64 + v.toNat = (2 ^ 192 - 1) / D by omega, Nat.mul_comm]
    omega
  clear hq hv
  unfold div3by2BV
  simp only []
  -- The words of the quotient approximation 2^64 * q1 + q0 = (2^64 + v) * u2 + u1.
  generalize hp0 : v * u2 = p0
  generalize hp1 : mulhu v u2 = p1
  generalize hq0 : p0 + u1 = q0
  generalize hc0 : (if q0 < p0 then 1#64 else 0#64) = c0
  generalize hq1 : u2 + p1 + c0 = q1
  have fq : 2 ^ 64 * q1.toNat + q0.toNat = v.toNat * u2.toNat + (2 ^ 64 * u2.toNat + u1.toNat) := by
    have hQl : v.toNat * u2.toNat + (2 ^ 64 * u2.toNat + u1.toNat) < 2 ^ 128 := by
      have h1 := Nat.mul_le_mul_left (2 ^ 64 + v.toNat) (show 2 ^ 64 * u2.toNat + u1.toNat + 1 ≤ D
        by omega)
      have h2 : 2 ^ 64 * (v.toNat * u2.toNat + (2 ^ 64 * u2.toNat + u1.toNat)) + v.toNat * u1.toNat +
          (2 ^ 64 + v.toNat) = (2 ^ 64 + v.toNat) * (2 ^ 64 * u2.toNat + u1.toNat + 1) := by ring
      omega
    rw [← hq1, ← hc0, ← hq0, ← hp1, ← hp0, BitVec.toNat_add, BitVec.toNat_add, toNat_ite_lt,
      BitVec.toNat_add, BitVec.toNat_mul, toNat_mulhu]
    split <;> omega
  have fq0 := q0.isLt
  have fq1 := q1.isLt
  clear hp0 hp1 hq0 hc0 hq1
  obtain ⟨hlo1, hlo2, hhi⟩ := Intx.div3by2_bounds u0.toNat u1.toNat u2.toNat D v.toNat q1.toNat
    q0.toNat hu0 hu1 (by omega) hD1 hDl hv1 hv2 fq q0.isLt
  -- The remainders of q1 and q1 + 1, modulo 2^128, with the words of the products.
  have frd := toNat_sub2 u0 u1 (q1 * d0) (q1 * d1 + mulhu q1 d0)
  have hy : (q1 * d0).toNat + 2 ^ 64 * (q1 * d1 + mulhu q1 d0).toNat =
      (q1.toNat * d0.toNat + 2 ^ 64 * (q1.toNat * d1.toNat)) % 2 ^ 128 := by
    rw [BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_mul, toNat_mulhu]
    omega
  rw [hy] at frd
  generalize u0 - q1 * d0 = rd0 at frd ⊢
  generalize (u1 - (q1 * d1 + mulhu q1 d0) - if u0 < rd0 then 1#64 else 0#64) = rd1 at frd ⊢
  have fr := toNat_sub2 rd0 rd1 d0 d1
  generalize rd0 - d0 = r0 at fr ⊢
  generalize (rd1 - d1 - if rd0 < r0 then 1#64 else 0#64) = r1 at fr ⊢
  have hP : q1.toNat * D = q1.toNat * d0.toNat + 2 ^ 64 * (q1.toNat * d1.toNat) := by
    rw [← hD]; ring
  -- q1 + 1 and q1 + 2 overflow only if their product with d is at least 2^64 * d.
  have hPq1 : q1.toNat + 1 < 2 ^ 64 ∨ q1.toNat * D + D = 2 ^ 64 * D := by
    rcases Nat.lt_or_ge (q1.toNat + 1) (2 ^ 64) with h | h
    · exact Or.inl h
    · right; rw [show q1.toNat * D + D = (q1.toNat + 1) * D by ring, show q1.toNat + 1 = 2 ^ 64 by omega]
  have hPq2 : q1.toNat + 2 < 2 ^ 64 ∨ 2 ^ 64 * D ≤ q1.toNat * D + 2 * D := by
    rcases Nat.lt_or_ge (q1.toNat + 2) (2 ^ 64) with h | h
    · exact Or.inl h
    · right; rw [show q1.toNat * D + 2 * D = (q1.toNat + 2) * D by ring]
      exact Nat.mul_le_mul_right D h
  have hDq : ∀ j, D * (q1.toNat + j) = q1.toNat * D + j * D := by intro j; ring
  rw [hP] at hlo1 hlo2 hhi hPq1 hPq2 hDq
  rw [hD] at fr
  have frd0 := rd0.isLt
  have frd1 := rd1.isLt
  have fr0 := r0.isLt
  have fr1 := r1.isLt
  generalize hPd : q1.toNat * d0.toNat + 2 ^ 64 * (q1.toNat * d1.toNat) = P
  rw [hPd] at frd hlo1 hlo2 hhi hPq1 hPq2 hDq
  clear hPd
  clear hy hP fq hv1 hv2
  -- The remainder t = u - q1 * d of the quotient q1: rd is t modulo 2^128.
  clear hX hd0 hd1 hvl
  have hU : 2 ^ 128 * u2.toNat + 2 ^ 64 * u1.toNat + u0.toNat =
      P + (2 ^ 128 * u2.toNat + 2 ^ 64 * u1.toNat + u0.toNat - P) := by
    clear frd fr hhi hlo2 hPq1 hPq2 hDq; omega
  have ht : (u0.toNat + 2 ^ 64 * u1.toNat + 2 ^ 128 - P % 2 ^ 128) % 2 ^ 128 =
      (2 ^ 128 * u2.toNat + 2 ^ 64 * u1.toNat + u0.toNat - P) % 2 ^ 128 := by
    clear frd fr hhi hlo2 hPq1 hPq2 hDq; omega
  rw [ht] at frd
  rw [hU] at hUD ⊢
  have hlo : 2 ^ 64 * q0.toNat + 1 + D ≤ (2 ^ 128 * u2.toNat + 2 ^ 64 * u1.toNat + u0.toNat - P) +
      2 ^ 128 := by
    clear frd fr hhi hPq1 hPq2 hDq ht hU hUD; omega
  have hhi' : (2 ^ 128 * u2.toNat + 2 ^ 64 * u1.toNat + u0.toNat - P) < 2 ^ 128 ∨
      (2 ^ 128 * u2.toNat + 2 ^ 64 * u1.toNat + u0.toNat - P) < D + 2 ^ 64 * q0.toNat := by
    clear frd fr hlo2 hPq1 hPq2 hDq ht hU hUD; omega
  generalize 2 ^ 128 * u2.toNat + 2 ^ 64 * u1.toNat + u0.toNat - P = t at frd hlo hhi' hUD ⊢
  clear hlo1 hlo2 hhi ht hU hu0 hu1 hu2
  have hDp : 0 < D := by omega
  have h1 : (1#64).toNat = 1 := rfl
  have h1' : (1 : BitVec 64).toNat = 1 := rfl
  by_cases hc : r1 < q0
  · simp only [hc, if_true]
    rw [BitVec.lt_def] at hc
    by_cases hl : (if r1 = d1 then r0 < d0 else r1 < d1)
    · simp only [hl, if_true]
      rw [lt2_iff, hD] at hl
      rw [BitVec.toNat_add, h1]
      exact div_mod_of (q := q1.toNat) hDp 1 (by omega) (by rw [hDq]; omega) (by omega)
    · simp only [hl, if_false]
      rw [lt2_iff, hD] at hl
      rw [toNat_sub2, BitVec.toNat_add, BitVec.toNat_add, h1, h1', hD]
      -- r < 2^64 * q0 < 2 * d: one subtraction of d leaves the remainder.
      have hr2 : r0.toNat + 2 ^ 64 * r1.toNat < 2 * D := by
        clear frd hhi' hlo hUD hPq1 hPq2 hDq fr; omega
      exact div_mod_of (q := q1.toNat) hDp 2 (by omega) (by rw [hDq]; omega)
        (by clear frd hhi' hlo hUD hPq1 hPq2 hDq fr; omega)
  · simp only [hc, if_false]
    rw [BitVec.lt_def] at hc
    have h0 : (0#64).toNat = 0 := rfl
    by_cases hl : (if rd1 = d1 then rd0 < d0 else rd1 < d1)
    · simp only [hl, if_true]
      rw [lt2_iff, hD] at hl
      rw [BitVec.toNat_add, h0]
      exact div_mod_of (q := q1.toNat) hDp 0 (by omega) (by rw [hDq]; omega) (by omega)
    · simp only [hl, if_false]
      rw [lt2_iff, hD] at hl
      rw [toNat_sub2, BitVec.toNat_add, BitVec.toNat_add, h0, h1', hD]
      exact div_mod_of (q := q1.toNat) hDp 1 (by omega) (by rw [hDq]; omega) (by omega)
end IntxRV
