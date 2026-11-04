import Intx.Proofs.Uint
import Intx.Model.Div
set_option warningAsError true
/-!
# Proofs: the divisions

What `div_wide_x86()`, `udivrem_2by1()` and `udivrem_top1()` of `Intx.Model` compute. For
`udivrem_top1()` this is the case `mulmod()` uses: the numerator has one word more than the
normalized divisor. The estimate of the quotient is at most 2 too large (Knuth, TAOCP Vol. 2,
4.3.1, Theorem B), so the correction loop ends within the 2 iterations of the model.
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

theorem udivrem_2by1_spec (u : U128) (d : Word) (h : u.hi < d) :
    ∃ q r, udivrem_2by1 u d = some (q, r) ∧ q.toNat = u.toNat / d.toNat ∧
      r.toNat = u.toNat % d.toNat := by
  obtain ⟨q, r, h1, h2, h3⟩ := div_wide_x86_spec u.hi u.lo d h
  refine ⟨q, r, h1, ?_, ?_⟩ <;> simp only [U128.toNat] <;> rw [Nat.add_comm, Nat.mul_comm] <;>
    assumption

/-- The words of `v` from the word `k`. -/
theorem val_div_pow {n : Nat} (v : Vector Word n) (k : Nat) (hk : k < n) :
    val v.toList / 2 ^ (64 * k) = v[k].toNat + 2 ^ 64 * (val v.toList / 2 ^ (64 * (k + 1))) := by
  rw [← val_drop, ← val_drop, List.drop_eq_getElem_cons (by simpa using hk), val_cons,
    Vector.getElem_toList]

theorem val_div_pow_top {n : Nat} (v : Vector Word n) (k : Nat) (hk : k + 1 = n) :
    val v.toList / 2 ^ (64 * k) = v[k].toNat := by
  rw [val_div_pow v k (by omega), Nat.div_eq_of_lt (by rw [hk]; exact val_toList_lt v)]
  simp

theorem correctLoop_spec (TOP : Nat) {nv : Nat} (vw : Vector Word (TOP + 1)) (h : 1 ≤ TOP ∧ TOP < nv)
    (hnv : nv = TOP + 1) (U qt : Nat) (hlo : qt * val vw.toList ≤ U)
    (hhi : U < (qt + 1) * val vw.toList) :
    ∀ (fuel : Nat) (q : Word) (r : Vector Word nv) (borrow : Word),
      (val r.toList : ℤ) - 2 ^ (64 * nv) * borrow.toNat = U - q.toNat * val vw.toList →
      qt ≤ q.toNat → q.toNat ≤ qt + fuel →
      ∃ q' r', correctLoop TOP vw fuel q r borrow h = some (q', r') ∧ q'.toNat = qt ∧
        val r'.toList = U - qt * val vw.toList := by
  have hV : 0 < val vw.toList := by
    rcases Nat.eq_zero_or_pos (val vw.toList) with h0 | h0
    · rw [h0] at hhi; simp at hhi
    · exact h0
  have hrl : ∀ r : Vector Word nv, val r.toList < 2 ^ (64 * nv) := fun r => val_toList_lt r
  intro fuel
  induction fuel with
  | zero =>
    intro q r borrow hinv hq1 hq2
    have hq : q.toNat = qt := by omega
    unfold correctLoop
    split_ifs with hb
    · subst hb
      refine ⟨q, r, rfl, hq, ?_⟩
      simp only [UInt64.toNat_zero, Nat.cast_zero, mul_zero, sub_zero] at hinv
      rw [hq] at hinv
      omega
    · exfalso
      have hb1 : 1 ≤ borrow.toNat := by
        rcases Nat.eq_zero_or_pos borrow.toNat with h0 | h0
        · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hb
        · exact h0
      have := hrl r
      rw [hq] at hinv
      have : (2 : ℤ) ^ (64 * nv) * 1 ≤ 2 ^ (64 * nv) * borrow.toNat :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hb1) (by positivity)
      have : (qt : ℤ) * val vw.toList ≤ U := by exact_mod_cast hlo
      have : (val r.toList : ℤ) < 2 ^ (64 * nv) := by exact_mod_cast hrl r
      linarith
  | succ fuel ih =>
    intro q r borrow hinv hq1 hq2
    unfold correctLoop
    split_ifs with hb
    · subst hb
      simp only [UInt64.toNat_zero, Nat.cast_zero, mul_zero, sub_zero] at hinv
      have hq : q.toNat = qt := by
        by_contra hne
        have : (qt + 1) * val vw.toList ≤ q.toNat * val vw.toList :=
          Nat.mul_le_mul_right _ (by omega)
        have : (q.toNat : ℤ) * val vw.toList ≤ U := by
          have := (Nat.cast_nonneg (val r.toList) : (0 : ℤ) ≤ _)
          linarith
        have : q.toNat * val vw.toList ≤ U := by exact_mod_cast this
        omega
      refine ⟨q, r, rfl, hq, ?_⟩
      rw [hq] at hinv
      omega
    · have hb1 : 1 ≤ borrow.toNat := by
        rcases Nat.eq_zero_or_pos borrow.toNat with h0 | h0
        · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hb
        · exact h0
      have hqgt : qt + 1 ≤ q.toNat := by
        have := hrl r
        have : (2 : ℤ) ^ (64 * nv) * 1 ≤ 2 ^ (64 * nv) * borrow.toNat :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hb1) (by positivity)
        have hlt : (U : ℤ) < q.toNat * val vw.toList := by
          have : (val r.toList : ℤ) < 2 ^ (64 * nv) := by exact_mod_cast hrl r
          linarith
        have : U < q.toNat * val vw.toList := by exact_mod_cast hlt
        by_contra hne
        have : q.toNat * val vw.toList ≤ qt * val vw.toList := Nat.mul_le_mul_right _ (by omega)
        omega
      simp only
      have hspan := val_span r 0 (TOP + 1) (by omega)
      have hrw : val (span r 0 (TOP + 1) (by omega)).toList = val r.toList := by
        simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one] at hspan
        rw [hspan, Nat.mod_eq_of_lt]
        rw [← hnv]; exact hrl r
      have hadd := add_spec (span r 0 (TOP + 1) (by omega)) vw (by omega)
      rw [hrw] at hadd
      set A := add (span r 0 (TOP + 1) (by omega)) vw (by omega) with hA
      have hc := Bool.toNat_le A.2
      have hq1 : (1 : Word) ≤ q := by rw [UInt64.le_iff_toNat_le]; show 1 ≤ q.toNat; omega
      have hqn : (q - 1).toNat = q.toNat - 1 := by rw [UInt64.toNat_sub_of_le _ _ hq1]; rfl
      have hcb : (if A.2 then (1 : Word) else 0) ≤ borrow := by
        rw [UInt64.le_iff_toNat_le, toNat_ite_bool]; omega
      have hbn : (borrow - if A.2 then 1 else 0).toNat = borrow.toNat - A.2.toNat := by
        rw [UInt64.toNat_sub_of_le _ _ hcb, toNat_ite_bool]
      have hset : val (setSpan r 0 A.1 (by omega)).toList = val A.1.toList := by
        rw [val_setSpan]
        simp only [Nat.pow_zero, Nat.mul_zero, Nat.mod_one, Nat.zero_add, Nat.one_mul]
        rw [Nat.div_eq_of_lt (by rw [← hnv]; exact hrl r)]
        simp
      obtain ⟨q', r', h1, h2, h3⟩ := ih (q - 1) (setSpan r 0 A.1 (by omega))
        (borrow - if A.2 then 1 else 0)
        (by
          rw [hset, hqn, hbn]
          rw [show 64 * nv = 64 * (TOP + 1) by rw [hnv]] at hinv ⊢
          have hadd' : (val A.1.toList : ℤ) + 2 ^ (64 * (TOP + 1)) * A.2.toNat =
              val r.toList + val vw.toList := by exact_mod_cast hadd
          push_cast [Nat.cast_sub hc, Nat.cast_sub (show 1 ≤ q.toNat by omega),
            Nat.cast_sub (show A.2.toNat ≤ borrow.toNat by omega)]
          linarith)
        (by rw [hqn]; omega)
        (by rw [hqn]; omega)
      exact ⟨q', r', h1, h2, h3⟩

end Intx.Model

namespace Intx.Model

@[simp] theorem fshl_zero (hi lo : Word) : fshl hi lo 0 = hi := by simp [fshl]

/-- Knuth, TAOCP Vol. 2, 4.3.1, Theorem B: the quotient estimate from the top words of a
normalized divisor is at most 2 too large. -/
theorem quotient_estimate (U V P vt qt qh : Nat) (hP : 0 < P) (hvt : 2 ^ 63 ≤ vt)
    (hV1 : vt * P ≤ V) (hV2 : V < (vt + 1) * P) (hqt : qt = U / V)
    (hqh : qh = U / P / vt) (hUt : U / P < vt * 2 ^ 64) :
    qt ≤ qh ∧ qh ≤ qt + 2 := by
  have hvt0 : 0 < vt := by omega
  have hV0 : 0 < V := lt_of_lt_of_le (Nat.mul_pos hvt0 hP) hV1
  have hle : qt ≤ qh := by
    rw [hqt, hqh, Nat.div_div_eq_div_mul, Nat.mul_comm P vt]
    exact Nat.div_le_div_left hV1 (Nat.mul_pos hvt0 hP)
  refine ⟨hle, ?_⟩
  by_contra hc
  have hqhB : qh < 2 ^ 64 := by
    rw [hqh, Nat.div_lt_iff_lt_mul hvt0, Nat.mul_comm]; exact hUt
  have ha : qh * vt ≤ U / P := by rw [hqh]; exact Nat.div_mul_le_self _ _
  have hb : U / P * P ≤ U := Nat.div_mul_le_self _ _
  have hd : U < V * (qt + 1) := by rw [hqt]; exact Nat.lt_mul_div_succ _ hV0
  have h1 : qh * vt * P ≤ U := le_trans (Nat.mul_le_mul_right _ ha) hb
  have h2 : V * (qt + 1) ≤ (vt + 1) * P * (qt + 1) := Nat.mul_le_mul_right _ hV2.le
  have h3 : qh * vt < (vt + 1) * (qt + 1) := by
    have : qh * vt * P < (vt + 1) * (qt + 1) * P := by nlinarith
    exact Nat.lt_of_mul_lt_mul_right this
  have h4 : (qt + 3) * vt ≤ qh * vt := Nat.mul_le_mul_right _ (by omega)
  nlinarith

/-- `udivrem_top1()` for a numerator of one word more than the normalized divisor, its top word less
than the top word of the divisor. -/
theorem udivrem_top1_spec (TOP : Nat) {nu nv : Nat} (u : Vector Word nu) (v : Vector Word nv)
    (h1 : 1 ≤ TOP ∧ TOP < nv) (h2 : nu = TOP + 1 ∨ nu = TOP + 2) (hnu : nu = TOP + 2)
    (hnv : nv = TOP + 1) (hv : 2 ^ 63 ≤ (v[TOP]'(by omega)).toNat)
    (hu : (u[TOP + 1]'(by omega)).toNat < (v[TOP]'(by omega)).toNat) :
    ∃ quot rem, udivrem_top1 TOP u v h1 h2 = some (quot, rem) ∧
      (quot[0]'(by omega)).toNat = val u.toList / val v.toList ∧
      val rem.toList = val u.toList % val v.toList := by
  have hW : decide (nu > nv) = true := decide_eq_true (by omega)
  have hv0 : v[TOP]'(by omega) ≠ 0 := by
    intro h0; rw [h0] at hv; simp at hv
  obtain ⟨s, hs, hs1, hs2⟩ := clz_nonzero_spec (v[TOP]'(by omega)) hv0
  have hs0 : s = 0 := by
    apply Fin.ext
    have hvl := (v[TOP]'(by omega)).toNat_lt
    by_contra hne
    have : 2 ≤ 2 ^ s.val := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ s.val := Nat.pow_le_pow_right (by norm_num) (by simp at hne ⊢; omega)
    nlinarith
  subst hs0
  -- The numbers.
  have hUl := val_toList_lt u
  have hVl := val_toList_lt v
  have hP : 0 < 2 ^ (64 * TOP) := by positivity
  have hvt : val v.toList / 2 ^ (64 * TOP) = (v[TOP]'(by omega)).toNat :=
    val_div_pow_top v TOP (by omega)
  have hut : val u.toList / 2 ^ (64 * TOP) =
      (u[TOP]'(by omega)).toNat + 2 ^ 64 * (u[TOP + 1]'(by omega)).toNat := by
    rw [val_div_pow u TOP (by omega), val_div_pow_top u (TOP + 1) (by omega)]
  have hue : val u.toList / 2 ^ (64 * (TOP + 1)) = (u[TOP + 1]'(by omega)).toNat :=
    val_div_pow_top u (TOP + 1) (by omega)
  have hV1 : (v[TOP]'(by omega)).toNat * 2 ^ (64 * TOP) ≤ val v.toList := by
    rw [← hvt]; exact Nat.div_mul_le_self _ _
  have hV2 : val v.toList < ((v[TOP]'(by omega)).toNat + 1) * 2 ^ (64 * TOP) := by
    rw [← hvt, Nat.mul_comm]; exact Nat.lt_mul_div_succ _ hP
  -- The estimate.
  obtain ⟨qh, rh, hdiv, hqh, _⟩ := udivrem_2by1_spec ⟨u[TOP]'(by omega), u[TOP + 1]'(by omega)⟩
    (v[TOP]'(by omega)) (UInt64.lt_iff_toNat_lt.mpr hu)
  have hqh' : qh.toNat = val u.toList / 2 ^ (64 * TOP) / (v[TOP]'(by omega)).toNat := by
    rw [hqh, hut]; rfl
  have hUt : val u.toList / 2 ^ (64 * TOP) < (v[TOP]'(by omega)).toNat * 2 ^ 64 := by
    rw [hut]
    have := (u[TOP]'(by omega)).toNat_lt
    nlinarith
  obtain ⟨hk1, hk2⟩ := quotient_estimate (val u.toList) (val v.toList) (2 ^ (64 * TOP))
    (v[TOP]'(by omega)).toNat (val u.toList / val v.toList) qh.toNat hP hv hV1 hV2 rfl hqh' hUt
  -- The remainder of the estimate.
  have hvw : val (span v 0 (TOP + 1) (by omega)).toList = val v.toList := by
    rw [val_span]; simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one]
    exact Nat.mod_eq_of_lt (by rw [← hnv]; exact hVl)
  have hul : val (span u 0 (TOP + 1) (by omega)).toList = val u.toList % 2 ^ (64 * (TOP + 1)) := by
    rw [val_span]; simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one]
  have hsub := submul_spec (span u 0 (TOP + 1) (by omega)) (span v 0 (TOP + 1) (by omega)) qh
    (by omega)
  rw [hvw, hul] at hsub
  set S := submul (span u 0 (TOP + 1) (by omega)) (span v 0 (TOP + 1) (by omega)) qh (by omega)
    with hS
  have hsplit := Nat.mod_add_div (val u.toList) (2 ^ (64 * (TOP + 1)))
  rw [hue] at hsplit
  have hVB : val v.toList < 2 ^ (64 * (TOP + 1)) := by rw [← hnv]; exact hVl
  have hV0 : 0 < val v.toList := lt_of_lt_of_le (Nat.mul_pos (by omega) hP) hV1
  have hqtV : val u.toList < (val u.toList / val v.toList + 1) * val v.toList := by
    rw [Nat.mul_comm]; exact Nat.lt_mul_div_succ _ hV0
  have hqtV' : val u.toList / val v.toList * val v.toList ≤ val u.toList := Nat.div_mul_le_self _ _
  have hqhV : val u.toList / val v.toList * val v.toList ≤ qh.toNat * val v.toList :=
    Nat.mul_le_mul_right _ hk1
  have hue_le : (u[TOP + 1]'(by omega)).toNat ≤ S.2.toNat := by
    by_contra hc
    have : 2 ^ (64 * (TOP + 1)) * (S.2.toNat + 1) ≤ 2 ^ (64 * (TOP + 1)) * (u[TOP + 1]'(by omega)).toNat :=
      Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_add, Nat.mul_one] at this
    rw [Nat.add_mul, Nat.one_mul] at hqtV
    omega
  have hb : (S.2 - u[TOP + 1]'(by omega)).toNat = S.2.toNat - (u[TOP + 1]'(by omega)).toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hue_le)]
  have hset : val (setSpan (Vector.replicate nv 0) 0 S.1 (by omega)).toList = val S.1.toList := by
    rw [val_setSpan]; simp
  obtain ⟨q', r', hcl, hq', hr'⟩ := correctLoop_spec TOP (span v 0 (TOP + 1) (by omega)) h1 hnv
    (val u.toList) (val u.toList / val v.toList) (by rw [hvw]; exact hqtV')
    (by rw [hvw]; exact hqtV) 2 qh (setSpan (Vector.replicate nv 0) 0 S.1 (by omega))
    (S.2 - u[TOP + 1]'(by omega))
    (by
      rw [hset, hb, hvw, show 64 * nv = 64 * (TOP + 1) by rw [hnv]]
      push_cast [Nat.cast_sub hue_le]
      have hsub' : (val S.1.toList : ℤ) + qh.toNat * val v.toList =
          (val u.toList % 2 ^ (64 * (TOP + 1)) : ℕ) + 2 ^ (64 * (TOP + 1)) * S.2.toNat := by
        exact_mod_cast hsub
      have hsplit' : ((val u.toList % 2 ^ (64 * (TOP + 1)) : ℕ) : ℤ) +
          2 ^ (64 * (TOP + 1)) * (u[TOP + 1]'(by omega)).toNat = val u.toList := by
        exact_mod_cast hsplit
      linarith)
    hk1 (by omega)
  refine ⟨resize nu #v[q'], r', ?_, ?_, ?_⟩
  · unfold udivrem_top1
    simp only [hW, Bool.not_true, Bool.false_eq_true, ↓reduceIte, dif_pos hnu, pure_bind, hs,
      Option.bind_eq_bind, Option.bind_some, fshl_zero]
    simp only [hdiv, Option.bind_some, ← hS, hcl, dif_neg (show ¬TOP + 1 < nv by omega)]
    rfl
  · simp [resize, hq']
  · rw [hr', hvw]
    have := Nat.mod_add_div (val u.toList) (val v.toList)
    rw [Nat.mul_comm] at this
    omega

end Intx.Model
