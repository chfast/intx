import Intx.Proofs.Div
import Intx.Proofs.FoldMath
import Intx.Model.MulmodFold
set_option warningAsError true
/-!
# Proofs: `mulmod()`

The main theorem `mulmod_correct`: the model of `mulmod()` computes `x * y mod m` for every nonzero
`m`, without undefined behavior, with and without the `div` instruction (`Platform`). `mulmod_fold_spec` follows `internal::mulmod_fold<N>()` through
its code: the normalized modulus `d`, `C0`, the power-of-2 case, `q` and `C1` from the division,
the folds (`Intx.fold_congr`, `Intx.fold_deficit`, `Intx.fold_q0`), the Barrett estimate
(`Intx.barrett`) and the final corrections.
-/

namespace Intx.Model

theorem val_vec2 (a b : Word) : val (#v[a, b] : Vector Word 2).toList = a.toNat + 2 ^ 64 * b.toNat := by
  simp

theorem getElem_top_toNat {n : Nat} (v : Vector Word (n + 1)) :
    v[n].toNat = val v.toList / 2 ^ (64 * n) := (val_div_pow_top v n rfl).symm

theorem val_split_top {n : Nat} (v : Vector Word (n + 1)) :
    val v.toList = val v.toList % 2 ^ (64 * n) + 2 ^ (64 * n) * v[n].toNat := by
  rw [getElem_top_toNat]; exact (Nat.mod_add_div _ _).symm

theorem val_span_low {n : Nat} (v : Vector Word (n + 1)) (h : 0 + n ≤ n + 1) :
    val (span v 0 n h).toList = val v.toList % 2 ^ (64 * n) := by
  rw [val_span]; simp

theorem val_set_top {n : Nat} (v : Vector Word (n + 1)) (x : Word) (h : n < n + 1) :
    val (v.set n x h).toList = val v.toList % 2 ^ (64 * n) + 2 ^ (64 * n) * x.toNat := by
  have h1 := val_toList_set v n x h
  have h2 := val_split_top v
  omega

theorem val_setSpan_low {n : Nat} (v : Vector Word (n + 1)) (w : Vector Word n) (h : 0 + n ≤ n + 1) :
    val (setSpan v 0 w h).toList = val w.toList + 2 ^ (64 * n) * v[n].toNat := by
  rw [val_setSpan, getElem_top_toNat]
  simp [Nat.mod_one]

theorem getElem_setSpan_top {n : Nat} (v : Vector Word (n + 1)) (w : Vector Word n) (h : 0 + n ≤ n + 1) :
    (setSpan v 0 w h)[n] = v[n] := by
  rw [getElem_setSpan]; simp

/-- The words 2 and 3 of a 4-word number. -/
theorem val_div_pow2 (v : Vector Word 4) :
    val v.toList / 2 ^ 128 = v[2].toNat + 2 ^ 64 * v[3].toNat := by
  have := val_div_pow v 2 (by omega)
  rw [show 64 * 2 = 128 by norm_num] at this
  rw [this, val_div_pow_top v 3 rfl]

set_option maxHeartbeats 4000000 in
theorem mulmod_fold_spec (P : Platform) (N : Nat) (x y m : U256) (hN : 1 ≤ N ∧ N ≤ 4)
    (hm : m[N - 1] ≠ 0) (hmN : val m.toList < 2 ^ (64 * N)) :
    ∃ r, mulmod_fold P N x y m hN = some r ∧
      val r.toList = val x.toList * val y.toList % val m.toList := by
  obtain ⟨s, hs, hs1, hs2⟩ := clz_nonzero_spec m[N - 1] hm
  unfold mulmod_fold
  simp (config := { zeta := false }) only [require_pos hm, Option.bind_eq_bind, Option.bind_some, hs]
  lift_lets
  intro d c0b c0b' c0 p pw res jp1 jp2 jp3 jp4
  have hN1 := hN.1
  have hN4 := hN.2
  -- The modulus and its normalized form d.
  have hP0 : 0 < 2 ^ (64 * (N - 1)) := by positivity
  have hBP : (2 : ℕ) ^ (64 * N) = 2 ^ 64 * 2 ^ (64 * (N - 1)) := by
    rw [← pow_add]; congr 1; omega
  have hmtop : val m.toList / 2 ^ (64 * (N - 1)) = m[N - 1].toNat := by
    rw [val_div_pow m (N - 1) (by omega),
      Nat.div_eq_of_lt (show val m.toList < 2 ^ (64 * (N - 1 + 1)) by rw [show N - 1 + 1 = N by omega]; exact hmN)]
    simp
  have hM1 : m[N - 1].toNat * 2 ^ (64 * (N - 1)) ≤ val m.toList := by
    rw [← hmtop]; exact Nat.div_mul_le_self _ _
  have hM2 : val m.toList < (m[N - 1].toNat + 1) * 2 ^ (64 * (N - 1)) := by
    rw [← hmtop, Nat.mul_comm]; exact Nat.lt_mul_div_succ _ hP0
  have hDlt : val m.toList * 2 ^ s.val < 2 ^ (64 * N) := by
    have h2s : (m[N - 1].toNat + 1) * 2 ^ s.val ≤ 2 ^ 64 := by
      have : 2 ^ s.val ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 (by omega)
      have : m[N - 1].toNat * 2 ^ s.val + 2 ^ s.val ≤ 2 ^ 64 := by
        obtain ⟨c, hc⟩ := this
        have : m[N - 1].toNat * 2 ^ s.val < 2 ^ s.val * c := by rw [← hc]; exact hs2
        have : m[N - 1].toNat < c := by
          rw [Nat.mul_comm] at this; exact Nat.lt_of_mul_lt_mul_left this
        nlinarith
      rw [Nat.add_mul, Nat.one_mul]; exact this
    calc val m.toList * 2 ^ s.val < (m[N - 1].toNat + 1) * 2 ^ (64 * (N - 1)) * 2 ^ s.val :=
          Nat.mul_lt_mul_of_pos_right hM2 (by positivity)
      _ = (m[N - 1].toNat + 1) * 2 ^ s.val * 2 ^ (64 * (N - 1)) := by ring
      _ ≤ 2 ^ 64 * 2 ^ (64 * (N - 1)) := Nat.mul_le_mul_right _ h2s
      _ = 2 ^ (64 * N) := hBP.symm
  have hDge : 2 ^ (64 * N) ≤ 2 * (val m.toList * 2 ^ s.val) := by
    rw [hBP]
    calc 2 ^ 64 * 2 ^ (64 * (N - 1)) = 2 * 2 ^ 63 * 2 ^ (64 * (N - 1)) := by norm_num
      _ ≤ 2 * (m[N - 1].toNat * 2 ^ s.val) * 2 ^ (64 * (N - 1)) := by
          apply Nat.mul_le_mul_right; omega
      _ ≤ 2 * (val m.toList * 2 ^ s.val) := by
          have := Nat.mul_le_mul_right (2 ^ s.val) hM1
          nlinarith
  have hd : val d.toList = val m.toList * 2 ^ s.val := by
    simp only [d]
    rw [shl_spec, val_span]
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one]
    rw [Nat.mod_eq_of_lt hmN, Nat.mod_eq_of_lt hDlt]
  -- C0 = B^N - D.
  -- C0 = B^N - D.
  have hDpos : 0 < val d.toList := by rw [hd]; omega
  have hsubc := submul_spec (span c0b 1 N (by omega)) d 1 (by omega)
  have hc0b0 : val c0b.toList = 0 := by simp [c0b]
  have hz : val (span c0b 1 N (by omega)).toList = 0 := by
    rw [val_span, hc0b0]; simp
  rw [hz] at hsubc
  simp only [UInt64.toNat_one, Nat.one_mul, Nat.zero_add] at hsubc
  have hwl := val_toList_lt (submul (span c0b 1 N (by omega)) d 1 (by omega)).1
  have hb1 : (submul (span c0b 1 N (by omega)) d 1 (by omega)).2.toNat = 1 := by
    have hdl := val_toList_lt d
    rcases Nat.lt_or_ge (submul (span c0b 1 N (by omega)) d 1 (by omega)).2.toNat 1 with h | h
    · have : (submul (span c0b 1 N (by omega)) d 1 (by omega)).2.toNat = 0 := by omega
      rw [this] at hsubc; omega
    · rcases Nat.lt_or_ge (submul (span c0b 1 N (by omega)) d 1 (by omega)).2.toNat 2 with h' | h'
      · omega
      · have := Nat.mul_le_mul_left (2 ^ (64 * N)) h'
        omega
  rw [hb1, Nat.mul_one] at hsubc
  have hc0b : val c0b'.toList = 2 ^ 64 * (2 ^ (64 * N) - val d.toList) := by
    simp only [c0b']
    rw [val_setSpan, hc0b0]
    simp only [Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.zero_add,
      show 64 * 1 = 64 by norm_num]
    omega
  have hc0 : val c0.toList = 2 ^ (64 * N) - val d.toList := by
    simp only [c0]
    rw [val_span, hc0b, show 64 * 1 = 64 by norm_num, Nat.mul_div_cancel_left _ (by positivity),
      Nat.mod_eq_of_lt (by omega)]
  have hp : val p.toList = val x.toList * val y.toList := umulWords_spec x y
  have hdl := val_toList_lt d
  -- The top words of C0 and d.
  have hc0t : c0[N - 1].toNat = val c0.toList / 2 ^ (64 * (N - 1)) :=
    (val_div_pow_top c0 (N - 1) (by omega)).symm
  have hdt : d[N - 1].toNat = val d.toList / 2 ^ (64 * (N - 1)) :=
    (val_div_pow_top d (N - 1) (by omega)).symm
  have hdt63 : 2 ^ 63 ≤ d[N - 1].toNat := by
    rw [hdt, Nat.le_div_iff_mul_le hP0]
    have : 2 ^ 64 * 2 ^ (64 * (N - 1)) ≤ 2 * val d.toList := by rw [← hBP, hd]; exact hDge
    omega
  -- The product shifted by s.
  have hXY : val x.toList * val y.toList < 2 ^ 512 := by
    calc val x.toList * val y.toList < 2 ^ 256 * 2 ^ 256 :=
          Nat.mul_lt_mul'' (by simpa using val_toList_lt x) (by simpa using val_toList_lt y)
      _ = 2 ^ 512 := by rw [← pow_add]
  have hpw : val pw.toList = val x.toList * val y.toList * 2 ^ s.val := by
    simp only [pw]
    rw [shl_spec, val_span, hp]
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one]
    rw [Nat.mod_eq_of_lt (show val x.toList * val y.toList < 2 ^ (64 * 8) by
        rw [show 64 * 8 = 512 by norm_num]; exact hXY),
      Nat.mod_eq_of_lt]
    calc val x.toList * val y.toList * 2 ^ s.val < 2 ^ 512 * 2 ^ 64 :=
          Nat.mul_lt_mul'' hXY (Nat.pow_lt_pow_right (by norm_num) s.isLt)
      _ = 2 ^ (64 * 9) := by rw [← pow_add]
  have hpwm : val pw.toList % val d.toList / 2 ^ s.val =
      val x.toList * val y.toList % val m.toList := by
    rw [hpw, hd, Nat.mul_mod_mul_right, Nat.mul_div_cancel _ (by positivity)]
  -- The final shift.
  have hjp1 : ∀ (r : Vector Word (N + 1)) (u : PUnit),
      val (span r 0 N (by omega)).toList = val pw.toList % val d.toList →
      ∃ w, jp1 r u = some w ∧ val w.toList = val x.toList * val y.toList % val m.toList := by
    intro r u hr
    refine ⟨_, rfl, ?_⟩
    rw [val_setSpan]
    simp only [res, val_toList_replicate_zero, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero,
      Nat.zero_add, Nat.mul_zero, pow_zero, Nat.one_mul]
    rw [shr_spec, hr, hpwm]
  -- The final subtraction of d.
  have hjp2 : ∀ (r : Vector Word (N + 1)) (u : PUnit), val r.toList < 2 * val d.toList →
      val r.toList % val d.toList = val pw.toList % val d.toList →
      ∃ w, jp2 r u = some w ∧ val w.toList = val x.toList * val y.toList % val m.toList := by
    intro r u hr hrm
    simp (config := { zeta := false }) only [jp2]
    lift_lets
    intro r1
    have hsub := submul_spec (span r 0 N (by omega)) d 1 (by omega)
    simp only [UInt64.toNat_one, Nat.one_mul] at hsub
    rw [val_span_low] at hsub
    have hsplit := val_split_top r
    have htl := val_toList_lt (submul (span r 0 N (by omega)) d 1 (by omega)).1
    have hBP2 : 2 ^ (64 * N) ≤ 2 * val d.toList := by rw [hd]; exact hDge
    have hrN : r[N].toNat ≤ 1 := by
      by_contra h
      have : 2 ^ (64 * N) * 2 ≤ 2 ^ (64 * N) * r[N].toNat := Nat.mul_le_mul_left _ (by omega)
      omega
    have hb2 : (submul (span r 0 N (by omega)) d 1 (by omega)).2.toNat ≤ 1 := by
      by_contra h
      have : 2 ^ (64 * N) * 2 ≤ 2 ^ (64 * N) * (submul (span r 0 N (by omega)) d 1 (by omega)).2.toNat :=
        Nat.mul_le_mul_left _ (by omega)
      have := Nat.mod_lt (val r.toList) (show 0 < 2 ^ (64 * N) by positivity)
      omega
    have hmodl := Nat.mod_lt (val r.toList) (show 0 < 2 ^ (64 * N) by positivity)
    have hcases : (r[N].toNat = 0 ∨ r[N].toNat = 1) ∧
        ((submul (span r 0 N (by omega)) d 1 (by omega)).2.toNat = 0 ∨
          (submul (span r 0 N (by omega)) d 1 (by omega)).2.toNat = 1) := ⟨by omega, by omega⟩
    by_cases hge : val d.toList ≤ val r.toList
    · have hcond : r[N] ≥ (submul (span r 0 N (by omega)) d 1 (by omega)).2 := by
        rw [ge_iff_le, UInt64.le_iff_toNat_le]
        rcases hcases with ⟨h0 | h0, h1 | h1⟩ <;> simp only [h0, h1, Nat.mul_zero, Nat.mul_one] at hsub hsplit ⊢ <;>
          omega
      rw [if_pos hcond]
      simp only [Option.pure_def, Option.bind_some]
      refine hjp1 r1 PUnit.unit ?_
      have : val (span r1 0 N (by omega)).toList =
          val (submul (span r 0 N (by omega)) d 1 (by omega)).1.toList := by
        simp only [r1, copy_eq_setSpan]
        rw [val_span_low, val_setSpan_low]
        have := val_toList_lt (submul (span r 0 N (by omega)) d 1 (by omega)).1
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt this]
      rw [this, ← hrm, Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
      rcases hcases with ⟨h0 | h0, h1 | h1⟩ <;> simp only [h0, h1, Nat.mul_zero, Nat.mul_one] at hsub hsplit hcond ⊢ <;>
        omega
    · have hcond : ¬ r[N] ≥ (submul (span r 0 N (by omega)) d 1 (by omega)).2 := by
        rw [ge_iff_le, UInt64.le_iff_toNat_le]
        rcases hcases with ⟨h0 | h0, h1 | h1⟩ <;> simp only [h0, h1, Nat.mul_zero, Nat.mul_one] at hsub hsplit ⊢ <;>
          omega
      rw [if_neg hcond]
      simp only [Option.pure_def, Option.bind_some]
      refine hjp1 r PUnit.unit ?_
      rw [val_span_low, ← hrm, Nat.mod_eq_of_lt (by omega : val r.toList < val d.toList)]
      apply Nat.mod_eq_of_lt
      rcases hcases with ⟨h0 | h0, h1 | h1⟩ <;> simp only [h0, h1, Nat.mul_zero, Nat.mul_one] at hsub hsplit ⊢ <;>
        omega
  -- The rest after q and C1.
  have hjp3 : ∀ (q : Word) (c1 : Vector Word N),
      q.toNat * val d.toList + val c1.toList = 2 ^ 64 * val c0.toList →
      val c1.toList < val d.toList →
      ∃ r, jp3 (q, c1) = some r ∧ val r.toList = val x.toList * val y.toList % val m.toList := by
    intro q c1 hq hc1
    simp (config := { zeta := false }) only [jp3]
    have hpwl : val pw.toList < 2 ^ 512 * 2 ^ 63 := by
      have h2 : 2 ^ s.val ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [hpw]
      exact Nat.mul_lt_mul_of_lt_of_le hXY h2 (by positivity)
    -- The top N + 1 words of the shifted product.
    refine ex_bind (fun r : Vector Word (N + 1) => val r.toList = val pw.toList / 2 ^ (64 * (8 - N)))
      (ex_mono (forIn'_rco0_ex
        (fun k (r : Vector Word (N + 1)) => ∀ i (hi : i < N + 1), i < k → r[i] = pw[8 - N + i])
        (fun i hi h => by omega)
        (fun j b hj hm hI => ⟨_, rfl, fun i hi hij => by
          rw [Vector.getElem_set]
          split_ifs with he
          · subst he; rfl
          · exact hI i hi (by omega)⟩))
        (fun r hr => by
          rw [val_toList_eq_of_getElem r (val pw.toList / 2 ^ (64 * (8 - N)))]
          · apply Nat.mod_eq_of_lt
            rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
            calc val pw.toList < 2 ^ (64 * 9) := val_toList_lt pw
              _ = 2 ^ (64 * (N + 1) + 64 * (8 - N)) := by congr 1; omega
          · intro i hi
            rw [hr i hi hi, getElem_toNat', Nat.div_div_eq_div_mul, ← pow_add]
            congr 3; omega)) ?_
    intro r0 hr0
    lift_lets
    intro rr
    have hBN : (2 : ℕ) ^ (64 * N) = 2 ^ 64 * 2 ^ (64 * (N - 1)) := hBP
    have hC0D' : val d.toList + val c0.toList = 2 ^ 64 * 2 ^ (64 * (N - 1)) := by
      rw [hc0, ← hBN]; omega
    have hqC : 2 ^ 64 * val c0.toList = q.toNat * val d.toList + val c1.toList := by omega
    refine ex_bind (fun r : Vector Word (N + 1) =>
        val r.toList % val d.toList = val pw.toList % val d.toList ∧
        val r.toList + 2 * 2 ^ (64 * N) ≤ 2 ^ 64 * 2 ^ (64 * N))
      (ex_mono (forIn'_rco0_ex
        (fun k (r : Vector Word (N + 1)) =>
          val r.toList % val d.toList = val pw.toList / 2 ^ (64 * (8 - N - k)) % val d.toList ∧
          (1 ≤ q.toNat → 2 ^ 64 * 2 ^ (64 * N) ≤ 2 ^ (k + 1) * (2 ^ 64 * 2 ^ (64 * N) - val r.toList)) ∧
          (q.toNat = 0 → val r.toList < (2 ^ 63 + k) * 2 ^ (64 * N)))
        ?_ ?_) ?_) ?_
    · -- Before the folds: the top N + 1 words of the product, less than 2^63 * B^N.
      have hR0 : val rr.toList < 2 ^ 63 * 2 ^ (64 * N) := by
        simp only [rr]
        rw [hr0, Nat.div_lt_iff_lt_mul (by positivity)]
        have e : (2 : ℕ) ^ 512 * 2 ^ 63 = 2 ^ 63 * 2 ^ (64 * N) * 2 ^ (64 * (8 - N)) := by
          rw [← pow_add, ← pow_add, ← pow_add]; congr 1; omega
        exact e ▸ hpwl
      refine ⟨by simp only [rr, Nat.sub_zero]; rw [hr0], fun _ => ?_, fun _ => ?_⟩
      · have : 2 * 2 ^ 63 = 2 ^ 64 := by norm_num
        have : 2 * (2 ^ 63 * 2 ^ (64 * N)) = 2 ^ 64 * 2 ^ (64 * N) := by rw [← Nat.mul_assoc, this]
        rw [show 0 + 1 = 1 by rfl, pow_one]
        omega
      · simpa using hR0
    · intro j b hj hm ⟨hI1, hI2, hI3⟩
      lift_lets
      intro rb acc0
      have ha := pw[8 - N - j - 1]'(by omega)
      -- The words of the next remainder before the multiplications.
      refine ex_bind_yield (fun acc : Vector Word (N + 1) =>
          val acc.toList = (pw[8 - N - j - 1]'(by omega)).toNat + 2 ^ 64 * (val b.toList % 2 ^ (64 * (N - 1))))
        (ex_mono (forIn'_rco_ex
          (fun k (acc : Vector Word (N + 1)) => acc[0] = pw[8 - N - j - 1]'(by omega) ∧
            (∀ i (hi : i < N + 1), 1 ≤ i → i < 1 + k → acc[i] = b[i - 1]) ∧
            (∀ i (hi : i < N + 1), 1 + k ≤ i → acc[i] = 0))
          ⟨by simp [acc0], fun i hi h1 h2 => by omega,
            fun i hi h1 => by
              simp only [acc0, c0b]
              rw [Vector.getElem_set, if_neg (by omega)]
              simp⟩
          (fun k acc hk hm' ⟨hA0, hA1, hA2⟩ => ⟨_, rfl, by
            rw [Vector.getElem_set, if_neg (by omega)]; exact hA0,
            fun i hi h1 h2 => by
              rw [Vector.getElem_set]
              split_ifs with he
              · subst he; rfl
              · exact hA1 i hi h1 (by omega),
            fun i hi h1 => by
              rw [Vector.getElem_set, if_neg (by omega)]
              exact hA2 i hi (by omega)⟩))
          (fun acc ⟨hA0, hA1, hA2⟩ => by
            have hlow := Nat.mod_lt (val b.toList) (show 0 < 2 ^ (64 * (N - 1)) by positivity)
            have hX : (pw[8 - N - j - 1]'(by omega)).toNat + 2 ^ 64 * (val b.toList % 2 ^ (64 * (N - 1))) <
                2 ^ (64 * N) := by
              have := (pw[8 - N - j - 1]'(by omega)).toNat_lt
              rw [hBN]
              have : 2 ^ 64 * (val b.toList % 2 ^ (64 * (N - 1)) + 1) ≤ 2 ^ 64 * 2 ^ (64 * (N - 1)) :=
                Nat.mul_le_mul_left _ hlow
              omega
            rw [val_toList_eq_of_getElem acc _ (fun i hi => ?_), Nat.mod_eq_of_lt (by
              calc _ < 2 ^ (64 * N) := hX
                _ ≤ 2 ^ (64 * (N + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega))]
            rcases Nat.eq_zero_or_pos i with h0 | h0
            · subst h0
              rw [hA0]
              simp only [Nat.mul_zero, pow_zero, Nat.div_one, Nat.add_mul_mod_self_left]
              rw [Nat.mod_eq_of_lt (UInt64.toNat_lt _)]
            · by_cases hiN : i < N
              · rw [hA1 i hi h0 (by omega), getElem_toNat' b (i - 1) (by omega)]
                have e : 2 ^ (64 * i) = 2 ^ 64 * 2 ^ (64 * (i - 1)) := by
                  rw [← pow_add]; congr 1; omega
                rw [e, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by positivity),
                  Nat.div_eq_of_lt (UInt64.toNat_lt _), Nat.zero_add,
                  mod_div_mod_pow _ _ _ _ (by omega)]
              · have : i = N := by omega
                subst this
                rw [hA2 i hi (by omega), Nat.div_eq_of_lt hX]
                rfl)) ?_
      intro acc hacc
      lift_lets
      intro accA a1 a2 a3 a4 rr'
      refine ⟨rr', rfl, ?_⟩
      -- The numbers of the fold.
      have hBl : (0 : ℕ) < 2 ^ 64 := by positivity
      have hlow := Nat.mod_lt (val b.toList) (show 0 < 2 ^ (64 * (N - 1)) by positivity)
      have hbt : val b.toList / 2 ^ (64 * (N - 1)) = b[N - 1].toNat + 2 ^ 64 * b[N].toNat := by
        rw [val_div_pow b (N - 1) (by omega), show N - 1 + 1 = N by omega, getElem_top_toNat]
      have hbsplit : val b.toList =
          b[N].toNat * (2 ^ 64 * 2 ^ (64 * (N - 1))) + b[N - 1].toNat * 2 ^ (64 * (N - 1)) +
            val b.toList % 2 ^ (64 * (N - 1)) := by
        have := Nat.mod_add_div (val b.toList) (2 ^ (64 * (N - 1)))
        rw [hbt] at this
        nth_rewrite 1 [← this]
        ring
      have hpwt : val pw.toList / 2 ^ (64 * (8 - N - (j + 1))) =
          (pw[8 - N - j - 1]'(by omega)).toNat + 2 ^ 64 * (val pw.toList / 2 ^ (64 * (8 - N - j))) := by
        rw [show 8 - N - (j + 1) = 8 - N - j - 1 by omega, val_div_pow pw (8 - N - j - 1) (by omega),
          show 8 - N - j - 1 + 1 = 8 - N - j by omega]
      -- The first multiplication: R[N - 1] * C0.
      have haccA : val accA.toList = (pw[8 - N - j - 1]'(by omega)).toNat +
          2 ^ 64 * (val b.toList % 2 ^ (64 * (N - 1))) := hacc
      have hXa : val accA.toList < 2 ^ (64 * N) := by
        rw [haccA, hBN]
        have := (pw[8 - N - j - 1]'(by omega)).toNat_lt
        have : 2 ^ 64 * (val b.toList % 2 ^ (64 * (N - 1)) + 1) ≤ 2 ^ 64 * 2 ^ (64 * (N - 1)) :=
          Nat.mul_le_mul_left _ hlow
        omega
      have haccN : accA[N].toNat = 0 := by rw [getElem_top_toNat, Nat.div_eq_of_lt hXa]
      obtain ⟨A1, c, hA1⟩ : ∃ A1 c, addmul (span accA 0 N (by omega)) c0 rb[N - 1] (by omega) = (A1, c) :=
        ⟨_, _, rfl⟩
      have hsA1 := addmul_spec (span accA 0 N (by omega)) c0 rb[N - 1] (by omega)
      rw [hA1, val_span_low, Nat.mod_eq_of_lt hXa] at hsA1
      have hrb : rb = b := rfl
      simp only [hrb] at hsA1
      have ha1 : a1 = setSpan accA 0 A1 (by omega) := by simp only [a1, hA1]
      have ha2 : a2 = a1.set N (a1[N] + c) (by omega) := by simp only [a2, a1, hA1]
      have hA1l := val_toList_lt A1
      have ha1v : val a1.toList = val A1.toList := by
        rw [ha1, val_setSpan_low, haccN, Nat.mul_zero, Nat.add_zero]
      have ha1N : a1[N] = accA[N] := by rw [ha1, getElem_setSpan_top]
      have hc0w : a1[N] + c = c := by
        rw [ha1N]; apply UInt64.toNat_inj.mp; rw [UInt64.toNat_add, haccN, Nat.zero_add,
          Nat.mod_eq_of_lt (UInt64.toNat_lt _)]
      have ha2v : val a2.toList = val A1.toList + 2 ^ (64 * N) * c.toNat := by
        rw [ha2, val_set_top, ha1v, Nat.mod_eq_of_lt hA1l, hc0w]
      have ha2N : a2[N] = c := by rw [ha2, Vector.getElem_set_self, hc0w]
      -- The second multiplication: R[N] * C1.
      obtain ⟨A2, c', hA2⟩ : ∃ A2 c', addmul (span a2 0 N (by omega)) c1 rb[N] (by omega) = (A2, c') :=
        ⟨_, _, rfl⟩
      have hsA2 := addmul_spec (span a2 0 N (by omega)) c1 rb[N] (by omega)
      rw [hA2, val_span_low, ha2v, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hA1l] at hsA2
      simp only [hrb] at hsA2
      have ha3 : a3 = setSpan a2 0 A2 (by omega) := by simp only [a3, hA2]
      have ha4 : a4 = a3.set N (a3[N] + c') (by omega) := by simp only [a4, a3, hA2]
      have hA2l := val_toList_lt A2
      have ha3N : a3[N] = c := by rw [ha3, getElem_setSpan_top, ha2N]
      have ha3v : val a3.toList = val A2.toList + 2 ^ (64 * N) * c.toNat := by
        rw [ha3, val_setSpan_low, ha2N]
      -- The new remainder.
      have hfl := fold_lt (2 ^ 64) (2 ^ (64 * (N - 1))) (val d.toList) (val c0.toList) (val c1.toList)
        (pw[8 - N - j - 1]'(by omega)).toNat (val b.toList % 2 ^ (64 * (N - 1))) b[N - 1].toNat
        b[N].toNat hC0D' hc1 (UInt64.toNat_lt _) hlow (UInt64.toNat_lt _) (UInt64.toNat_lt _)
      have hRv : val rr'.toList = (pw[8 - N - j - 1]'(by omega)).toNat +
          2 ^ 64 * (val b.toList % 2 ^ (64 * (N - 1))) + b[N - 1].toNat * val c0.toList +
            b[N].toNat * val c1.toList := by
        show val a4.toList = _
        rw [haccA] at hsA1
        have hfl' : (pw[8 - N - j - 1]'(by omega)).toNat + 2 ^ 64 * (val b.toList % 2 ^ (64 * (N - 1))) +
            b[N - 1].toNat * val c0.toList + b[N].toNat * val c1.toList < 2 ^ 64 * 2 ^ (64 * N) := by
          rw [hBN]; exact hfl
        have hcc : c.toNat + c'.toNat < 2 ^ 64 := by
          have h1 : 2 ^ (64 * N) * (c.toNat + c'.toNat) < 2 ^ (64 * N) * 2 ^ 64 := by
            rw [Nat.mul_add]; omega
          exact Nat.lt_of_mul_lt_mul_left h1
        rw [ha4, val_set_top, ha3v, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hA2l, ha3N,
          UInt64.toNat_add, Nat.mod_eq_of_lt hcc, Nat.mul_add]
        omega
      have hBP2 : 2 ^ (64 * N) ≤ 2 * val d.toList := by rw [hd]; exact hDge
      have hbl : val b.toList < 2 ^ 64 * 2 ^ (64 * N) := by
        have := val_toList_lt b
        rwa [show 64 * (N + 1) = 64 + 64 * N by ring, pow_add] at this
      have hrl : val rr'.toList < 2 ^ 64 * 2 ^ (64 * N) := by
        have := val_toList_lt rr'
        rwa [show 64 * (N + 1) = 64 + 64 * N by ring, pow_add] at this
      refine ⟨?_, fun hq1 => ?_, fun hq0 => ?_⟩
      · -- The congruence: R * B + a = R' + (R[N] * (B + q) + R[N - 1]) * D.
        have hcg := fold_congr (2 ^ 64) (2 ^ (64 * (N - 1))) (val d.toList) (val c0.toList)
          (val c1.toList) q.toNat (pw[8 - N - j - 1]'(by omega)).toNat
          (val b.toList % 2 ^ (64 * (N - 1))) b[N - 1].toNat b[N].toNat hC0D' hqC
        rw [← hbsplit, ← hRv] at hcg
        have h1 : val b.toList * 2 ^ 64 + (pw[8 - N - j - 1]'(by omega)).toNat ≡
            val pw.toList / 2 ^ (64 * (8 - N - j)) * 2 ^ 64 + (pw[8 - N - j - 1]'(by omega)).toNat
            [MOD val d.toList] :=
          (Nat.ModEq.mul_right _ hI1).add_right _
        have h2 : val rr'.toList ≡ val b.toList * 2 ^ 64 + (pw[8 - N - j - 1]'(by omega)).toNat
            [MOD val d.toList] := by
          rw [hcg]; exact (Nat.add_mul_mod_self_right _ _ _).symm
        have h3 := h2.trans h1
        rw [hpwt]
        unfold Nat.ModEq at h3
        rw [h3, Nat.add_comm, Nat.mul_comm]
      · -- The deficit at least halves.
        have hdef := fold_deficit (2 ^ 64) (2 ^ (64 * (N - 1))) (val d.toList) (val c0.toList)
          (val c1.toList) q.toNat (pw[8 - N - j - 1]'(by omega)).toNat
          (val b.toList % 2 ^ (64 * (N - 1))) b[N - 1].toNat b[N].toNat hC0D' hqC hc1 hq1
          (UInt64.toNat_lt _) hlow (UInt64.toNat_lt _) (UInt64.toNat_lt _)
        rw [← hbsplit, ← hRv, ← hBN] at hdef
        have h1 : 2 ^ (64 * N) * (2 ^ 64 * 2 ^ (64 * N) - val b.toList) ≤
            2 ^ (64 * N) * (2 * (2 ^ 64 * 2 ^ (64 * N) - val rr'.toList)) := by
          calc 2 ^ (64 * N) * (2 ^ 64 * 2 ^ (64 * N) - val b.toList)
              ≤ (2 * val d.toList) * (2 ^ 64 * 2 ^ (64 * N) - val b.toList) := Nat.mul_le_mul_right _ hBP2
            _ = 2 * (val d.toList * (2 ^ 64 * 2 ^ (64 * N) - val b.toList)) := by ring
            _ ≤ 2 * (2 ^ (64 * N) * (2 ^ 64 * 2 ^ (64 * N) - val rr'.toList)) := Nat.mul_le_mul_left _ hdef
            _ = 2 ^ (64 * N) * (2 * (2 ^ 64 * 2 ^ (64 * N) - val rr'.toList)) := by ring
        have h2 := Nat.le_of_mul_le_mul_left h1 (by positivity)
        calc 2 ^ 64 * 2 ^ (64 * N) ≤ 2 ^ (j + 1) * (2 ^ 64 * 2 ^ (64 * N) - val b.toList) := hI2 hq1
          _ ≤ 2 ^ (j + 1) * (2 * (2 ^ 64 * 2 ^ (64 * N) - val rr'.toList)) := Nat.mul_le_mul_left _ h2
          _ = 2 ^ (j + 1 + 1) * (2 ^ 64 * 2 ^ (64 * N) - val rr'.toList) := by ring
      · -- The top word grows by at most 1.
        have hq0' : 2 ^ 64 * val c0.toList = val c1.toList := by rw [hqC, hq0]; simp
        have hf0 := fold_q0 (2 ^ 64) (2 ^ (64 * (N - 1))) (val d.toList) (val c0.toList)
          (val c1.toList) (pw[8 - N - j - 1]'(by omega)).toNat (val b.toList % 2 ^ (64 * (N - 1)))
          b[N - 1].toNat b[N].toNat hC0D' hq0' hc1 (UInt64.toNat_lt _) hlow (UInt64.toNat_lt _)
        rw [← hRv, ← hBN] at hf0
        have ht : b[N].toNat < 2 ^ 63 + j := by
          rw [getElem_top_toNat]
          exact (Nat.div_lt_iff_lt_mul (by positivity)).mpr (hI3 hq0)
        calc val rr'.toList < 2 ^ (64 * N) * (b[N].toNat + 2) := hf0
          _ ≤ 2 ^ (64 * N) * (2 ^ 63 + (j + 1)) := Nat.mul_le_mul_left _ (by omega)
          _ = (2 ^ 63 + (j + 1)) * 2 ^ (64 * N) := by ring
    · -- After the folds.
      intro r ⟨hI1, hI2, hI3⟩
      have hrl : val r.toList < 2 ^ 64 * 2 ^ (64 * N) := by
        have := val_toList_lt r
        rwa [show 64 * (N + 1) = 64 + 64 * N by ring, pow_add] at this
      refine ⟨by simpa using hI1, ?_⟩
      rcases Nat.eq_zero_or_pos q.toNat with hq0 | hq1
      · have := hI3 hq0
        have : (2 ^ 63 + (8 - N)) * 2 ^ (64 * N) ≤ (2 ^ 63 + 7) * 2 ^ (64 * N) :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      · have h := hI2 hq1
        have : 2 ^ (8 - N + 1) * (2 ^ 64 * 2 ^ (64 * N) - val r.toList) ≤
            2 ^ 8 * (2 ^ 64 * 2 ^ (64 * N) - val r.toList) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
        omega
    · -- The Barrett step.
      intro R ⟨hRm, hRb⟩
      lift_lets
      intro rR qh r1 r1' r2
      have hRl : val R.toList < 2 ^ 64 * 2 ^ (64 * N) := by
        have := val_toList_lt R
        rwa [show 64 * (N + 1) = 64 + 64 * N by ring, pow_add] at this
      have hRt : val R.toList / 2 ^ (64 * (N - 1)) = R[N - 1].toNat + 2 ^ 64 * R[N].toNat := by
        rw [val_div_pow R (N - 1) (by omega), show N - 1 + 1 = N by omega, getElem_top_toNat]
      have hqhv : val qh.toList = val R.toList / 2 ^ (64 * (N - 1)) * (2 ^ 64 + q.toNat) := by
        simp only [qh, rR]
        rw [umulWords_spec, val_vec2, val_vec2, hRt]
        simp only [UInt64.toNat_one, Nat.mul_one]
        ring
      have hQh : qh[2].toNat + 2 ^ 64 * qh[3].toNat =
          val R.toList / 2 ^ (64 * (N - 1)) * (2 ^ 64 + q.toNat) / (2 ^ 64 * 2 ^ 64) := by
        rw [← hqhv, show (2 : ℕ) ^ 64 * 2 ^ 64 = 2 ^ 128 by rw [← pow_add]]
        exact (val_div_pow2 qh).symm
      have hmu : 2 ^ 64 * (2 ^ 64 * 2 ^ (64 * (N - 1))) =
          (2 ^ 64 + q.toNat) * val d.toList + val c1.toList := by
        have : 2 ^ 64 * (val d.toList + val c0.toList) = 2 ^ 64 * (2 ^ 64 * 2 ^ (64 * (N - 1))) := by
          rw [hC0D']
        rw [← this, Nat.mul_add, hqC]; ring
      have hBP2 : 2 ^ 64 * 2 ^ (64 * (N - 1)) ≤ 2 * val d.toList := by rw [← hBN, hd]; exact hDge
      obtain ⟨hb1, hb2⟩ := barrett (2 ^ 64) (2 ^ (64 * (N - 1))) (val d.toList) (val c1.toList)
        q.toNat (val R.toList) (by positivity) hP0 hmu hc1 hBP2 (by rw [← hBN]; omega)
      rw [← hQh] at hb1 hb2
      -- Qh < 2B: the word qh[3] is 0 or 1.
      have hq3 : qh[3].toNat ≤ 1 := by
        by_contra h
        have : 2 ^ 64 * 2 * val d.toList ≤ (qh[2].toNat + 2 ^ 64 * qh[3].toNat) * val d.toList :=
          Nat.mul_le_mul_right _ (by omega)
        have : 2 ^ 64 * 2 ^ (64 * N) ≤ 2 ^ 64 * 2 * val d.toList := by
          rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (by rw [hBN]; exact hBP2)
        omega
      -- R - qh[2] * d.
      obtain ⟨A, bw, hAb⟩ : ∃ A bw, submul (span rR 0 N (by omega)) d qh[2] (by omega) = (A, bw) :=
        ⟨_, _, rfl⟩
      have hsub := submul_spec (span rR 0 N (by omega)) d qh[2] (by omega)
      rw [hAb, val_span_low] at hsub
      have hrR : rR = R := rfl
      simp only [hrR] at hsub
      have hAl := val_toList_lt A
      have hRsplit := val_split_top R
      have hr1 : r1 = setSpan R 0 A (by omega) := by simp only [r1, rR, hAb]
      have hr1' : r1' = r1.set N (r1[N] - bw) (by omega) := by simp only [r1', r1, rR, hAb]
      have hr1N : r1[N] = R[N] := by rw [hr1, getElem_setSpan_top]
      have hq2D : qh[2].toNat * val d.toList ≤ val R.toList := by
        have : qh[2].toNat * val d.toList ≤ (qh[2].toNat + 2 ^ 64 * qh[3].toNat) * val d.toList :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      have hbw : bw.toNat ≤ R[N].toNat := by
        by_contra h
        have : 2 ^ (64 * N) * (R[N].toNat + 1) ≤ 2 ^ (64 * N) * bw.toNat :=
          Nat.mul_le_mul_left _ (by omega)
        rw [Nat.mul_add, Nat.mul_one] at this
        omega
      have hr1'v : val r1'.toList = val R.toList - qh[2].toNat * val d.toList := by
        rw [hr1', val_set_top, hr1N, hr1, val_setSpan_low, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hAl,
          UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hbw), Nat.mul_sub]
        have : 2 ^ (64 * N) * bw.toNat ≤ 2 ^ (64 * N) * R[N].toNat := Nat.mul_le_mul_left _ hbw
        omega
      have hsubmod : ∀ k, k * val d.toList ≤ val R.toList →
          (val R.toList - k * val d.toList) % val d.toList = val R.toList % val d.toList := by
        intro k hk
        rw [Nat.mul_comm] at hk ⊢
        exact Nat.sub_mul_mod hk
      have hDm : (val R.toList - qh[2].toNat * val d.toList) % val d.toList =
          val pw.toList % val d.toList := by
        rw [← hRm, hsubmod _ hq2D]
      by_cases h3 : qh[3] ≠ 0
      · -- Subtract d * B too.
        rw [if_pos h3]
        have h31 : qh[3].toNat = 1 := by
          have : qh[3].toNat ≠ 0 := fun h => h3 (UInt64.toNat_inj.mp (by simpa using h))
          omega
        rw [h31, Nat.mul_one] at hb1 hb2
        have hr1'l : val r1'.toList < 2 ^ 64 * 2 ^ (64 * N) := by rw [hr1'v]; omega
        have hge : 2 ^ 64 * val d.toList ≤ val r1'.toList := by
          rw [hr1'v]
          have := Nat.add_mul (qh[2].toNat) (2 ^ 64) (val d.toList)
          omega
        obtain ⟨W, bw', hWb⟩ : ∃ W bw', submul (span r1' 1 N (by omega)) d 1 (by omega) = (W, bw') :=
          ⟨_, _, rfl⟩
        have hsub' := submul_spec (span r1' 1 N (by omega)) d 1 (by omega)
        rw [hWb, val_span] at hsub'
        simp only [UInt64.toNat_one, Nat.one_mul, show 64 * 1 = 64 by norm_num] at hsub'
        have hdivl : val r1'.toList / 2 ^ 64 < 2 ^ (64 * N) := by
          rw [Nat.div_lt_iff_lt_mul (by positivity), Nat.mul_comm]; exact hr1'l
        rw [Nat.mod_eq_of_lt hdivl] at hsub'
        have hdg : val d.toList ≤ val r1'.toList / 2 ^ 64 := by
          rw [Nat.le_div_iff_mul_le (by positivity), Nat.mul_comm]; exact hge
        have hWl := val_toList_lt W
        have hbw' : bw'.toNat = 0 := by
          by_contra h
          have : 2 ^ (64 * N) * 1 ≤ 2 ^ (64 * N) * bw'.toNat := Nat.mul_le_mul_left _ (by omega)
          omega
        rw [hbw', Nat.mul_zero, Nat.add_zero] at hsub'
        have hr2v : val r2.toList = val R.toList - (qh[2].toNat + 2 ^ 64) * val d.toList := by
          have hr2 : r2 = setSpan r1' 1 W (by omega) := by simp only [r2, hWb]
          have hr1'l2 : val r1'.toList < 2 ^ 64 * 2 ^ (64 * N) := hr1'l
          rw [hr2, val_setSpan, show 64 * 1 = 64 by norm_num, show 64 * (1 + N) = 64 + 64 * N by ring,
            pow_add, Nat.div_eq_of_lt hr1'l2, Nat.mul_zero, Nat.add_zero]
          have hsplit := Nat.mod_add_div (val r1'.toList) (2 ^ 64)
          rw [Nat.add_mul (qh[2].toNat) (2 ^ 64) (val d.toList)]
          have hW2 : 2 ^ 64 * val W.toList + 2 ^ 64 * val d.toList = 2 ^ 64 * (val r1'.toList / 2 ^ 64) := by
            rw [← Nat.mul_add, hsub']
          rw [hr1'v] at hsplit hge
          omega
        simp (config := { zeta := false }) only [Option.pure_def, Option.bind_some]
        have h2D := Nat.add_mul (qh[2].toNat + 2 ^ 64) 2 (val d.toList)
        refine hjp2 r2 PUnit.unit (by rw [hr2v]; omega) ?_
        rw [hr2v, hsubmod _ hb1, hRm]
      · rw [if_neg h3]
        have h30 : qh[3].toNat = 0 := by
          have : qh[3] = 0 := by simpa using h3
          rw [this]; rfl
        simp only [h30, Nat.mul_zero, Nat.add_zero] at hb1 hb2
        simp (config := { zeta := false }) only [Option.pure_def, Option.bind_some]
        have h2D := Nat.add_mul (qh[2].toNat) 2 (val d.toList)
        refine hjp2 r1' PUnit.unit (by rw [hr1'v]; omega) ?_
        rw [hr1'v, hDm]
  by_cases hpow : c0[N - 1] = d[N - 1]
  · -- m is a power of 2.
    rw [if_pos hpow]
    refine ⟨_, rfl, ?_⟩
    have hct := congrArg UInt64.toNat hpow
    rw [hc0t, hdt, hc0] at hct
    have hD2 : 2 * val d.toList = 2 ^ (64 * N) := by
      have h1 : 2 ^ 63 * 2 ^ (64 * (N - 1)) ≤ val d.toList := by
        have := hdt63; rw [hdt, Nat.le_div_iff_mul_le hP0] at this; exact this
      have h2 : 2 ^ 63 * 2 ^ (64 * (N - 1)) ≤ 2 ^ (64 * N) - val d.toList := by
        have h3 : 2 ^ 63 ≤ (2 ^ (64 * N) - val d.toList) / 2 ^ (64 * (N - 1)) := by
          rw [hct]; exact (Nat.le_div_iff_mul_le hP0).mpr h1
        exact (Nat.le_div_iff_mul_le hP0).mp h3
      have : 2 ^ 64 * 2 ^ (64 * (N - 1)) = 2 * (2 ^ 63 * 2 ^ (64 * (N - 1))) := by ring
      omega
    have hM : val m.toList ∣ 2 ^ (64 * N) := ⟨2 ^ s.val * 2, by rw [← hD2, hd]; ring⟩
    obtain ⟨k, hk, hMk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hM
    have hk256 : k ≤ 256 := by omega
    have h256 : 2 ^ k ∣ 2 ^ 256 := Nat.pow_dvd_pow 2 hk256
    have hkle : 2 ^ k ≤ 2 ^ 256 := Nat.pow_le_pow_right (by norm_num) hk256
    have h1 : val (#v[(1 : Word)] : Vector Word 1).toList = 1 := by simp
    rw [val_andWords, val_resize, hp, subWords_spec, val_resize, h1,
      show 64 * 4 = 256 by norm_num, Nat.mod_eq_of_lt (show 1 < 2 ^ 256 by norm_num), hMk]
    have hk1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    rw [show 2 ^ k + 2 ^ 256 - 1 = (2 ^ k - 1) + 2 ^ 256 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (show 2 ^ k - 1 < 2 ^ 256 by omega), Nat.and_two_pow_sub_one_eq_mod,
      Nat.mod_mod_of_dvd _ h256]
  · rw [if_neg hpow]
    simp (config := { zeta := false }) only [Option.pure_def, Option.bind_some]
    simp (config := { zeta := false }) only [jp4]
    have hC0D : val c0.toList < val d.toList := by
      have h1 : val c0.toList ≤ val d.toList := by rw [hc0]; omega
      rcases Nat.lt_or_ge (val c0.toList) (val d.toList) with h | h
      · exact h
      · exfalso; apply hpow; apply UInt64.toNat_inj.mp; rw [hc0t, hdt, show val c0.toList = val d.toList by omega]
    -- C0 * B / d and C0 * B % d.
    have hc0bt : ∀ i (hi : i < N + 1), c0b'[i].toNat = 2 ^ 64 * val c0.toList / 2 ^ (64 * i) % 2 ^ 64 := by
      intro i hi; rw [getElem_toNat', hc0b, hc0]
    have hC0lt : val c0.toList < 2 ^ (64 * N) := by rw [hc0]; omega
    by_cases hN1 : N = 1
    · rw [dif_pos hN1]
      have hB1 : 2 ^ (64 * N) = 2 ^ 64 := by rw [hN1]
      have hlo : c0b'[0].toNat = 0 := by
        rw [hc0bt 0 (by omega)]; simp [Nat.mul_mod_right]
      have hhi : c0b'[1].toNat = val c0.toList := by
        rw [hc0bt 1 (by omega), show 64 * 1 = 64 by norm_num, Nat.mul_div_cancel_left _ (by positivity),
          Nat.mod_eq_of_lt (by rw [← hB1]; exact hC0lt)]
      have hd0 : d[0].toNat = val d.toList := by
        rw [getElem_toNat']; simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one]
        exact Nat.mod_eq_of_lt (by rw [← hB1]; exact hdl)
      have hd063 : 2 ^ 63 ≤ d[0].toNat := by
        have := hdt63
        rw [hdt, show N - 1 = 0 by omega] at this
        rw [hd0]; simpa using this
      obtain ⟨q, c10, hdiv, hq, hc10⟩ := udivrem_2by1_spec P ⟨c0b'[0], c0b'[1]⟩ d[0] hd063
        (by rw [UInt64.lt_iff_toNat_lt]; show c0b'[1].toNat < d[0].toNat; rw [hhi, hd0]; exact hC0D)
      have hU : (⟨c0b'[0], c0b'[1]⟩ : U128).toNat = 2 ^ 64 * val c0.toList := by
        simp only [U128.toNat_mk, hlo, hhi]; ring
      rw [hU, hd0] at hq hc10
      refine ex_bind (fun v : Word × Word => v.1.toNat = 2 ^ 64 * val c0.toList / val d.toList ∧
        v.2.toNat = 2 ^ 64 * val c0.toList % val d.toList) ⟨(q, c10), hdiv, hq, hc10⟩ ?_
      intro v ⟨hv1, hv2⟩
      simp (config := { zeta := false }) only [Option.pure_def, Option.bind_some]
      have hv : val ((Vector.replicate N 0).set 0 v.2 (by omega)).toList = v.2.toNat := by
        have := val_toList_set (Vector.replicate N (0 : Word)) 0 v.2 (by omega)
        simpa using this
      apply hjp3
      · rw [hv, hv1, hv2]; exact Nat.div_add_mod' _ _
      · rw [hv, hv2]; exact Nat.mod_lt _ hDpos
    · rw [dif_neg hN1]
      have hsd : ∀ i (hi : i < N), (ofSpan N d (by omega))[i] = d[i] := by
        intro i hi; simp [ofSpan, copy, getElem_setSpan, hi]
      have hvs : val (ofSpan N d (by omega)).toList = val d.toList := by
        simp only [ofSpan, copy]; rw [val_setSpan]; simp
      have hct : c0b'[N].toNat = val c0.toList / 2 ^ (64 * (N - 1)) := by
        rw [hc0bt N (by omega), hBP, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel_left _ (by positivity),
          Nat.mod_eq_of_lt]
        rw [Nat.div_lt_iff_lt_mul hP0, ← hBP]; exact hC0lt
      have htop : c0b'[N].toNat < d[N - 1].toNat := by
        rw [hct, hdt]
        have h1 : val c0.toList / 2 ^ (64 * (N - 1)) ≤ val d.toList / 2 ^ (64 * (N - 1)) :=
          Nat.div_le_div_right hC0D.le
        rcases Nat.lt_or_ge (val c0.toList / 2 ^ (64 * (N - 1))) (val d.toList / 2 ^ (64 * (N - 1))) with h | h
        · exact h
        · exfalso; apply hpow; apply UInt64.toNat_inj.mp; rw [hc0t, hdt]; omega
      obtain ⟨quot, rem, hdiv, hq, hr⟩ := udivrem_top1_spec P (N - 1) c0b' (ofSpan N d (by omega))
        (by omega) (by omega) (by omega) (by omega)
        (by rw [hsd (N - 1) (by omega)]; exact hdt63)
        (by
          rw [hsd (N - 1) (by omega)]
          have : c0b'[N - 1 + 1].toNat = c0b'[N].toNat := by
            rw [getElem_toNat', getElem_toNat', show N - 1 + 1 = N by omega]
          rw [this]; exact htop)
      rw [hvs, hc0b, ← hc0] at hq hr
      refine ex_bind (fun v : Vector Word (N + 1) × Vector Word N =>
        (v.1[0]'(by omega)).toNat = 2 ^ 64 * val c0.toList / val d.toList ∧
        val v.2.toList = 2 ^ 64 * val c0.toList % val d.toList) ⟨(quot, rem), hdiv, hq, hr⟩ ?_
      intro v ⟨hv1, hv2⟩
      simp (config := { zeta := false }) only [Option.pure_def, Option.bind_some]
      have hv : val (copy v.2 (Vector.replicate N 0) (by omega)).toList = val v.2.toList := by
        simp only [copy]; rw [val_setSpan]; simp
      apply hjp3
      · rw [hv, hv1, hv2]; exact Nat.div_add_mod' _ _
      · rw [hv, hv2]; exact Nat.mod_lt _ hDpos

/-- The words of `m` above the word `k` are zero. -/
theorem val_lt_of_div_eq_zero (X k : Nat) (h : X / 2 ^ (64 * k) = 0) : X < 2 ^ (64 * k) := by
  rcases Nat.lt_or_ge X (2 ^ (64 * k)) with h' | h'
  · exact h'
  · have := Nat.div_pos h' (by positivity : 0 < 2 ^ (64 * k)); omega

end Intx.Model

namespace Intx

open Model in
/-- `mulmod()` computes `x * y mod m` for every nonzero `m`, without undefined behavior, on every
code path. -/
theorem mulmod_correct (P : Platform) : MulmodCorrect (Model.mulmod P) := by
  intro x y m hm
  have h3t : val m.toList / 2 ^ (64 * 3) = m[3].toNat := val_div_pow_top m 3 rfl
  have h2t : val m.toList / 2 ^ (64 * 2) = m[2].toNat + 2 ^ 64 * m[3].toNat := by
    rw [val_div_pow m 2 (by omega), h3t]
  have h1t : val m.toList / 2 ^ (64 * 1) = m[1].toNat + 2 ^ 64 * (m[2].toNat + 2 ^ 64 * m[3].toNat) := by
    rw [val_div_pow m 1 (by omega), h2t]
  have h0t : val m.toList = m[0].toNat + 2 ^ 64 * (val m.toList / 2 ^ (64 * 1)) := by
    have := val_div_pow m 0 (by omega)
    simpa using this
  have hz : ∀ w : Word, w = 0 ↔ w.toNat = 0 := fun w => ⟨fun h => by rw [h]; rfl,
    fun h => UInt64.toNat_inj.mp (by rw [h]; rfl)⟩
  unfold mulmod
  by_cases h3 : m[3] ≠ 0
  · rw [if_pos h3]
    exact mulmod_fold_spec P 4 x y m (by omega) h3 (val_toList_lt m)
  rw [if_neg h3]
  have h3' : m[3].toNat = 0 := (hz _).mp (by simpa using h3)
  by_cases h2 : m[2] ≠ 0
  · rw [if_pos h2]
    exact mulmod_fold_spec P 3 x y m (by omega) h2 (val_lt_of_div_eq_zero _ _ (by rw [h3t, h3']))
  rw [if_neg h2]
  have h2' : m[2].toNat = 0 := (hz _).mp (by simpa using h2)
  by_cases h1 : m[1] ≠ 0
  · rw [if_pos h1]
    exact mulmod_fold_spec P 2 x y m (by omega) h1
      (val_lt_of_div_eq_zero _ _ (by rw [h2t, h2', h3']; simp))
  rw [if_neg h1]
  have h1' : m[1].toNat = 0 := (hz _).mp (by simpa using h1)
  have hlt : val m.toList < 2 ^ (64 * 1) :=
    val_lt_of_div_eq_zero _ _ (by rw [h1t, h1', h2', h3']; simp)
  have h0 : m[0] ≠ 0 := by
    intro h0
    apply hm
    rw [h0t, (hz _).mp h0, Nat.div_eq_of_lt hlt]
    simp
  exact mulmod_fold_spec P 1 x y m (by omega) h0 hlt

end Intx
