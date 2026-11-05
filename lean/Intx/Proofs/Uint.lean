import Intx.Proofs.Words
set_option warningAsError true
/-!
# Proofs: the `uint<N>` operations

What `umul()`, `subc()`, `operator-` and `operator&` of `Intx.Model` compute, as numbers.
-/

namespace Intx.Model

/-- The product and a 2-word sum fit in `uint128`. -/
theorem umul_add_mk_toNat (x y lo : Word) (c : Bool)
    (h : lo.toNat + 2 ^ 64 * c.toNat ≤ 2 * (2 ^ 64 - 1)) :
    (umul x y + ⟨lo, if c then 1 else 0⟩).toNat = x.toNat * y.toNat + lo.toNat + 2 ^ 64 * c.toNat := by
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  have : x.toNat * y.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  rw [U128.toNat_add, umul_toNat, U128.toNat_mk, toNat_ite_bool]
  have hc := Bool.toNat_le c
  rw [Nat.mod_eq_of_lt (by omega)]
  ring

theorem umulWords_spec {n : Nat} (x y : Vector Word n) :
    val (umulWords x y).toList = val x.toList * val y.toList := by
  unfold umulWords
  refine forIn'_rco0_id
    (P := fun (v : Vector Word (2 * n)) => val v.toList = val x.toList * val y.toList)
    (fun j (p : Vector Word (2 * n)) => val p.toList = val x.toList * val (y.toList.take j) ∧
      ∀ t (ht : t < 2 * n), j + n ≤ t → p[t] = 0)
    ⟨by simp, fun t ht _ => by simp⟩ ?_ ?_
  · intro j p hj hm ⟨hv, hz⟩
    refine forIn'_rco0_id
      (P := fun (v : ForInStep (Vector Word (2 * n))) => ∃ b', v = .yield b' ∧
        (val b'.toList = val x.toList * val (y.toList.take (j + 1)) ∧
          ∀ t (ht : t < 2 * n), j + 1 + n ≤ t → b'[t] = 0))
      (fun i (b : Vector Word (2 * n) × Word) =>
        val b.1.toList + 2 ^ (64 * (i + j)) * b.2.toNat =
          val p.toList + 2 ^ (64 * j) * y[j].toNat * val (x.toList.take i) ∧
        ∀ t (ht : t < 2 * n), (t < j ∨ i + j ≤ t) → b.1[t] = p[t])
      ⟨by simp, fun t ht _ => rfl⟩ ?_ ?_
    · intro i b hi hm' ⟨hv', hp'⟩
      refine ⟨_, rfl, ?_, ?_⟩
      · simp only [U128.getElem_zero, U128.getElem_one]
        have hA := addc_spec b.1[i + j] b.2 false
        simp only [Bool.toNat_false, Nat.add_zero] at hA
        have hAl := (addc b.1[i + j] b.2 false).1.toNat_lt
        have hpl := b.1[i + j].toNat_lt
        have hbl := b.2.toNat_lt
        have hT := umul_add_mk_toNat x[i] y[j] (addc b.1[i + j] b.2 false).1
          (addc b.1[i + j] b.2 false).2 (by omega)
        simp only [U128.toNat] at hT
        have hset := val_toList_set b.1 (i + j)
          (umul x[i] y[j] + ⟨(addc b.1[i + j] b.2 false).1,
            if (addc b.1[i + j] b.2 false).2 then 1 else 0⟩).lo (by omega)
        have hpij := congrArg UInt64.toNat (hp' (i + j) (by omega) (Or.inr le_rfl))
        have htake := val_take_succ' x i hi
        rw [show i + 1 + j = i + j + 1 by omega, Nat.mul_succ, pow_add, htake]
        rw [Nat.mul_add, pow_add] at hset hv' ⊢
        have hT' := congrArg (fun t => 2 ^ (64 * i) * 2 ^ (64 * j) * t) hT
        have hA' := congrArg (fun t => 2 ^ (64 * i) * 2 ^ (64 * j) * t) hA
        simp only [Nat.mul_add] at hT' hA'
        nlinarith
      · intro t ht h1
        rw [Vector.getElem_set, if_neg (by omega)]
        exact hp' t ht (by omega)
    · intro b ⟨hv', hp'⟩
      obtain ⟨pp, kk⟩ := b
      refine ⟨_, rfl, ?_, ?_⟩
      · have hset := val_toList_set pp (j + n) kk (by omega)
        have h0 : pp[j + n] = 0 := by rw [hp' (j + n) (by omega) (Or.inr (by omega))]; exact hz _ _ le_rfl
        rw [h0] at hset
        rw [take_toList_self] at hv'
        rw [val_take_succ' y j hj, Nat.mul_add, hv.symm]
        simp only [UInt64.toNat_zero, Nat.mul_zero, Nat.add_zero] at hset
        rw [show n + j = j + n by omega] at hv'
        nlinarith
      · intro t ht h1
        rw [Vector.getElem_set, if_neg (by omega)]
        rw [hp' t ht (Or.inr (by omega))]
        exact hz t ht (by omega)
  · intro p ⟨hv, _⟩
    rw [take_toList_self] at hv
    exact hv

theorem subcWords_spec {n : Nat} (x y : Vector Word n) (c : Bool) :
    val (subcWords x y c).1.toList + val y.toList + c.toNat =
      val x.toList + 2 ^ (64 * n) * (subcWords x y c).2.toNat := by
  unfold subcWords
  refine forIn'_rco0_id
    (P := fun (v : Vector Word n × Bool) =>
      val v.1.toList + val y.toList + c.toNat = val x.toList + 2 ^ (64 * n) * v.2.toNat)
    (fun k (b : Vector Word n × Bool) =>
      val (b.1.toList.take k) + val (y.toList.take k) + c.toNat =
        val (x.toList.take k) + 2 ^ (64 * k) * b.2.toNat ∧
      ∀ i (hi : i < n), k ≤ i → b.1[i] = 0)
    ⟨by simp, fun i hi _ => by simp⟩ ?_ ?_
  · intro k b hk hm ⟨hv, hz⟩
    refine ⟨_, rfl, ?_, ?_⟩
    · have hs := subc_spec x[k] y[k] b.2
      have hs' := congrArg (fun t => 2 ^ (64 * k) * t) hs
      simp only [Nat.mul_add] at hs'
      have htz : (b.1.set k (subc x[k] y[k] b.2).1 hk).toList.take k = b.1.toList.take k := by
        apply List.ext_getElem (by simp)
        intro i h1 h2
        simp only [List.getElem_take, Vector.getElem_toList]
        rw [Vector.getElem_set, if_neg (by simp at h1; omega)]
      rw [val_take_succ' _ k hk, val_take_succ' y k hk, val_take_succ' x k hk, htz,
        Vector.getElem_set_self, Nat.mul_succ, pow_add]
      nlinarith
    · intro i hi hki
      rw [Vector.getElem_set, if_neg (by omega)]
      exact hz i hi (by omega)
  · intro b ⟨hv, _⟩
    rw [take_toList_self, take_toList_self, take_toList_self] at hv
    exact hv

theorem subWords_spec {n : Nat} (x y : Vector Word n) :
    val (subWords x y).toList = (val x.toList + 2 ^ (64 * n) - val y.toList) % 2 ^ (64 * n) := by
  have h := subcWords_spec x y false
  have hz := val_toList_lt (subcWords x y false).1
  have hy := val_toList_lt y
  have hb := Bool.toNat_le (subcWords x y false).2
  simp only [Bool.toNat_false, Nat.add_zero] at h
  unfold subWords
  rcases Nat.eq_zero_or_pos (subcWords x y false).2.toNat with h0 | h0
  · rw [h0] at h
    have : (val x.toList + 2 ^ (64 * n) - val y.toList) = val (subcWords x y false).1.toList + 2 ^ (64 * n) := by
      omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by simpa using hz)]
  · have h1 : (subcWords x y false).2.toNat = 1 := by omega
    rw [h1] at h
    have : (val x.toList + 2 ^ (64 * n) - val y.toList) = val (subcWords x y false).1.toList := by
      omega
    rw [this, Nat.mod_eq_of_lt (by simpa using hz)]

theorem andWords_eq {n : Nat} (x y : Vector Word n) :
    andWords x y = Vector.zipWith (· &&& ·) x y := by
  unfold andWords
  refine forIn'_rco0_id (P := fun v => v = _)
    (fun k z => ∀ i (hi : i < n), z[i] = if i < k then x[i] &&& y[i] else 0)
    (by intro i hi; simp)
    (fun k z hk hm hI => ⟨_, rfl, fun i hi => by
      rw [Vector.getElem_set]
      split_ifs <;> simp_all <;> omega⟩) ?_
  intro z hz
  apply Vector.ext
  intro i hi
  simpa [hi] using hz i hi

theorem and_two_pow_mul_add (a b c e : Nat) (hb : b < 2 ^ 64) (he : e < 2 ^ 64) :
    (2 ^ 64 * a + b) &&& (2 ^ 64 * c + e) = 2 ^ 64 * (a &&& c) + (b &&& e) := by
  apply Nat.eq_of_testBit_eq
  intro j
  have hbe : b &&& e < 2 ^ 64 := Nat.lt_of_le_of_lt Nat.and_le_left hb
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ hb, Nat.testBit_two_pow_mul_add _ he,
    Nat.testBit_two_pow_mul_add _ hbe, Nat.testBit_and, Nat.testBit_and]
  split_ifs <;> rfl

theorem val_zipWith_and (xs ys : List Word) (h : xs.length = ys.length) :
    val (List.zipWith (· &&& ·) xs ys) = val xs &&& val ys := by
  induction xs generalizing ys with
  | nil => simp
  | cons a as ih =>
    cases ys with
    | nil => simp at h
    | cons b bs =>
      simp only [List.zipWith_cons_cons, val_cons, UInt64.toNat_and]
      rw [ih bs (by simpa using h), Nat.add_comm, Nat.add_comm a.toNat,
        Nat.add_comm b.toNat, and_two_pow_mul_add _ _ _ _ a.toNat_lt b.toNat_lt]

theorem val_andWords {n : Nat} (x y : Vector Word n) :
    val (andWords x y).toList = val x.toList &&& val y.toList := by
  rw [andWords_eq, Vector.toList_zipWith, val_zipWith_and _ _ (by simp)]

end Intx.Model
