import Intx.Proofs.Word
set_option warningAsError true
/-!
# Proofs: the word-array helpers

What `add()`, `submul()`, `addmul()`, `shl()` and `shr()` of `Intx.Model` compute, as numbers.
-/

namespace Intx.Model

theorem val_take_succ (l : List Word) (k : Nat) (h : k < l.length) :
    val (l.take (k + 1)) = val (l.take k) + 2 ^ (64 * k) * l[k].toNat := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, val_append,
    List.length_take, Nat.min_eq_left (by omega)]
  simp

theorem val_take_succ' {n : Nat} (v : Vector Word n) (k : Nat) (h : k < n) :
    val (v.toList.take (k + 1)) = val (v.toList.take k) + 2 ^ (64 * k) * v[k].toNat := by
  rw [val_take_succ v.toList k (by simpa using h), Vector.getElem_toList]

theorem take_toList_self {n : Nat} (v : Vector Word n) : v.toList.take n = v.toList :=
  List.take_of_length_le (by simp)

theorem add_spec {n : Nat} (x y : Vector Word n) (h : 2 ≤ n) :
    val (add x y h).1.toList + 2 ^ (64 * n) * (add x y h).2.toNat =
      val x.toList + val y.toList := by
  unfold add
  refine forIn'_rco0_id
    (P := fun (v : Vector Word n × Bool) =>
      val v.1.toList + 2 ^ (64 * n) * v.2.toNat = val x.toList + val y.toList)
    (fun k (b : MProd Bool (Vector Word n)) =>
      val b.2.toList + 2 ^ (64 * k) * b.1.toNat = val x.toList + val (y.toList.take k) ∧
      ∀ i (hi : i < n), k ≤ i → b.2[i] = x[i])
    ⟨by simp, fun i hi _ => rfl⟩ ?_ ?_
  · intro k b hk hm ⟨hv, hx⟩
    refine ⟨_, rfl, ?_, ?_⟩
    · have hs := val_toList_set b.2 k (addc b.2[k] y[k] b.1).1 hk
      have ha := addc_spec b.2[k] y[k] b.1
      have ha' := congrArg (fun t => 2 ^ (64 * k) * t) ha
      simp only [Nat.mul_add] at ha'
      rw [Nat.mul_succ, pow_add, val_take_succ' y k hk]
      linarith [hx k hk le_rfl]
    · intro i hi hki
      rw [Vector.getElem_set, if_neg (by omega)]
      exact hx i hi (by omega)
  · intro b ⟨hv, _⟩
    rw [take_toList_self] at hv
    simpa using hv

theorem submul_spec {n : Nat} (x y : Vector Word n) (m : Word) (h : 0 < n) :
    val (submul x y m h).1.toList + m.toNat * val y.toList =
      val x.toList + 2 ^ (64 * n) * (submul x y m h).2.toNat := by
  unfold submul
  refine forIn'_rco0_id
    (P := fun (v : Vector Word n × Word) =>
      val v.1.toList + m.toNat * val y.toList = val x.toList + 2 ^ (64 * n) * v.2.toNat)
    (fun k (b : MProd Bool (MProd Word (Vector Word n))) =>
      val b.2.2.toList + m.toNat * val (y.toList.take k) =
        val x.toList + 2 ^ (64 * k) * (b.2.1.toNat + b.1.toNat) ∧
      b.2.1.toNat ≤ 2 ^ 64 - 2 ∧
      ∀ i (hi : i < n), k ≤ i → b.2.2[i] = x[i])
    ⟨by simp, by simp, fun i hi _ => rfl⟩ ?_ ?_
  · intro k b hk hm ⟨hv, hkw, hx⟩
    refine ⟨_, rfl, ?_, ?_, ?_⟩
    · simp only [U128.getElem_zero, U128.getElem_one]
      have hp := umul_add_toNat y[k] m b.2.1
      have hpl := (umul y[k] m + U128.ofWord b.2.1).lo.toNat_lt
      simp only [U128.toNat] at hp
      have hs := subc_spec x[k] (umul y[k] m + U128.ofWord b.2.1).lo b.1
      have hr := val_toList_set b.2.2 k (subc x[k] (umul y[k] m + U128.ofWord b.2.1).lo b.1).1 hk
      have hs' := congrArg (fun t => 2 ^ (64 * k) * t) hs
      have hp' := congrArg (fun t => 2 ^ (64 * k) * t) hp
      simp only [Nat.mul_add] at hs' hp'
      rw [Nat.mul_succ, pow_add, val_take_succ' y k hk]
      have hxk := hx k hk le_rfl
      rw [hxk] at hr
      nlinarith
    · simp only [U128.getElem_one]
      have hp := umul_add_toNat y[k] m b.2.1
      simp only [U128.toNat] at hp
      have hy := y[k].toNat_lt
      have hm := m.toNat_lt
      have hym : y[k].toNat * m.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      omega
    · intro i hi hki
      rw [Vector.getElem_set, if_neg (by omega)]
      exact hx i hi (by omega)
  · intro b ⟨hv, hkw, _⟩
    rw [take_toList_self] at hv
    have hb := Bool.toNat_le b.1
    have : (b.2.1 + if b.1 = true then 1 else 0).toNat = b.2.1.toNat + b.1.toNat := by
      rw [UInt64.toNat_add, toNat_ite_bool, Nat.mod_eq_of_lt (by omega)]
    show val b.2.2.toList + m.toNat * val y.toList =
      val x.toList + 2 ^ (64 * n) * (b.2.1 + if b.1 = true then 1 else 0).toNat
    rw [this]
    exact hv

theorem addmul_spec {n : Nat} (x y : Vector Word n) (m : Word) (h : 0 < n) :
    val (addmul x y m h).1.toList + 2 ^ (64 * n) * (addmul x y m h).2.toNat =
      val x.toList + m.toNat * val y.toList := by
  unfold addmul
  refine forIn'_rco0_id
    (P := fun (v : Vector Word n × Word) =>
      val v.1.toList + 2 ^ (64 * n) * v.2.toNat = val x.toList + m.toNat * val y.toList)
    (fun k (b : MProd Word (Vector Word n)) =>
      val b.2.toList + 2 ^ (64 * k) * b.1.toNat = val x.toList + m.toNat * val (y.toList.take k) ∧
      ∀ i (hi : i < n), k ≤ i → b.2[i] = x[i])
    ⟨by simp, fun i hi _ => rfl⟩ ?_ ?_
  · intro k b hk hm ⟨hv, hx⟩
    refine ⟨_, rfl, ?_, ?_⟩
    · simp only [U128.getElem_zero, U128.getElem_one]
      have ht := umul_add_add_toNat y[k] m b.2[k] b.1
      simp only [U128.toNat] at ht
      have hr := val_toList_set b.2 k (umul y[k] m + U128.ofWord b.2[k] + U128.ofWord b.1).lo hk
      have ht' := congrArg (fun t => 2 ^ (64 * k) * t) ht
      simp only [Nat.mul_add] at ht'
      rw [Nat.mul_succ, pow_add, val_take_succ' y k hk]
      have hxk := congrArg UInt64.toNat (hx k hk le_rfl)
      linarith
    · intro i hi hki
      rw [Vector.getElem_set, if_neg (by omega)]
      exact hx i hi (by omega)
  · intro b ⟨hv, _⟩
    rw [take_toList_self] at hv
    simpa using hv

/-! ## The shifts -/

/-- The word `i` of `X * 2 ^ s`: the words `i` and `i - 1` of `X` funnel-shifted. -/
theorem shl_word (X i s : Nat) (hs : s < 64) (hi : 1 ≤ i) :
    X * 2 ^ s / 2 ^ (64 * i) % 2 ^ 64 =
      X / 2 ^ (64 * i) % 2 ^ 64 * 2 ^ s % 2 ^ 64 + X / 2 ^ (64 * (i - 1)) % 2 ^ 64 / 2 ^ (64 - s) := by
  have e64 : (2 : Nat) ^ 64 = 2 ^ s * 2 ^ (64 - s) := by rw [← pow_add]; congr 1; omega
  have hb : X / 2 ^ (64 * (i - 1)) % 2 ^ 64 / 2 ^ (64 - s) < 2 ^ s := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← e64]; exact Nat.mod_lt _ (by positivity)
  rw [e64, Nat.mul_comm (X / 2 ^ (64 * i) % (2 ^ s * 2 ^ (64 - s))), Nat.mul_mod_mul_left, ← e64,
    Nat.two_pow_add_eq_or_of_lt hb]
  apply Nat.eq_of_testBit_eq
  intro b
  simp only [Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_mul_two_pow,
    Nat.testBit_two_pow_mul]
  by_cases h1 : b < 64 <;> by_cases h2 : s ≤ b <;> simp [h1, h2]
  · rw [decide_eq_true (by omega : s ≤ b + 64 * i), decide_eq_true (by omega : b - s < 64 - s),
      decide_eq_true (by omega : b - s < 64), decide_eq_false (by omega : ¬b + (64 - s) < 64),
      show b + 64 * i - s = b - s + 64 * i by omega]
    simp
  · rw [decide_eq_true (by omega : s ≤ b + 64 * i), decide_eq_true (by omega : b + (64 - s) < 64),
      show b + (64 - s) + 64 * (i - 1) = b + 64 * i - s by omega]
  · exact ⟨fun h => by omega, fun h => by omega⟩
  · intro h; omega

/-- The word `i` of `X / 2 ^ s`: the words `i + 1` and `i` of `X` funnel-shifted. -/
theorem shr_word (X i s : Nat) (hs : s < 64) :
    X / 2 ^ s / 2 ^ (64 * i) % 2 ^ 64 =
      X / 2 ^ (64 * i) % 2 ^ 64 / 2 ^ s + X / 2 ^ (64 * (i + 1)) % 2 ^ 64 * 2 ^ (64 - s) % 2 ^ 64 := by
  have e64 : (2 : Nat) ^ 64 = 2 ^ (64 - s) * 2 ^ s := by rw [← pow_add]; congr 1; omega
  have hb : X / 2 ^ (64 * i) % 2 ^ 64 / 2 ^ s < 2 ^ (64 - s) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← e64]; exact Nat.mod_lt _ (by positivity)
  rw [e64, Nat.mul_comm (X / 2 ^ (64 * (i + 1)) % (2 ^ (64 - s) * 2 ^ s)), Nat.mul_mod_mul_left, ← e64,
    Nat.add_comm, Nat.two_pow_add_eq_or_of_lt hb]
  apply Nat.eq_of_testBit_eq
  intro b
  simp only [Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
    Nat.testBit_two_pow_mul]
  by_cases h1 : b < 64 <;> by_cases h2 : b + s < 64 <;> simp [h1, h2]
  · rw [decide_eq_false (by omega : ¬64 ≤ b + s), show b + 64 * i + s = b + s + 64 * i by omega]
    simp
  · rw [decide_eq_true (by omega : 64 ≤ b + s), decide_eq_true (by omega : b - (64 - s) < s),
      decide_eq_true (by omega : b - (64 - s) < 64),
      show b - (64 - s) + 64 * (i + 1) = b + 64 * i + s by omega]
    simp
  · omega
  · intro h3 h4; omega

theorem shl_getElem {n : Nat} (rn : Nat) (x : Vector Word n) (s : Fin 64) (hx : 0 < n)
    (hr : rn = n ∨ rn = n + 1) (t : Nat) (ht : t < rn) :
    (shl rn x s hx hr)[t] =
      if t = 0 then x[0] <<< s.val.toUInt64
      else if h : t < n then fshl x[t] x[t - 1] s else fshl 0 x[n - 1] s := by
  revert t
  unfold shl
  dsimp only
  split <;> rename_i hrn <;> simp only [pure_bind]
  all_goals
    refine forIn'_rco0_id (P := fun (v : Vector Word rn) => ∀ t (ht : t < rn), v[t] =
        if t = 0 then x[0] <<< s.val.toUInt64
        else if h : t < n then fshl x[t] x[t - 1] s else fshl 0 x[n - 1] s)
      (fun j (r : Vector Word rn) =>
        (∀ t (ht : t < rn), n - 1 - j ≤ t - 1 → t ≠ 0 → (h : t < n) → r[t] = fshl x[t] x[t - 1] s) ∧
        (∀ t (ht : t < rn), n ≤ t → r[t] = fshl 0 x[n - 1] s))
      ⟨fun t ht h1 h2 h3 => by omega, fun t ht h1 => ?_⟩ ?_ ?_
    rotate_left
    · intro j r hj hm ⟨hI, hJ⟩
      refine ⟨_, rfl, fun t ht h1 h2 h3 => ?_, fun t ht h1 => ?_⟩
      · rw [Vector.getElem_set]
        split_ifs with he
        · subst he; rfl
        · exact hI t ht (by omega) h2 h3
      · rw [Vector.getElem_set, if_neg (by omega)]
        exact hJ t ht h1
    · intro r ⟨hI, hJ⟩ t ht
      show (r.set 0 (x[0] <<< s.val.toUInt64) (by omega))[t] = _
      rw [Vector.getElem_set]
      by_cases h0 : t = 0
      · subst h0; simp
      · rw [if_neg (Ne.symm h0), if_neg h0]
        split_ifs with h1
        · exact hI t ht (by omega) h0 h1
        · exact hJ t ht (by omega)
  · rw [Vector.getElem_set, if_pos (by omega)]
  · omega

theorem shl_spec {n : Nat} (rn : Nat) (x : Vector Word n) (s : Fin 64) (hx : 0 < n)
    (hr : rn = n ∨ rn = n + 1) :
    val (shl rn x s hx hr).toList = val x.toList * 2 ^ s.val % 2 ^ (64 * rn) := by
  apply val_toList_eq_of_getElem
  intro t ht
  have hs := s.isLt
  rw [shl_getElem]
  split_ifs with h0 h1
  · subst h0
    rw [UInt64.toNat_shiftLeft, getElem_toNat' x 0 hx]
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.shiftLeft_eq, Nat.mul_zero, pow_zero,
      Nat.div_one]
    rw [Nat.mod_eq_of_lt (show s.val < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show s.val < 64 by omega),
      Nat.mod_mul_mod]
  · rw [toNat_fshl, shl_word _ _ _ hs (by omega), getElem_toNat' x t h1,
      getElem_toNat' x (t - 1) (by omega)]
  · have ht' : t = n := by omega
    subst ht'
    have h0' : val x.toList / 2 ^ (64 * t) = 0 := Nat.div_eq_of_lt (val_toList_lt x)
    rw [toNat_fshl, shl_word _ _ _ hs (by omega), getElem_toNat' x (t - 1) (by omega), h0']
    simp

theorem shr_getElem {n : Nat} (x : Vector Word n) (s : Fin 64) (hx : 0 < n) (t : Nat)
    (ht : t < n) :
    (shr x s hx)[t] = if h : t + 1 < n then fshr x[t + 1] x[t] s else x[n - 1] >>> s.val.toUInt64 := by
  revert t
  unfold shr
  dsimp only
  refine forIn'_rco_id (P := fun (v : Vector Word n) => ∀ t (ht : t < n), v[t] =
      if h : t + 1 < n then fshr x[t + 1] x[t] s else x[n - 1] >>> s.val.toUInt64)
    (fun j (r : Vector Word n) => ∀ t (ht : t < n), t < j → (h : t + 1 < n) →
      r[t] = fshr x[t + 1] x[t] s)
    (fun t ht h1 h2 => by omega) ?_ ?_
  · intro j r hj hm hI
    refine ⟨_, rfl, fun t ht h1 h2 => ?_⟩
    rw [Vector.getElem_set]
    split_ifs with he
    · have : t = j := by omega
      subst this
      simp only [show 1 + t = t + 1 by omega, Nat.add_sub_cancel]
    · exact hI t ht (by omega) h2
  · intro r hI t ht
    show (r.set (n - 1) (x[n - 1] >>> s.val.toUInt64) (by omega))[t] = _
    rw [Vector.getElem_set]
    split_ifs with h1 h2 h2
    · omega
    · subst h1; rfl
    · exact hI t ht (by omega) h2
    · omega

theorem shr_spec {n : Nat} (x : Vector Word n) (s : Fin 64) (hx : 0 < n) :
    val (shr x s hx).toList = val x.toList / 2 ^ s.val := by
  have hX := val_toList_lt x
  have hd : val x.toList / 2 ^ s.val < 2 ^ (64 * n) :=
    lt_of_le_of_lt (Nat.div_le_self _ _) hX
  rw [val_toList_eq_of_getElem (shr x s hx) (val x.toList / 2 ^ s.val), Nat.mod_eq_of_lt hd]
  intro t ht
  have hs := s.isLt
  rw [shr_getElem, shr_word _ _ _ hs]
  split_ifs with h1
  · rw [toNat_fshr, getElem_toNat' x t ht, getElem_toNat' x (t + 1) h1]
  · have ht' : t = n - 1 := by omega
    subst ht'
    have h0' : val x.toList / 2 ^ (64 * (n - 1 + 1)) = 0 :=
      Nat.div_eq_of_lt (by rw [show n - 1 + 1 = n by omega]; exact hX)
    rw [UInt64.toNat_shiftRight, getElem_toNat' x (n - 1) ht, h0']
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.shiftRight_eq_div_pow, Nat.zero_mod,
      Nat.zero_mul, Nat.add_zero]
    rw [Nat.mod_eq_of_lt (show s.val < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show s.val < 64 by omega)]

end Intx.Model
