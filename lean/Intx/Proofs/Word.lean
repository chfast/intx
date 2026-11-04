import Intx.ProofSupport.Basic
set_option warningAsError true
/-!
# Proofs: the word operations

What the word operations of `Intx.Model` compute, as numbers.
-/

namespace Intx.Model

/-- The number of a `uint128`. -/
def U128.toNat (a : U128) : Nat := a.lo.toNat + 2 ^ 64 * a.hi.toNat

@[simp] theorem U128.getElem_zero (p : U128) : p[0] = p.lo := rfl
@[simp] theorem U128.getElem_one (p : U128) : p[1] = p.hi := rfl

theorem U128.toNat_lt (a : U128) : a.toNat < 2 ^ 128 := by
  have := a.lo.toNat_lt
  have := a.hi.toNat_lt
  simp only [U128.toNat]
  omega

@[simp] theorem U128.toNat_ofWord (x : Word) : (U128.ofWord x).toNat = x.toNat := by
  simp [U128.ofWord, U128.toNat]

@[simp] theorem U128.toNat_mk (lo hi : Word) :
    (⟨lo, hi⟩ : U128).toNat = lo.toNat + 2 ^ 64 * hi.toNat := rfl

theorem toNat_ite_bool (c : Bool) : (if c then (1 : Word) else 0).toNat = c.toNat := by
  cases c <;> rfl

theorem addc_spec (x y : Word) (c : Bool) :
    (addc x y c).1.toNat + 2 ^ 64 * (addc x y c).2.toNat = x.toNat + y.toNat + c.toNat := by
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  unfold addc
  by_cases h1 : x + y < x <;> by_cases h2 : x + y + (if c then 1 else 0) < x + y <;>
    simp only [h1, h2, decide_true, decide_false, Bool.or_true, Bool.or_false,
      Bool.toNat_true, Bool.toNat_false] <;>
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at h1 h2 <;>
    rw [UInt64.toNat_add] at h2 ⊢ <;> rw [UInt64.toNat_add] <;> cases c <;> simp at h2 ⊢ <;> omega

theorem subc_spec (x y : Word) (c : Bool) :
    (subc x y c).1.toNat + y.toNat + c.toNat = x.toNat + 2 ^ 64 * (subc x y c).2.toNat := by
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  unfold subc
  by_cases h1 : x < y <;> by_cases h2 : x - y < (if c then 1 else 0) <;>
    simp only [h1, h2, decide_true, decide_false, Bool.or_true, Bool.or_false,
      Bool.toNat_true, Bool.toNat_false] <;>
    rw [UInt64.lt_iff_toNat_lt] at h1 h2 <;>
    rw [UInt64.toNat_sub] at h2 ⊢ <;> rw [UInt64.toNat_sub] <;> cases c <;> simp at h2 ⊢ <;> omega

theorem U128.toNat_add (a b : U128) : (a + b).toNat = (a.toNat + b.toNat) % 2 ^ 128 := by
  have h1 := addc_spec a.lo b.lo false
  have h2 := addc_spec a.hi b.hi (addc a.lo b.lo false).2
  have := (addc a.hi b.hi (addc a.lo b.lo false).2).1.toNat_lt
  have := (addc a.lo b.lo false).1.toNat_lt
  have : (addc a.hi b.hi (addc a.lo b.lo false).2).2.toNat ≤ 1 := Bool.toNat_le _
  show (U128.add a b).toNat = _
  simp only [U128.add, U128.toNat] at *
  simp only [Bool.toNat_false, Nat.add_zero] at h1
  omega

theorem U128.lt_eq (a b : U128) : U128.lt a b = decide (a.toNat < b.toNat) := by
  simp only [U128.lt, U128.toNat]
  congr 1
  apply propext
  omega

theorem umul_toNat (x y : Word) : (umul x y).toNat = x.toNat * y.toNat := by
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  have : x.toNat * y.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' hx hy
  simp only [umul, U128.toNat, UInt64.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul this)]
  exact Nat.mod_add_div _ _

/-- The sum of a product and two words fits in `uint128`. -/
theorem umul_add_add_toNat (x y a b : Word) :
    (umul x y + U128.ofWord a + U128.ofWord b).toNat = x.toNat * y.toNat + a.toNat + b.toNat := by
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have : x.toNat * y.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  rw [U128.toNat_add, U128.toNat_add, umul_toNat, U128.toNat_ofWord, U128.toNat_ofWord,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem umul_add_toNat (x y a : Word) :
    (umul x y + U128.ofWord a).toNat = x.toNat * y.toNat + a.toNat := by
  have h := umul_add_add_toNat x y a 0
  have : (U128.ofWord a + U128.ofWord 0) = U128.ofWord a + U128.ofWord 0 := rfl
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  have ha := a.toNat_lt
  have : x.toNat * y.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  rw [U128.toNat_add, umul_toNat, U128.toNat_ofWord, Nat.mod_eq_of_lt (by omega)]

theorem toNat_fshl (hi lo : Word) (s : Fin 64) :
    (fshl hi lo s).toNat = hi.toNat * 2 ^ s.val % 2 ^ 64 + lo.toNat / 2 ^ (64 - s.val) := by
  have hs := s.isLt
  have hl := lo.toNat_lt
  unfold fshl
  split_ifs with h0
  · subst h0
    simp [Nat.mod_eq_of_lt hi.toNat_lt, Nat.div_eq_of_lt hl]
  · have hs0 : s.val ≠ 0 := fun h => h0 (Fin.ext h)
    rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight]
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (show s.val < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show s.val < 64 by omega),
      Nat.mod_eq_of_lt (show 64 - s.val < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show 64 - s.val < 64 by omega)]
    have e : (2 : Nat) ^ 64 = 2 ^ s.val * 2 ^ (64 - s.val) := by rw [← pow_add]; congr 1; omega
    have hb : lo.toNat / 2 ^ (64 - s.val) < 2 ^ s.val := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show s.val + (64 - s.val) = 64 by omega]
      exact hl
    rw [e, Nat.mul_comm hi.toNat, Nat.mul_mod_mul_left, Nat.two_pow_add_eq_or_of_lt hb]

theorem toNat_fshr (hi lo : Word) (s : Fin 64) :
    (fshr hi lo s).toNat = lo.toNat / 2 ^ s.val + hi.toNat * 2 ^ (64 - s.val) % 2 ^ 64 := by
  have hs := s.isLt
  have hl := lo.toNat_lt
  unfold fshr
  split_ifs with h0
  · subst h0
    simp [Nat.mul_mod_left]
  · have hs0 : s.val ≠ 0 := fun h => h0 (Fin.ext h)
    rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight]
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (show s.val < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show s.val < 64 by omega),
      Nat.mod_eq_of_lt (show 64 - s.val < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show 64 - s.val < 64 by omega)]
    have e : (2 : Nat) ^ 64 = 2 ^ (64 - s.val) * 2 ^ s.val := by rw [← pow_add]; congr 1; omega
    have hb : lo.toNat / 2 ^ s.val < 2 ^ (64 - s.val) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show 64 - s.val + s.val = 64 by omega]
      exact hl
    rw [e, Nat.mul_comm hi.toNat, Nat.mul_mod_mul_left, Nat.add_comm,
      Nat.two_pow_add_eq_or_of_lt hb, Nat.lor_comm]

theorem clz_nonzero_spec (x : Word) (h : x ≠ 0) :
    ∃ s, clz_nonzero x = some s ∧ 2 ^ 63 ≤ x.toNat * 2 ^ s.val ∧ x.toNat * 2 ^ s.val < 2 ^ 64 := by
  have hx := x.toNat_lt
  have hx0 : x.toNat ≠ 0 := fun h0 => h (UInt64.toNat_inj.mp (by simpa using h0))
  have hL : Nat.log2 x.toNat < 64 := (Nat.log2_lt hx0).mpr hx
  have h1 := Nat.log2_self_le hx0
  have h2 : x.toNat < 2 ^ (Nat.log2 x.toNat + 1) := Nat.lt_log2_self
  refine ⟨⟨63 - Nat.log2 x.toNat, by omega⟩, by simp [clz_nonzero, h], ?_, ?_⟩
  · calc 2 ^ 63 = 2 ^ Nat.log2 x.toNat * 2 ^ (63 - Nat.log2 x.toNat) := by
          rw [← pow_add]; congr 1; omega
      _ ≤ x.toNat * 2 ^ (63 - Nat.log2 x.toNat) := Nat.mul_le_mul_right _ h1
  · calc x.toNat * 2 ^ (63 - Nat.log2 x.toNat)
        < 2 ^ (Nat.log2 x.toNat + 1) * 2 ^ (63 - Nat.log2 x.toNat) :=
          Nat.mul_lt_mul_of_pos_right h2 (by positivity)
      _ = 2 ^ 64 := by rw [← pow_add]; congr 1; omega

end Intx.Model
