import IntxRV.Words
/-!
# Conversions and comparisons with builtin integers

The specifications of the conversions of `uint256` to and from builtin integers and of its
comparisons with them state the signed values as integers (`toInt` of the register) modulo
`2^64` or `2^32`: `toInt_emod` and `toInt_signExtend32_emod` give them as the bits of the register.
`words4_lt_iff` and `lt_words4_iff` compare a word with the 4 words of a `uint256` as the code
does: the low word and the high words 0.
-/

namespace IntxRV

theorem toInt_emod (v : BitVec 64) : v.toInt % 2 ^ 64 = (v.toNat : Int) := by
  rw [BitVec.toInt_eq_toNat_cond]
  split <;> omega

theorem toInt_emod_toNat (v : BitVec 64) : (v.toInt % 2 ^ 64).toNat = v.toNat := by
  rw [toInt_emod]; simp

/-- An `int` in a register, sign-extended from 32 bits, modulo `2^32`. -/
theorem toInt_signExtend32_emod (v : BitVec 64) (h : v = (v.setWidth 32).signExtend 64) :
    v.toInt % 2 ^ 32 = ((v.toNat % 2 ^ 32 : Nat) : Int) := by
  conv => lhs; rw [h]
  rw [BitVec.toInt_signExtend_of_le (by decide), BitVec.toInt_eq_toNat_cond]
  simp only [BitVec.toNat_setWidth]
  split <;> omega

theorem toInt_signExtend_emod32 (v : BitVec 32) :
    (v.signExtend 64).toInt % 2 ^ 32 = (v.toNat : Int) := by
  rw [BitVec.toInt_signExtend_of_le (by decide), BitVec.toInt_eq_toNat_cond]
  split <;> omega

/-- A 32-bit value sign-extended to the register, as the calling convention requires of `int`. -/
theorem signExtend_setWidth32 (v : BitVec 32) :
    v.signExtend 64 = ((v.signExtend 64).setWidth 32).signExtend 64 := by
  congr 1
  apply BitVec.eq_of_getElem_eq; intro i hi
  simp [BitVec.getElem_setWidth, BitVec.getLsbD_signExtend, hi, BitVec.getLsbD_eq_getElem]
  intro; omega

/-- The words of a `uint256` are 0 if each word is. -/
theorem words4_eq_zero_iff (x0 x1 x2 x3 : BitVec 64) :
    x0.toNat + 2 ^ 64 * (x1.toNat + 2 ^ 64 * (x2.toNat + 2 ^ 64 * x3.toNat)) = 0 ↔
      x0 = 0#64 ∧ x1 = 0#64 ∧ x2 = 0#64 ∧ x3 = 0#64 := by
  simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.zero_mod]
  omega

/-- The 4 words below a word: the high words 0 and the low word below it. -/
theorem words4_lt_iff (x0 x1 x2 x3 y : BitVec 64) :
    x0.toNat + 2 ^ 64 * (x1.toNat + 2 ^ 64 * (x2.toNat + 2 ^ 64 * x3.toNat)) < y.toNat ↔
      x1 = 0#64 ∧ x2 = 0#64 ∧ x3 = 0#64 ∧ x0 < y := by
  have := y.isLt
  simp only [← BitVec.toNat_inj, BitVec.lt_def, BitVec.toNat_ofNat, Nat.zero_mod]
  omega

/-- A word below the 4 words: below the low word or a high word not 0. -/
theorem lt_words4_iff (x0 x1 x2 x3 y : BitVec 64) :
    y.toNat < x0.toNat + 2 ^ 64 * (x1.toNat + 2 ^ 64 * (x2.toNat + 2 ^ 64 * x3.toNat)) ↔
      y < x0 ∨ x1 ≠ 0#64 ∨ x2 ≠ 0#64 ∨ x3 ≠ 0#64 := by
  have := y.isLt; have := x0.isLt
  simp only [ne_eq, ← BitVec.toNat_inj, BitVec.lt_def, BitVec.toNat_ofNat, Nat.zero_mod]
  omega

/-- The result 1 of `sltu` and the other comparisons. -/
theorem ite_eq_one (p : Prop) [Decidable p] :
    ((if p then 1#64 else 0#64) = 1#64) ↔ p := by
  by_cases hp : p <;> simp [hp]

theorem ite_and_ite_eq_one (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1#64 else 0#64) &&& (if q then 1#64 else 0#64)) = 1#64 ↔ p ∧ q := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem ite_or_ite_eq_one (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1#64 else 0#64) ||| (if q then 1#64 else 0#64)) = 1#64 ↔ p ∨ q := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- The results of `sltu`, `and` and `or` of them are 0 or 1. -/
theorem ite_cases (p : Prop) [Decidable p] :
    (if p then 1#64 else 0#64) = 0#64 ∨ (if p then 1#64 else 0#64) = 1#64 := by
  by_cases hp : p <;> simp [hp]

theorem ite_and_ite_cases (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1#64 else 0#64) &&& (if q then 1#64 else 0#64)) = 0#64 ∨
      ((if p then 1#64 else 0#64) &&& (if q then 1#64 else 0#64)) = 1#64 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem ite_or_ite_cases (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1#64 else 0#64) ||| (if q then 1#64 else 0#64)) = 0#64 ∨
      ((if p then 1#64 else 0#64) ||| (if q then 1#64 else 0#64)) = 1#64 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem zero_lt_iff_ne_zero (v : BitVec 64) : 0#64 < v ↔ v ≠ 0#64 := by
  simp only [BitVec.lt_def, ne_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.zero_mod]
  omega

/-- The low 160 bits of the 4 words: the low 2 words and the low 32 bits of the third. -/
theorem words4_mod160 (x0 x1 x2 x3 : BitVec 64) :
    (x0.toNat + 2 ^ 64 * (x1.toNat + 2 ^ 64 * (x2.toNat + 2 ^ 64 * x3.toNat))) % 2 ^ (8 * 20) =
      x0.toNat + 2 ^ 64 * (x1.toNat + 2 ^ 64 * (x2.toNat % 2 ^ 32)) := by
  have := x0.isLt; have := x1.isLt; have := x2.isLt
  omega

end IntxRV
