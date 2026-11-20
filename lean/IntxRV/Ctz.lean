import Init
/-!
# The trailing zeros of a word

`ctz()` of a nonzero word isolates its lowest set bit with `x & -x` and looks up its index in a
table of a de Bruijn sequence. `and_neg_self` gives the isolated bit, `toNat_mod_two_pow_ctz` and
`testBit_ctz` the properties of the index that the specification states.
-/

namespace IntxRV

theorem ctz_lt {w : Nat} {x : BitVec w} (hx : x ≠ 0#w) : x.ctz.toNat < w := by
  have h := (BitVec.ctz_lt_iff_ne_zero (x := x)).mpr hx
  rw [BitVec.lt_def, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt Nat.lt_two_pow_self] at h
  exact h

/-- `x & -x` is the lowest set bit of `x`. -/
theorem and_neg_self {w : Nat} {x : BitVec w} (hx : x ≠ 0#w) :
    x &&& -x = BitVec.twoPow w x.ctz.toNat := by
  have ht := ctz_lt hx
  have hb := BitVec.getLsbD_true_ctz_of_ne_zero hx
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_neg, BitVec.getLsbD_twoPow]
  rcases Nat.lt_trichotomy i x.ctz.toNat with h | h | h
  · simp [BitVec.getLsbD_false_of_lt_ctz h]
    omega
  · subst h
    have : ¬ ∃ j < x.ctz.toNat, x.getLsbD j = true := by
      rintro ⟨j, hj, hj'⟩
      rw [BitVec.getLsbD_false_of_lt_ctz hj] at hj'
      cases hj'
    simp [hb, hi, this]
  · have : ∃ j < i, x.getLsbD j = true := ⟨_, h, hb⟩
    cases x.getLsbD i <;> simp [this, hi] <;> omega

/-- The bits of `x` below `ctz x` are zero. -/
theorem toNat_mod_two_pow_ctz {w : Nat} (x : BitVec w) : x.toNat % 2 ^ x.ctz.toNat = 0 := by
  rw [← BitVec.toNat_setWidth]
  have : x.setWidth x.ctz.toNat = 0#_ := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [hi, BitVec.getLsbD_false_of_lt_ctz hi]
  rw [this, BitVec.toNat_zero]

/-- The bit `ctz x` of a nonzero `x` is set. -/
theorem testBit_ctz {w : Nat} {x : BitVec w} (hx : x ≠ 0#w) : x.toNat.testBit x.ctz.toNat :=
  BitVec.getLsbD_true_ctz_of_ne_zero hx

/-- The specification of `ctz()` for the number `2^(64k) * (w + 2^64 * R)`: its first nonzero
word `w` at `k` has the trailing zeros `t`. -/
theorem ctz_spec_of_word (k t w R : Nat) (hw : w < 2 ^ 64) (ht : t < 64) (hm : w % 2 ^ t = 0)
    (hb : w.testBit t) :
    2 ^ (64 * k) * (w + 2 ^ 64 * R) % 2 ^ (64 * k + t) = 0 ∧
      (2 ^ (64 * k) * (w + 2 ^ 64 * R)).testBit (64 * k + t) := by
  constructor
  · rw [Nat.pow_add, Nat.mul_mod_mul_left,
      show 2 ^ 64 * R = 2 ^ t * (2 ^ (64 - t) * R) by
        rw [← Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_cancel' (by omega)],
      Nat.add_mul_mod_self_left, hm, Nat.mul_zero]
  · rw [Nat.testBit_two_pow_mul, Nat.add_comm w, Nat.testBit_two_pow_mul_add _ hw]
    simp [ht, hb]

/-- The result of `ctz()`: the `or` of the word index `64 i` and the count `t < 64` adds them. -/
theorem toNat_or_lt (i t : Nat) (hi : i < 2 ^ 58) (ht : t < 64) :
    (BitVec.ofNat 64 (64 * i) ||| BitVec.ofNat 64 t).toNat = 64 * i + t := by
  rw [BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), show 64 * i = i <<< 6 by rw [Nat.shiftLeft_eq]; omega,
    ← Nat.shiftLeft_add_eq_or_of_lt (by omega : t < 2 ^ 6), Nat.shiftLeft_eq]

/-- The index of the table that `ctz()` reads for the lowest set bit `t` of a word. -/
def deBruijnIdx (t : Nat) : Nat :=
  ((BitVec.twoPow 64 t * 0x0218a392cd3d5dbf#64) >>> 58).toNat

end IntxRV
