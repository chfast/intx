import IntxRV.Words
import IntxRV.Values
import Intx.Proofs.Words
/-!
# Models of the uint256 operators

The models of `operator+` and `operator-` of `uint<256>`: the chains of `addc()` and `subc()` of
`Intx.Model` on the 4 words, with their specifications proved from `addc_spec` and `subc_spec`.
The bitwise operators are the operation on each word (`List.zipWith`), and `val_zipWith_or`,
`val_zipWith_and` and `val_zipWith_xor` give their values.
`wordList m a k` are the `k` words at `a` in the memory `m` as `Word`s.
-/

namespace IntxRV
open Intx Intx.Model

/-- The `k` words at `a` in `m`, the lowest word first. -/
def wordList (m : Mem) (a : BitVec 64) : Nat → List Word
  | 0 => []
  | k + 1 => .ofBitVec (memWord m a.toNat) :: wordList m (a + 8) k

theorem val_wordList (m : Mem) (a : BitVec 64) (k : Nat) :
    val (wordList m a k) = words m a k := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => simp [wordList, words, val, ← ih]

/-- `operator+(const uint256&, const uint256&)`: `addc(x, y).value`. -/
def add4 : List Word → List Word → List Word
  | [a0, a1, a2, a3], [b0, b1, b2, b3] =>
    let (s0, c1) := addc a0 b0
    let (s1, c2) := addc a1 b1 c1
    let (s2, c3) := addc a2 b2 c2
    [s0, s1, s2, (addc a3 b3 c3).1]
  | _, _ => []

/-- `operator-(const uint256&, const uint256&)`: `subc(x, y).value`. -/
def sub4 : List Word → List Word → List Word
  | [a0, a1, a2, a3], [b0, b1, b2, b3] =>
    let (d0, c1) := subc a0 b0
    let (d1, c2) := subc a1 b1 c1
    let (d2, c3) := subc a2 b2 c2
    [d0, d1, d2, (subc a3 b3 c3).1]
  | _, _ => []

theorem add4_spec (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    val (add4 [a0, a1, a2, a3] [b0, b1, b2, b3]) =
      (val [a0, a1, a2, a3] + val [b0, b1, b2, b3]) % 2 ^ 256 := by
  simp only [add4, val, List.foldr]
  have h0 := addc_spec a0 b0 false
  have h1 := addc_spec a1 b1 (addc a0 b0).2
  have h2 := addc_spec a2 b2 (addc a1 b1 (addc a0 b0).2).2
  have h3 := addc_spec a3 b3 (addc a2 b2 (addc a1 b1 (addc a0 b0).2).2).2
  have := (addc a0 b0).1.toNat_lt
  have := (addc a1 b1 (addc a0 b0).2).1.toNat_lt
  have := (addc a2 b2 (addc a1 b1 (addc a0 b0).2).2).1.toNat_lt
  have := (addc a3 b3 (addc a2 b2 (addc a1 b1 (addc a0 b0).2).2).2).1.toNat_lt
  have := (addc a3 b3 (addc a2 b2 (addc a1 b1 (addc a0 b0).2).2).2).2.toNat_le
  simp only [Bool.toNat_false, Nat.add_zero] at h0
  omega

theorem sub4_spec (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    val (sub4 [a0, a1, a2, a3] [b0, b1, b2, b3]) =
      (val [a0, a1, a2, a3] + 2 ^ 256 - val [b0, b1, b2, b3]) % 2 ^ 256 := by
  simp only [sub4, val, List.foldr]
  have h0 := subc_spec a0 b0 false
  have h1 := subc_spec a1 b1 (subc a0 b0).2
  have h2 := subc_spec a2 b2 (subc a1 b1 (subc a0 b0).2).2
  have h3 := subc_spec a3 b3 (subc a2 b2 (subc a1 b1 (subc a0 b0).2).2).2
  have := (subc a0 b0).1.toNat_lt
  have := (subc a1 b1 (subc a0 b0).2).1.toNat_lt
  have := (subc a2 b2 (subc a1 b1 (subc a0 b0).2).2).1.toNat_lt
  have := (subc a3 b3 (subc a2 b2 (subc a1 b1 (subc a0 b0).2).2).2).1.toNat_lt
  have := (subc a3 b3 (subc a2 b2 (subc a1 b1 (subc a0 b0).2).2).2).2.toNat_le
  have := a0.toNat_lt
  have := a1.toNat_lt
  have := a2.toNat_lt
  have := a3.toNat_lt
  have := b0.toNat_lt
  have := b1.toNat_lt
  have := b2.toNat_lt
  have := b3.toNat_lt
  simp only [Bool.toNat_false, Nat.add_zero] at h0
  omega

/-- A bitwise operation of `Nat` on two words joined with their higher parts. -/
theorem bitwise_two_pow_mul_add {f : Bool → Bool → Bool} (hf : f false false = false)
    {a b : Nat} (c d : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    Nat.bitwise f (2 ^ 64 * c + a) (2 ^ 64 * d + b) =
      2 ^ 64 * Nat.bitwise f c d + Nat.bitwise f a b := by
  have hab : Nat.bitwise f a b < 2 ^ 64 := Nat.bitwise_lt_two_pow ha hb
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_bitwise hf, Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_two_pow_mul_add _ hb,
    Nat.testBit_two_pow_mul_add _ hab]
  split
  · rw [Nat.testBit_bitwise hf]
  · rw [Nat.testBit_bitwise hf]

theorem val_zipWith_bitwise {f : Bool → Bool → Bool} (hf : f false false = false)
    (g : Word → Word → Word) (hg : ∀ a b : Word, (g a b).toNat = Nat.bitwise f a.toNat b.toNat) :
    ∀ xs ys : List Word, xs.length = ys.length →
      val (List.zipWith g xs ys) = Nat.bitwise f (val xs) (val ys)
  | [], [], _ => by simp only [val, List.zipWith_nil_left, List.foldr]; unfold Nat.bitwise; simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
    simp only [List.zipWith_cons_cons, val, List.foldr] at *
    have := val_zipWith_bitwise hf g hg xs ys (by simpa using h)
    simp only [val] at this
    rw [this, hg, Nat.add_comm, Nat.add_comm x.toNat, Nat.add_comm y.toNat,
      bitwise_two_pow_mul_add hf _ _ x.toNat_lt y.toNat_lt]

theorem val_zipWith_or (xs ys : List Word) (h : xs.length = ys.length) :
    val (List.zipWith (· ||| ·) xs ys) = val xs ||| val ys :=
  val_zipWith_bitwise rfl _ (fun a b => by simp [UInt64.toNat_or]; rfl) xs ys h

theorem val_zipWith_and (xs ys : List Word) (h : xs.length = ys.length) :
    val (List.zipWith (· &&& ·) xs ys) = val xs &&& val ys :=
  val_zipWith_bitwise rfl _ (fun a b => by simp [UInt64.toNat_and]; rfl) xs ys h

theorem val_zipWith_xor (xs ys : List Word) (h : xs.length = ys.length) :
    val (List.zipWith (· ^^^ ·) xs ys) = val xs ^^^ val ys :=
  val_zipWith_bitwise rfl _ (fun a b => by simp [UInt64.toNat_xor]; rfl) xs ys h

theorem length_wordList (m : Mem) (a : BitVec 64) (k : Nat) : (wordList m a k).length = k := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => simp [wordList, ih]

/-- The bitwise or of two 0/1 values. -/
theorem ite_or_ite (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1#64 else 0#64) ||| if q then 1#64 else 0#64) = if p ∨ q then 1#64 else 0#64 := by
  by_cases p <;> by_cases q <;> simp_all

/-- The negation of a 0/1 value. -/
theorem ite_xor_one (p : Prop) [Decidable p] :
    ((if p then 1#64 else 0#64) ^^^ 1#64) = if ¬p then 1#64 else 0#64 := by
  by_cases p <;> simp_all

/-- The and of a 0/1 value with the complement of another. -/
theorem ite_and_not_ite (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1#64 else 0#64) &&& ((if q then 1#64 else 0#64) ^^^ 18446744073709551615#64)) =
      if p ∧ ¬q then 1#64 else 0#64 := by
  by_cases p <;> by_cases q <;> simp_all

theorem not_ite_and_ite (p q : Prop) [Decidable p] [Decidable q] :
    (((if q then 1#64 else 0#64) ^^^ 18446744073709551615#64) &&& (if p then 1#64 else 0#64)) =
      if p ∧ ¬q then 1#64 else 0#64 := by
  rw [BitVec.and_comm, ite_and_not_ite]

theorem zero_lt_iff (a : BitVec 64) : 0#64 < a ↔ ¬a = 0#64 := by
  constructor <;> intro h <;> bv_omega

/-- The bitwise and of two 0/1 values. -/
theorem ite_and_ite (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1#64 else 0#64) &&& if q then 1#64 else 0#64) = if p ∧ q then 1#64 else 0#64 := by
  by_cases p <;> by_cases q <;> simp_all

/-- The words of `w * 2 ^ s`, `w` of 8 words: the funnel shifts of the words of `w`. -/
theorem val_shl_words (w r : List Word) (hw : w.length = 8) (hr : r.length = 9) (s : Nat)
    (hs : s < 64)
    (h : ∀ i (hi : i < 9), r[i].toNat =
      if i = 0 then w[0].toNat * 2 ^ s % 2 ^ 64
      else if h : i < 8 then w[i].toNat * 2 ^ s % 2 ^ 64 + w[i - 1].toNat / 2 ^ (64 - s)
      else 0 * 2 ^ s % 2 ^ 64 + w[7].toNat / 2 ^ (64 - s)) :
    val r = val w * 2 ^ s % 2 ^ 576 := by
  let xv : Vector Word 8 := ⟨w.toArray, by simpa using hw⟩
  have hsp := shl_spec 9 xv ⟨s, hs⟩ (by omega) (by omega)
  have hx : xv.toList = w := by simp [xv]
  rw [hx] at hsp
  rw [← hsp]
  congr 1
  apply List.ext_getElem (by simp [hr])
  intro i h1 h2
  apply UInt64.toNat_inj.mp
  rw [h i (by omega), Vector.getElem_toList, shl_getElem]
  split_ifs with h0 h3
  · subst h0
    simp only [xv, UInt64.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.toUInt64_eq, UInt64.toNat_ofNat']
    rw [Nat.mod_eq_of_lt (show s < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show s < 64 by omega)]
    rfl
  · rw [toNat_fshl]; rfl
  · rw [toNat_fshl]; rfl
/-- An `unsigned` argument less than 2^31 in a register, sign-extended by the calling
convention: the register is its value. -/
theorem toNat_of_signExtend {v : BitVec 64} (h : v = (v.setWidth 32).signExtend 64)
    (hs : v.toNat % 2 ^ 32 < 2 ^ 31) : v.toNat = v.toNat % 2 ^ 32 := by
  have hm : (v.setWidth 32).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt, BitVec.toNat_setWidth]; omega
  rw [h, BitVec.signExtend_eq_setWidth_of_msb_false hm]
  simp; omega

theorem subw_64_toNat (s : BitVec 64) (hs : s.toNat < 64) :
    (64#32 - s.setWidth 32).signExtend 64 = 64#64 - s := by
  have hm : (64#32 - s.setWidth 32).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt, BitVec.toNat_sub, BitVec.toNat_setWidth]
    simp; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_sub]; omega

/-- The funnel shift of `a:b` left by `s`, as a number. -/
theorem toNat_funnel (a b : BitVec 64) (s : Nat) (h0 : 0 < s) (h : s < 64) :
    ((a <<< s) ||| (b >>> (64 - s))).toNat = a.toNat * 2 ^ s % 2 ^ 64 + b.toNat / 2 ^ (64 - s) := by
  have e64 : (2 : Nat) ^ 64 = 2 ^ s * 2 ^ (64 - s) := by rw [← pow_add]; congr 1; omega
  have hb : b.toNat / 2 ^ (64 - s) < 2 ^ s := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← e64]; exact b.isLt
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, e64, Nat.mul_comm a.toNat, Nat.mul_mod_mul_left,
    ← Nat.two_pow_add_eq_or_of_lt hb]

end IntxRV
