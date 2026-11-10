import IntxRV.Words
import IntxRV.Values
/-!
# Models of the uint256 operators

The models of `operator+` and `operator-` of `uint<256>`: the chains of `addc()` and `subc()` of
`Intx.Model` on the 4 words, with their specifications proved from `addc_spec` and `subc_spec`.
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

/-- The bitwise or of two 0/1 values. -/
theorem ite_or_ite (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1#64 else 0#64) ||| if q then 1#64 else 0#64) = if p ∨ q then 1#64 else 0#64 := by
  by_cases p <;> by_cases q <;> simp_all

/-- The bitwise and of two 0/1 values. -/
theorem ite_and_ite (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1#64 else 0#64) &&& if q then 1#64 else 0#64) = if p ∧ q then 1#64 else 0#64 := by
  by_cases p <;> by_cases q <;> simp_all

end IntxRV
