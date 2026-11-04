set_option warningAsError true
/-!
# Specification

The statement an auditor must accept: what `intx::mulmod()` computes. It uses only the Lean core.
-/

namespace Intx

/-- A `uint64_t`. -/
abbrev Word := UInt64

/-- An `intx::uint256`: its 4 words, the least significant first. -/
abbrev U256 := Vector Word 4

/-- The number with the words `w`, the least significant first. -/
def val (w : List Word) : Nat := w.foldr (fun x acc => x.toNat + 2 ^ 64 * acc) 0

/-- `f` computes `x * y mod m` for every nonzero `m`. The result `none` stands for undefined
behavior of the C++ code (see `Intx.Model`), so `f` must not have it for these arguments. -/
def MulmodCorrect (f : U256 → U256 → U256 → Option U256) : Prop :=
  ∀ x y m : U256, val m.toList ≠ 0 →
    ∃ r, f x y m = some r ∧ val r.toList = val x.toList * val y.toList % val m.toList

end Intx
