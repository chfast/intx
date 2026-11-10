set_option warningAsError true
/-!
# Specification

The vocabulary of the specifications: the words of a number and their value. It uses only the Lean
core. The specifications are the @post commands of the documentation of intx.hpp, which
scripts/rv_api.py states in Intx/Gen/Spec.lean for the models (`Intx.Spec.<name>.spec`). A model
returns `none` for undefined behavior of the C++ code (see `Intx.Model`), so a specification
`∃ res, model … = some res ∧ …` excludes it.
-/

namespace Intx

/-- A `uint64_t`. -/
abbrev Word := UInt64

/-- An `intx::uint256`: its 4 words, the least significant first. -/
abbrev U256 := Vector Word 4

/-- The number with the words `w`, the least significant first. -/
def val (w : List Word) : Nat := w.foldr (fun x acc => x.toNat + 2 ^ 64 * acc) 0

end Intx
