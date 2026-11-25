import Lean
/-!
# `kernel_rfl`

`kernel_rfl` proves an equation `a = b` by `rfl` that only the kernel checks. The elaborator's
`rfl` evaluates the sides in `MetaM` before the kernel checks them again: seconds more for the
lists of the instructions of an image.
-/

open Lean Meta Elab Tactic in
/-- Proves `a = b` by `Eq.refl b`, checked by the kernel only (as `decide +kernel` does). -/
elab "kernel_rfl" : tactic => liftMetaFinishingTactic fun g => do
  let t ← instantiateMVars (← g.getType)
  let some (_, _, b) := t.eq? | throwError "kernel_rfl: not an equality: {t}"
  g.assign (← mkEqRefl b)
