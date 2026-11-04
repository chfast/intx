import Intx
set_option warningAsError true
/-!
# Checks: the main theorem

The main theorem proves the specification for the model of `mulmod()`, and its proof uses only the
axioms of Lean and Mathlib: no `sorry` (`sorryAx`), no `native_decide` (`Lean.ofReduceBool`) and no
axioms of this project.
-/

example : Intx.MulmodCorrect Intx.Model.mulmod := Intx.mulmod_correct

/-- info: 'Intx.mulmod_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Intx.mulmod_correct
