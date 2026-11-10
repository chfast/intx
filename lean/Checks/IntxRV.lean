import IntxRV
import IntxRV.EnvM
set_option warningAsError true
/-!
# Checks: the RV64 machine code

The environments of IntxRV exist, and its theorems (`#check_rv_axioms`, also used for the
specifications in Checks/IntxRVApi.lean) use only the axioms of Lean and the opaque functions
that the Sail model declares as axioms (`SAIL_AXIOMS`): no `sorry` (`sorryAx`), no
`native_decide` and no `bv_decide` (whose proofs add axioms `*._native.bv_decide.*`, checked by
compiled code).
-/

open Lean Elab Command in
/-- Fails unless every axiom that `thm` depends on is an axiom of Lean or one of the opaque
functions of the Sail model (declared in `LeanRV64D`). -/
elab "#check_rv_axioms " thm:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo thm
  let axioms ← liftCoreM <| collectAxioms name
  let env ← getEnv
  for ax in axioms do
    let lean := [``propext, ``Classical.choice, ``Quot.sound].contains ax
    let sail := (env.getModuleIdxFor? ax).any fun i =>
      (env.header.moduleNames[i.toNat]!).getRoot == `LeanRV64D
    unless lean || sail do
      throwError "{name} depends on the axiom {ax}"

#check_rv_axioms IntxRV.env_exists
#check_rv_axioms IntxRV.inv_mkState
#check_rv_axioms IntxRV.envM_exists
