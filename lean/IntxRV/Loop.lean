import IntxRV.StepTactic
import IntxRV.Words
/-!
# Loops

`Reach.loop` proves the run from the head of a loop by induction on the iterations left: the
invariant `I n` at the head, and the run of one iteration back to the head with a smaller `n` or
out of the loop. `rv_exec_cut` is `rv_exec_loop` that stops at the cut points: the head and the
exit. `rv_has`, `rv_lacks` and `rv_get` select the paths of a run by the conditions of their
branches, which they compare without unfolding: unifying with the hypotheses of the loaded words
would unfold `memWord`. The lemmas of `words` split a buffer at its top word and keep its words over a store
outside it.
-/

namespace IntxRV
open LeanRV64D.Defs

/-- A loop: the run from its head reaches `tgt` if each state of the invariant `I n` at the head
reaches `tgt`, given that the states `I k` of the smaller `k` do (the iterations left). -/
theorem Reach.loop {A : List (BitVec 64)} {prog : List instruction} {base head tgt : BitVec 64}
    {Q : Regs → Mem → Prop} (I : Nat → Regs → Mem → Prop)
    (h : ∀ n x m, I n x m → (∀ k < n, ∀ x' m', I k x' m' → Reach A prog base head x' m' tgt Q) →
      Reach A prog base head x m tgt Q) :
    ∀ n x m, I n x m → Reach A prog base head x m tgt Q := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih => exact fun x m hi => h n x m hi fun k hk => ih k hk

/-- The words of a buffer with its top word split off. -/
theorem words_succ_top (m : Mem) : ∀ (n : Nat) (a : BitVec 64),
    words m a (n + 1) = words m a n + 2 ^ (64 * n) * (memWord m (a + BitVec.ofNat 64 (8 * n)).toNat).toNat
  | 0, a => by simp [words]
  | n + 1, a => by
    rw [words, words_succ_top m n (a + 8), words]
    rw [show a + 8 + BitVec.ofNat 64 (8 * n) = a + BitVec.ofNat 64 (8 * (n + 1)) by
      rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega]
    rw [show 64 * (n + 1) = 64 + 64 * n by ring, pow_add]
    ring

/-- A store outside a buffer does not change its words. -/
theorem words_memStore_of_disjoint (m : Mem) (b : Nat) (v : BitVec 64) : ∀ (n : Nat) (a : BitVec 64),
    a.toNat + 8 * n ≤ 2 ^ 64 → (b + 8 ≤ a.toNat ∨ a.toNat + 8 * n ≤ b) →
      words (memStore m b v) a n = words m a n
  | 0, _, _, _ => rfl
  | n + 1, a, ha, h => by
    rw [words, words, memWord_memStore_of_ne _ _ _ _ (by omega)]
    cases n with
    | zero => rfl
    | succ k =>
      have h8 : (a + 8).toNat = a.toNat + 8 := by
        rw [BitVec.toNat_add]; simp; omega
      rw [words_memStore_of_disjoint m b v (k + 1) (a + 8) (by omega) (by omega)]

end IntxRV

namespace IntxRV
open Lean Meta Elab Tactic

/-- Fails if the goal is a `Reach` from the instruction `k` of one of `ks`: a cut point where a
run stops. -/
elab "rv_not_at " ks:num* : tactic => withMainContext do
  let t ← whnfR (← getMainTarget)
  unless t.isAppOfArity ``Reach 8 do return
  let pc := t.getArg! 3
  if pc.isAppOfArity ``pcAt 2 then
    if let some k := (pc.getArg! 1).rawNatLit? <|> (pc.getArg! 1).nat? then
      if ks.any (·.getNat == k) then throwError "rv_not_at: the cut point {k}"

/-- `rv_exec_loop` that stops at the instructions `ks`. -/
macro "rv_exec_cut " ks:num* : tactic => `(tactic| (
  repeat' (first | refine Reach.refl_at ?_ | (rv_not_at $ks*; rv_step_loop))))

end IntxRV

namespace IntxRV

open Lean Meta Elab Tactic in
/-- Succeeds if a hypothesis has the type `t`, compared without unfolding: the condition of a
branch on a path of a run. -/
elab "rv_has " t:term : tactic => withMainContext do
  let t ← instantiateMVars (← Term.elabTerm t none)
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if (← instantiateMVars d.type) == t then return
  throwError "rv_has: no hypothesis {t}"

open Lean Meta Elab Tactic in
/-- Succeeds if no hypothesis has the type `t`, compared without unfolding. -/
elab "rv_lacks " t:term : tactic => withMainContext do
  let t ← instantiateMVars (← Term.elabTerm t none)
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if (← instantiateMVars d.type) == t then throwError "rv_lacks: {t}"

open Lean Meta Elab Tactic in
/-- Names `h` the hypothesis of the type `t`, compared without unfolding. -/
elab "rv_get " h:ident " : " t:term : tactic => withMainContext do
  let t ← instantiateMVars (← Term.elabTerm t none)
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if (← instantiateMVars d.type) == t then
      let g ← getMainGoal
      let (_, g) ← (← g.assert h.getId t d.toExpr).intro1P
      replaceMainGoal [g]
      return
  throwError "rv_get: no hypothesis {t}"
end IntxRV
