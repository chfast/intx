import IntxRV.StepTactic
import Mathlib.Tactic.Linarith
/-!
# The arithmetic of a run

After `rv_exec` the values of a run are names `w` with their definitions `Defn w v`. `rv_arith`
proves an equation of the numbers of the names from exact linear facts of the definitions:
- a sum and its carry: `s + 2^64 * c = a + b`, also of a sum of more summands (`s < t` for a
  summand `t`), by `omega` from the facts of the summands,
- the words of a product: `lo + 2^64 * hi = a * b` (the product is an atom),
- a sum without a carry that cannot overflow: `w = a + b`, by `omega` from the facts that the
  operands depend on (as a high word of a product plus carries).
Each `omega` sees only the facts it needs. `linarith` proves the equation from all the exact
facts. `rv_copies` substitutes the names that are copies of other values.
-/

open Lean Meta Elab Tactic

namespace IntxRV

theorem Defn.eq {w v : BitVec 64} (h : Defn w v) : w = v := h

theorem defn_add {w a b : BitVec 64} (h : Defn w (a + b)) :
    w.toNat = (a.toNat + b.toNat) % 2 ^ 64 := by rw [h.eq, BitVec.toNat_add]

theorem defn_sub {w a b : BitVec 64} (h : Defn w (a - b)) :
    w.toNat = (a.toNat + (2 ^ 64 - b.toNat)) % 2 ^ 64 := by
  rw [h.eq, BitVec.toNat_sub]; omega

theorem defn_mul {w a b : BitVec 64} (h : Defn w (a * b)) :
    w.toNat = a.toNat * b.toNat % 2 ^ 64 := by rw [h.eq, BitVec.toNat_mul]

theorem defn_mulhu {w a b : BitVec 64} (h : Defn w (mulhu a b)) :
    w.toNat = a.toNat * b.toNat / 2 ^ 64 := by
  rw [h.eq, mulhu, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  exact Nat.div_lt_of_lt_mul (Nat.mul_lt_mul'' a.isLt b.isLt)

theorem defn_carry_left {s c a b : BitVec 64} (hs : Defn s (a + b))
    (hc : Defn c (if s < a then 1#64 else 0#64)) :
    s.toNat + 2 ^ 64 * c.toNat = a.toNat + b.toNat := by
  rw [hc.eq]
  have := defn_add hs
  have ha := a.isLt
  have hb := b.isLt
  split <;> rename_i h <;> simp only [BitVec.lt_def] at h <;> simp <;> omega

theorem defn_carry_right {s c a b : BitVec 64} (hs : Defn s (a + b))
    (hc : Defn c (if s < b then 1#64 else 0#64)) :
    s.toNat + 2 ^ 64 * c.toNat = a.toNat + b.toNat := by
  rw [hc.eq]
  have := defn_add hs
  have ha := a.isLt
  have hb := b.isLt
  split <;> rename_i h <;> simp only [BitVec.lt_def] at h <;> simp <;> omega

theorem defn_mul_mulhu {lo hi a b : BitVec 64} (hl : Defn lo (a * b)) (hh : Defn hi (mulhu a b)) :
    lo.toNat + 2 ^ 64 * hi.toNat = a.toNat * b.toNat := by
  rw [defn_mul hl, defn_mulhu hh]; omega

theorem defn_mul_mulhu' {lo hi a b : BitVec 64} (hl : Defn lo (b * a)) (hh : Defn hi (mulhu a b)) :
    lo.toNat + 2 ^ 64 * hi.toNat = a.toNat * b.toNat := by
  rw [defn_mul hl, defn_mulhu hh, Nat.mul_comm b.toNat]; omega

theorem defn_lt_cases {c s t : BitVec 64} (hc : Defn c (if s < t then 1#64 else 0#64)) :
    c.toNat = 1 ∧ s.toNat < t.toNat ∨ c.toNat = 0 ∧ t.toNat ≤ s.toNat := by
  rw [hc.eq]; split <;> rename_i h <;> simp only [BitVec.lt_def] at h <;> simp <;> omega

theorem defn_add_exact {w a b : BitVec 64} (h : Defn w (a + b)) (hlt : a.toNat + b.toNat < 2 ^ 64) :
    w.toNat = a.toNat + b.toNat := by rw [defn_add h]; omega

theorem toNat_mul_le (a b : BitVec 64) : a.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
  Nat.mul_le_mul (by have := a.isLt; omega) (by have := b.isLt; omega)

/-- The high word of a product is at most 2^64 - 2: a carry added to it does not overflow. -/
theorem defn_mulhu_le {hi a b : BitVec 64} (hh : Defn hi (mulhu a b)) : hi.toNat ≤ 2 ^ 64 - 2 := by
  rw [defn_mulhu hh]
  have ha := a.isLt
  have hb := b.isLt
  have : a.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem Regs.set_apply (x : Regs) (i j : BitVec 5) (v : BitVec 64) :
    x.set i v j = if i = 0 then x j else if j = i then v else x j := by
  unfold Regs.set; split <;> rfl

/-- The product of two 4-word numbers by the sums of the products of the words. -/
theorem mul_words4 (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) :
    (a0 + 2 ^ 64 * (a1 + 2 ^ 64 * (a2 + 2 ^ 64 * a3))) *
      (b0 + 2 ^ 64 * (b1 + 2 ^ 64 * (b2 + 2 ^ 64 * b3))) =
    a0 * b0 + 2 ^ 64 * ((a1 * b0 + a0 * b1) + 2 ^ 64 * ((a2 * b0 + a1 * b1 + a0 * b2) +
      2 ^ 64 * ((a3 * b0 + a2 * b1 + a1 * b2 + a0 * b3) + 2 ^ 64 * ((a3 * b1 + a2 * b2 + a1 * b3) +
      2 ^ 64 * ((a3 * b2 + a2 * b3) + 2 ^ 64 * (a3 * b3)))))) := by
  ring

theorem defn_bit {c : BitVec 64} {p : Prop} [Decidable p] (hc : Defn c (if p then 1#64 else 0#64)) :
    c.toNat ≤ 1 := by
  rw [hc.eq]; split <;> simp

/-- The definitions `Defn w v` of the context. -/
def defns : TacticM (Array (Expr × Expr × Expr)) := do
  let mut r := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if let some (w, v) := t.app2? ``Defn then
      r := r.push (d.toExpr, w, v)
  return r

/-- Substitutes the names that are copies: of a register of the start or of another name. -/
elab "rv_copies" : tactic => withMainContext do
  for (h, w, v) in ← defns do
    if v.isFVar || v.isAppOfArity ``Regs.get 2 then
      let g ← getMainGoal
      g.withContext do
        let eq ← mkAppM ``Defn.eq #[h]
        let (fv, g) ← (← g.assert `hcopy (← mkEq w v) eq).intro1P
        let g ← g.clear h.fvarId!
        let g ← subst g fv
        replaceMainGoal [g]

/-- The operands `(a, b)` of a binary operation `f a b` with `n` arguments. -/
def operands (e : Expr) (f : Name) (n : Nat) : Option (Expr × Expr) :=
  if e.isAppOfArity f n then some (e.getArg! (n - 2), e.getArg! (n - 1)) else none


/-- What is known of a name: its defining fact, its bounds, and the names the fact uses. -/
structure NameInfo where
  fact : Option Expr := none
  bounds : Array Expr := #[]
  deps : Array Expr := #[]

/-- Proves `target` from the proofs `facts` by `omega`, in the context of the current goal without
its hypotheses: `omega` sees these facts only. -/
def proveWith (tac : TSyntax `tactic) (facts : Array Expr) (target : Expr) : TacticM Expr := do
  let mut lctx ← getLCtx
  for d in lctx do
    if !d.isImplementationDetail && (← isProp d.type) then lctx := lctx.erase d.fvarId
  let types ← facts.mapM fun f => inferType f
  let ty := types.foldr (fun t acc => mkForall `h .default t acc) target
  let mv ← mkFreshExprMVarAt lctx (← getLocalInstances) ty
  let gs ← Elab.Tactic.run mv.mvarId! (evalTactic (← `(tactic| (intros; $tac))))
  unless gs.isEmpty do throwError "proveWith: goals left"
  return mkAppN mv facts

def omegaWith (facts : Array Expr) (target : Expr) : TacticM Expr := do
  proveWith (← `(tactic| omega)) facts target

/-- Proves the goal, an equation of numbers of names, from the definitions of the names: the
sums with a carry, the products by their words, the sums that cannot overflow (by `omega` from the
facts that the operands depend on), the others modulo 2^64. -/
elab "rv_arith" : tactic => withMainContext do
  let ds ← defns
  let proofOf : Std.HashMap Expr Expr := ds.foldl (fun m (h, w, _) => m.insert w h) {}
  let valOf : Std.HashMap Expr Expr := ds.foldl (fun m (_, w, v) => m.insert w v) {}
  let mut info : Std.HashMap Expr NameInfo := {}
  let get := fun (i : Std.HashMap Expr NameInfo) (w : Expr) => (i.get? w).getD {}
  let isLt := fun (w : Expr) => mkAppM ``BitVec.isLt #[w]
  -- The pairs: a sum and its carry, the words of a product.
  for (h, w, v) in ds do
    if v.isAppOfArity ``ite 5 then
      let mut ni := get info w
      ni := { ni with bounds := ni.bounds.push (← mkAppM ``defn_bit #[h]) }
      if let some (s, t) := operands (v.getArg! 1) ``LT.lt 4 then
        if let (some hs, some sv) := (proofOf.get? s, valOf.get? s) then
          if let some (a, b) := operands sv ``HAdd.hAdd 6 then
            let lem := if t == a then some ``defn_carry_left else if t == b then
              some ``defn_carry_right else none
            if let some lem := lem then
              info := info.insert s { get info s with
                fact := some (← mkAppM lem #[hs, h]), deps := #[a, b, w] }
              ni := { ni with deps := ni.deps.push s }
      info := info.insert w ni
    if let some (a, b) := operands v ``mulhu 2 then
      let mut ni := get info w
      ni := { ni with bounds := ni.bounds ++ #[← mkAppM ``defn_mulhu_le #[h],
        ← mkAppM ``toNat_mul_le #[a, b]] }
      for (hl, wl, lv) in ds do
        if let some (p, q) := operands lv ``HMul.hMul 6 then
          let lem := if p == a && q == b then some ``defn_mul_mulhu else
            if p == b && q == a then some ``defn_mul_mulhu' else none
          if let some lem := lem then
            info := info.insert wl { get info wl with
              fact := some (← mkAppM lem #[hl, h]), deps := #[a, b, w] }
            ni := { ni with deps := ni.deps.push wl }
      info := info.insert w ni
  -- The facts that a name depends on, to the depth `d`.
  let rec cone (i : Std.HashMap Expr NameInfo) (w : Expr) : Nat → MetaM (Array Expr)
    | 0 => return (get i w).bounds.push (← isLt w)
    | d + 1 => do
      let ni := get i w
      let mut r := ni.bounds.push (← isLt w)
      if let some f := ni.fact then r := r.push f
      for x in ni.deps do r := r ++ (← cone i x d)
      return r
  let toNat := fun (w : Expr) => mkAppM ``BitVec.toNat #[w]
  -- The summands of a sum, through the sums of at most `d` levels.
  let rec leaves (w : Expr) : Nat → Array Expr
    | 0 => #[w]
    | d + 1 => match (valOf.get? w).bind (operands · ``HAdd.hAdd 6) with
      | some (a, b) => leaves a d ++ leaves b d
      | none => #[w]
  let mut carried : Std.HashSet Expr := {}
  for (_, w, _) in ds do
    if (get info w).fact.isSome then carried := carried.insert w
  for _round in [0, 1] do
    -- Sums: exact if they cannot overflow, by the facts of their operands.
    for (h, w, v) in ds do
      if carried.contains w then continue
      if let some (a, b) := operands v ``HAdd.hAdd 6 then
        let target ← mkAppM ``LT.lt #[← mkAppM ``HAdd.hAdd #[← toNat a, ← toNat b],
          mkNatLit (2 ^ 64)]
        let fs := (← cone info a 4) ++ (← cone info b 4)
        let f ← try
            let hlt ← omegaWith fs target
            carried := carried.insert w
            mkAppM ``defn_add_exact #[h, hlt]
          catch _ => mkAppM ``defn_add #[h]
        info := info.insert w { get info w with fact := some f, deps := #[a, b] }
      else if (operands v ``HSub.hSub 6).isSome then
        info := info.insert w { get info w with fact := some (← mkAppM ``defn_sub #[h]) }
      else if (operands v ``HMul.hMul 6).isSome then
        info := info.insert w { get info w with fact := some (← mkAppM ``defn_mul #[h]) }
    -- The carries of sums of more than two summands: `s < t` for a summand `t` of `s`.
    for (h, c, v) in ds do
      if !v.isAppOfArity ``ite 5 then continue
      let some (s, t) := operands (v.getArg! 1) ``LT.lt 4 | continue
      if carried.contains s then continue
      let ls := leaves s 3
      unless ls.contains t do continue
      let rest := ls.erase t
      let restSum ← rest.foldlM (fun acc x => do mkAppM ``HAdd.hAdd #[acc, ← toNat x])
        (← toNat t)
      let lhs ← mkAppM ``HAdd.hAdd #[← toNat s,
        ← mkAppM ``HMul.hMul #[mkNatLit (2 ^ 64), ← toNat c]]
      let target ← mkEq lhs restSum
      let mut fs := (← cone info s 4).push (← mkAppM ``defn_lt_cases #[h])
      for x in ls do fs := fs ++ (← cone info x 2)
      try
        let f ← omegaWith fs target
        info := info.insert s { get info s with fact := some f, deps := ls.push c }
        info := info.insert c { get info c with deps := (get info c).deps.push s }
        carried := carried.insert s
      catch _ => pure ()
  -- The exact facts: equations without remainders.
  let mut facts : Array Expr := #[]
  -- The products of the words in both orders: `omega` takes a product for an atom.
  for (_, _, v) in ds do
    if let some (a, b) := operands v ``mulhu 2 then
      facts := facts.push (← mkAppM ``Nat.mul_comm #[← toNat a, ← toNat b])
  for (_, w, _) in ds do
    if let some f := (get info w).fact then
      if ((← inferType f).find? (·.isAppOfArity ``HMod.hMod 6)).isNone then
        facts := facts.push f
  -- The loads of the start memory by their names in the goal.
  for (h, _, v) in ds do
    if v.isAppOfArity ``memWord 2 then
      let eq ← mkAppM ``Eq.symm #[← mkAppM ``Defn.eq #[h]]
      let g ← getMainGoal
      try
        let r ← g.rewrite (← g.getType) eq
        let g' ← g.replaceTargetEq r.eNew r.eqProof
        replaceMainGoal (g' :: r.mvarIds)
      catch _ => pure ()
  let g ← getMainGoal
  g.withContext do
    let p ← proveWith (← `(tactic| linarith)) facts (← g.getType)
    g.assign p
    replaceMainGoal []

end IntxRV
