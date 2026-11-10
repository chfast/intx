import IntxRV.Step
import IntxRV.Values
import IntxRV.TacticM
/-!
# The tactic `rv_exec`

`rv_exec` proves `Reach A prog base (pcAt base k) x m tgt Q` by running the instructions one by
one (`Reach.step`) until the address `tgt`, splitting the paths at the branches, and leaves `Q`
of the registers and the memory at `tgt`. A value that an instruction computes is the new name
`w` with its definition `Defn w v` in the context, with `v` in terms of the earlier names: the
work of a step does not grow with the length of the run.
-/

open Sail LeanRV64D LeanRV64D.Functions LeanRV64D.Defs

namespace IntxRV

theorem Regs.get_set (x : Regs) (i j : BitVec 5) (v : BitVec 64) :
    (x.set i v).get j = if j = 0 then 0 else if j = i then v else x.get j := by
  unfold Regs.set Regs.get
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp_all

theorem Regs.get_zero (x : Regs) : x.get 0 = 0 := rfl

/-- `seqz`: `sltiu rd, rs, 1`. -/
theorem itypeVal_seqz (a : BitVec 64) :
    itypeVal .SLTIU 1#12 a = if a = 0#64 then 1#64 else 0#64 := by
  rw [itypeVal_sltiu]
  by_cases h : a = 0#64 <;> simp [h]

/-- A register of the start: the specifications read `x i`, the runs `x.get i`. -/
theorem Regs.eq_get (x : Regs) {i : BitVec 5} (h : i ≠ 0) : x i = x.get i := by
  unfold Regs.get; rw [if_neg h]

theorem Reach.refl_at {A : List (BitVec 64)} {prog : List instruction} {base : BitVec 64}
    {k : Nat} {x : Regs} {m : Mem} {Q : Regs → Mem → Prop} (h : Q x m) :
    Reach A prog base (pcAt base k) x m (pcAt base k) Q :=
  Reach.refl h

/-- The simplification of the values of a step. -/
macro "rv_val" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic| (
  simp (config := { decide := true }) (disch := first | bv_omega | fail) only [Regs.get_set,
    Regs.get_zero, ↓reduceIte, memWord_memStore_of_ne, memHalf_memStore_of_ne,
    rtypeVal_add, rtypeVal_sub, rtypeVal_and, rtypeVal_or, rtypeVal_xor, rtypeVal_sltu,
    rtypeVal_sll, rtypeVal_srl, rtypewVal_subw,
    itypeVal_addi, itypeVal_xori, itypeVal_andi, itypeVal_ori, itypeVal_seqz, shiftiopVal_srli,
    shiftiopVal_slli, utypeVal_lui, utypeVal_auipc, BitVec.reduceAppend, BitVec.reduceToNat,
    BitVec.reduceHShiftLeft, BitVec.reduceHShiftRight, BitVec.reduceShiftLeft,
    BitVec.reduceUShiftRight,
    mulVal_lo, mulVal_hu, BitVec.reduceSignExtend, BitVec.add_zero, BitVec.add_assoc,
    BitVec.reduceAdd, memWord_memStore_self, btypeTaken, beq_iff_eq, bne_iff_ne, ne_eq,
    Bool.not_eq_true, decide_eq_true_eq, decide_eq_false_iff_not] $(loc)?))

theorem Reach.start {A : List (BitVec 64)} {prog : List instruction} {base tgt : BitVec 64}
    {x : Regs} {m : Mem} {Q : Regs → Mem → Prop} (h : Reach A prog base (pcAt base 0) x m tgt Q) :
    Reach A prog base base x m tgt Q := by
  rwa [pcAt_zero] at h

open Lean Meta Elab Tactic in
/-- Substitutes the name of the definition `h` if its value is a numeral or a numeral added to a
value (an address): the addresses of the loads and stores must show their base. -/
elab "rv_const " h:ident : tactic => withMainContext do
  let d ← getLocalDeclFromUserName h.getId
  let t ← instantiateMVars d.type
  let isNum := fun (e : Expr) => e.isAppOfArity ``BitVec.ofNat 2 && (e.getArg! 1).nat?.isSome
  if let some (_, v) := t.app2? ``Defn then
    let addNum := v.isAppOfArity ``HAdd.hAdd 6 && (isNum (v.getArg! 4) || isNum (v.getArg! 5))
    if isNum v || addNum then
      if addNum && isNum (v.getArg! 4) then  -- The numeral to the right, as in the addresses.
        evalTactic (← `(tactic| rw [Defn, BitVec.add_comm] at $h:ident))
      else
        evalTactic (← `(tactic| unfold Defn at $h:ident))
      evalTactic (← `(tactic| subst $h:ident))

/-- The membership of an address in the list of the words of the buffers. -/
macro "rv_mem" : tactic => `(tactic| (
  simp (config := { decide := true }) only [Regs.get_set, Regs.get_zero, ↓reduceIte,
    List.mem_append, List.mem_cons, bufWords, List.not_mem_nil, BitVec.add_assoc,
    BitVec.sub_eq_add_neg, BitVec.reduceNeg, BitVec.reduceAdd, BitVec.add_right_inj,
    BitVec.add_zero, BitVec.reduceSignExtend, or_false, false_or, or_true, true_or,
    BitVec.add_left_inj]
  done))

/-- Runs one instruction. -/
macro "rv_step" : tactic => `(tactic| (
  refine Reach.step ?hk rfl ?_
  case hk => decide
  simp only [StepGoal, Nat.reduceAdd, true_and, jumpIdx, BitVec.reduceToInt, Nat.reduceMul,
    Int.reduceAdd, Int.reduceToNat, Nat.reduceDiv, Nat.cast_ofNat]
  -- The side conditions are separate goals, so a failed one fails the step.
  first
  | (apply And.intro; (focus decide); apply And.intro <;> intro hb <;> rv_val at hb)
  | (apply And.intro <;> intro hb <;> rv_val at hb)
  | (apply And.intro; (focus rv_mem); intro w hw; rv_val at hw; rv_const hw)
  | (apply And.intro; (focus rv_mem); show Reach _ _ _ _ _ _ _ _)
  | (apply And.intro; (focus decide); show Reach _ _ _ _ _ _ _ _)
  | (intro w hw; rv_val at hw; rv_const hw)
  | (show Reach _ _ _ _ _ _ _ _; rv_val)))

/-- Runs the instructions until the address `tgt`. -/
macro "rv_exec" : tactic => `(tactic| (
  repeat' (first | refine Reach.refl_at ?_ | rv_step)))

end IntxRV
