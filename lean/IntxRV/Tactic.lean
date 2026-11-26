import IntxRV.Values
import IntxRV.Run
import Mathlib.Tactic.Ring
import Mathlib.Data.BitVec
/-!
# The tactic `rv_run`

`rv_run d` proves `Runs code pre post` from `d : Decodes code prog`: it evaluates `arun` on the
instructions `prog` with symbolic registers, splits the paths at the branches, and proves `post`
at the return by the value lemmas and `bv_omega` (so the kernel checks the whole proof).
-/

open Sail LeanRV64D LeanRV64D.Functions LeanRV64D.Defs

namespace IntxRV

theorem exists_some_ite {α : Type} (c : Prop) [Decidable c] (a b : α) (P : α → Prop) :
    (∃ y, (if c then some a else some b) = some y ∧ P y) ↔ (if c then P a else P b) := by
  split <;> simp

theorem mask_all (x : BitVec 64) : 18446744073709551615#64 &&& x = x := by
  rw [show 18446744073709551615#64 = BitVec.allOnes 64 from rfl, BitVec.allOnes_and]

/-- The mask of the first correction of `udivrem_2by1_v`. -/
theorem uint64_and_neg_ite (d : UInt64) (p : Prop) [Decidable p] :
    (d &&& (0 - if p then 1 else 0)) = if p then d else 0 := by
  split <;> apply UInt64.toBitVec_inj.mp <;> simp

theorem U128.add_eq (a b : Intx.Model.U128) : a + b = Intx.Model.U128.add a b := rfl

/-- Proves `Runs code pre post` from `d : Decodes code prog`; `c` and `p` are the definitions of
`code` and `prog`, `ls` the definitions of the model to unfold. -/
macro "rv_run" d:term " with " c:ident p:ident " using " "[" ls:Lean.Parser.Tactic.simpLemma,* "]" :
    tactic => `(tactic| (
  apply runs_of_arun $d
  intro base ret hb hr hl x hx1 hpre
  have hne := ne_ret hl
  have hne0 := ne_ret_zero hl (by simp [$c:ident])
  have hupd := update_aligned hr
  refine ⟨List.length $p + 1, ?_⟩
  -- Run the instructions: one path for each combination of the branch conditions.
  simp (config := { decide := true }) [arun, fetch, exec, Regs.get, Regs.set, hne, hne0, hupd,
    hx1, BitVec.add_assoc, ↓arun_ite, sign_extend, Sail.BitVec.signExtend, $c:ident, $p:ident,
    exists_some_ite, btypeTaken, zopz0zI_u_eq]
  -- The values of the instructions and of the model as BitVec operations.
  simp (config := { decide := true }) only [rtypeVal_add, rtypeVal_sub, rtypeVal_and,
    rtypeVal_or, rtypeVal_xor, rtypeVal_sltu, itypeVal_addi, itypeVal_xori, itypeVal_andi,
    itypeVal_ori, mulVal_lo, mulVal_hu, umul_lo_toBitVec, umul_hi_toBitVec,
    UInt64.toBitVec_ofBitVec, calleeSaved, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, forall_eq, or_false, ↓reduceIte, and_true, true_and, $ls,*]
  try simp only [BitVec.mul_comm, mulhu_comm, BitVec.reduceSignExtend, BitVec.add_zero, and_self]
  try simp only [uint64_and_neg_ite, Intx.Model.U128.getElem_zero, Intx.Model.U128.getElem_one,
    U128.add_eq,
    Intx.Model.U128.add, Intx.Model.addc, Id.run, pure, UInt64.toBitVec_add, UInt64.toBitVec_sub,
    UInt64.toBitVec_mul, UInt64.toBitVec_ofBitVec, UInt64.lt_iff_toBitVec_lt,
    UInt64.le_iff_toBitVec_le, gt_iff_lt, ge_iff_le, apply_ite UInt64.toBitVec,
    UInt64.toBitVec_one, UInt64.toBitVec_zero, umul_lo_toBitVec, umul_hi_toBitVec,
    decide_eq_true_eq, Bool.or_eq_true, Bool.false_or, Bool.or_false]
  try simp only [apply_ite Prod.fst, apply_ite Prod.snd, UInt64.toBitVec_add,
    UInt64.toBitVec_sub, UInt64.toBitVec_mul, apply_ite UInt64.toBitVec, UInt64.toBitVec_one,
    UInt64.toBitVec_zero, umul_hi_toBitVec, UInt64.toBitVec_ofBitVec, Bool.false_eq_true,
    ite_false, BitVec.add_zero]
  -- One goal for each combination of the conditions, decided by the numbers. bv_omega and ring
  -- are kernel-checked (bv_decide is not: it checks its SAT proofs by native code).
  all_goals (try simp only [hpre]) <;> (try split_ifs) <;> (try simp only [UInt64.toBitVec_add,
      UInt64.toBitVec_sub,
    UInt64.toBitVec_mul, UInt64.toBitVec_one, UInt64.toBitVec_zero, umul_lo_toBitVec,
    umul_hi_toBitVec, UInt64.toBitVec_ofBitVec, BitVec.reduceSub, BitVec.reduceAdd, mask_all,
    BitVec.zero_and, BitVec.and_zero, BitVec.sub_zero, BitVec.add_zero, BitVec.zero_add,
    mulhu_comm, and_self, true_and, and_true, ite_true, ite_false,
    Bool.false_eq_true] at *) <;> (try ac_nf at *) <;>
    (try simp only [BitVec.reduceAdd, ← BitVec.add_assoc] at *) <;> (try ac_nf at *) <;>
    first | bv_omega | (simp only [← BitVec.natCast_eq_ofNat]; push_cast; ring)))

end IntxRV
