import IntxRV.Tactic
import IntxRV.ApiModel
/-!
# The tactic `rv_runm`

`rv_runm d` proves `RunsM code bufs pre post` from `d : Decodes code prog`, as `rv_run` proves
`Runs`: it evaluates `arunM` on the instructions `prog` with symbolic registers and memory,
splits the paths at the branches, reads the words stored by the function back from the memory,
and proves `post` by the lemmas of the model, `ac_nf` and `bv_omega`.
-/

open Sail LeanRV64D LeanRV64D.Functions LeanRV64D.Defs

namespace IntxRV
open Intx Intx.Model

theorem arunM_ite {A : List (BitVec 64)} {prog : List instruction} {base ret : BitVec 64} {n : Nat}
    (c : Prop) [Decidable c] (a b : BitVec 64) (x : Regs) (m : Mem) :
    arunM A prog base ret n (if c then a else b) x m =
      if c then arunM A prog base ret n a x m else arunM A prog base ret n b x m := by
  split <;> rfl

theorem exists2_some_ite {α β : Type} (c : Prop) [Decidable c] (a b : α × β)
    (P : α → β → Prop) :
    (∃ x y, (if c then some a else some b) = some (x, y) ∧ P x y) ↔
      (if c then P a.1 a.2 else P b.1 b.2) := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  split <;> simp

/-- A run that ends on one of two paths: the end state as one value. -/
theorem ite_some_some {α : Type} (c : Prop) [Decidable c] (a b : α) :
    (if c then some a else some b) = some (if c then a else b) := by
  split <;> rfl

theorem itypeVal_sltiu (imm : BitVec 12) (a : BitVec 64) :
    itypeVal .SLTIU imm a = if a < imm.signExtend 64 then 1#64 else 0#64 := by
  simp [itypeVal, zopz0zI_u_eq, zero_extend_bool_to_bit, sign_extend, Sail.BitVec.signExtend]

theorem lt_one_iff (a : BitVec 64) : a < 1#64 ↔ a = 0#64 := by
  constructor <;> intro h <;> bv_omega

theorem ofBitVec_eq_iff (a : BitVec 64) (b : UInt64) : UInt64.ofBitVec a = b ↔ a = b.toBitVec :=
  ⟨fun h => h ▸ rfl, fun h => h ▸ rfl⟩

/-- Proves `RunsM code bufs pre post` from `d : Decodes code prog`; `c` and `p` are the
definitions of `code` and `prog`, `ls` the definitions of the model and of `pre` to unfold. -/
macro "rv_runm" d:term " with " c:ident p:ident " using " "[" ls:Lean.Parser.Tactic.simpLemma,* "]"
    " finish " "[" fs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  apply runsM_of_arunM $d
  intro base ret hb hr hl x m hx1 hpre
  have hne := ne_ret hl
  have hne0 := ne_ret_zero hl (by simp [$c:ident])
  have hupd := update_aligned hr
  try simp only [$ls,*] at hpre
  refine ⟨List.length $p + 1, ?_⟩
  -- Run the instructions: one path for each combination of the branch conditions.
  simp (config := { decide := true }) [arunM, execM, fetch, exec, Regs.get, Regs.set, hne, hne0,
    hupd, hx1, BitVec.add_assoc, ↓arunM_ite, sign_extend, Sail.BitVec.signExtend, $c:ident,
    $p:ident, exists2_some_ite, btypeTaken, zopz0zI_u_eq, zopz0zI_s_zero, bufWords, wordList, words,
    -BitVec.toNat_add, $ls,*]
  -- The paths that the conditions of the branches did not decide.
  all_goals try split_ifs
  all_goals try simp (config := { decide := true }) only [ite_some_some, Option.some.injEq,
    Prod.mk.injEq, Prod.ext_iff, existsAndEq, apply_ite Prod.fst, apply_ite Prod.snd, ite_apply,
    exists_eq_left', exists_eq_right', exists_eq_left, exists_eq_right, exists_and_left,
    exists_and_right, exists_eq_right_right, exists_eq_right_right', and_true, true_and,
    ↓reduceIte]
  -- The values of the instructions and the words stored by the function.
  all_goals try simp (config := { decide := true }) only [rtypeVal_add, rtypeVal_sub, rtypeVal_and,
    rtypeVal_or, rtypeVal_xor, rtypeVal_sltu, itypeVal_addi, itypeVal_xori, itypeVal_andi,
    itypeVal_ori, itypeVal_sltiu, shiftiopVal_srli, BitVec.reduceSignExtend, BitVec.add_zero,
    calleeSaved,
        List.mem_cons,
    List.not_mem_nil, forall_eq_or_imp, forall_eq, or_false, ↓reduceIte, and_true, true_and]
  all_goals try simp (disch := bv_omega) only [memWord_memStore_self, memWord_memStore_of_ne,
    unchangedExcept_memStore, unchangedExcept_refl, and_true, true_and]
  -- The model as BitVec operations.
  all_goals try simp only [ofBitVec_eq_iff, addc, subc, UInt64.toBitVec_add,
    UInt64.toBitVec_sub, apply_ite UInt64.toBitVec, UInt64.lt_iff_toBitVec_lt,
    UInt64.toBitVec_ofBitVec, UInt64.toBitVec_or, UInt64.toBitVec_and, UInt64.toBitVec_xor,
    List.zipWith_cons_cons, List.zipWith_nil_left, Bool.or_eq_true, decide_eq_true_eq,
    UInt64.toBitVec_one,
    UInt64.toBitVec_zero, ite_or_ite, ite_and_ite, ite_xor_one, ite_and_not_ite,
    not_ite_and_ite, zero_lt_iff, Bool.false_eq_true, ite_false, BitVec.add_zero,
    BitVec.sub_zero, true_and, and_true, BitVec.lt_irrefl, or_false, List.cons.injEq,
    lt_one_iff, BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff, and_self]
  all_goals try ac_nf
  all_goals (try simp only [sign_xor, BitVec.reduceToNat, ite_self, $fs,*] at *) <;>
    (try split_ifs) <;> (try simp only [and_self, true_and, and_true] at *) <;>
    (try simp only [$c:ident, List.length_cons, List.length_nil] at *) <;>
    (repeat' (first | apply And.intro | apply Iff.intro)) <;> (try intro) <;> (try trivial) <;>
    bv_omega))

/-- `rv_runm` with no definitions to unfold at the end. -/
macro "rv_runm" d:term " with " c:ident p:ident " using "
    "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| rv_runm $d with $c $p using [$ls,*] finish [])

end IntxRV
