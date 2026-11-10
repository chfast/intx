import IntxRV.Machine
/-!
# The instruction semantics

`exec i pc x` is the effect of the instruction `i` of the Sail model at the program counter `pc` on
the registers `x`: the next program counter and the registers. It covers the instructions of the
verified functions and is `none` for the others. The theorems `exec_*` show that the Sail model
executes these instructions this way (`execute` of the Sail model, with `nextPC` set to `pc + 4`
as the step of the Sail model does before it).
-/

open Sail Sail.ConcurrencyInterfaceV1 PreSail
open LeanRV64D LeanRV64D.Functions LeanRV64D.Defs

namespace IntxRV

/-- The result of a register-register operation, as in `execute_RTYPE`. -/
def rtypeVal (op : rop) (a b : BitVec 64) : BitVec 64 :=
  match op with
  | .ADD => a + b
  | .SLT => zero_extend (m := 64) (bool_to_bit (zopz0zI_s a b))
  | .SLTU => zero_extend (m := 64) (bool_to_bit (zopz0zI_u a b))
  | .AND => a &&& b
  | .OR => a ||| b
  | .XOR => a ^^^ b
  | .SLL => shift_bits_left a (Sail.BitVec.extractLsb b (↑Functions.log2_xlen -i 1) 0)
  | .SRL => shift_bits_right a (Sail.BitVec.extractLsb b (↑Functions.log2_xlen -i 1) 0)
  | .SUB => a - b
  | .SRA => shift_bits_right_arith a (Sail.BitVec.extractLsb b (↑Functions.log2_xlen -i 1) 0)

/-- The result of a register-immediate operation, as in `execute_ITYPE`. -/
def itypeVal (op : iop) (imm : BitVec 12) (a : BitVec 64) : BitVec 64 :=
  let immext : BitVec 64 := sign_extend (m := 64) imm
  match op with
  | .ADDI => a + immext
  | .SLTI => zero_extend (m := 64) (bool_to_bit (zopz0zI_s a immext))
  | .SLTIU => zero_extend (m := 64) (bool_to_bit (zopz0zI_u a immext))
  | .ANDI => a &&& immext
  | .ORI => a ||| immext
  | .XORI => a ^^^ immext

/-- The result of a shift by an immediate, as in `execute_SHIFTIOP`. -/
def shiftiopVal (op : sop) (shamt : BitVec 6) (a : BitVec 64) : BitVec 64 :=
  let shamt := Sail.BitVec.extractLsb shamt (↑Functions.log2_xlen -i 1) 0
  match op with
  | .SLLI => shift_bits_left a shamt
  | .SRLI => shift_bits_right a shamt
  | .SRAI => shift_bits_right_arith a shamt

/-- The result of a multiplication, as in `execute_MUL`. -/
def mulVal (op : mul_op) (a b : BitVec 64) : BitVec 64 :=
  mult_to_bits_half (l := 64) op.signed_rs1 op.signed_rs2 a b op.result_part

/-- Whether a branch is taken, as in `execute_BTYPE`. -/
def btypeTaken (op : bop) (a b : BitVec 64) : Bool :=
  match op with
  | .BEQ => a == b
  | .BNE => a != b
  | .BLT => zopz0zI_s a b
  | .BGE => zopz0zKzJ_s a b
  | .BLTU => zopz0zI_u a b
  | .BGEU => zopz0zKzJ_u a b

/-- The next program counter and the registers after the instruction `i` at `pc`. A jump `JALR`
is supported with the source register x1, x5 or x7: these leave no landing pad expected
(Zicfilp). -/
def exec (i : instruction) (pc : BitVec 64) (x : Regs) : Option (BitVec 64 × Regs) :=
  match i with
  | .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, op) =>
    some (pc + 4, x.set rd (rtypeVal op (x.get rs1) (x.get rs2)))
  | .ITYPE (imm, .Regidx rs1, .Regidx rd, op) =>
    some (pc + 4, x.set rd (itypeVal op imm (x.get rs1)))
  | .SHIFTIOP (shamt, .Regidx rs1, .Regidx rd, op) =>
    some (pc + 4, x.set rd (shiftiopVal op shamt (x.get rs1)))
  | .MUL (.Regidx rs2, .Regidx rs1, .Regidx rd, op) =>
    some (pc + 4, x.set rd (mulVal op (x.get rs1) (x.get rs2)))
  | .BTYPE (imm, .Regidx rs2, .Regidx rs1, op) =>
    some (if btypeTaken op (x.get rs1) (x.get rs2) then pc + sign_extend (m := 64) imm else pc +
        4, x)
  | .JALR (imm, .Regidx rs1, .Regidx rd) =>
    if rs1 = 1 ∨ rs1 = 5 ∨ rs1 = 7 then
      some (BitVec.update (x.get rs1 + sign_extend (m := 64) imm) 0 0#1, x.set rd (pc + 4))
    else none
  | _ => none

/-! ## The Sail model executes the instructions as `exec` -/

theorem Inv.set_npc {S s : SailState} {pc npc : BitVec 64} {x : Regs} (h : Inv S s pc npc x)
    (t : BitVec 64) : Inv S { s with regs := s.regs.insert .nextPC t } pc t x := by
  inv_insert h

theorem Inv.set_pc {S s : SailState} {pc npc : BitVec 64} {x : Regs} (h : Inv S s pc npc x)
    (t : BitVec 64) : Inv S { s with regs := s.regs.insert .PC t } t npc x := by
  inv_insert h

/-- Writing 0 to `elp`, the value of the environment. -/
theorem Inv.set_elp {S s : SailState} {val : (r : Register) → RegisterType r} {pc npc : BitVec 64}
    {x : Regs} (e : Env S val) (h : Inv S s pc npc x) :
    Inv S { s with regs := s.regs.insert .elp 0#1 } pc npc x := by
  constructor
  · exact h.rest
  · intro r hr
    simp only [Std.ExtDHashMap.get?_insert]
    split
    · rename_i he; rw [beq_iff_eq] at he; subst he; rw [e.get, e.elp]; rfl
    · exact h.other r hr
  all_goals simp [Std.ExtDHashMap.get?_insert, h.pc, h.npc, h.x1, h.x2, h.x3, h.x4, h.x5, h.x6,
      h.x7, h.x8, h.x9, h.x10, h.x11, h.x12, h.x13, h.x14, h.x15, h.x16, h.x17, h.x18, h.x19, h.x20,
      h.x21, h.x22, h.x23, h.x24, h.x25, h.x26, h.x27, h.x28, h.x29, h.x30, h.x31]

theorem get_xLPE_env {S s : SailState} {val : (r : Register) → RegisterType r} {pc npc : BitVec 64}
    {x : Regs} (e : Env S val) (h : Inv S s pc npc x) :
    ∃ b, get_xLPE (val .cur_privilege) s = .ok b s := by
  rcases e.priv with hp | hp | hp <;> rw [hp] <;>
    simp (config := { decide := true }) [get_xLPE, readReg_env e h, isRunReg, LeanRV64D.readReg,
      currentlyEnabled, hartSupports, read_senvcfg, bind, EStateM.bind, pure, EStateM.pure,
      ite_apply'] <;> split <;> simp

theorem jump_to_inv {S s : SailState} {val : (r : Register) → RegisterType r} {pc npc : BitVec 64}
    {x : Regs} (e : Env S val) (h : Inv S s pc npc x) (t : BitVec 64)
    (h0 : t.getLsbD 0 = false) (h1 : t.getLsbD 1 = false) :
    ∃ s', jump_to t s = .ok RETIRE_SUCCESS s' ∧ Inv S s' pc t x := by
  have a0 : Sail.BitVec.access t 0 = 0#1 := by
    simp [Sail.BitVec.access, ← BitVec.getLsbD_eq_getElem, h0]
  have a1 : bit_to_bool (Sail.BitVec.access t 1) = false := by
    simp [Sail.BitVec.access, ← BitVec.getLsbD_eq_getElem, h1, bit_to_bool, bool_bit_backwards]
  refine ⟨_, ?_, h.set_npc t⟩
  simp (config := { decide := true }) [jump_to, ext_control_check_pc, a0, a1, currentlyEnabled,
    hartSupports, readReg_env e h, isRunReg, LeanRV64D.readReg, set_next_pc, writeReg_ok,
    LeanRV64D.writeReg, LeanRV64D.assert, PreSail.assert, bind, EStateM.bind, pure, EStateM.pure,
    SailME.run, PreSailME.run, ExceptT.run, liftM, monadLift, MonadLift.monadLift, ExceptT.lift,
    ExceptT.bind, ExceptT.mk, ExceptT.bindCont, ExceptT.pure, Functor.map, EStateM.map]

theorem exec_rtype {S s : SailState} {pc npc : BitVec 64} {x : Regs} (h : Inv S s pc npc x)
    (rs2 rs1 rd : BitVec 5) (op : rop) :
    ∃ s', execute (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, op)) s = .ok RETIRE_SUCCESS s' ∧
      Inv S s' pc npc (x.set rd (rtypeVal op (x.get rs1) (x.get rs2))) := by
  obtain ⟨s', hs, hi⟩ := wX_bits_inv h rd (rtypeVal op (x.get rs1) (x.get rs2))
  refine ⟨s', ?_, hi⟩
  show execute_RTYPE _ _ _ _ s = _
  cases op <;> simp [execute_RTYPE, rtypeVal, rX_bits_inv h, hs, bind, EStateM.bind, pure,
    EStateM.pure] at hs ⊢ <;> rfl

theorem exec_itype {S s : SailState} {pc npc : BitVec 64} {x : Regs} (h : Inv S s pc npc x)
    (imm : BitVec 12) (rs1 rd : BitVec 5) (op : iop) :
    ∃ s', execute (.ITYPE (imm, .Regidx rs1, .Regidx rd, op)) s = .ok RETIRE_SUCCESS s' ∧
      Inv S s' pc npc (x.set rd (itypeVal op imm (x.get rs1))) := by
  obtain ⟨s', hs, hi⟩ := wX_bits_inv h rd (itypeVal op imm (x.get rs1))
  refine ⟨s', ?_, hi⟩
  show execute_ITYPE _ _ _ _ s = _
  cases op <;> simp [execute_ITYPE, itypeVal, rX_bits_inv h, hs, bind, EStateM.bind, pure,
    EStateM.pure] at hs ⊢ <;> rfl

theorem exec_shiftiop {S s : SailState} {pc npc : BitVec 64} {x : Regs} (h : Inv S s pc npc x)
    (shamt : BitVec 6) (rs1 rd : BitVec 5) (op : sop) :
    ∃ s', execute (.SHIFTIOP (shamt, .Regidx rs1, .Regidx rd, op)) s = .ok RETIRE_SUCCESS s' ∧
      Inv S s' pc npc (x.set rd (shiftiopVal op shamt (x.get rs1))) := by
  obtain ⟨s', hs, hi⟩ := wX_bits_inv h rd (shiftiopVal op shamt (x.get rs1))
  refine ⟨s', ?_, hi⟩
  show execute_SHIFTIOP _ _ _ _ s = _
  cases op <;> simp [execute_SHIFTIOP, shiftiopVal, rX_bits_inv h, hs, bind, EStateM.bind, pure,
    EStateM.pure] at hs ⊢ <;> rfl

theorem exec_mul {S s : SailState} {pc npc : BitVec 64} {x : Regs} (h : Inv S s pc npc x)
    (rs2 rs1 rd : BitVec 5) (op : mul_op) :
    ∃ s', execute (.MUL (.Regidx rs2, .Regidx rs1, .Regidx rd, op)) s = .ok RETIRE_SUCCESS s' ∧
      Inv S s' pc npc (x.set rd (mulVal op (x.get rs1) (x.get rs2))) := by
  obtain ⟨s', hs, hi⟩ := wX_bits_inv h rd (mulVal op (x.get rs1) (x.get rs2))
  refine ⟨s', ?_, hi⟩
  show execute_MUL _ _ _ _ s = _
  simp only [mulVal] at hs
  simp [execute_MUL, rX_bits_inv h, bind, EStateM.bind, pure, EStateM.pure]
  erw [hs]

theorem exec_btype {S s : SailState} {val : (r : Register) → RegisterType r} {pc npc : BitVec 64}
    {x : Regs} (e : Env S val) (h : Inv S s pc npc x) (imm : BitVec 13) (rs2 rs1 : BitVec 5)
    (op : bop) (ha : btypeTaken op (x.get rs1) (x.get rs2) = true →
      (pc + sign_extend (m := 64) imm).getLsbD 0 = false ∧
        (pc + sign_extend (m := 64) imm).getLsbD 1 = false) :
    ∃ s', execute (.BTYPE (imm, .Regidx rs2, .Regidx rs1, op)) s = .ok RETIRE_SUCCESS s' ∧
      Inv S s' pc (if btypeTaken op (x.get rs1) (x.get rs2) then pc + sign_extend (m := 64) imm
        else npc) x := by
  show ∃ s', execute_BTYPE _ _ _ _ s = _ ∧ _
  by_cases ht : btypeTaken op (x.get rs1) (x.get rs2) = true
  · obtain ⟨s', hs, hi⟩ := jump_to_inv e h _ (ha ht).1 (ha ht).2
    refine ⟨s', ?_, by rw [if_pos ht]; exact hi⟩
    cases op <;> simp [btypeTaken] at ht <;>
      simp [execute_BTYPE, rX_bits_inv h, readReg_ok h.pc, LeanRV64D.readReg, ht, hs, bind,
        EStateM.bind, pure, EStateM.pure]
  · refine ⟨s, ?_, by rw [if_neg ht]; exact h⟩
    simp only [Bool.not_eq_true] at ht
    cases op <;> simp [btypeTaken] at ht <;>
      simp [execute_BTYPE, rX_bits_inv h, ht, bind, EStateM.bind, pure, EStateM.pure]

theorem update0_getLsbD (v : BitVec 64) : (BitVec.update v 0 0#1).getLsbD 0 = false := by
  simp [Sail.BitVec.update, Sail.BitVec.updateSubrange']

theorem exec_jalr {S s : SailState} {val : (r : Register) → RegisterType r} {pc npc : BitVec 64}
    {x : Regs} (e : Env S val) (h : Inv S s pc npc x) (imm : BitVec 12) (rs1 rd : BitVec 5)
    (hr : rs1 = 1 ∨ rs1 = 5 ∨ rs1 = 7)
    (ha : (BitVec.update (x.get rs1 + sign_extend (m := 64) imm) 0 0#1).getLsbD 1 = false) :
    ∃ s', execute (.JALR (imm, .Regidx rs1, .Regidx rd)) s = .ok RETIRE_SUCCESS s' ∧
      Inv S s' pc (BitVec.update (x.get rs1 + sign_extend (m := 64) imm) 0 0#1) (x.set rd npc) := by
  show ∃ s', execute_JALR _ _ _ s = _ ∧ _
  obtain ⟨b, hb⟩ := get_xLPE_env e h
  -- The state after update_elp_state.
  obtain ⟨s1, hs1, h1⟩ : ∃ s1, update_elp_state (.Regidx rs1) s = .ok () s1 ∧ Inv S s1 pc npc x
      := by
    cases b
    · exact ⟨s, by
        simp (config := { decide := true }) [update_elp_state, currentlyEnabled, hartSupports,
          readReg_env e h, isRunReg, LeanRV64D.readReg, hb, bind, EStateM.bind, pure,
          EStateM.pure], h⟩
    · refine ⟨_, ?_, h.set_elp e⟩
      rcases hr with rfl | rfl | rfl <;>
        simp (config := { decide := true }) [update_elp_state, currentlyEnabled, hartSupports,
          readReg_env e h, isRunReg, LeanRV64D.readReg, hb, bind, EStateM.bind, pure,
          EStateM.pure, writeReg_ok, LeanRV64D.writeReg, bool_to_bit, bool_bit_forwards] <;> rfl
  obtain ⟨s2, hs2, h2⟩ := jump_to_inv e h1 _ (update0_getLsbD _) ha
  obtain ⟨s3, hs3, h3⟩ := wX_bits_inv h2 rd npc
  refine ⟨s3, ?_, h3⟩
  simp [execute_JALR, hs1, get_next_pc, readReg_ok h1.npc, LeanRV64D.readReg, rX_bits_inv h1, hs2,
    hs3, bind, EStateM.bind, pure, EStateM.pure, RETIRE_SUCCESS]

/-- The Sail model executes the instructions as `exec`, with the next program counter `pc + 4`
set by the step. The jump targets must be aligned to 4 bytes. -/
theorem exec_sim {S s : SailState} {val : (r : Register) → RegisterType r} {pc : BitVec 64}
    {x : Regs} {i : instruction} {pc' : BitVec 64} {x' : Regs} (e : Env S val)
    (h : Inv S s pc (pc + 4) x) (hi : exec i pc x = some (pc', x'))
    (ha : pc'.getLsbD 0 = false ∧ pc'.getLsbD 1 = false) :
    ∃ s', execute i s = .ok RETIRE_SUCCESS s' ∧ Inv S s' pc pc' x' := by
  unfold exec at hi
  split at hi
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hi).symm; exact exec_rtype h _ _ _ _
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hi).symm; exact exec_itype h _ _ _ _
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hi).symm; exact exec_shiftiop h _ _ _ _
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hi).symm; exact exec_mul h _ _ _ _
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hi).symm
    refine exec_btype e h _ _ _ _ fun ht => ?_
    simpa [ht] using ha
  · split at hi
    · rename_i hr
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hi).symm
      exact exec_jalr e h _ _ _ hr ha.2
    · contradiction
  · contradiction

end IntxRV
