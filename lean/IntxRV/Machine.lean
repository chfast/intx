import LeanRV64D.DecodeExt
/-!
# The machine

The states of the Sail RISC-V model (`LeanRV64D`) running a function. A state `S` of the
environment (the CSRs, the memory, the privilege level, ...) is fixed; the function changes only
the program counters and the general purpose registers. `Inv S s pc npc x` says that the state `s`
is `S` with the program counter `pc`, the next program counter `npc` and the general purpose
registers `x`.
-/

open Sail Sail.ConcurrencyInterfaceV1 PreSail
open LeanRV64D LeanRV64D.Functions LeanRV64D.Defs

namespace IntxRV

/-- A state of the Sail model. -/
abbrev SailState := SequentialState RegisterType trivialChoiceSource

/-- The values of the general purpose registers by their index (the value of `x 0` is ignored). -/
abbrev Regs := BitVec 5 → BitVec 64

/-- The value of the register `i`: x0 is zero. -/
def Regs.get (x : Regs) (i : BitVec 5) : BitVec 64 := if i = 0 then 0 else x i

/-- The registers `x` with the register `i` set to `v`: writes to x0 are ignored. -/
def Regs.set (x : Regs) (i : BitVec 5) (v : BitVec 64) : Regs :=
  if i = 0 then x else fun j => if j = i then v else x j

/-- The registers that a function changes: the program counters and the general purpose
registers. -/
def isRunReg : Register → Bool
  | .x1 | .x2 | .x3 | .x4 | .x5 | .x6 | .x7 | .x8 | .x9 | .x10 | .x11 | .x12 | .x13 | .x14 | .x15
  | .x16 | .x17 | .x18 | .x19 | .x20 | .x21 | .x22 | .x23 | .x24 | .x25 | .x26 | .x27 | .x28
  | .x29 | .x30 | .x31 | .PC | .nextPC => true
  | _ => false

/-- The state `s` is the environment `S` with the program counter `pc`, the next program counter
`npc` and the general purpose registers `x`. -/
structure Inv (S s : SailState) (pc npc : BitVec 64) (x : Regs) : Prop where
  rest : { s with regs := S.regs } = S
  other : ∀ r, isRunReg r = false → s.regs.get? r = S.regs.get? r
  pc : s.regs.get? .PC = some pc
  npc : s.regs.get? .nextPC = some npc
  x1 : s.regs.get? .x1 = some (x 1#5)
  x2 : s.regs.get? .x2 = some (x 2#5)
  x3 : s.regs.get? .x3 = some (x 3#5)
  x4 : s.regs.get? .x4 = some (x 4#5)
  x5 : s.regs.get? .x5 = some (x 5#5)
  x6 : s.regs.get? .x6 = some (x 6#5)
  x7 : s.regs.get? .x7 = some (x 7#5)
  x8 : s.regs.get? .x8 = some (x 8#5)
  x9 : s.regs.get? .x9 = some (x 9#5)
  x10 : s.regs.get? .x10 = some (x 10#5)
  x11 : s.regs.get? .x11 = some (x 11#5)
  x12 : s.regs.get? .x12 = some (x 12#5)
  x13 : s.regs.get? .x13 = some (x 13#5)
  x14 : s.regs.get? .x14 = some (x 14#5)
  x15 : s.regs.get? .x15 = some (x 15#5)
  x16 : s.regs.get? .x16 = some (x 16#5)
  x17 : s.regs.get? .x17 = some (x 17#5)
  x18 : s.regs.get? .x18 = some (x 18#5)
  x19 : s.regs.get? .x19 = some (x 19#5)
  x20 : s.regs.get? .x20 = some (x 20#5)
  x21 : s.regs.get? .x21 = some (x 21#5)
  x22 : s.regs.get? .x22 = some (x 22#5)
  x23 : s.regs.get? .x23 = some (x 23#5)
  x24 : s.regs.get? .x24 = some (x 24#5)
  x25 : s.regs.get? .x25 = some (x 25#5)
  x26 : s.regs.get? .x26 = some (x 26#5)
  x27 : s.regs.get? .x27 = some (x 27#5)
  x28 : s.regs.get? .x28 = some (x 28#5)
  x29 : s.regs.get? .x29 = some (x 29#5)
  x30 : s.regs.get? .x30 = some (x 30#5)
  x31 : s.regs.get? .x31 = some (x 31#5)

/-! ## Reading and writing the registers -/

theorem run_beq {r : Register} (hr : isRunReg r = false) (k : Register) (hk : isRunReg k = true) :
    (k == r) = false := by
  rw [beq_eq_false_iff_ne]; rintro rfl; rw [hk] at hr; contradiction

theorem readReg_ok {s : SailState} {r : Register} {v : RegisterType r}
    (h : s.regs.get? r = some v) : (PreSail.readReg r : SailM (RegisterType r)) s = .ok v s := by
  simp [PreSail.readReg, h, get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure,
    EStateM.pure]

theorem writeReg_ok {s : SailState} {r : Register} (v : RegisterType r) :
    (PreSail.writeReg r v : SailM PUnit) s = .ok () { s with regs := s.regs.insert r v } := rfl

/-- Proves `Inv S s' pc' npc' x'` for the state `s'` of inserts into `s` with
`h : Inv S s pc npc x`. -/
macro "inv_insert" h:term : tactic => `(tactic| exact {
    rest := ($h).rest
    other := fun r hr => by
      simp (config := { decide := true }) only [Std.ExtDHashMap.get?_insert, run_beq hr,
        Bool.false_eq_true, dite_false]
      exact ($h).other r hr
    pc := by simp [Std.ExtDHashMap.get?_insert, ($h).pc]
    npc := by simp [Std.ExtDHashMap.get?_insert, ($h).npc]
    x1 := by simp [Std.ExtDHashMap.get?_insert, Regs.set, ($h).x1]
    x2 := by simp [Std.ExtDHashMap.get?_insert, Regs.set, ($h).x2]
    x3 := by simp [Std.ExtDHashMap.get?_insert, Regs.set, ($h).x3]
    x4 := by simp [Std.ExtDHashMap.get?_insert, Regs.set, ($h).x4]
    x5 := by simp [Std.ExtDHashMap.get?_insert, Regs.set, ($h).x5]
    x6 := by simp [Std.ExtDHashMap.get?_insert, Regs.set, ($h).x6]
    x7 := by simp [Std.ExtDHashMap.get?_insert, Regs.set, ($h).x7]
    x8 := by simp [Std.ExtDHashMap.get?_insert, Regs.set, ($h).x8]
    x9 := by simp [Std.ExtDHashMap.get?_insert, Regs.set, ($h).x9]
    x10 := by simp [Std.ExtDHashMap.get?_insert, Regs.set, ($h).x10]
    x11 := by simp [Std.ExtDHashMap.get?_insert, Regs.set, ($h).x11]
    x12 := by simp [Std.ExtDHashMap.get?_insert, Regs.set, ($h).x12]
    x13 := by simp [Std.ExtDHashMap.get?_insert, Regs.set, ($h).x13]
    x14 := by simp [Std.ExtDHashMap.get?_insert, Regs.set, ($h).x14]
    x15 := by simp [Std.ExtDHashMap.get?_insert, Regs.set, ($h).x15]
    x16 := by simp [Std.ExtDHashMap.get?_insert, Regs.set, ($h).x16]
    x17 := by simp [Std.ExtDHashMap.get?_insert, Regs.set, ($h).x17]
    x18 := by simp [Std.ExtDHashMap.get?_insert, Regs.set, ($h).x18]
    x19 := by simp [Std.ExtDHashMap.get?_insert, Regs.set, ($h).x19]
    x20 := by simp [Std.ExtDHashMap.get?_insert, Regs.set, ($h).x20]
    x21 := by simp [Std.ExtDHashMap.get?_insert, Regs.set, ($h).x21]
    x22 := by simp [Std.ExtDHashMap.get?_insert, Regs.set, ($h).x22]
    x23 := by simp [Std.ExtDHashMap.get?_insert, Regs.set, ($h).x23]
    x24 := by simp [Std.ExtDHashMap.get?_insert, Regs.set, ($h).x24]
    x25 := by simp [Std.ExtDHashMap.get?_insert, Regs.set, ($h).x25]
    x26 := by simp [Std.ExtDHashMap.get?_insert, Regs.set, ($h).x26]
    x27 := by simp [Std.ExtDHashMap.get?_insert, Regs.set, ($h).x27]
    x28 := by simp [Std.ExtDHashMap.get?_insert, Regs.set, ($h).x28]
    x29 := by simp [Std.ExtDHashMap.get?_insert, Regs.set, ($h).x29]
    x30 := by simp [Std.ExtDHashMap.get?_insert, Regs.set, ($h).x30]
    x31 := by simp [Std.ExtDHashMap.get?_insert, Regs.set, ($h).x31]
  })

theorem rX_bits_inv {S s : SailState} {pc npc : BitVec 64} {x : Regs} (h : Inv S s pc npc x)
    (i : BitVec 5) : rX_bits (.Regidx i) s = .ok (x.get i) s := by
  obtain ⟨⟨n, hn⟩⟩ := i
  iterate 32 (rcases n with _ | n; · simp [rX_bits, rX, Regs.get, BitVec.toNatInt, readReg_ok,
      h.x1, h.x2, h.x3, h.x4, h.x5, h.x6, h.x7, h.x8, h.x9, h.x10, h.x11, h.x12, h.x13, h.x14,
          h.x15, h.x16, h.x17, h.x18, h.x19, h.x20, h.x21, h.x22, h.x23, h.x24, h.x25, h.x26, h.x27,
          h.x28, h.x29, h.x30, h.x31, regval_from_reg, pure, EStateM.pure, bind, EStateM.bind,
          zero_reg] <;> rfl)
  omega

theorem wX_bits_inv {S s : SailState} {pc npc : BitVec 64} {x : Regs} (h : Inv S s pc npc x)
    (i : BitVec 5) (v : BitVec 64) :
    ∃ s', wX_bits (.Regidx i) v s = .ok () s' ∧ Inv S s' pc npc (x.set i v) := by
  obtain ⟨⟨n, hn⟩⟩ := i
  rcases n with _ | n
  · exact ⟨s, rfl, by simpa [Regs.set] using h⟩
  iterate 31 (rcases n with _ | n; · exact ⟨_, by
      simp [wX_bits, wX, BitVec.toNatInt, writeReg_ok, regval_into_reg, xreg_write_callback,
        reg_name_forwards, pure, EStateM.pure, bind, EStateM.bind]; rfl, by inv_insert h⟩)
  omega

/-! ## Evaluating the monad -/

theorem pure_bind' {α β : Type} (a : α) (f : α → SailM β) :
    (EStateM.pure a : SailM α).bind f = f a := rfl

theorem pure_apply' {α : Type} (a : α) (s : SailState) :
    (EStateM.pure a : SailM α) s = .ok a s := rfl

theorem ite_apply' {α : Type} (c : Prop) [Decidable c] (f g : SailM α) (s : SailState) :
    (if c then f else g) s = if c then f s else g s := by split <;> rfl

/-! ## The environment -/

/-- The environment `S` in which the functions run, with the values `val` of its registers:
every register of the model exists, no landing pad is expected (Zicfilp), the M extension is
enabled in `misa`, and the privilege level is machine, supervisor or user. -/
structure Env (S : SailState) (val : (r : Register) → RegisterType r) : Prop where
  get : ∀ r, S.regs.get? r = some (val r)
  elp : val .elp = 0#1
  misa_M : _get_Misa_M (val .misa) = 1#1
  priv : val .cur_privilege = .Machine ∨ val .cur_privilege = .Supervisor ∨
    val .cur_privilege = .User

theorem readReg_env {S s : SailState} {val : (r : Register) → RegisterType r} {pc npc : BitVec 64}
    {x : Regs} (e : Env S val) (h : Inv S s pc npc x) (r : Register) (hr : isRunReg r = false) :
    (PreSail.readReg r : SailM (RegisterType r)) s = .ok (val r) s :=
  readReg_ok (by rw [h.other r hr, e.get])

end IntxRV
