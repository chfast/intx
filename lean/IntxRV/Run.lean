import IntxRV.Semantics
/-!
# Running a function

`run` runs the machine code of a function in the Sail model until it returns. A step follows the
`F_Base` case of `run_hart_active` and `tick_pc` of `try_step` in the Sail model (`Step.lean`):
decode the instruction, check that no landing pad is expected (Zicfilp), set `nextPC` to
`PC + 4`, execute, and set `PC` to `nextPC`. The model of the fetch is the code at the address
`base`. Interrupts, the waiting states and the counting of the retired instructions (`minstret`)
are not modeled, and a step that does not retire the instruction ends the run.

`arun` runs the instructions of the function by `exec`, and `run_sim` shows that `run` computes
the same.
-/

open Sail Sail.ConcurrencyInterfaceV1 PreSail
open LeanRV64D LeanRV64D.Functions LeanRV64D.Defs

namespace IntxRV

/-- The machine code of a function: its 32-bit instructions. -/
abbrev Code := List (BitVec 32)

/-- The instruction of `code` at `base` at the address `pc`. -/
def fetch {α : Type} (code : List α) (base pc : BitVec 64) : Option α :=
  if (pc - base) &&& 3 = 0 then code[((pc - base) >>> 2).toNat]? else none

/-- One step of the Sail model for the instruction `w`. -/
noncomputable def step (w : BitVec 32) : SailM ExecutionResult := do
  let instruction ← ext_decode w
  if (← is_landing_pad_expected ()) && !is_lpad_instruction instruction then
    return .Illegal_Instruction ()
  LeanRV64D.writeReg .nextPC (BitVec.addInt (← LeanRV64D.readReg .PC) 4)
  let result ← execute instruction
  tick_pc ()
  pure result

/-- Runs `code` at `base` for at most `n` steps, until the program counter is `ret`. -/
noncomputable def run (code : Code) (base ret : BitVec 64) : Nat → SailM Bool
  | 0 => pure false
  | n + 1 => do
    let pc ← LeanRV64D.readReg .PC
    if pc = ret then return true
    match fetch code base pc with
    | none => return false
    | some w =>
      match ← step w with
      | .Retire_Success () => run code base ret n
      | _ => return false

/-- Runs the instructions `prog` at `base` by `exec` for at most `n` steps, until the program
    counter
is `ret`. -/
def arun (prog : List instruction) (base ret : BitVec 64) : Nat → BitVec 64 → Regs → Option Regs
  | 0, _, _ => none
  | n + 1, pc, x =>
    if pc = ret then some x
    else match fetch prog base pc with
      | none => none
      | some i => match exec i pc x with
        | none => none
        | some (pc', x') => arun prog base ret n pc' x'

/-- The instructions `prog` are the instructions of `code` decoded by the Sail model. -/
def Decodes (code : Code) (prog : List instruction) : Prop :=
  code.length = prog.length ∧
    ∀ k (hk : k < code.length) (hk' : k < prog.length) (S s : SailState)
      (val : (r : Register) → RegisterType r) (pc npc : BitVec 64) (x : Regs),
      Env S val → Inv S s pc npc x → ext_decode code[k] s = .ok prog[k] s

theorem fetch_decodes {code : Code} {prog : List instruction} (hd : Decodes code prog)
    {base pc : BitVec 64} {i : instruction} (hf : fetch prog base pc = some i) :
    ∃ w, fetch code base pc = some w ∧
      ∀ (S s : SailState) (val : (r : Register) → RegisterType r) (npc : BitVec 64) (x : Regs),
        Env S val → Inv S s pc npc x → ext_decode w s = .ok i s := by
  unfold fetch at hf ⊢
  split at hf
  · rw [if_pos (by assumption)]
    obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.mp hf
    exact ⟨_, List.getElem?_eq_getElem (hd.1 ▸ hk), fun S s val npc x e h =>
      hd.2 _ (hd.1 ▸ hk) hk S s val pc npc x e h⟩
  · contradiction

theorem fetch_aligned {α : Type} {code : List α} {base pc : BitVec 64} {i : α}
    (h : fetch code base pc = some i) : (pc - base) &&& 3 = 0 := by
  unfold fetch at h; split at h
  · assumption
  · cases h

/-! ## Alignment -/

theorem aligned_iff (x : BitVec 64) : x &&& 3 = 0 ↔ x.toNat % 4 = 0 := by
  rw [← BitVec.toNat_inj, BitVec.toNat_and, show (3 : BitVec 64).toNat = 2 ^ 2 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  simp

theorem getLsbD_of_aligned {x : BitVec 64} (h : x &&& 3 = 0) :
    x.getLsbD 0 = false ∧ x.getLsbD 1 = false := by
  rw [aligned_iff] at h
  simp only [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_eq_div_pow]
  constructor <;> simp <;> omega

theorem aligned_add {a b : BitVec 64} (ha : a &&& 3 = 0) (hb : b &&& 3 = 0) :
    (a + b) &&& 3 = 0 := by
  rw [aligned_iff] at *; rw [BitVec.toNat_add]; omega

/-- An address that `arun` reaches is `ret` or in the code: aligned to 4 bytes. -/
theorem arun_aligned {prog : List instruction} {base ret pc : BitVec 64} {n : Nat} {x x' : Regs}
    (hb : base &&& 3 = 0) (hr : ret &&& 3 = 0) (h : arun prog base ret n pc x = some x') :
    pc.getLsbD 0 = false ∧ pc.getLsbD 1 = false := by
  cases n with
  | zero => rw [arun] at h; cases h
  | succ n =>
    rw [arun] at h
    by_cases hp : pc = ret
    · subst hp; exact getLsbD_of_aligned hr
    · rw [if_neg hp] at h
      cases hf : fetch prog base pc with
      | none => rw [hf] at h; cases h
      | some i =>
        have ha := aligned_add (fetch_aligned hf) hb
        rw [BitVec.sub_add_cancel] at ha
        exact getLsbD_of_aligned ha

theorem readReg_pc {S s : SailState} {pc npc : BitVec 64} {x : Regs} (h : Inv S s pc npc x) :
    (LeanRV64D.readReg .PC : SailM (BitVec 64)) s = .ok pc s := readReg_ok h.pc

/-- A step of the Sail model computes as `exec`. -/
theorem step_sim {S s : SailState} {val : (r : Register) → RegisterType r} {pc npc : BitVec 64}
    {x : Regs} {w : BitVec 32} {i : instruction} {pc' : BitVec 64} {x' : Regs} (e : Env S val)
    (h : Inv S s pc npc x) (hdec : ∀ (s : SailState) (npc : BitVec 64), Inv S s pc npc x →
      ext_decode w s = .ok i s)
    (hi : exec i pc x = some (pc', x')) (ha : pc'.getLsbD 0 = false ∧ pc'.getLsbD 1 = false) :
    ∃ s', step w s = .ok RETIRE_SUCCESS s' ∧ Inv S s' pc' pc' x' := by
  have h1 := h.set_npc (pc + 4)
  obtain ⟨s2, hs2, h2⟩ := exec_sim e h1 hi ha
  have h3 := h2.set_pc pc'
  refine ⟨_, ?_, h3⟩
  have hlp : (is_landing_pad_expected () : SailM Bool) s = .ok false s := by
    simp (config := { decide := true }) [is_landing_pad_expected, readReg_env e h, isRunReg,
      LeanRV64D.readReg, e.elp, landing_pad_bits_backwards, bind, EStateM.bind, pure,
      EStateM.pure]
  have hpc : BitVec.addInt pc 4 = pc + 4 := by simp [Sail.BitVec.addInt]
  simp only [step, hdec s npc h, hlp, readReg_ok h.pc, LeanRV64D.readReg, LeanRV64D.writeReg,
    writeReg_ok, hpc, bind, EStateM.bind, pure, EStateM.pure, Bool.false_and, Bool.false_eq_true,
    if_false]
  erw [hs2]
  simp [tick_pc, readReg_ok h2.npc, readReg_ok h3.pc, LeanRV64D.readReg, LeanRV64D.writeReg,
    writeReg_ok, bind, EStateM.bind, pure, EStateM.pure, RETIRE_SUCCESS]

/-- `run` computes as `arun`. -/
theorem run_sim {code : Code} {prog : List instruction} (hd : Decodes code prog)
    {S : SailState} {val : (r : Register) → RegisterType r} (e : Env S val) {base ret : BitVec 64}
    (hb : base &&& 3 = 0) (hr : ret &&& 3 = 0) :
    ∀ (n : Nat) (s : SailState) (pc npc : BitVec 64) (x x' : Regs),
      Inv S s pc npc x → arun prog base ret n pc x = some x' →
      ∃ s' npc', run code base ret n s = .ok true s' ∧ Inv S s' ret npc' x' := by
  intro n
  induction n with
  | zero => intro s pc npc x x' _ ha; simp [arun] at ha
  | succ n ih =>
    intro s pc npc x x' h ha
    unfold arun at ha
    by_cases hp : pc = ret
    · rw [if_pos hp] at ha
      cases ha
      subst hp
      exact ⟨s, npc, by simp [run, readReg_pc h, bind, EStateM.bind, pure, EStateM.pure], h⟩
    · rw [if_neg hp] at ha
      split at ha
      · contradiction
      · rename_i i hf
        split at ha
        · contradiction
        · rename_i pc' x'' hi
          obtain ⟨w, hw, hdec⟩ := fetch_decodes hd hf
          obtain ⟨s1, hs1, h1⟩ := step_sim e h (fun s npc h => hdec S s val npc x e h) hi
            (arun_aligned hb hr ha)
          obtain ⟨s', npc', hr', h'⟩ := ih s1 pc' pc' x'' x' h1 ha
          refine ⟨s', npc', ?_, h'⟩
          simp [run, readReg_pc h, hp, hw, hs1, hr', bind, EStateM.bind, pure, EStateM.pure,
            RETIRE_SUCCESS]

/-! ## Functions -/

/-- The registers that a function must preserve in the RISC-V calling convention: sp, gp, tp and
s0 to s11. -/
def calleeSaved : List (BitVec 5) := [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

/-- The function `code` computes `post` from the registers satisfying `pre`. For every
environment `S`, the addresses `base` of the code and `ret` of the return (aligned to 4 bytes,
`ret` not in the code) and the registers `x` with the return address `ret` in ra (x1), the Sail
model runs the code until it returns to `ret` and ends with the registers `x'` with `post x x'`.
The run changes nothing else in the machine (`Inv S`). -/
def Runs (code : Code) (pre : Regs → Prop) (post : Regs → Regs → Prop) : Prop :=
  ∀ (S : SailState) (val : (r : Register) → RegisterType r), Env S val →
  ∀ (base ret : BitVec 64), base &&& 3 = 0 → ret &&& 3 = 0 → 4 * code.length ≤ (ret - base).toNat →
  ∀ (s : SailState) (npc : BitVec 64) (x : Regs), Inv S s base npc x → x 1#5 = ret → pre x →
    ∃ n s' npc' x', run code base ret n s = .ok true s' ∧ Inv S s' ret npc' x' ∧ post x x'

theorem runs_of_arun {code : Code} {prog : List instruction} {pre : Regs → Prop}
    {post : Regs → Regs → Prop} (hd : Decodes code prog)
    (h : ∀ base ret : BitVec 64, base &&& 3 = 0 → ret &&& 3 = 0 →
      4 * code.length ≤ (ret - base).toNat → ∀ x : Regs, x 1#5 = ret → pre x →
      ∃ n x', arun prog base ret n base x = some x' ∧ post x x') :
    Runs code pre post := by
  intro S val e base ret hb hr hl s npc x hs hx hpre
  obtain ⟨n, x', ha, hp⟩ := h base ret hb hr hl x hx hpre
  obtain ⟨s', npc', hrun, hs'⟩ := run_sim hd e hb hr n s base npc x x' hs ha
  exact ⟨n, s', npc', x', hrun, hs', hp⟩

/-- A function computing `post` under `pre` computes `post'` under `pre'` if `pre'` implies `pre`
and `post` implies `post'` under `pre'`. -/
theorem Runs.mono {code : Code} {pre pre' : Regs → Prop} {post post' : Regs → Regs → Prop}
    (h : Runs code pre post) (hpre : ∀ x, pre' x → pre x)
    (hpost : ∀ x x', pre' x → post x x' → post' x x') : Runs code pre' post' := by
  intro S val e base ret hb hr hl s npc x hs hx hp
  obtain ⟨n, s', npc', x', hrun, hs', hq⟩ := h S val e base ret hb hr hl s npc x hs hx (hpre x hp)
  exact ⟨n, s', npc', x', hrun, hs', hpost x x' hp hq⟩

/-! ## Evaluating `arun` -/

theorem add_sub_cancel_left' (x y : BitVec 64) : x + y - x = y := by
  rw [BitVec.add_comm, BitVec.add_sub_cancel]

theorem ne_ret {base ret : BitVec 64} {len : Nat} (hl : 4 * len ≤ (ret - base).toNat)
    (k : BitVec 64) (hk : k.toNat < 4 * len) : (base + k = ret) = False := by
  simp only [eq_iff_iff, iff_false]
  rintro rfl
  rw [add_sub_cancel_left'] at hl
  omega

theorem ne_ret_zero {base ret : BitVec 64} {len : Nat} (hl : 4 * len ≤ (ret - base).toNat)
    (hlen : 0 < len) : (base = ret) = False := by
  simp only [eq_iff_iff, iff_false]
  rintro rfl
  simp at hl
  omega

theorem update_aligned {ret : BitVec 64} (hr : ret &&& 3 = 0) : BitVec.update ret 0 0#1 = ret := by
  have h0 := (getLsbD_of_aligned hr).1
  simp only [Sail.BitVec.update, Sail.BitVec.updateSubrange']
  ext i hi
  simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_shiftLeft]
  by_cases h : i = 0
  · subst h; simp [← BitVec.getLsbD_eq_getElem, h0]
  · simp [h]

theorem arun_ite {prog : List instruction} {base ret : BitVec 64} {n : Nat} (c : Prop)
    [Decidable c] (a b : BitVec 64) (x : Regs) :
    arun prog base ret n (if c then a else b) x =
      if c then arun prog base ret n a x else arun prog base ret n b x := by
  split <;> rfl

end IntxRV
