import IntxRV.Reach
import IntxRV.Words
/-!
# Running the instructions one by one

`Reach.step` runs the instruction at the address `pcAt base k` (the `k`-th instruction of
`prog`): the instruction comes from `prog[k]?` by evaluation, and `StepGoal` states what is left
to prove after it. The values that an instruction computes get a name `w` with its definition
`Defn w v`: the registers hold names, and the terms stay small however long the run is. `Defn`
hides the definitions from `omega`; the proof of a postcondition unfolds them.
-/

open Sail LeanRV64D.Defs

namespace IntxRV

/-- The address of the `k`-th instruction of the code at `base`. -/
@[irreducible] def pcAt (base : BitVec 64) (k : Nat) : BitVec 64 := base + BitVec.ofNat 64 (4 * k)

/-- The name `w` stands for the value `v`. -/
def Defn (w v : BitVec 64) : Prop := w = v

/-- The index of the target of a branch or jump by `imm` from the `k`-th instruction. -/
def jumpIdx {n : Nat} (k : Nat) (imm : BitVec n) : Nat :=
  (((4 * k : Nat) : Int) + imm.toInt).toNat / 4

theorem pcAt_zero (base : BitVec 64) : pcAt base 0 = base := by simp [pcAt]

theorem pcAt_sub (base : BitVec 64) (k : Nat) : pcAt base k - base = BitVec.ofNat 64 (4 * k) := by
  simp only [pcAt]; bv_omega

theorem fetch_pcAt {α : Type} (prog : List α) (base : BitVec 64) (k : Nat) (hk : k < 2 ^ 62) :
    fetch prog base (pcAt base k) = prog[k]? := by
  unfold fetch
  rw [pcAt_sub, if_pos]
  · congr
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat,
      show BitVec.toNat (3 : BitVec 64) = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      show BitVec.toNat (0 : BitVec 64) = 0 from rfl]
    omega

theorem pcAt_succ (base : BitVec 64) (k : Nat) : pcAt base k + 4#64 = pcAt base (k + 1) := by
  simp only [pcAt, BitVec.add_assoc]
  congr 1
  rw [show 4 * (k + 1) = 4 * k + 4 by omega, BitVec.ofNat_add]

theorem pcAt_jump {n : Nat} (base : BitVec 64) (k : Nat) (imm : BitVec n)
    (h : 0 ≤ ((4 * k : Nat) : Int) + imm.toInt ∧ imm.toInt % 4 = 0) :
    pcAt base k + imm.signExtend 64 = pcAt base (jumpIdx k imm) := by
  have he : ((4 * jumpIdx k imm : Nat) : Int) = ((4 * k : Nat) : Int) + imm.toInt := by
    unfold jumpIdx; omega
  simp only [pcAt, BitVec.add_assoc]
  congr 1
  rw [show imm.signExtend 64 = BitVec.ofInt 64 imm.toInt from rfl,
    show BitVec.ofNat 64 (4 * k) = BitVec.ofInt 64 ((4 * k : Nat) : Int) by
      rw [BitVec.ofInt_natCast],
    show BitVec.ofNat 64 (4 * jumpIdx k imm) = BitVec.ofInt 64 ((4 * jumpIdx k imm : Nat) : Int)
      by rw [BitVec.ofInt_natCast], ← BitVec.ofInt_add, he]

/-- What is left to prove after the instruction `i` at `pcAt base k`. -/
def StepGoal (A : List (BitVec 64)) (prog : List instruction) (base : BitVec 64) (k : Nat)
    (x : Regs) (m : Mem) (tgt : BitVec 64) (Q : Regs → Mem → Prop) : instruction → Prop
  | .RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, op) =>
    ∀ w, Defn w (rtypeVal op (x.get rs1) (x.get rs2)) →
      Reach A prog base (pcAt base (k + 1)) (x.set rd w) m tgt Q
  | .ITYPE (imm, .Regidx rs1, .Regidx rd, op) =>
    Reach A prog base (pcAt base (k + 1)) (x.set rd (itypeVal op imm (x.get rs1))) m tgt Q
  | .SHIFTIOP (shamt, .Regidx rs1, .Regidx rd, op) =>
    ∀ w, Defn w (shiftiopVal op shamt (x.get rs1)) →
      Reach A prog base (pcAt base (k + 1)) (x.set rd w) m tgt Q
  | .MUL (.Regidx rs2, .Regidx rs1, .Regidx rd, op) =>
    ∀ w, Defn w (mulVal op (x.get rs1) (x.get rs2)) →
      Reach A prog base (pcAt base (k + 1)) (x.set rd w) m tgt Q
  | .RTYPEW (.Regidx rs2, .Regidx rs1, .Regidx rd, op) =>
    ∀ w, Defn w (rtypewVal op (x.get rs1) (x.get rs2)) →
      Reach A prog base (pcAt base (k + 1)) (x.set rd w) m tgt Q
  | .UTYPE (imm, .Regidx rd, op) =>
    Reach A prog base (pcAt base (k + 1)) (x.set rd (utypeVal op imm (pcAt base k))) m tgt Q
  | .JAL (imm, .Regidx rd) =>
    (0 ≤ ((4 * k : Nat) : Int) + imm.toInt ∧ imm.toInt % 4 = 0) ∧
      Reach A prog base (pcAt base (jumpIdx k imm)) (x.set rd (pcAt base (k + 1))) m tgt Q
  | .LOAD (imm, .Regidx rs1, .Regidx rd, u, width) =>
    u = false ∧ width = 8 ∧ x.get rs1 + imm.signExtend 64 ∈ A ∧
      ∀ w, Defn w (memWord m (x.get rs1 + imm.signExtend 64).toNat) →
        Reach A prog base (pcAt base (k + 1)) (x.set rd w) m tgt Q
  | .STORE (imm, .Regidx rs2, .Regidx rs1, width) =>
    width = 8 ∧ x.get rs1 + imm.signExtend 64 ∈ A ∧
      Reach A prog base (pcAt base (k + 1)) x
        (memStore m (x.get rs1 + imm.signExtend 64).toNat (x.get rs2)) tgt Q
  | .BTYPE (imm, .Regidx rs2, .Regidx rs1, op) =>
    (0 ≤ ((4 * k : Nat) : Int) + imm.toInt ∧ imm.toInt % 4 = 0) ∧
      (btypeTaken op (x.get rs1) (x.get rs2) = true →
        Reach A prog base (pcAt base (jumpIdx k imm)) x m tgt Q) ∧
      (btypeTaken op (x.get rs1) (x.get rs2) = false →
        Reach A prog base (pcAt base (k + 1)) x m tgt Q)
  | .JALR (imm, .Regidx rs1, .Regidx rd) =>
    (rs1 = 1 ∨ rs1 = 5 ∨ rs1 = 7) ∧
      Reach A prog base (BitVec.update (x.get rs1 + imm.signExtend 64) 0 0#1)
        (x.set rd (pcAt base (k + 1))) m tgt Q
  | _ => False

/-- One step: from the instruction `i` that `execM` runs to `pc'`, `x'` and `m'`. -/
theorem Reach.step_execM {A : List (BitVec 64)} {prog : List instruction}
    {base pc pc' tgt : BitVec 64}
    {x x' : Regs} {m m' : Mem} {Q : Regs → Mem → Prop} {i : instruction}
    (hf : fetch prog base pc = some i) (he : execM A i pc x m = some (pc', x', m'))
    (h : Reach A prog base pc' x' m' tgt Q) : Reach A prog base pc x m tgt Q := by
  obtain ⟨k, x'', m'', hk, hq⟩ := h
  exact ⟨k + 1, x'', m'', by simp [stepsM, hf, he, hk], hq⟩

theorem sign_extend_eq {n : Nat} (v : BitVec n) :
    LeanRV64D.Functions.sign_extend (m := 64) v = v.signExtend 64 := rfl

/-- Runs the `k`-th instruction of `prog`. -/
theorem Reach.step {A : List (BitVec 64)} {prog : List instruction} {base tgt : BitVec 64}
    {k : Nat} {x : Regs} {m : Mem} {Q : Regs → Mem → Prop} {i : instruction} (hk : k < 2 ^ 62)
    (hf : prog[k]? = some i) (h : StepGoal A prog base k x m tgt Q i) :
    Reach A prog base (pcAt base k) x m tgt Q := by
  rw [← fetch_pcAt prog base k hk] at hf
  unfold StepGoal at h
  split at h
  · exact Reach.step_execM hf (by simp [execM, exec, pcAt_succ]) (h _ rfl)
  · exact Reach.step_execM hf (by simp [execM, exec, pcAt_succ]) h
  · exact Reach.step_execM hf (by simp [execM, exec, pcAt_succ]) (h _ rfl)
  · exact Reach.step_execM hf (by simp [execM, exec, pcAt_succ]) (h _ rfl)
  · exact Reach.step_execM hf (by simp [execM, exec, pcAt_succ]) (h _ rfl)
  · exact Reach.step_execM hf (by simp [execM, exec, pcAt_succ]) h
  · rename_i imm rd
    obtain ⟨hj, h⟩ := h
    exact Reach.step_execM hf (by
      simp [execM, exec, sign_extend_eq, pcAt_jump base k imm hj, pcAt_succ]) h
  · obtain ⟨rfl, rfl, hA, h⟩ := h
    exact Reach.step_execM hf (by simp [execM, sign_extend_eq, hA, pcAt_succ]) (h _ rfl)
  · obtain ⟨rfl, hA, h⟩ := h
    exact Reach.step_execM hf (by simp [execM, sign_extend_eq, hA, pcAt_succ]) h
  · rename_i imm rs2 rs1 op
    obtain ⟨hj, ht, hn⟩ := h
    by_cases hb : btypeTaken op (x.get rs1) (x.get rs2) = true
    · exact Reach.step_execM hf (by
        simp [execM, exec, hb, sign_extend_eq, pcAt_jump base k imm hj]) (ht hb)
    · have hb' : btypeTaken op (x.get rs1) (x.get rs2) = false := by simpa using hb
      exact Reach.step_execM hf (by simp [execM, exec, hb', pcAt_succ]) (hn hb')
  · obtain ⟨hr, h⟩ := h
    exact Reach.step_execM hf (by
      rcases hr with rfl | rfl | rfl <;> simp [execM, exec, sign_extend_eq, pcAt_succ]) h
  · exact h.elim

end IntxRV
