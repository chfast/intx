import IntxRV.Mem4
/-!
# Running a function with memory

`execM` and `arunM` extend `exec` and `arun` with the loads (`ld`) and stores (`sd`) of the
aligned 64-bit words at the addresses of a list `A`: the words of the buffers that the pointer
arguments of the function address. `run_simM` shows that `run` computes as `arunM` in the
environment `EnvM` if the words of `A` are ordinary memory (`WordOk`) and present in the memory.
`RunsM` is `Runs` with the memory: the state at the return is the start state with the general
purpose registers, the program counters and the memory changed.
-/

open Sail Sail.ConcurrencyInterfaceV1 PreSail
open LeanRV64D LeanRV64D.Functions LeanRV64D.Defs

namespace IntxRV

/-- The memory of a state of the Sail model: the bytes by their address. -/
abbrev Mem := Std.ExtHashMap Nat (BitVec 8)

/-- The 8 bytes of the word at `a` are in the memory `m`. -/
def Present (m : Mem) (a : BitVec 64) : Prop := ∀ k < 8, a.toNat + k ∈ m

theorem present_memStore {m : Mem} {a : BitVec 64} (h : Present m a) (b : Nat) (v : BitVec 64) :
    Present (memStore m b v) a := by
  intro k hk
  simp [memStore, Std.ExtHashMap.mem_insert, h k hk]

/-- The next program counter, the registers and the memory after the instruction `i` at `pc`:
`exec`, and the loads and stores of the words at the addresses `A`. -/
def execM (A : List (BitVec 64)) (i : instruction) (pc : BitVec 64) (x : Regs) (m : Mem) :
    Option (BitVec 64 × Regs × Mem) :=
  match i with
  | .LOAD (imm, .Regidx rs1, .Regidx rd, u, w) =>
    if u = false ∧ w = 8 ∧ x.get rs1 + sign_extend (m := 64) imm ∈ A then
      some (pc + 4, x.set rd (memWord m (x.get rs1 + sign_extend (m := 64) imm).toNat), m)
    else if u = true ∧ w = 4 ∧ (x.get rs1 + sign_extend (m := 64) imm ∈ A ∨
        x.get rs1 + sign_extend (m := 64) imm - 4#64 ∈ A) then
      some (pc + 4,
        x.set rd ((memHalf m (x.get rs1 + sign_extend (m := 64) imm).toNat).setWidth 64), m)
    else none
  | .STORE (imm, .Regidx rs2, .Regidx rs1, w) =>
    if w = 8 ∧ x.get rs1 + sign_extend (m := 64) imm ∈ A then
      some (pc + 4, x, memStore m (x.get rs1 + sign_extend (m := 64) imm).toNat (x.get rs2))
    else none
  | i => (exec i pc x).map fun p => (p.1, p.2, m)

theorem execM_present {A : List (BitVec 64)} {i : instruction} {pc pc' : BitVec 64} {x x' : Regs}
    {m m' : Mem} (hi : execM A i pc x m = some (pc', x', m')) (hA : ∀ a ∈ A, Present m a) :
    ∀ a ∈ A, Present m' a := by
  unfold execM at hi
  split at hi
  · split at hi
    · cases hi; exact hA
    · split at hi
      · cases hi; exact hA
      · contradiction
  · split at hi
    · cases hi; exact fun a ha => present_memStore (hA a ha) _ _
    · contradiction
  · obtain ⟨_, _, h⟩ := Option.map_eq_some_iff.mp hi
    cases h; exact hA

/-- The Sail model executes the instructions as `execM`, with the next program counter `pc + 4`
set by the step. -/
theorem exec_simM {S s : SailState} {val : (r : Register) → RegisterType r} {pc : BitVec 64}
    {x : Regs} {A : List (BitVec 64)} {i : instruction} {pc' : BitVec 64} {x' : Regs} {m' : Mem}
    (e : EnvM S val) (hA : ∀ a ∈ A, WordOk val a ∧ Present S.mem a)
    (h : Inv S s pc (pc + 4) x) (hi : execM A i pc x S.mem = some (pc', x', m'))
    (ha : pc'.getLsbD 0 = false ∧ pc'.getLsbD 1 = false) :
    ∃ s', execute i s = .ok RETIRE_SUCCESS s' ∧ Inv { S with mem := m' } s' pc pc' x' := by
  unfold execM at hi
  split at hi
  · rename_i imm rs1 rd u w
    split at hi
    · rename_i hc
      obtain ⟨rfl, rfl, hm⟩ := hc
      obtain ⟨rfl, rfl, rfl⟩ := hi
      obtain ⟨s', hs, hi'⟩ := exec_load e h imm rs1 rd (hA _ hm).1 (h.mem ▸ (hA _ hm).2)
      rw [h.mem] at hi'
      exact ⟨s', hs, hi'⟩
    · split at hi
      · rename_i _ hc
        obtain ⟨rfl, rfl, hm⟩ := hc
        obtain ⟨rfl, rfl, rfl⟩ := hi
        obtain ⟨ho, hp⟩ : HalfOk val (x.get rs1 + sign_extend (m := 64) imm) ∧
            ∀ k < 4, (x.get rs1 + sign_extend (m := 64) imm).toNat + k ∈ S.mem := by
          rcases hm with hm | hm
          · exact ⟨(hA _ hm).1.half_lo, fun k hk => (hA _ hm).2 k (by omega)⟩
          · have ha := (hA _ hm).1
            have hal := ha.aligned
            refine ⟨by simpa only [BitVec.sub_add_cancel] using ha.half_hi, fun k hk => ?_⟩
            have := (hA _ hm).2 (k + 4) (by omega)
            have e : (x.get rs1 + sign_extend (m := 64) imm).toNat =
                (x.get rs1 + sign_extend (m := 64) imm - 4#64).toNat + 4 := by bv_omega
            rw [e, Nat.add_assoc, Nat.add_comm 4 k]; exact this
        obtain ⟨s', hs, hi'⟩ := exec_lwu e h imm rs1 rd ho (h.mem ▸ hp)
        rw [h.mem] at hi'
        exact ⟨s', hs, hi'⟩
      · contradiction
  · rename_i imm rs2 rs1 w
    split at hi
    · rename_i hc
      obtain ⟨rfl, hm⟩ := hc
      obtain ⟨rfl, rfl, rfl⟩ := hi
      obtain ⟨s', hs, rfl⟩ := exec_store e h imm rs2 rs1 (hA _ hm).1
      refine ⟨_, hs, ?_⟩
      rw [h.mem]
      exact h.with_mem _
    · contradiction
  · obtain ⟨⟨pc'', x''⟩, he, hp⟩ := Option.map_eq_some_iff.mp hi
    cases hp
    exact exec_sim e.toEnv h he ha

/-- A step of the Sail model computes as `execM`. -/
theorem step_simM {S s : SailState} {val : (r : Register) → RegisterType r} {pc npc : BitVec 64}
    {x : Regs} {A : List (BitVec 64)} {w : BitVec 32} {i : instruction} {pc' : BitVec 64}
    {x' : Regs} {m' : Mem} (e : EnvM S val) (hA : ∀ a ∈ A, WordOk val a ∧ Present S.mem a)
    (h : Inv S s pc npc x)
    (hdec : ∀ (s : SailState) (npc : BitVec 64), Inv S s pc npc x → ext_decode w s = .ok i s)
    (hi : execM A i pc x S.mem = some (pc', x', m'))
    (ha : pc'.getLsbD 0 = false ∧ pc'.getLsbD 1 = false) :
    ∃ s', step w s = .ok RETIRE_SUCCESS s' ∧ Inv { S with mem := m' } s' pc' pc' x' := by
  have h1 := h.set_npc (pc + 4)
  obtain ⟨s2, hs2, h2⟩ := exec_simM e hA h1 hi ha
  have h3 := h2.set_pc pc'
  refine ⟨_, ?_, h3⟩
  have hlp : (is_landing_pad_expected () : SailM Bool) s = .ok false s := by
    simp (config := { decide := true }) [is_landing_pad_expected, readReg_env e.toEnv h,
      isRunReg, LeanRV64D.readReg, e.elp, landing_pad_bits_backwards, bind, EStateM.bind, pure,
      EStateM.pure]
  have hpc : BitVec.addInt pc 4 = pc + 4 := by simp [Sail.BitVec.addInt]
  simp only [step, hdec s npc h, hlp, readReg_ok h.pc, LeanRV64D.readReg, LeanRV64D.writeReg,
    writeReg_ok, hpc, bind, EStateM.bind, pure, EStateM.pure, Bool.false_and, Bool.false_eq_true,
    if_false]
  erw [hs2]
  simp [tick_pc, readReg_ok h2.npc, readReg_ok h3.pc, LeanRV64D.readReg, LeanRV64D.writeReg,
    writeReg_ok, bind, EStateM.bind, pure, EStateM.pure, RETIRE_SUCCESS]

/-- Runs the instructions `prog` at `base` by `execM` for at most `n` steps, until the program
counter is `ret`. -/
def arunM (A : List (BitVec 64)) (prog : List instruction) (base ret : BitVec 64) :
    Nat → BitVec 64 → Regs → Mem → Option (Regs × Mem)
  | 0, _, _, _ => none
  | n + 1, pc, x, m =>
    if pc = ret then some (x, m)
    else match fetch prog base pc with
      | none => none
      | some i => match execM A i pc x m with
        | none => none
        | some (pc', x', m') => arunM A prog base ret n pc' x' m'

/-- An address that `arunM` reaches is `ret` or in the code: aligned to 4 bytes. -/
theorem arunM_aligned {A : List (BitVec 64)} {prog : List instruction} {base ret pc : BitVec 64}
    {n : Nat} {x x' : Regs} {m m' : Mem} (hb : base &&& 3 = 0) (hr : ret &&& 3 = 0)
    (h : arunM A prog base ret n pc x m = some (x', m')) :
    pc.getLsbD 0 = false ∧ pc.getLsbD 1 = false := by
  cases n with
  | zero => rw [arunM] at h; cases h
  | succ n =>
    rw [arunM] at h
    by_cases hp : pc = ret
    · subst hp; exact getLsbD_of_aligned hr
    · rw [if_neg hp] at h
      cases hf : fetch prog base pc with
      | none => rw [hf] at h; cases h
      | some i =>
        have ha := aligned_add (fetch_aligned hf) hb
        rw [BitVec.sub_add_cancel] at ha
        exact getLsbD_of_aligned ha

/-- `run` computes as `arunM`. -/
theorem run_simM {code : Code} {prog : List instruction} (hd : Decodes code prog)
    {val : (r : Register) → RegisterType r} {A : List (BitVec 64)} (hw : ∀ a ∈ A, WordOk val a)
    {base ret : BitVec 64} (hb : base &&& 3 = 0) (hr : ret &&& 3 = 0) :
    ∀ (n : Nat) (S s : SailState) (pc npc : BitVec 64) (x x' : Regs) (m' : Mem),
      EnvM S val → (∀ a ∈ A, Present S.mem a) → Inv S s pc npc x →
      arunM A prog base ret n pc x S.mem = some (x', m') →
      ∃ s' npc', run code base ret n s = .ok true s' ∧ s'.mem = m' ∧
        Inv { S with mem := m' } s' ret npc' x' := by
  intro n
  induction n with
  | zero => intro S s pc npc x x' m' _ _ _ ha; simp [arunM] at ha
  | succ n ih =>
    intro S s pc npc x x' m' e hp h ha
    unfold arunM at ha
    by_cases hpr : pc = ret
    · rw [if_pos hpr] at ha
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj ha)
      subst hpr
      refine ⟨s, npc, by simp [run, readReg_pc h, bind, EStateM.bind, pure, EStateM.pure],
        h.mem, h⟩
    · rw [if_neg hpr] at ha
      split at ha
      · contradiction
      · rename_i i hf
        split at ha
        · contradiction
        · rename_i pc' x'' m'' hi
          obtain ⟨w, hw', hdec⟩ := fetch_decodes hd hf
          obtain ⟨s1, hs1, h1⟩ := step_simM e (fun a ha => ⟨hw a ha, hp a ha⟩) h
            (fun s npc h => hdec S s val npc x e.toEnv h) hi (arunM_aligned hb hr ha)
          obtain ⟨s', npc', hr', hm', h'⟩ := ih { S with mem := m'' } s1 pc' pc' x'' x' m'
            (e.with_mem m'') (execM_present hi hp) h1 ha
          refine ⟨s', npc', ?_, hm', h'⟩
          simp [run, readReg_pc h, hpr, hw', hs1, hr', bind, EStateM.bind,
            RETIRE_SUCCESS]

/-- The function `code` computes `post` from the registers and the memory satisfying `pre`, with
the loads and stores of the words at the addresses `bufs x`. As `Runs`, for every environment
`EnvM` in which the words of `bufs x` are ordinary memory, present in the memory and outside the
code: the Sail model runs the code until it returns to `ret` and ends with the registers `x'` and
the memory `m'` with `post x m x' m'`, where `m` is the memory at the start. The run changes
nothing else in the machine. -/
def RunsM (code : Code) (bufs : Regs → List (BitVec 64)) (pre : Regs → Mem → Prop)
    (post : Regs → Mem → Regs → Mem → Prop) : Prop :=
  ∀ (S : SailState) (val : (r : Register) → RegisterType r), EnvM S val →
  ∀ (base ret : BitVec 64), base &&& 3 = 0 → ret &&& 3 = 0 → 4 * code.length ≤ (ret - base).toNat →
  ∀ (s : SailState) (npc : BitVec 64) (x : Regs), Inv S s base npc x → x 1#5 = ret →
    (∀ a ∈ bufs x, WordOk val a ∧ Present S.mem a ∧
      (a.toNat + 8 ≤ base.toNat ∨ base.toNat + 4 * code.length ≤ a.toNat)) →
    pre x S.mem →
    ∃ n s' npc' x', run code base ret n s = .ok true s' ∧
      Inv { S with mem := s'.mem } s' ret npc' x' ∧ post x S.mem x' s'.mem

theorem runsM_of_arunM {code : Code} {prog : List instruction} {bufs : Regs → List (BitVec 64)}
    {pre : Regs → Mem → Prop} {post : Regs → Mem → Regs → Mem → Prop} (hd : Decodes code prog)
    (h : ∀ base ret : BitVec 64, base &&& 3 = 0 → ret &&& 3 = 0 →
      4 * code.length ≤ (ret - base).toNat → ∀ (x : Regs) (m : Mem), x 1#5 = ret → pre x m →
      ∃ n x' m', arunM (bufs x) prog base ret n base x m = some (x', m') ∧ post x m x' m') :
    RunsM code bufs pre post := by
  intro S val e base ret hb hr hl s npc x hs hx hbuf hpre
  obtain ⟨n, x', m', ha, hp⟩ := h base ret hb hr hl x S.mem hx hpre
  obtain ⟨s', npc', hrun, hm, hs'⟩ := run_simM hd (fun a h => (hbuf a h).1) hb hr n S s base npc x
    x' m' e (fun a h => (hbuf a h).2.1) hs ha
  subst hm
  exact ⟨n, s', npc', x', hrun, hs', hp⟩

theorem RunsM.mono {code : Code} {bufs : Regs → List (BitVec 64)} {pre pre' : Regs → Mem → Prop}
    {post post' : Regs → Mem → Regs → Mem → Prop} (h : RunsM code bufs pre post)
    (hpre : ∀ x m, pre' x m → pre x m)
    (hpost : ∀ x m x' m', pre' x m → post x m x' m' → post' x m x' m') :
    RunsM code bufs pre' post' := by
  intro S val e base ret hb hr hl s npc x hs hx hbuf hp
  obtain ⟨n, s', npc', x', hrun, hs', hq⟩ :=
    h S val e base ret hb hr hl s npc x hs hx hbuf (hpre x S.mem hp)
  exact ⟨n, s', npc', x', hrun, hs', hpost x S.mem x' s'.mem hp hq⟩

end IntxRV
