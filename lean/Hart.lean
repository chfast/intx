import IntxRV.RunM
import IntxRV.Decode
import LeanRV64D.Step
/-!
# The hart of the Sail model

The proofs run the code by `run` (`IntxRV/Run.lean`), which renders the step of the Sail model:
the instruction comes from the list of the code, and the interrupts and the count of the retired
instructions are not modeled. This file proves that the hart of the Sail model itself runs the code
as the proofs do: `try_step`, the step of `loop`, fetches the instruction from the memory through
the address translation and the PMP and PMA checks (`fetch_M`), takes no interrupt in machine mode
with `mstatus.MIE` clear, executes the instruction, and counts it in `minstret` (`try_step_simM`).
`hart_simM` lifts it to a run of `arunM` with the code in the memory, which the stores do not
overwrite.

The specifications do not use it, for the cost: `try_step` imports `LeanRV64D.RvfiDii` of the
model, whose build takes 28 minutes and 13.3 GiB, and 50 minutes under a limit of 14 GiB: barely
within the 16 GB runner of CI. They would also
assume more: the code in an executable region of the memory, outside the buffers, the interrupts
off, and machine mode for the functions without memory. `lake build Hart` checks this file; CI does
not.
-/

open Sail Sail.ConcurrencyInterfaceV1 PreSail
open LeanRV64D LeanRV64D.Functions LeanRV64D.Defs

set_option linter.unusedSimpArgs false

namespace IntxRV

/-- The aligned 4-byte word at `a` is ordinary memory with code: readable (`HalfOk`) and in an
executable PMA region. -/
structure CodeOk (val : (r : Register) → RegisterType r) (a : BitVec 64) : Prop where
  half : HalfOk val a
  exec : ∀ r, matching_pma_region (val .pma_regions) (.Physaddr a) 4 = some r →
    r.attributes.executable = true

/-- No address translation of the fetch in machine mode. -/
theorem translate_fetch_M {S s : SailState} {val : (r : Register) → RegisterType r}
    {pc npc : BitVec 64} {x : Regs} (e : EnvM S val) (h : Inv S s pc npc x) (a : BitVec 64) :
    translateAddr (.Virtaddr a) (.InstructionFetch ()) s =
      .ok (.Ok (.Physaddr a, .PBMT_PMA, ())) s := by
  simp (config := { decide := true }) [translateAddr, effectivePrivilege, readReg_env e.toEnv h,
    isRunReg, LeanRV64D.readReg, e.mprv, e.priv_M, translationMode, is_shadow_stack_access,
    bind, EStateM.bind, pure, EStateM.pure, SailME.run, PreSailME.run, ExceptT.run, liftM,
    monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
    ExceptT.pure, Functor.map, EStateM.map, zero_extend, Sail.BitVec.zeroExtend, bits_of_virtaddr,
    init_ext_ptw]

/-- The fetch of the 4 bytes of code at `a` reads them, little-endian. -/
theorem mem_read_fetch {S s : SailState} {val : (r : Register) → RegisterType r}
    {pc npc : BitVec 64} {x : Regs} (e : EnvM S val) (h : Inv S s pc npc x) (a : BitVec 64)
    (ha : CodeOk val a) (hb : ∀ k < 4, a.toNat + k ∈ s.mem) :
    mem_read (.InstructionFetch ()) .PBMT_PMA (.Physaddr a) 4 false false false s =
      .ok (.Ok (memHalf s.mem a.toNat)) s := by
  have hr := readReg_env e.toEnv h
  obtain ⟨r, hm, hrd⟩ := ha.half.pma
  have hex := ha.exec r hm
  have hal : (BitVec.toNatInt a).tmod 4 = 0 := by
    have := ha.half.aligned
    simp only [BitVec.toNatInt, Int.ofNat_eq_natCast]
    rw [Int.tmod_eq_emod_of_nonneg (by omega)]
    omega
  simp (config := { decide := true }) [hal, LeanRV64D.assert, PreSail.assert, Functions.not,
    mem_read, mem_read_priv, mem_read_priv_meta, checked_mem_read,
    check_pma_with_pmp_priority, pmp_M e h, pmaCheck, hm, hrd, hex, override_PMA, mag_pma_check,
    is_aligned_paddr, is_mag_applicable_access, effectivePrivilege, hr, isRunReg,
    LeanRV64D.readReg, e.mprv, e.priv_M, read_ram_ok4 s a hb, updateSubrange_all32,
    split_misaligned, misaligned_order, untilFuelM, untilFuelM.go, mmio_M4 e h a ha.half,
    addInt_zero, bits_of_physaddr, read_kind_of_flags, MemoryOpResult_drop_meta,
    bind, EStateM.bind, pure, EStateM.pure, SailME.run, PreSailME.run, ExceptT.run, liftM,
    monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
    ExceptT.pure, Functor.map, EStateM.map]

/-- The word of code at `pc` is a 32-bit instruction: its low bits are `11` (not compressed). -/
def NotRVC (w : BitVec 32) : Prop := w &&& 3#32 = 3#32

theorem isRVC_false {w : BitVec 32} (hw : NotRVC w) :
    isRVC (Sail.BitVec.extractLsb w 15 0) = false := by
  unfold NotRVC at hw
  have hm : w.toNat % 4 = 3 := by
    have := congrArg BitVec.toNat hw
    rw [BitVec.toNat_and, show (3#32).toNat = 2 ^ 2 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod] at this
    simpa using this
  have h3 : BitVec.extractLsb 1 0 (BitVec.extractLsb 15 0 w) = 3#2 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb_toNat, Nat.shiftRight_zero]
    simp
    omega
  simp [isRVC, Sail.BitVec.extractLsb, h3, Functions.not]

/-- The fetch of the Sail model reads the 32-bit instruction at the program counter. -/
theorem fetch_M {S s : SailState} {val : (r : Register) → RegisterType r} {pc npc : BitVec 64}
    {x : Regs} (e : EnvM S val) (h : Inv S s pc npc x) (hpc : pc.toNat % 4 = 0)
    (hc : CodeOk val pc) (hb : ∀ k < 4, pc.toNat + k ∈ s.mem)
    (hw : NotRVC (memHalf s.mem pc.toNat)) :
    LeanRV64D.Functions.fetch () s = .ok (.F_Base (memHalf s.mem pc.toNat)) s := by
  have hr := readReg_env e.toEnv h
  have hal : (BitVec.toNatInt pc).tmod 4 = 0 := by
    simp only [BitVec.toNatInt, Int.ofNat_eq_natCast]
    rw [Int.tmod_eq_emod_of_nonneg (by omega)]
    omega
  obtain ⟨g0, g1⟩ := getLsbD_of_aligned ((aligned_iff pc).mpr hpc)
  have h0 : Sail.BitVec.access pc 0 = 0#1 := by
    simp [Sail.BitVec.access, ← BitVec.getLsbD_eq_getElem, g0]
  have h1 : Sail.BitVec.access pc 1 = 0#1 := by
    simp [Sail.BitVec.access, ← BitVec.getLsbD_eq_getElem, g1]
  simp (config := { decide := true }) [LeanRV64D.Functions.fetch, fetch_bytes, get_config_rvfi,
    ext_fetch_check_pc, readReg_ok h.pc, hr, isRunReg, LeanRV64D.readReg, h0, h1, is_aligned_vaddr,
    hal, currentlyEnabled,
    hartSupports, translate_fetch_M e h, mem_read_fetch e h pc hc hb, isRVC_false hw,
    bind, EStateM.bind, pure, EStateM.pure, SailME.run, PreSailME.run, ExceptT.run, liftM,
    monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
    ExceptT.pure, Functor.map, EStateM.map]

/-! ## The step of the hart -/

/-- The environment of the hart: `EnvM`, the hart active, and the interrupts of machine mode off
(`mstatus.MIE`), so that no interrupt is taken. -/
structure EnvH (S : SailState) (val : (r : Register) → RegisterType r) : Prop
    extends EnvM S val where
  active : val .hart_state = .HART_ACTIVE ()
  mie : _get_Mstatus_MIE (val .mstatus) = 0#1

/-- The hart counts the retired instructions of machine mode in `minstret`. -/
def countsInstret (val : (r : Register) → RegisterType r) : Bool :=
  (_get_Counterin_IR (val .mcountinhibit) == 0#1) &&
    (counter_priv_filter_bit (val .minstretcfg) .Machine == 0#1)

/-- The state `S` with the register `r` set to `v`. -/
def withReg (S : SailState) (r : Register) (v : RegisterType r) : SailState :=
  { S with regs := S.regs.insert r v }

theorem run_beq' {r : Register} (hr : isRunReg r = false) (k : Register) (hk : isRunReg k = true) :
    (r == k) = false := by
  rw [beq_eq_false_iff_ne]; rintro rfl; rw [hk] at hr; contradiction

theorem get?_insert_run {m : Std.ExtDHashMap Register RegisterType} {r : Register}
    (hr : isRunReg r = false) (v : RegisterType r) {k : Register} (hk : isRunReg k = true) :
    (m.insert r v).get? k = m.get? k := by
  rw [Std.ExtDHashMap.get?_insert, dif_neg (by simp [run_beq' hr k hk])]

/-- Setting a register that a function does not change in the state and in the environment. -/
theorem Inv.withReg {S s : SailState} {pc npc : BitVec 64} {x : Regs} (h : Inv S s pc npc x)
    {r : Register} (hr : isRunReg r = false) (v : RegisterType r) :
    Inv (withReg S r v) { s with regs := s.regs.insert r v } pc npc x where
  rest := by
    have hs := h.rest
    cases s; cases S
    simp only [IntxRV.withReg, SequentialState.mk.injEq] at hs ⊢
    simp_all
  other k hk := by
    simp only [IntxRV.withReg, Std.ExtDHashMap.get?_insert]
    split
    · rfl
    · exact h.other k hk
  pc := by rw [get?_insert_run hr v (k := .PC) rfl]; exact h.pc
  npc := by rw [get?_insert_run hr v (k := .nextPC) rfl]; exact h.npc
  x1 := by rw [get?_insert_run hr v (k := .x1) rfl]; exact h.x1
  x2 := by rw [get?_insert_run hr v (k := .x2) rfl]; exact h.x2
  x3 := by rw [get?_insert_run hr v (k := .x3) rfl]; exact h.x3
  x4 := by rw [get?_insert_run hr v (k := .x4) rfl]; exact h.x4
  x5 := by rw [get?_insert_run hr v (k := .x5) rfl]; exact h.x5
  x6 := by rw [get?_insert_run hr v (k := .x6) rfl]; exact h.x6
  x7 := by rw [get?_insert_run hr v (k := .x7) rfl]; exact h.x7
  x8 := by rw [get?_insert_run hr v (k := .x8) rfl]; exact h.x8
  x9 := by rw [get?_insert_run hr v (k := .x9) rfl]; exact h.x9
  x10 := by rw [get?_insert_run hr v (k := .x10) rfl]; exact h.x10
  x11 := by rw [get?_insert_run hr v (k := .x11) rfl]; exact h.x11
  x12 := by rw [get?_insert_run hr v (k := .x12) rfl]; exact h.x12
  x13 := by rw [get?_insert_run hr v (k := .x13) rfl]; exact h.x13
  x14 := by rw [get?_insert_run hr v (k := .x14) rfl]; exact h.x14
  x15 := by rw [get?_insert_run hr v (k := .x15) rfl]; exact h.x15
  x16 := by rw [get?_insert_run hr v (k := .x16) rfl]; exact h.x16
  x17 := by rw [get?_insert_run hr v (k := .x17) rfl]; exact h.x17
  x18 := by rw [get?_insert_run hr v (k := .x18) rfl]; exact h.x18
  x19 := by rw [get?_insert_run hr v (k := .x19) rfl]; exact h.x19
  x20 := by rw [get?_insert_run hr v (k := .x20) rfl]; exact h.x20
  x21 := by rw [get?_insert_run hr v (k := .x21) rfl]; exact h.x21
  x22 := by rw [get?_insert_run hr v (k := .x22) rfl]; exact h.x22
  x23 := by rw [get?_insert_run hr v (k := .x23) rfl]; exact h.x23
  x24 := by rw [get?_insert_run hr v (k := .x24) rfl]; exact h.x24
  x25 := by rw [get?_insert_run hr v (k := .x25) rfl]; exact h.x25
  x26 := by rw [get?_insert_run hr v (k := .x26) rfl]; exact h.x26
  x27 := by rw [get?_insert_run hr v (k := .x27) rfl]; exact h.x27
  x28 := by rw [get?_insert_run hr v (k := .x28) rfl]; exact h.x28
  x29 := by rw [get?_insert_run hr v (k := .x29) rfl]; exact h.x29
  x30 := by rw [get?_insert_run hr v (k := .x30) rfl]; exact h.x30
  x31 := by rw [get?_insert_run hr v (k := .x31) rfl]; exact h.x31

/-- The values `val` of the registers with the value `v` of the register `r`. -/
def updateVal (val : (r : Register) → RegisterType r) (r : Register) (v : RegisterType r) :
    (k : Register) → RegisterType k :=
  fun k => if h : r = k then h ▸ v else val k

theorem updateVal_self (val : (r : Register) → RegisterType r) (r : Register) (v : RegisterType r) :
    updateVal val r v r = v := by
  simp [updateVal]

theorem updateVal_ne {val : (r : Register) → RegisterType r} {r k : Register} (v : RegisterType r)
    (h : r ≠ k) : updateVal val r v k = val k := by
  simp [updateVal, h]

/-- The counters of the retired instructions are not registers of the environment `EnvH`. -/
theorem EnvH.withReg {S : SailState} {val : (r : Register) → RegisterType r} (e : EnvH S val)
    (r : Register) (hr : r = .minstret ∨ r = .minstret_increment) (v : RegisterType r) :
    EnvH (withReg S r v) (updateVal val r v) := by
  have ne : ∀ k, k ∈ [Register.elp, .misa, .cur_privilege, .mstatus, .mseccfg, .pmpcfg_n,
      .hart_state] → updateVal val r v k = val k := by
    intro k hk
    apply updateVal_ne
    rcases hr with rfl | rfl <;> simp at hk <;>
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  exact {
    get := fun k => by
      simp only [IntxRV.withReg, Std.ExtDHashMap.get?_insert]
      split
      · rename_i hk
        have := beq_iff_eq.mp hk
        subst this
        simp [updateVal]
      · rename_i hk
        rw [updateVal_ne v (fun h => hk (beq_iff_eq.mpr h)), e.get]
    elp := by rw [ne _ (by simp)]; exact e.elp
    misa_M := by rw [ne _ (by simp)]; exact e.misa_M
    priv := by rw [ne _ (by simp)]; exact e.priv
    priv_M := by rw [ne _ (by simp)]; exact e.priv_M
    mprv := by rw [ne _ (by simp)]; exact e.mprv
    pmm := by rw [ne _ (by simp)]; exact e.pmm
    pmp := by rw [ne _ (by simp)]; exact e.pmp
    active := by rw [ne _ (by simp)]; exact e.active
    mie := by rw [ne _ (by simp)]; exact e.mie }

theorem should_inc_minstret_M {S s : SailState} {val : (r : Register) → RegisterType r}
    {pc npc : BitVec 64} {x : Regs} (e : EnvH S val) (h : Inv S s pc npc x) :
    should_inc_minstret .Machine s = .ok (countsInstret val) s := by
  simp [should_inc_minstret, readReg_env e.toEnv h, isRunReg, LeanRV64D.readReg, countsInstret,
    bind, EStateM.bind, pure, EStateM.pure]

/-- No interrupt is pending to be taken in machine mode with `mstatus.MIE` clear. -/
theorem getPendingSet_M {S s : SailState} {val : (r : Register) → RegisterType r}
    {pc npc : BitVec 64} {x : Regs} (e : EnvH S val) (h : Inv S s pc npc x) :
    getPendingSet .Machine s = .ok none s := by
  have hr := readReg_env e.toEnv h
  cases hS : (_get_Misa_S (val .misa) == 1#1) <;>
  simp (config := { decide := true }) [getPendingSet, read_mip, external_interrupts_pending,
    currentlyEnabled, hartSupports, hr, isRunReg, LeanRV64D.readReg, e.mie, hS, bind,
    EStateM.bind, pure, EStateM.pure]

/-- No interrupt is taken in machine mode with `mstatus.MIE` clear. -/
theorem dispatchInterrupt_M {S s : SailState} {val : (r : Register) → RegisterType r}
    {pc npc : BitVec 64} {x : Regs} (e : EnvH S val) (h : Inv S s pc npc x) :
    dispatchInterrupt .Machine s = .ok none s := by
  simp [dispatchInterrupt, getPendingSet_M e h, bind, EStateM.bind, pure, EStateM.pure]

/-- The environment `EnvH` with another memory. -/
theorem EnvH.withMem {S : SailState} {val : (r : Register) → RegisterType r} (e : EnvH S val)
    (m : Mem) : EnvH { S with mem := m } val :=
  ⟨⟨⟨e.get, e.elp, e.misa_M, e.priv⟩, e.priv_M, e.mprv, e.pmm, e.pmp⟩, e.active, e.mie⟩

theorem codeOk_updateVal {val : (r : Register) → RegisterType r} {a : BitVec 64} (hc : CodeOk val a)
    {r : Register} (hr : r = .minstret ∨ r = .minstret_increment) (v : RegisterType r) :
    CodeOk (updateVal val r v) a := by
  have hp : updateVal val r v .pma_regions = val .pma_regions :=
    updateVal_ne v (by rcases hr with rfl | rfl <;> decide)
  have hh : updateVal val r v .htif_tohost_base = val .htif_tohost_base :=
    updateVal_ne v (by rcases hr with rfl | rfl <;> decide)
  exact ⟨⟨hc.half.aligned, hp ▸ hc.half.pma, hc.half.clint, hc.half.sig, hh ▸ hc.half.htif⟩,
    hp ▸ hc.exec⟩

theorem wordOk_updateVal {val : (r : Register) → RegisterType r} {a : BitVec 64} (hw : WordOk val a)
    {r : Register} (hr : r = .minstret ∨ r = .minstret_increment) (v : RegisterType r) :
    WordOk (updateVal val r v) a := by
  have hp : updateVal val r v .pma_regions = val .pma_regions :=
    updateVal_ne v (by rcases hr with rfl | rfl <;> decide)
  have hh : updateVal val r v .htif_tohost_base = val .htif_tohost_base :=
    updateVal_ne v (by rcases hr with rfl | rfl <;> decide)
  exact ⟨hw.aligned, hp ▸ hw.pma, hw.clint, hw.sig, hh ▸ hw.htif,
    ⟨hw.half_lo.aligned, hp ▸ hw.half_lo.pma, hw.half_lo.clint, hw.half_lo.sig,
      hh ▸ hw.half_lo.htif⟩,
    ⟨hw.half_hi.aligned, hp ▸ hw.half_hi.pma, hw.half_hi.clint, hw.half_hi.sig,
      hh ▸ hw.half_hi.htif⟩,
    fun j hj => ⟨hp ▸ (hw.byte j hj).pma, (hw.byte j hj).clint, (hw.byte j hj).sig,
      hh ▸ (hw.byte j hj).htif⟩⟩

/-- The state of the environment after a step of the hart: the memory `m`, and the counters of the
retired instructions. -/
def hartNext (S : SailState) (val : (r : Register) → RegisterType r) (m : Mem) : SailState :=
  let S1 := withReg { S with mem := m } .minstret_increment (countsInstret val)
  if countsInstret val then withReg S1 .minstret (BitVec.addInt (val .minstret) 1) else S1

/-- The values of the registers of the environment after a step of the hart. -/
def hartVal (val : (r : Register) → RegisterType r) : (r : Register) → RegisterType r :=
  let v1 := updateVal val .minstret_increment (countsInstret val)
  if countsInstret val then updateVal v1 .minstret (BitVec.addInt (val .minstret) 1) else v1

/-- A step of the hart of the Sail model (`try_step`) fetches the instruction at the program
counter from the memory and executes it as `execM`, and counts it in `minstret`. -/
theorem try_step_simM {S s : SailState} {val : (r : Register) → RegisterType r}
    {pc npc : BitVec 64} {x : Regs} {A : List (BitVec 64)} {i : instruction} {pc' : BitVec 64}
    {x' : Regs} {m' : Mem} (k : Nat) (e : EnvH S val)
    (hA : ∀ a ∈ A, WordOk val a ∧ Present S.mem a) (h : Inv S s pc npc x)
    (hpc : pc.toNat % 4 = 0) (hc : CodeOk val pc) (hb : ∀ j < 4, pc.toNat + j ∈ S.mem)
    (hrvc : NotRVC (memHalf S.mem pc.toNat))
    (hdec : ∀ (S1 s1 : SailState) (val1 : (r : Register) → RegisterType r) (npc1 : BitVec 64)
      (y : Regs), Env S1 val1 → Inv S1 s1 pc npc1 y →
        ext_decode (memHalf S.mem pc.toNat) s1 = .ok i s1)
    (hi : execM A i pc x S.mem = some (pc', x', m'))
    (ha : pc'.getLsbD 0 = false ∧ pc'.getLsbD 1 = false) :
    ∃ s', try_step k true s = .ok false s' ∧ Inv (hartNext S val m') s' pc' pc' x' := by
  have hm : s.mem = S.mem := by
    have := congrArg SequentialState.mem h.rest
    simpa using this
  rw [← hm] at hb hrvc hdec
  have hr := readReg_env e.toEnv h
  -- The count of the instruction.
  have h1 := h.withReg (r := .minstret_increment) rfl (countsInstret val)
  have e1 := e.withReg .minstret_increment (Or.inr rfl) (countsInstret val)
  have hr1 := readReg_env e1.toEnv h1
  -- The fetch, the decoding and the landing pad.
  have hf := fetch_M e1.toEnvM h1 hpc (codeOk_updateVal hc (Or.inr rfl) _) hb hrvc
  have hd := hdec _ _ _ npc x e1.toEnv h1
  have hlp : (is_landing_pad_expected () : SailM Bool)
      { s with regs := (s.regs.insert .minstret_increment (countsInstret val)) } =
      .ok false { s with regs := (s.regs.insert .minstret_increment (countsInstret val)) } := by
    simp (config := { decide := true }) [is_landing_pad_expected, hr1, isRunReg,
      LeanRV64D.readReg, e1.elp, landing_pad_bits_backwards, bind, EStateM.bind, pure,
      EStateM.pure]
  -- The execution.
  have h2 := h1.set_npc (pc + 4)
  obtain ⟨s3, hs3, h3⟩ := exec_simM e1.toEnvM
    (fun a ha => ⟨wordOk_updateVal (hA a ha).1 (Or.inr rfl) _, (hA a ha).2⟩) h2 hi ha
  have e3 := e1.withMem m'
  have hr3 := readReg_env e3.toEnv h3
  have h4 := h3.set_pc pc'
  have hr4 := readReg_env e3.toEnv h4
  have hpc4 : BitVec.addInt pc 4 = pc + 4 := by simp [Sail.BitVec.addInt]
  have hprivS : (PreSail.readReg Register.cur_privilege : SailM _) s = .ok .Machine s := by
    rw [hr _ rfl, e.priv_M]
  have hmi : updateVal val .minstret_increment (countsInstret val) .minstret = val .minstret :=
    updateVal_ne _ (by decide)
  refine ⟨if countsInstret val then
      { s3 with
        regs := ((s3.regs.insert .PC pc').insert .minstret (BitVec.addInt (val .minstret) 1)) }
    else { s3 with regs := s3.regs.insert .PC pc' }, ?_, ?_⟩
  · simp only [try_step, ext_pre_step_hook, LeanRV64D.readReg, LeanRV64D.writeReg, hprivS,
      should_inc_minstret_M e h, writeReg_ok, bind, EStateM.bind, pure, EStateM.pure]
    simp (config := { decide := true }) only [hr1, isRunReg, e1.active, run_hart_active,
      LeanRV64D.readReg, e1.priv_M, dispatchInterrupt_M e1 h1, hf, ext_fetch_hook, hd,
      get_config_print_instr, hlp, readReg_ok h1.pc, hpc4, writeReg_ok, Bool.false_and,
      Bool.false_eq_true, if_false, bind, EStateM.bind, pure, EStateM.pure, SailME.run,
      PreSailME.run, ExceptT.run, liftM, monadLift, MonadLift.monadLift, ExceptT.lift,
      ExceptT.bind, ExceptT.mk, ExceptT.bindCont, ExceptT.pure, Functor.map, EStateM.map]
    erw [hs3]
    simp (config := { decide := true }) only [RETIRE_SUCCESS, hr3, isRunReg, e3.active,
      hart_is_active, LeanRV64D.assert, PreSail.assert, tick_pc, LeanRV64D.readReg,
      LeanRV64D.writeReg, readReg_ok h3.npc, writeReg_ok, readReg_ok h4.pc, hr4, updateVal_self,
      updateVal_ne _ (show Register.minstret_increment ≠ .minstret by decide), get_config_rvfi,
      ↓reduceIte, if_true, if_false, ext_post_step_hook, instret_callback, pc_write_callback,
      Bool.true_and,
      bind, EStateM.bind, pure, EStateM.pure, SailME.run, PreSailME.run, ExceptT.run, liftM,
      monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
      ExceptT.pure, Functor.map, EStateM.map]
    cases hcnt : countsInstret val <;>
    simp [hr4, isRunReg, hmi, writeReg_ok, bind, EStateM.bind, pure, EStateM.pure]
  · cases hcnt : countsInstret val <;> rw [hcnt] at h4 <;>
      simp only [hartNext, hcnt, Bool.false_eq_true, ↓reduceIte]
    · exact h4
    · exact h4.withReg (r := .minstret) rfl _

/-! ## The code in the memory -/

/-- The words of `code` are in the memory `m` at the address `base`, little-endian. -/
def CodeIn (m : Mem) (base : Nat) (code : Code) : Prop :=
  ∀ j (hj : j < code.length), (∀ t < 4, base + 4 * j + t ∈ m) ∧ memHalf m (base + 4 * j) = code[j]

/-- A store of a byte outside the code keeps it. -/
theorem codeIn_insert {m : Mem} {base : Nat} {code : Code} (h : CodeIn m base code) {q : Nat}
    (hq : q < base ∨ base + 4 * code.length ≤ q) (v : BitVec 8) :
    CodeIn (m.insert q v) base code := by
  intro j hj
  obtain ⟨hp, hw⟩ := h j hj
  refine ⟨fun t ht => Std.ExtHashMap.mem_insert.mpr (Or.inr (hp t ht)), ?_⟩
  have ne : ∀ t < 4, (q == base + 4 * j + t) = false := by
    intro t ht; simp only [beq_eq_false_iff_ne]; omega
  rw [← hw]
  simp only [memHalf, Std.ExtHashMap.getD_insert, ne 0 (by omega), ne 1 (by omega),
    ne 2 (by omega), ne 3 (by omega), Nat.add_zero, Bool.false_eq_true, if_false]
  have e0 := ne 0 (by omega)
  simp only [Nat.add_zero] at e0
  simp only [e0, Bool.false_eq_true, if_false]

/-- A store of a word outside the code keeps it. -/
theorem codeIn_memStore {m : Mem} {base : Nat} {code : Code} (h : CodeIn m base code) {a : Nat}
    (ha : a + 8 ≤ base ∨ base + 4 * code.length ≤ a) (v : BitVec 64) :
    CodeIn (memStore m a v) base code := by
  unfold memStore
  repeat (first | apply codeIn_insert _ (by omega) | exact h)

/-- `execM` stores only to the words of `A`, so it keeps the code outside them. -/
theorem execM_codeIn {A : List (BitVec 64)} {i : instruction} {pc pc' : BitVec 64} {x x' : Regs}
    {m m' : Mem} {base : Nat} {code : Code} (hi : execM A i pc x m = some (pc', x', m'))
    (hA : ∀ a ∈ A, a.toNat + 8 ≤ base ∨ base + 4 * code.length ≤ a.toNat)
    (h : CodeIn m base code) : CodeIn m' base code := by
  unfold execM at hi
  split at hi
  · split at hi
    · cases hi; exact h
    · split at hi
      · cases hi; exact h
      · split at hi
        · cases hi; exact h
        · split at hi
          · cases hi; exact h
          · split at hi
            · cases hi; exact h
            · contradiction
  · split at hi
    · rename_i hc
      cases hi; exact codeIn_memStore h (hA _ hc.2) _
    · split at hi
      · rename_i imm rs2 rs1 w _ hc
        cases hi
        have hw := hA _ hc.2
        have hn := toNat_and_not7 (x.get rs1 + sign_extend (m := 64) imm)
        have := Nat.mod_lt (x.get rs1 + sign_extend (m := 64) imm).toNat (show 8 > 0 by decide)
        exact codeIn_insert h (by omega) _
      · contradiction
  · obtain ⟨_, _, h'⟩ := Option.map_eq_some_iff.mp hi
    cases h'; exact h

/-- The instruction that `fetch` gets from the code is in the memory at the program counter. -/
theorem fetch_codeIn {code : Code} {m : Mem} {base pc : BitVec 64} {w : BitVec 32}
    (h : CodeIn m base.toNat code) (hn : base.toNat + 4 * code.length ≤ 2 ^ 64)
    (hf : fetch code base pc = some w) :
    ∃ j, j < code.length ∧ pc.toNat = base.toNat + 4 * j ∧ (∀ t < 4, pc.toNat + t ∈ m) ∧
      memHalf m pc.toNat = w := by
  have ha := fetch_aligned hf
  unfold fetch at hf
  rw [if_pos ha] at hf
  obtain ⟨hj, hw⟩ := List.getElem?_eq_some_iff.mp hf
  have hpc : pc.toNat = base.toNat + 4 * ((pc - base) >>> 2).toNat := by
    have h4 := (aligned_iff _).mp ha
    have hs : ((pc - base) >>> 2).toNat = (pc - base).toNat / 4 := by
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rw [hs]
    have hd : (pc - base).toNat = (pc.toNat + (2 ^ 64 - base.toNat)) % 2 ^ 64 := by
      rw [BitVec.toNat_sub]; omega
    have hj' := hj
    rw [hs] at hj'
    have hp := pc.isLt
    have hb := base.isLt
    omega
  obtain ⟨hp, hm⟩ := h _ hj
  refine ⟨_, hj, hpc, fun t ht => hpc ▸ hp t ht, ?_⟩
  rw [hpc, hm, hw]

/-! ## The environment after a step -/

theorem countsInstret_hartVal (val : (r : Register) → RegisterType r) :
    countsInstret (hartVal val) = countsInstret val := by
  unfold hartVal countsInstret
  split <;> simp [updateVal_ne _ (show Register.minstret_increment ≠ .mcountinhibit by decide),
    updateVal_ne _ (show Register.minstret_increment ≠ .minstretcfg by decide),
    updateVal_ne _ (show Register.minstret ≠ .mcountinhibit by decide),
    updateVal_ne _ (show Register.minstret ≠ .minstretcfg by decide)]

theorem codeOk_hartVal {val : (r : Register) → RegisterType r} {a : BitVec 64}
    (hc : CodeOk val a) : CodeOk (hartVal val) a := by
  unfold hartVal
  have h1 := codeOk_updateVal hc (Or.inr rfl) (countsInstret val)
  split
  · exact codeOk_updateVal h1 (Or.inl rfl) _
  · exact h1

theorem wordOk_hartVal {val : (r : Register) → RegisterType r} {a : BitVec 64}
    (hw : WordOk val a) : WordOk (hartVal val) a := by
  unfold hartVal
  have h1 := wordOk_updateVal hw (Or.inr rfl) (countsInstret val)
  split
  · exact wordOk_updateVal h1 (Or.inl rfl) _
  · exact h1

theorem envH_hartNext {S : SailState} {val : (r : Register) → RegisterType r} (e : EnvH S val)
    (m : Mem) : EnvH (hartNext S val m) (hartVal val) := by
  unfold hartNext hartVal
  have e1 := (e.withMem m).withReg .minstret_increment (Or.inr rfl) (countsInstret val)
  split
  · exact e1.withReg .minstret (Or.inl rfl) _
  · exact e1

theorem hartNext_mem (S : SailState) (val : (r : Register) → RegisterType r) (m : Mem) :
    (hartNext S val m).mem = m := by
  unfold hartNext; split <;> rfl

/-! ## The run of the hart -/

/-- `j` steps of the hart of the Sail model, with the step number `k` of `loop` (for its output
only). -/
noncomputable def hartRun (k : Nat) : Nat → SailM Unit
  | 0 => pure ()
  | j + 1 => do
    let _ ← try_step k true
    hartRun k j

/-- The environment `S'` is the environment `S` (with the values `val` of its registers) after `j`
retired instructions with the memory `m`: the same but the memory, `minstret`, advanced by `j` if
the hart counts the instructions, and `minstret_increment`, set by a step. -/
structure Retired (S S' : SailState) (val : (r : Register) → RegisterType r) (m : Mem) (j : Nat) :
    Prop where
  mem : S'.mem = m
  rest : { S' with regs := S.regs, mem := S.mem } = S
  other : ∀ r, r ≠ .minstret → r ≠ .minstret_increment → S'.regs.get? r = S.regs.get? r
  inc : S'.regs.get? .minstret_increment =
    if j = 0 then S.regs.get? .minstret_increment else some (countsInstret val)
  instret : S'.regs.get? .minstret =
    some (if countsInstret val then BitVec.addInt (val .minstret) j else val .minstret)

theorem Retired.zero {S : SailState} {val : (r : Register) → RegisterType r} (e : Env S val) :
    Retired S S val S.mem 0 where
  mem := rfl
  rest := rfl
  other _ _ _ := rfl
  inc := by simp
  instret := by rw [e.get]; split <;> simp [addInt_zero]

theorem addInt_addInt (v : BitVec 64) (a b : Int) :
    BitVec.addInt (BitVec.addInt v a) b = BitVec.addInt v (a + b) := by
  simp only [Sail.BitVec.addInt, BitVec.add_assoc, BitVec.ofInt_add]

theorem hartVal_minstret (val : (r : Register) → RegisterType r) :
    hartVal val .minstret =
      if countsInstret val then BitVec.addInt (val .minstret) 1 else val .minstret := by
  unfold hartVal
  split
  · simp [updateVal_self]
  · simp [updateVal_ne _ (show Register.minstret_increment ≠ .minstret by decide)]

/-- A step of the hart and then `j`. -/
theorem Retired.step {S S2 : SailState} {val : (r : Register) → RegisterType r} {m1 m2 : Mem}
    {j : Nat} (e : Env S val) (h : Retired (hartNext S val m1) S2 (hartVal val) m2 j) :
    Retired S S2 val m2 (j + 1) := by
  have hi : (hartNext S val m1).regs.get? .minstret_increment = some (countsInstret val) := by
    unfold hartNext; split <;> simp [withReg, Std.ExtDHashMap.get?_insert]
  have hm : (hartNext S val m1).regs.get? .minstret =
      some (if countsInstret val then BitVec.addInt (val .minstret) 1 else val .minstret) := by
    unfold hartNext
    split <;> rename_i hc <;> simp [withReg, Std.ExtDHashMap.get?_insert, hc, e.get]
  have ho : ∀ r, r ≠ .minstret → r ≠ .minstret_increment →
      (hartNext S val m1).regs.get? r = S.regs.get? r := by
    intro r h1 h2
    unfold hartNext
    split <;> simp [withReg, Std.ExtDHashMap.get?_insert, Ne.symm h1, Ne.symm h2]
  exact {
    mem := h.mem
    rest := by
      have h2 := h.rest
      unfold hartNext at h2
      cases S; cases S2
      split at h2 <;> simp only [withReg, SequentialState.mk.injEq] at h2 ⊢ <;> simp_all
    other := fun r h1 h2 => (h.other r h1 h2).trans (ho r h1 h2)
    inc := by
      rw [h.inc, countsInstret_hartVal]
      split <;> simp [hi]
    instret := by
      rw [h.instret, countsInstret_hartVal, hartVal_minstret]
      split
      · simp only [addInt_addInt, Option.some.injEq]
        congr 1
        omega
      · rfl }

theorem fetch_mem {α : Type} {code : List α} {base pc : BitVec 64} {w : α}
    (h : fetch code base pc = some w) : w ∈ code := by
  unfold fetch at h
  split at h
  · exact List.mem_of_getElem? h
  · contradiction

/-- The hart of the Sail model runs the code as `arunM`: from the code in the memory, with the
interrupts off, counting the retired instructions. -/
theorem hart_simM {code : Code} {prog : List instruction} (hd : Decodes code prog)
    (hrvc : ∀ w ∈ code, NotRVC w) {A : List (BitVec 64)} {base ret : BitVec 64}
    (hb : base &&& 3 = 0) (hr : ret &&& 3 = 0) (hn : base.toNat + 4 * code.length ≤ 2 ^ 64)
    (hout : ∀ a ∈ A, a.toNat + 8 ≤ base.toNat ∨ base.toNat + 4 * code.length ≤ a.toNat)
    (k : Nat) :
    ∀ (n : Nat) (S s : SailState) (val : (r : Register) → RegisterType r) (pc npc : BitVec 64)
      (x x' : Regs) (m' : Mem),
      EnvH S val → (∀ a ∈ A, WordOk val a ∧ Present S.mem a) → CodeIn S.mem base.toNat code →
      (∀ j < code.length, CodeOk val (base + BitVec.ofNat 64 (4 * j))) → Inv S s pc npc x →
      arunM A prog base ret n pc x S.mem = some (x', m') →
      ∃ j s' S' npc', hartRun k j s = .ok () s' ∧ Retired S S' val m' j ∧
        Inv S' s' ret npc' x' := by
  intro n
  induction n with
  | zero => intro S s val pc npc x x' m' _ _ _ _ _ ha; simp [arunM] at ha
  | succ n ih =>
    intro S s val pc npc x x' m' e hA hc hco h ha
    unfold arunM at ha
    by_cases hpr : pc = ret
    · rw [if_pos hpr] at ha
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj ha)
      subst hpr
      exact ⟨0, s, S, npc, rfl, Retired.zero e.toEnv, h⟩
    · rw [if_neg hpr] at ha
      split at ha
      · contradiction
      · rename_i i hf
        split at ha
        · contradiction
        · rename_i pc1 x1 m1 hi
          obtain ⟨w, hw, hdec⟩ := fetch_decodes hd hf
          obtain ⟨j, hj, hpcj, hpres, hmw⟩ := fetch_codeIn hc hn hw
          have hb4 := (aligned_iff base).mp hb
          have hpc4 : pc.toNat % 4 = 0 := by omega
          have hpcb : pc = base + BitVec.ofNat 64 (4 * j) := by
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_add, BitVec.toNat_ofNat, hpcj]
            omega
          obtain ⟨s1, hs1, h1⟩ := try_step_simM k e hA h hpc4 (hpcb ▸ hco j hj) hpres
            (hmw ▸ hrvc w (fetch_mem hw)) (hmw ▸ hdec) hi (arunM_aligned hb hr ha)
          obtain ⟨j', s', S', npc', hrun, hret, h'⟩ := ih (hartNext S val m1) s1 (hartVal val)
            pc1 pc1 x1 x' m' (envH_hartNext e m1)
            (fun a ha => ⟨wordOk_hartVal (hA a ha).1, by
              rw [hartNext_mem]; exact execM_present hi (fun a ha => (hA a ha).2) a ha⟩)
            (by rw [hartNext_mem]; exact execM_codeIn hi hout hc)
            (fun j hj => codeOk_hartVal (hco j hj)) h1 (by rw [hartNext_mem]; exact ha)
          refine ⟨j' + 1, s', S', npc', ?_, Retired.step e.toEnv hret, h'⟩
          simp [hartRun, hs1, hrun, bind, EStateM.bind]

end IntxRV
