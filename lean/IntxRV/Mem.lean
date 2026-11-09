import IntxRV.Run
/-!
# The memory

Loads and stores of aligned 64-bit words in the Sail model: `exec_load` and `exec_store` show
that `ld` and `sd` read and write the 8 bytes of the word in the memory of the state (the `mem`
byte map), little-endian, and change nothing else. They evaluate the memory access of the Sail
model (`vmem_read`, `vmem_write`): the address translation, the PMP and PMA checks and the
memory-mapped devices. The environment `EnvM` makes these pass through: machine mode without
`MPRV`, no pointer masking, no PMP entries enabled. `WordOk` says that a word is ordinary memory.
-/

/-! ## Loops of the Sail model -/

/-- A loop over an `IntRange` whose body leaves the state unchanged and continues. -/
theorem IntRange.loop_yield {ε ε' σ β : Type} (r : IntRange) (b : β)
    (f : (i : Int) → i ∈ r → β → ExceptT ε (EStateM ε' σ) (ForInStep β)) (s : σ)
    (hf : ∀ i h, f i h b s = .ok (.ok (.yield b)) s) :
    ∀ (n : Nat) (i : Int) hs,
      (if r.step > 0 then (r.stop - i + 1).toNat else (i - r.stop + 1).toNat) = n →
      (IntRange.forIn'.loop r f b i hs : ExceptT ε (EStateM ε' σ) β) s = .ok (.ok b) s := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro i hs hn
    rw [IntRange.forIn'.loop]
    by_cases hm : i ∈ r
    · rw [dif_pos hm]
      have hsp := r.step_pos
      have := ih _ ?_ (i + r.step) (by rw [Int.add_comm, Int.add_sub_assoc]; simp_all) rfl
      · simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, EStateM.bind] at this ⊢
        rw [hf]; simpa using this
      · subst hn
        simp only [Membership.mem] at hm
        split <;> split at hm <;> omega
    · rw [dif_neg hm]; rfl

theorem IntRange.forIn_yield {ε ε' σ β : Type} (r : IntRange) (b : β)
    (f : Int → β → ExceptT ε (EStateM ε' σ) (ForInStep β)) (s : σ)
    (hf : ∀ i, i ∈ r → f i b s = .ok (.ok (.yield b)) s) :
    (forIn r b f : ExceptT ε (EStateM ε' σ) β) s = .ok (.ok b) s :=
  IntRange.loop_yield r b (fun i _ b => f i b) s (fun i h => hf i h) _ _ _ rfl

open Sail Sail.ConcurrencyInterfaceV1 PreSail
open LeanRV64D LeanRV64D.Functions LeanRV64D.Defs

-- The memory accesses are evaluated with simp, and some lemmas apply to loads or stores only.
set_option linter.unusedSimpArgs false

namespace IntxRV

/-- The environment of the functions with memory: `Env` in machine mode, with `mstatus.MPRV` clear
(the accesses are not translated), no pointer masking (`mseccfg.PMM`) and no PMP entry enabled. -/
structure EnvM (S : SailState) (val : (r : Register) → RegisterType r) : Prop
    extends Env S val where
  priv_M : val .cur_privilege = .Machine
  mprv : _get_Mstatus_MPRV (val .mstatus) = 0#1
  pmm : _get_Seccfg_PMM (val .mseccfg) = 0#2
  pmp : ∀ i : Nat, _get_Pmpcfg_ent_A (val .pmpcfg_n)[i]! = 0#2

theorem getElem!_int {α : Type} [Inhabited α] {n : Nat} (v : Vector α n) (i : Int) :
    v[i]! = v[i.toNat]! := rfl

/-! ## The memory access of the Sail model in `EnvM` -/

/-- The address of a load: no pointer masking. -/
theorem data_addr {S s : SailState} {val : (r : Register) → RegisterType r} {pc npc : BitVec 64}
    {x : Regs} (e : EnvM S val) (h : Inv S s pc npc x) (rs : BitVec 5) (off : BitVec 64) :
    get_transformed_data_addr (.Regidx rs) off (.Load .Data) 8 s =
      .ok (.Ext_DataAddr_OK (.Virtaddr (x.get rs + off))) s := by
  simp (config := { decide := true }) [get_transformed_data_addr, ext_data_get_addr,
    rX_bits_inv h, transform_effective_address, effectivePrivilege, readReg_env e.toEnv h,
    isRunReg, LeanRV64D.readReg, e.mprv, e.priv_M, get_pmlen, is_pmm_applicable, get_pmm, e.pmm,
    translationMode, pm_transform_PA, pmm_mode_backwards, bind, EStateM.bind, pure, EStateM.pure]
  simp [Functions.xlen, Sail.BitVec.extractLsb, zero_extend, Sail.BitVec.zeroExtend]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb_toNat]

/-- No address translation in machine mode without `MPRV`. -/
theorem translate_M {S s : SailState} {val : (r : Register) → RegisterType r} {pc npc : BitVec 64}
    {x : Regs} (e : EnvM S val) (h : Inv S s pc npc x) (a : BitVec 64) (acc : MemoryAccessType
        mem_payload)
    (hacc : acc = .Load .Data ∨ acc = .Store .Data) :
    translateAddr (.Virtaddr a) acc s = .ok (.Ok (.Physaddr a, .PBMT_PMA, ())) s := by
  rcases hacc with rfl | rfl <;>
  simp (config := { decide := true }) [translateAddr, effectivePrivilege, readReg_env e.toEnv h,
    isRunReg, LeanRV64D.readReg, e.mprv, e.priv_M, translationMode, is_shadow_stack_access,
    bind, EStateM.bind, pure, EStateM.pure, SailME.run, PreSailME.run, ExceptT.run, liftM,
    monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
    ExceptT.pure, Functor.map, EStateM.map, zero_extend, Sail.BitVec.zeroExtend, bits_of_virtaddr,
    init_ext_ptw]

/-- The PMP check passes in machine mode with no PMP entry enabled. -/
theorem pmp_M {S s : SailState} {val : (r : Register) → RegisterType r} {pc npc : BitVec 64}
    {x : Regs} (e : EnvM S val) (h : Inv S s pc npc x) (a : physaddr) (w : Nat)
    (acc : MemoryAccessType mem_payload) :
    pmpCheck a w acc .Machine s = .ok none s := by
  simp (config := { decide := true }) [pmpCheck, readReg_env e.toEnv h, isRunReg,
    LeanRV64D.readReg, pmpMatchAddr, e.pmp, sys_pmp_count, pmpReadAddrReg,
    bind, EStateM.bind, pure, EStateM.pure, SailME.run, PreSailME.run, ExceptT.run, liftM,
    monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
    ExceptT.pure, Functor.map, EStateM.map]
  rw [IntRange.forIn_yield]
  · rfl
  · intro i hi
    have hr := readReg_env e.toEnv h
    split <;>
    simp (config := { decide := true }) [hr, isRunReg, e.pmp, getElem!_int,
      pmpAddrMatchType_encdec_backwards, Sail.BitVec.access, bind, EStateM.bind, pure,
      EStateM.pure, ExceptT.bindCont,
      EStateM.map]

/-- The 8 bytes at `a` in `m`, little-endian. -/
def memWord (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) : BitVec 64 :=
  m.getD (a + 7) 0 ++ m.getD (a + 6) 0 ++ m.getD (a + 5) 0 ++ m.getD (a + 4) 0 ++
    m.getD (a + 3) 0 ++ m.getD (a + 2) 0 ++ m.getD (a + 1) 0 ++ m.getD a 0

/-- The 4 bytes at `a` in `m`, little-endian. -/
def memHalf (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) : BitVec 32 :=
  m.getD (a + 3) 0 ++ m.getD (a + 2) 0 ++ m.getD (a + 1) 0 ++ m.getD a 0

/-- The aligned 4-byte word at `a` is ordinary readable memory: in a readable PMA region and not
in a memory-mapped device. -/
structure HalfOk (val : (r : Register) → RegisterType r) (a : BitVec 64) : Prop where
  aligned : a.toNat % 4 = 0
  pma : ∃ r, matching_pma_region (val .pma_regions) (.Physaddr a) 4 = some r ∧
    r.attributes.readable = true
  clint : ¬ (plat_clint_base.toNat ≤ a.toNat ∧ a.toNat + 4 ≤ plat_clint_base.toNat +
      plat_clint_size.toNat)
  sig : ¬ (plat_sig_base.toNat ≤ a.toNat ∧ a.toNat + 4 ≤ plat_sig_base.toNat + plat_sig_size.toNat)
  htif : ∀ b, val .htif_tohost_base = some b →
    (zopz0zI_u a (BitVec.addInt b htif_tohost_size) && zopz0zK_u (BitVec.addInt a 4) b) = false

/-- The aligned 8-byte word at `a` is ordinary memory: in a PMA region that is readable and
writable, and not in a memory-mapped device. Its two 4-byte halves are ordinary readable memory
too (the PMA region of a 4-byte access is the first one that covers it, which may differ). -/
structure WordOk (val : (r : Register) → RegisterType r) (a : BitVec 64) : Prop where
  aligned : a.toNat % 8 = 0
  pma : ∃ r, matching_pma_region (val .pma_regions) (.Physaddr a) 8 = some r ∧
    r.attributes.readable = true ∧ r.attributes.writable = true
  clint : ¬ (plat_clint_base.toNat ≤ a.toNat ∧ a.toNat + 8 ≤ plat_clint_base.toNat +
      plat_clint_size.toNat)
  sig : ¬ (plat_sig_base.toNat ≤ a.toNat ∧ a.toNat + 8 ≤ plat_sig_base.toNat + plat_sig_size.toNat)
  htif : ∀ b, val .htif_tohost_base = some b →
    (zopz0zI_u a (BitVec.addInt b htif_tohost_size) && zopz0zK_u (BitVec.addInt a 8) b) = false
  half_lo : HalfOk val a
  half_hi : HalfOk val (a + 4#64)

theorem addInt_zero (a : BitVec 64) : BitVec.addInt a 0 = a := by
  simp [Sail.BitVec.addInt]

theorem clint_base_toNat : BitVec.toNat plat_clint_base = 0x2000000 := by decide
theorem clint_size_toNat : BitVec.toNat plat_clint_size = 0xc0000 := by decide
theorem sig_base_toNat : BitVec.toNat plat_sig_base = 0xc000000 := by decide
theorem sig_size_toNat : BitVec.toNat plat_sig_size = 0x20 := by decide
theorem clint_base_toNat' : BitVec.toNat (w := 64) plat_clint_base = 0x2000000 := by decide
theorem clint_size_toNat' : BitVec.toNat (w := 64) plat_clint_size = 0xc0000 := by decide
theorem sig_base_toNat' : BitVec.toNat (w := 64) plat_sig_base = 0xc000000 := by decide
theorem sig_size_toNat' : BitVec.toNat (w := 64) plat_sig_size = 0x20 := by decide

/-- An ordinary word is not in a memory-mapped device. -/
theorem mmio_M {S s : SailState} {val : (r : Register) → RegisterType r} {pc npc : BitVec 64}
    {x : Regs} (e : EnvM S val) (h : Inv S s pc npc x) (a : BitVec 64) (ha : WordOk val a) :
    within_mmio_readable (.Physaddr a) 8 s = .ok false s ∧
      within_mmio_writable (.Physaddr a) 8 s = .ok false s := by
  have hr := readReg_env e.toEnv h
  have hc := ha.clint
  have hs := ha.sig
  have hh := ha.htif
  constructor <;>
  simp (config := { decide := true }) [within_mmio_readable, within_mmio_writable, within_clint,
    within_sig, within_htif_readable, within_htif_writable, get_config_rvfi, hr, isRunReg,
    BitVec.toNatInt, bind, EStateM.bind, pure, EStateM.pure] <;>
  (simp only [clint_base_toNat, clint_size_toNat, sig_base_toNat, sig_size_toNat,
      clint_base_toNat', clint_size_toNat', sig_base_toNat', sig_size_toNat'] at hc hs ⊢
   cases hv : val .htif_tohost_base with
   | none => simp [pure, EStateM.pure]; omega
   | some b => simp [hh _ hv, pure, EStateM.pure]; omega)

theorem updateSubrange_all (x v : BitVec 64) : BitVec.updateSubrange x 63 0 v = v := by
  simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange']
  ext i hi
  simp

theorem read_ram_ok (s : SailState) (a : BitVec 64) (hb : ∀ k < 8, a.toNat + k ∈ s.mem) :
    Functions.read_ram .Read_plain (.Physaddr a) 8 false s = .ok (memWord s.mem a.toNat, ()) s := by
  have h0 := hb 0 (by omega)
  have h1 := hb 1 (by omega)
  have h2 := hb 2 (by omega)
  have h3 := hb 3 (by omega)
  have h4 := hb 4 (by omega)
  have h5 := hb 5 (by omega)
  have h6 := hb 6 (by omega)
  have h7 := hb 7 (by omega)
  simp only [Nat.add_zero] at h0
  simp [Functions.read_ram, sail_mem_read, readBytes, readByte, memWord,
    Std.ExtHashMap.getElem_eq_getD (fallback := 0#8), h0, h1, h2, h3, h4, h5, h6, h7,
    get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure,
    Nat.add_assoc]

theorem mem_read_M {S s : SailState} {val : (r : Register) → RegisterType r} {pc npc : BitVec 64}
    {x : Regs} (e : EnvM S val) (h : Inv S s pc npc x) (a : BitVec 64) (ha : WordOk val a)
    (hb : ∀ k < 8, a.toNat + k ∈ s.mem) :
    mem_read (.Load .Data) .PBMT_PMA (.Physaddr a) 8 false false false s =
      .ok (.Ok (memWord s.mem a.toNat)) s := by
  have hr := readReg_env e.toEnv h
  obtain ⟨r, hm, hrd, hwr⟩ := ha.pma
  have hal : (BitVec.toNatInt a).tmod 8 = 0 := by
    have := ha.aligned
    simp only [BitVec.toNatInt, Int.ofNat_eq_natCast]
    rw [Int.tmod_eq_emod_of_nonneg (by omega)]
    omega
  simp (config := { decide := true }) [hal, LeanRV64D.assert, PreSail.assert, Functions.not,
    mem_read, mem_read_priv, mem_read_priv_meta, checked_mem_read,
    check_pma_with_pmp_priority, pmp_M e h, pmaCheck, hm, hrd, override_PMA, mag_pma_check,
    is_aligned_paddr, is_mag_applicable_access, effectivePrivilege, hr, isRunReg,
    LeanRV64D.readReg, e.mprv, e.priv_M, read_ram_ok s a hb, updateSubrange_all,
    split_misaligned, misaligned_order, untilFuelM, untilFuelM.go, (mmio_M e h a ha).1,
    addInt_zero, bits_of_physaddr, read_kind_of_flags, MemoryOpResult_drop_meta,
    bind, EStateM.bind, pure, EStateM.pure, SailME.run, PreSailME.run, ExceptT.run, liftM,
    monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
    ExceptT.pure, Functor.map, EStateM.map]
theorem and7_of_aligned {a : BitVec 64} (ha : a.toNat % 8 = 0) : a &&& 7#64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (7#64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simpa using ha

/-- An aligned word does not cross a page. -/
theorem split_page (s : SailState) (a : BitVec 64) (ha : a.toNat % 8 = 0) :
    (split_on_page_boundary a 8 : SailM _) s = .ok (8, 0) s := by
  have h7 : BitVec.subInt (BitVec.addInt a ((8 : Nat) : Int)) 1 = a ||| 7#64 := by
    rw [← BitVec.add_eq_or_of_and_eq_zero _ _ (and7_of_aligned ha)]
    simp [Sail.BitVec.subInt, Sail.BitVec.addInt]
    bv_omega
  have hc : ∀ M : BitVec 64, (∀ i < 3, M.getLsbD i = false) →
      a &&& M = (a ||| 7#64) &&& M := by
    intro M hM
    ext i hi
    simp only [BitVec.getElem_and, BitVec.getElem_or]
    by_cases h3 : i < 3
    · have := hM i h3
      simp only [BitVec.getLsbD_eq_getElem hi] at this
      simp [this]
    · have : (7#64)[i] = false := by
        rw [← BitVec.getLsbD_eq_getElem]
        simp only [BitVec.getLsbD_ofNat]
        simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
        rw [Nat.div_eq_of_lt (by
          have : 2 ^ 3 ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
          omega)]
        simp
      simp [this]
  simp only [split_on_page_boundary, Sail.BitVec.length, h7]
  rw [if_pos]
  · rfl
  · simp only [beq_iff_eq]
    apply hc
    intro i hi
    simp [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', zeros, Functions.pagesize_bits]
    intro h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> simp at h

theorem sign_extend_64 (v : BitVec 64) : sign_extend (m := 64) v = v := by
  simp [sign_extend, Sail.BitVec.signExtend]

/-- `ld rd, imm(rs1)` of an ordinary word present in the memory reads its 8 bytes into `rd`. -/
theorem exec_load {S s : SailState} {val : (r : Register) → RegisterType r} {pc npc : BitVec 64}
    {x : Regs} (e : EnvM S val) (h : Inv S s pc npc x) (imm : BitVec 12) (rs1 rd : BitVec 5)
    (ha : WordOk val (x.get rs1 + sign_extend (m := 64) imm))
    (hb : ∀ k < 8, (x.get rs1 + sign_extend (m := 64) imm).toNat + k ∈ s.mem) :
    ∃ s', execute (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8)) s = .ok RETIRE_SUCCESS s' ∧
      Inv S s' pc npc (x.set rd (memWord s.mem (x.get rs1 + sign_extend (m := 64) imm).toNat)) := by
  obtain ⟨s', hs,
      hi⟩ := wX_bits_inv h rd (memWord s.mem (x.get rs1 + sign_extend (m := 64) imm).toNat)
  refine ⟨s', ?_, hi⟩
  have hr := readReg_env e.toEnv h
  show execute_LOAD _ _ _ _ _ s = _
  have hal : is_aligned_vaddr (.Virtaddr (x.get rs1 + sign_extend (m := 64) imm)) 8 = true := by
    have := ha.aligned
    simp only [is_aligned_vaddr, BitVec.toNatInt, beq_iff_eq, Int.ofNat_eq_natCast]
    rw [Int.tmod_eq_emod_of_nonneg (by omega)]
    omega
  simp (config := { decide := true }) [execute_LOAD, vmem_read, data_addr e h, vmem_read_addr,
    LeanRV64D.assert, PreSail.assert, Functions.not, hal, bits_of_virtaddr,
    split_page s _ ha.aligned, effectivePrivilege, hr, isRunReg, LeanRV64D.readReg, e.mprv,
    e.priv_M, translationMode, translate_and_read_value, translate_M e h _ _ (.inl rfl),
    mem_read_M e h _ ha hb, updateSubrange_all, extend_value, sign_extend_64, hs,
    -BitVec.toNat_add,
    bind, EStateM.bind, pure, EStateM.pure, SailME.run, PreSailME.run, ExceptT.run, liftM,
    monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
    ExceptT.pure, Functor.map, EStateM.map]

/-- The memory `m` with the 8 bytes of `v` stored at `a`, little-endian. -/
def memStore (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (v : BitVec 64) :
    Std.ExtHashMap Nat (BitVec 8) :=
  ((((((((m.insert a (v.extractLsb' 0 8)).insert (a + 1) (v.extractLsb' 8 8)).insert (a + 2)
    (v.extractLsb' 16 8)).insert (a + 3) (v.extractLsb' 24 8)).insert (a + 4)
    (v.extractLsb' 32 8)).insert (a + 5) (v.extractLsb' 40 8)).insert (a + 6)
    (v.extractLsb' 48 8)).insert (a + 7) (v.extractLsb' 56 8))

theorem extractLsb_63 (v : BitVec 64) : Sail.BitVec.extractLsb v 63 0 = v := by
  apply BitVec.eq_of_toNat_eq
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb_toNat]
  exact v.isLt

theorem write_ram_ok (s : SailState) (a : BitVec 64) (v : BitVec 64) (me : Unit) :
    Functions.write_ram .Write_plain (.Physaddr a) 8 v me s =
      .ok true { s with mem := memStore s.mem a.toNat v } := by
  simp [Functions.write_ram, sail_mem_write, writeBytes, writeByte, memStore, List.ofFn,
    Fin.foldr, Fin.foldr.loop, List.forM, modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet, bind, EStateM.bind, pure, EStateM.pure]
/-- The address of a store: no pointer masking. -/
theorem data_addr_store {S s : SailState} {val : (r : Register) → RegisterType r}
    {pc npc : BitVec 64} {x : Regs} (e : EnvM S val) (h : Inv S s pc npc x) (rs : BitVec 5)
    (off : BitVec 64) :
    get_transformed_data_addr (.Regidx rs) off (.Store .Data) 8 s =
      .ok (.Ext_DataAddr_OK (.Virtaddr (x.get rs + off))) s := by
  simp (config := { decide := true }) [get_transformed_data_addr, ext_data_get_addr,
    rX_bits_inv h, transform_effective_address, effectivePrivilege, readReg_env e.toEnv h,
    isRunReg, LeanRV64D.readReg, e.mprv, e.priv_M, get_pmlen, is_pmm_applicable, get_pmm, e.pmm,
    translationMode, pm_transform_PA, pmm_mode_backwards, bind, EStateM.bind, pure, EStateM.pure]
  simp [Functions.xlen, Sail.BitVec.extractLsb, zero_extend, Sail.BitVec.zeroExtend]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb_toNat]

/-- `sd rs2, imm(rs1)` of an ordinary word writes the 8 bytes of `rs2` to the memory and changes
nothing else. -/
theorem exec_store {S s : SailState} {val : (r : Register) → RegisterType r} {pc npc : BitVec 64}
    {x : Regs} (e : EnvM S val) (h : Inv S s pc npc x) (imm : BitVec 12) (rs2 rs1 : BitVec 5)
    (ha : WordOk val (x.get rs1 + sign_extend (m := 64) imm)) :
    ∃ s', execute (.STORE (imm, .Regidx rs2, .Regidx rs1, 8)) s = .ok RETIRE_SUCCESS s' ∧
      s' = { s with mem := (memStore s.mem (x.get rs1 + (sign_extend imm : BitVec 64)).toNat
        (x.get rs2)) } := by
  refine ⟨_, ?_, rfl⟩
  have hr := readReg_env e.toEnv h
  obtain ⟨r, hm, hrd, hwr⟩ := ha.pma
  show execute_STORE _ _ _ _ s = _
  have hal : is_aligned_vaddr (.Virtaddr (x.get rs1 + sign_extend (m := 64) imm)) 8 = true := by
    have := ha.aligned
    simp only [is_aligned_vaddr, BitVec.toNatInt, beq_iff_eq, Int.ofNat_eq_natCast]
    rw [Int.tmod_eq_emod_of_nonneg (by omega)]
    omega
  have hal' : (BitVec.toNatInt (x.get rs1 + sign_extend (m := 64) imm)).tmod 8 = 0 := by
    have := ha.aligned
    simp only [BitVec.toNatInt, Int.ofNat_eq_natCast]
    rw [Int.tmod_eq_emod_of_nonneg (by omega)]
    omega
  simp (config := { decide := true }) [execute_STORE, vmem_write, data_addr_store e h,
    vmem_write_addr, rX_bits_inv h,
    LeanRV64D.assert, PreSail.assert, Functions.not, hal, hal', bits_of_virtaddr, bits_of_physaddr,
    split_page s _ ha.aligned, effectivePrivilege, hr, isRunReg, LeanRV64D.readReg, e.mprv,
    e.priv_M, translationMode, translate_M e h _ _ (.inr rfl), is_store_conditional,
    mem_write_ea, mem_write_value, mem_write_value_meta, mem_write_value_priv_meta,
    checked_mem_write, check_pma_with_pmp_priority, pmp_M e h, pmaCheck, hm, hwr, override_PMA,
    mag_pma_check, is_aligned_paddr, is_mag_applicable_access, split_misaligned,
    misaligned_order, untilFuelM, untilFuelM.go, (mmio_M e h _ ha).2, addInt_zero,
    write_kind_of_flags, write_ram_ok, extractLsb_63, updateSubrange_all, sign_extend_64,
    bind, EStateM.bind, pure, EStateM.pure, SailME.run, PreSailME.run, ExceptT.run, liftM,
    monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
    ExceptT.pure, Functor.map, EStateM.map, -BitVec.toNat_add,
    show max (8 : Int) 0 = 8 from rfl, show max (8 : Nat) 0 = 8 from rfl]

/-! ## The memory of the environment -/

theorem Inv.mem {S s : SailState} {pc npc : BitVec 64} {x : Regs} (h : Inv S s pc npc x) :
    s.mem = S.mem := by
  have := congrArg SequentialState.mem h.rest
  exact this

theorem Inv.with_mem {S s : SailState} {pc npc : BitVec 64} {x : Regs} (h : Inv S s pc npc x)
    (m : Std.ExtHashMap Nat (BitVec 8)) :
    Inv { S with mem := m } { s with mem := m } pc npc x where
  rest := by rw [← h.rest]
  other := h.other
  pc := h.pc
  npc := h.npc
  x1 := h.x1
  x2 := h.x2
  x3 := h.x3
  x4 := h.x4
  x5 := h.x5
  x6 := h.x6
  x7 := h.x7
  x8 := h.x8
  x9 := h.x9
  x10 := h.x10
  x11 := h.x11
  x12 := h.x12
  x13 := h.x13
  x14 := h.x14
  x15 := h.x15
  x16 := h.x16
  x17 := h.x17
  x18 := h.x18
  x19 := h.x19
  x20 := h.x20
  x21 := h.x21
  x22 := h.x22
  x23 := h.x23
  x24 := h.x24
  x25 := h.x25
  x26 := h.x26
  x27 := h.x27
  x28 := h.x28
  x29 := h.x29
  x30 := h.x30
  x31 := h.x31

theorem EnvM.with_mem {S : SailState} {val : (r : Register) → RegisterType r} (e : EnvM S val)
    (m : Std.ExtHashMap Nat (BitVec 8)) : EnvM { S with mem := m } val :=
  { e with get := e.get }

theorem with_mem_self (S : SailState) : { S with mem := S.mem } = S := rfl

end IntxRV
