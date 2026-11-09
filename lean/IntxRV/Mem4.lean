import IntxRV.Mem
/-!
# Loads of 4 bytes

`exec_lwu` shows that `lwu` of an aligned 4-byte word reads its 4 bytes, little-endian, zero
extended: as `exec_load` for `ld`. `reciprocal_2by1()` reads the `uint32_t` entries of
`RECIPROCAL_TABLE` with it. `HalfOk` says that a 4-byte word is ordinary readable memory.
-/

open Sail Sail.ConcurrencyInterfaceV1 PreSail
open LeanRV64D LeanRV64D.Functions LeanRV64D.Defs

set_option linter.unusedSimpArgs false

namespace IntxRV

theorem data_addr4 {S s : SailState} {val : (r : Register) → RegisterType r} {pc npc : BitVec 64}
    {x : Regs} (e : EnvM S val) (h : Inv S s pc npc x) (rs : BitVec 5) (off : BitVec 64) :
    get_transformed_data_addr (.Regidx rs) off (.Load .Data) 4 s =
      .ok (.Ext_DataAddr_OK (.Virtaddr (x.get rs + off))) s := by
  simp (config := { decide := true }) [get_transformed_data_addr, ext_data_get_addr,
    rX_bits_inv h, transform_effective_address, effectivePrivilege, readReg_env e.toEnv h,
    isRunReg, LeanRV64D.readReg, e.mprv, e.priv_M, get_pmlen, is_pmm_applicable, get_pmm, e.pmm,
    translationMode, pm_transform_PA, pmm_mode_backwards, bind, EStateM.bind, pure, EStateM.pure]
  simp [Functions.xlen, Sail.BitVec.extractLsb, zero_extend, Sail.BitVec.zeroExtend]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb_toNat]

theorem mmio_M4 {S s : SailState} {val : (r : Register) → RegisterType r} {pc npc : BitVec 64}
    {x : Regs} (e : EnvM S val) (h : Inv S s pc npc x) (a : BitVec 64) (ha : HalfOk val a) :
    within_mmio_readable (.Physaddr a) 4 s = .ok false s := by
  have hr := readReg_env e.toEnv h
  have hc := ha.clint
  have hs := ha.sig
  have hh := ha.htif
  simp (config := { decide := true }) [within_mmio_readable, within_clint,
    within_sig, within_htif_readable, within_htif_writable, get_config_rvfi, hr, isRunReg,
    BitVec.toNatInt, bind, EStateM.bind, pure, EStateM.pure]
  simp only [clint_base_toNat, clint_size_toNat, sig_base_toNat, sig_size_toNat,
    clint_base_toNat', clint_size_toNat', sig_base_toNat', sig_size_toNat'] at hc hs ⊢
  cases hv : val .htif_tohost_base with
  | none => simp [pure, EStateM.pure]; omega
  | some b => simp [hh _ hv, pure, EStateM.pure]; omega

theorem read_ram_ok4 (s : SailState) (a : BitVec 64) (hb : ∀ k < 4, a.toNat + k ∈ s.mem) :
    Functions.read_ram .Read_plain (.Physaddr a) 4 false s = .ok (memHalf s.mem a.toNat, ()) s := by
  have h0 := hb 0 (by omega)
  have h1 := hb 1 (by omega)
  have h2 := hb 2 (by omega)
  have h3 := hb 3 (by omega)
  simp only [Nat.add_zero] at h0
  simp [Functions.read_ram, sail_mem_read, readBytes, readByte, memHalf,
    Std.ExtHashMap.getElem_eq_getD (fallback := 0#8), h0, h1, h2, h3,
    get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure,
    Nat.add_assoc]

theorem updateSubrange_all32 (x v : BitVec 32) : BitVec.updateSubrange x 31 0 v = v := by
  simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange']
  ext i hi
  simp

theorem mem_read_M4 {S s : SailState} {val : (r : Register) → RegisterType r} {pc npc : BitVec 64}
    {x : Regs} (e : EnvM S val) (h : Inv S s pc npc x) (a : BitVec 64) (ha : HalfOk val a)
    (hb : ∀ k < 4, a.toNat + k ∈ s.mem) :
    mem_read (.Load .Data) .PBMT_PMA (.Physaddr a) 4 false false false s =
      .ok (.Ok (memHalf s.mem a.toNat)) s := by
  have hr := readReg_env e.toEnv h
  obtain ⟨r, hm, hrd⟩ := ha.pma
  have hal : (BitVec.toNatInt a).tmod 4 = 0 := by
    have := ha.aligned
    simp only [BitVec.toNatInt, Int.ofNat_eq_natCast]
    rw [Int.tmod_eq_emod_of_nonneg (by omega)]
    omega
  simp (config := { decide := true }) [hal, LeanRV64D.assert, PreSail.assert, Functions.not,
    mem_read, mem_read_priv, mem_read_priv_meta, checked_mem_read,
    check_pma_with_pmp_priority, pmp_M e h, pmaCheck, hm, hrd, override_PMA, mag_pma_check,
    is_aligned_paddr, is_mag_applicable_access, effectivePrivilege, hr, isRunReg,
    LeanRV64D.readReg, e.mprv, e.priv_M, read_ram_ok4 s a hb, updateSubrange_all32,
    split_misaligned, misaligned_order, untilFuelM, untilFuelM.go, mmio_M4 e h a ha,
    addInt_zero, bits_of_physaddr, read_kind_of_flags, MemoryOpResult_drop_meta,
    bind, EStateM.bind, pure, EStateM.pure, SailME.run, PreSailME.run, ExceptT.run, liftM,
    monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
    ExceptT.pure, Functor.map, EStateM.map]

theorem and3_of_aligned {a : BitVec 64} (ha : a.toNat % 4 = 0) : a &&& 3#64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (3#64).toNat = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simpa using ha

/-- An aligned 4-byte word does not cross a page. -/
theorem split_page4 (s : SailState) (a : BitVec 64) (ha : a.toNat % 4 = 0) :
    (split_on_page_boundary a 4 : SailM _) s = .ok (4, 0) s := by
  have h3 : BitVec.subInt (BitVec.addInt a ((4 : Nat) : Int)) 1 = a ||| 3#64 := by
    rw [← BitVec.add_eq_or_of_and_eq_zero _ _ (and3_of_aligned ha)]
    simp [Sail.BitVec.subInt, Sail.BitVec.addInt]
    bv_omega
  have hc : ∀ M : BitVec 64, (∀ i < 2, M.getLsbD i = false) →
      a &&& M = (a ||| 3#64) &&& M := by
    intro M hM
    ext i hi
    simp only [BitVec.getElem_and, BitVec.getElem_or]
    by_cases h2 : i < 2
    · have := hM i h2
      simp only [BitVec.getLsbD_eq_getElem hi] at this
      simp [this]
    · have : (3#64)[i] = false := by
        rw [← BitVec.getLsbD_eq_getElem]
        simp only [BitVec.getLsbD_ofNat]
        simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
        rw [Nat.div_eq_of_lt (by
          have : 2 ^ 2 ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
          omega)]
        simp
      simp [this]
  simp only [split_on_page_boundary, Sail.BitVec.length, h3]
  rw [if_pos]
  · rfl
  · simp only [beq_iff_eq]
    apply hc
    intro i hi
    simp [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', zeros, Functions.pagesize_bits]
    intro h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp at h

/-- `lwu rd, imm(rs1)` of an ordinary 4-byte word present in the memory reads its 4 bytes into
`rd`, zero-extended. -/
theorem exec_lwu {S s : SailState} {val : (r : Register) → RegisterType r} {pc npc : BitVec 64}
    {x : Regs} (e : EnvM S val) (h : Inv S s pc npc x) (imm : BitVec 12) (rs1 rd : BitVec 5)
    (ha : HalfOk val (x.get rs1 + sign_extend (m := 64) imm))
    (hb : ∀ k < 4, (x.get rs1 + sign_extend (m := 64) imm).toNat + k ∈ s.mem) :
    ∃ s', execute (.LOAD (imm, .Regidx rs1, .Regidx rd, true, 4)) s = .ok RETIRE_SUCCESS s' ∧
      Inv S s' pc npc (x.set rd
        ((memHalf s.mem (x.get rs1 + sign_extend (m := 64) imm).toNat).setWidth 64)) := by
  obtain ⟨s', hs, hi⟩ := wX_bits_inv h rd
    ((memHalf s.mem (x.get rs1 + sign_extend (m := 64) imm).toNat).setWidth 64)
  refine ⟨s', ?_, hi⟩
  have hr := readReg_env e.toEnv h
  show execute_LOAD _ _ _ _ _ s = _
  have hal : is_aligned_vaddr (.Virtaddr (x.get rs1 + sign_extend (m := 64) imm)) 4 = true := by
    have := ha.aligned
    simp only [is_aligned_vaddr, BitVec.toNatInt, beq_iff_eq, Int.ofNat_eq_natCast]
    rw [Int.tmod_eq_emod_of_nonneg (by omega)]
    omega
  simp (config := { decide := true }) [execute_LOAD, vmem_read, data_addr4 e h, vmem_read_addr,
    LeanRV64D.assert, PreSail.assert, Functions.not, hal, bits_of_virtaddr,
    split_page4 s _ ha.aligned, effectivePrivilege, hr, isRunReg, LeanRV64D.readReg, e.mprv,
    e.priv_M, translationMode, translate_and_read_value, translate_M e h _ _ (.inl rfl),
    mem_read_M4 e h _ ha hb, updateSubrange_all32, extend_value, zero_extend,
    Sail.BitVec.zeroExtend, hs, -BitVec.toNat_add,
    bind, EStateM.bind, pure, EStateM.pure, SailME.run, PreSailME.run, ExceptT.run, liftM,
    monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
    ExceptT.pure, Functor.map, EStateM.map]

end IntxRV
