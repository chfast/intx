import IntxRV.Mem
/-!
# Loads of 1 byte

`exec_lbu` shows that `lbu` reads 1 byte, zero extended: as `exec_load` for `ld`. `ctz()` reads
the table of its de Bruijn sequence with it. `ByteOk` (in `Mem.lean`) says that a byte is ordinary
readable memory.
-/

open Sail Sail.ConcurrencyInterfaceV1 PreSail
open LeanRV64D LeanRV64D.Functions LeanRV64D.Defs

set_option linter.unusedSimpArgs false

namespace IntxRV

/-- The address of the aligned word of the byte at `a`. -/
theorem toNat_and_not7 (a : BitVec 64) : (a &&& ~~~7#64).toNat = a.toNat - a.toNat % 8 := by
  have h7 : (a &&& 7#64).toNat = a.toNat % 8 := by
    rw [BitVec.toNat_and, show (7#64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have hs : (a &&& ~~~7#64) + (a &&& 7#64) = a := by
    rw [BitVec.add_eq_or_of_and_eq_zero]
    · rw [← BitVec.and_or_distrib_left, BitVec.or_comm, BitVec.or_not_self, BitVec.and_allOnes]
    · ext i hi
      simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero]
      cases (7#64)[i] <;> simp
  have := congrArg BitVec.toNat hs
  rw [BitVec.toNat_add, h7] at this
  have hlt := (a &&& ~~~7#64).isLt
  have h8 := Nat.mod_lt a.toNat (show 8 > 0 by decide)
  omega

theorem data_addr1 {S s : SailState} {val : (r : Register) → RegisterType r} {pc npc : BitVec 64}
    {x : Regs} (e : EnvM S val) (h : Inv S s pc npc x) (rs : BitVec 5) (off : BitVec 64) :
    get_transformed_data_addr (.Regidx rs) off (.Load .Data) 1 s =
      .ok (.Ext_DataAddr_OK (.Virtaddr (x.get rs + off))) s := by
  simp (config := { decide := true }) [get_transformed_data_addr, ext_data_get_addr,
    rX_bits_inv h, transform_effective_address, effectivePrivilege, readReg_env e.toEnv h,
    isRunReg, LeanRV64D.readReg, e.mprv, e.priv_M, get_pmlen, is_pmm_applicable, get_pmm, e.pmm,
    translationMode, pm_transform_PA, pmm_mode_backwards, bind, EStateM.bind, pure, EStateM.pure]
  simp [Functions.xlen, Sail.BitVec.extractLsb, zero_extend, Sail.BitVec.zeroExtend]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb_toNat]

theorem mmio_M1 {S s : SailState} {val : (r : Register) → RegisterType r} {pc npc : BitVec 64}
    {x : Regs} (e : EnvM S val) (h : Inv S s pc npc x) (a : BitVec 64) (ha : ByteOk val a) :
    within_mmio_readable (.Physaddr a) 1 s = .ok false s := by
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

theorem read_ram_ok1 (s : SailState) (a : BitVec 64) (hb : a.toNat ∈ s.mem) :
    Functions.read_ram .Read_plain (.Physaddr a) 1 false s = .ok (memByte s.mem a.toNat, ()) s := by
  simp [Functions.read_ram, sail_mem_read, readBytes, readByte, memByte,
    Std.ExtHashMap.getElem_eq_getD (fallback := 0#8), hb,
    get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure]

theorem updateSubrange_all8 (x v : BitVec 8) : BitVec.updateSubrange x 7 0 v = v := by
  simp only [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange']
  ext i hi
  simp

theorem mem_read_M1 {S s : SailState} {val : (r : Register) → RegisterType r} {pc npc : BitVec 64}
    {x : Regs} (e : EnvM S val) (h : Inv S s pc npc x) (a : BitVec 64) (ha : ByteOk val a)
    (hb : a.toNat ∈ s.mem) :
    mem_read (.Load .Data) .PBMT_PMA (.Physaddr a) 1 false false false s =
      .ok (.Ok (memByte s.mem a.toNat)) s := by
  have hr := readReg_env e.toEnv h
  obtain ⟨r, hm, hrd⟩ := ha.pma
  simp (config := { decide := true }) [LeanRV64D.assert, PreSail.assert, Functions.not,
    mem_read, mem_read_priv, mem_read_priv_meta, checked_mem_read,
    check_pma_with_pmp_priority, pmp_M e h, pmaCheck, hm, hrd, override_PMA, mag_pma_check,
    is_aligned_paddr, is_mag_applicable_access, effectivePrivilege, hr, isRunReg,
    LeanRV64D.readReg, e.mprv, e.priv_M, read_ram_ok1 s a hb, updateSubrange_all8,
    split_misaligned, misaligned_order, untilFuelM, untilFuelM.go, mmio_M1 e h a ha,
    addInt_zero, bits_of_physaddr, read_kind_of_flags, MemoryOpResult_drop_meta,
    bind, EStateM.bind, pure, EStateM.pure, SailME.run, PreSailME.run, ExceptT.run, liftM,
    monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
    ExceptT.pure, Functor.map, EStateM.map]

/-- A byte does not cross a page. -/
theorem split_page1 (s : SailState) (a : BitVec 64) :
    (split_on_page_boundary a 1 : SailM _) s = .ok (1, 0) s := by
  have h0 : BitVec.subInt (BitVec.addInt a ((1 : Nat) : Int)) 1 = a := by
    simp [Sail.BitVec.subInt, Sail.BitVec.addInt]
    bv_omega
  simp only [split_on_page_boundary, Sail.BitVec.length, h0]
  rw [if_pos]
  · rfl
  · simp

/-- `lbu rd, imm(rs1)` of an ordinary byte present in the memory reads it into `rd`,
zero-extended. -/
theorem exec_lbu {S s : SailState} {val : (r : Register) → RegisterType r} {pc npc : BitVec 64}
    {x : Regs} (e : EnvM S val) (h : Inv S s pc npc x) (imm : BitVec 12) (rs1 rd : BitVec 5)
    (ha : ByteOk val (x.get rs1 + sign_extend (m := 64) imm))
    (hb : (x.get rs1 + sign_extend (m := 64) imm).toNat ∈ s.mem) :
    ∃ s', execute (.LOAD (imm, .Regidx rs1, .Regidx rd, true, 1)) s = .ok RETIRE_SUCCESS s' ∧
      Inv S s' pc npc (x.set rd
        ((memByte s.mem (x.get rs1 + sign_extend (m := 64) imm).toNat).setWidth 64)) := by
  obtain ⟨s', hs, hi⟩ := wX_bits_inv h rd
    ((memByte s.mem (x.get rs1 + sign_extend (m := 64) imm).toNat).setWidth 64)
  refine ⟨s', ?_, hi⟩
  have hr := readReg_env e.toEnv h
  show execute_LOAD _ _ _ _ _ s = _
  have hal : is_aligned_vaddr (.Virtaddr (x.get rs1 + sign_extend (m := 64) imm)) 1 = true := by
    simp [is_aligned_vaddr]
  simp (config := { decide := true }) [execute_LOAD, vmem_read, data_addr1 e h, vmem_read_addr,
    LeanRV64D.assert, PreSail.assert, Functions.not, hal, bits_of_virtaddr,
    split_page1 s _, effectivePrivilege, hr, isRunReg, LeanRV64D.readReg, e.mprv,
    e.priv_M, translationMode, translate_and_read_value, translate_M e h _ _ (.inl rfl),
    mem_read_M1 e h _ ha hb, updateSubrange_all8, extend_value, zero_extend,
    Sail.BitVec.zeroExtend, hs, -BitVec.toNat_add,
    bind, EStateM.bind, pure, EStateM.pure, SailME.run, PreSailME.run, ExceptT.run, liftM,
    monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
    ExceptT.pure, Functor.map, EStateM.map]

end IntxRV
