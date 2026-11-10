import IntxRV.Run
/-!
# The theorems are not vacuous

`Runs` assumes a state `S` of the environment (`Env S val`) and a start state `s` with
`Inv S s base npc x`. This file shows that such states exist, so the theorems say something about
the machine: `env_exists` builds an environment from a value of each register of the model, and
`inv_mkState` shows that `mkState S pc npc x` (S with the program counters and the general purpose
registers set) satisfies `Inv`.
-/

open Sail Sail.ConcurrencyInterfaceV1 PreSail
open LeanRV64D LeanRV64D.Functions LeanRV64D.Defs

namespace IntxRV

/-- All the registers of the model. -/
def allRegisters : List Register := [
  .hart_state, .mhpmcounter, .mhpmevent, .ssp, .srmcfg, .satp, .tlb, .pma_regions,
  .htif_payload_writes, .htif_cmd_write, .htif_exit_code, .htif_done, .htif_tohost, .stimecmp,
      .mtimecmp, .htif_tohost_base,
  .pc_reset_address, .elp, .minstretcfg, .mcyclecfg, .vcsr, .vr31, .vr30, .vr29,
  .vr28, .vr27, .vr26, .vr25, .vr24, .vr23, .vr22, .vr21,
  .vr20, .vr19, .vr18, .vr17, .vr16, .vr15, .vr14, .vr13,
  .vr12, .vr11, .vr10, .vr9, .vr8, .vr7, .vr6, .vr5,
  .vr4, .vr3, .vr2, .vr1, .vr0, .fcsr, .f31, .f30,
  .f29, .f28, .f27, .f26, .f25, .f24, .f23, .f22,
  .f21, .f20, .f19, .f18, .f17, .f16, .f15, .f14,
  .f13, .f12, .f11, .f10, .f9, .f8, .f7, .f6,
  .f5, .f4, .f3, .f2, .f1, .f0, .pmpaddr_n, .pmpcfg_n,
  .sig_seip, .sig_meip, .mideleg, .medeleg, .mip, .mie, .tselect, .stval,
  .scause, .sepc, .sscratch, .stvec, .mconfigptr, .mhartid, .marchid, .mimpid,
  .mvendorid, .minstret_increment, .minstret, .mtime, .mcycle, .mcountinhibit, .mcounteren,
      .scounteren,
  .mscratch, .mtval, .mepc, .mcause, .mtvec, .cur_inst, .x31, .x30,
  .x29, .x28, .x27, .x26, .x25, .x24, .x23, .x22,
  .x21, .x20, .x19, .x18, .x17, .x16, .x15, .x14,
  .x13, .x12, .x11, .x10, .x9, .x8, .x7, .x6,
  .x5, .x4, .x3, .x2, .x1, .nextPC, .PC, .vstart,
  .vl, .vtype, .menvcfg, .mseccfg, .senvcfg, .sstateen3, .sstateen2, .sstateen1,
  .sstateen0, .mstateen3, .mstateen2, .mstateen1, .mstateen0, .hstateen3, .hstateen2, .hstateen1,
  .hstateen0, .mstatus, .misa, .cur_privilege, .rvfi_mem_data_present, .rvfi_mem_data,
      .rvfi_int_data_present, .rvfi_int_data,
  .rvfi_pc_data, .rvfi_inst_data, .rvfi_instruction, .fp_rounding_global]

set_option maxRecDepth 100000 in
theorem mem_allRegisters (r : Register) : r ∈ allRegisters := by
  cases r <;> simp [allRegisters]

instance (r : Register) : Inhabited (RegisterType r) := by
  cases r <;> exact inferInstance

/-- The registers of a machine in an environment: the M extension enabled in `misa` (bit 12), the
machine privilege level, no landing pad expected, and the default values of the others. -/
def envVal (r : Register) : RegisterType r :=
  match r with
  | .misa => 0x1000#64
  | .cur_privilege => .Machine
  | .elp => 0#1
  | _ => default

/-- The map of the registers `l` to their values `val`. -/
def regMap (val : (r : Register) → RegisterType r) (l : List Register) :
    Std.ExtDHashMap Register RegisterType :=
  l.foldl (fun m r => m.insert r (val r)) ∅

theorem regMap_get? (val : (r : Register) → RegisterType r) (l : List Register) (r : Register)
    (m : Std.ExtDHashMap Register RegisterType) (hm : ∀ k, m.get? k = none ∨ m.get? k = some
        (val k))
    (hr : r ∈ l ∨ m.get? r = some (val r)) :
    (l.foldl (fun m r => m.insert r (val r)) m).get? r = some (val r) := by
  induction l generalizing m with
  | nil => simpa using hr
  | cons k l ih =>
    apply ih
    · intro k'
      rw [Std.ExtDHashMap.get?_insert]
      split
      · rename_i h; rw [beq_iff_eq] at h; subst h; right; rfl
      · exact hm k'
    · rcases hr with hr | hr
      · rcases List.mem_cons.mp hr with rfl | hr
        · right; simp
        · left; exact hr
      · right
        rw [Std.ExtDHashMap.get?_insert]
        split
        · rename_i h; rw [beq_iff_eq] at h; subst h; rfl
        · exact hr

set_option maxRecDepth 100000 in
theorem env_exists : ∃ (S : SailState) (val : (r : Register) → RegisterType r), Env S val := by
  refine ⟨{ (default : SailState) with regs := regMap envVal allRegisters }, envVal,
    ⟨fun r => ?_, rfl, by decide, Or.inl rfl⟩⟩
  exact regMap_get? envVal allRegisters r ∅ (fun k => by simp) (Or.inl (mem_allRegisters r))

/-- The state `S` with the program counters `pc`, `npc` and the general purpose registers `x`. -/
def mkState (S : SailState) (pc npc : BitVec 64) (x : Regs) : SailState :=
  { S with regs := S.regs
      |>.insert .x1 (x 1#5) |>.insert .x2 (x 2#5) |>.insert .x3 (x 3#5) |>.insert .x4 (x 4#5)
      |>.insert .x5 (x 5#5) |>.insert .x6 (x 6#5) |>.insert .x7 (x 7#5) |>.insert .x8 (x 8#5)
      |>.insert .x9 (x 9#5) |>.insert .x10 (x 10#5) |>.insert .x11 (x 11#5)
      |>.insert .x12 (x 12#5) |>.insert .x13 (x 13#5) |>.insert .x14 (x 14#5)
      |>.insert .x15 (x 15#5) |>.insert .x16 (x 16#5) |>.insert .x17 (x 17#5)
      |>.insert .x18 (x 18#5) |>.insert .x19 (x 19#5) |>.insert .x20 (x 20#5)
      |>.insert .x21 (x 21#5) |>.insert .x22 (x 22#5) |>.insert .x23 (x 23#5)
      |>.insert .x24 (x 24#5) |>.insert .x25 (x 25#5) |>.insert .x26 (x 26#5)
      |>.insert .x27 (x 27#5) |>.insert .x28 (x 28#5) |>.insert .x29 (x 29#5)
      |>.insert .x30 (x 30#5) |>.insert .x31 (x 31#5) |>.insert .PC pc |>.insert .nextPC npc }

theorem inv_mkState (S : SailState) (pc npc : BitVec 64) (x : Regs) :
    Inv S (mkState S pc npc x) pc npc x where
  rest := rfl
  other r hr := by
    simp (config := { decide := true }) only [mkState, Std.ExtDHashMap.get?_insert, run_beq hr,
      Bool.false_eq_true, dite_false]
  pc := by simp [mkState, Std.ExtDHashMap.get?_insert]
  npc := by simp [mkState]
  x1 := by simp [mkState, Std.ExtDHashMap.get?_insert]
  x2 := by simp [mkState, Std.ExtDHashMap.get?_insert]
  x3 := by simp [mkState, Std.ExtDHashMap.get?_insert]
  x4 := by simp [mkState, Std.ExtDHashMap.get?_insert]
  x5 := by simp [mkState, Std.ExtDHashMap.get?_insert]
  x6 := by simp [mkState, Std.ExtDHashMap.get?_insert]
  x7 := by simp [mkState, Std.ExtDHashMap.get?_insert]
  x8 := by simp [mkState, Std.ExtDHashMap.get?_insert]
  x9 := by simp [mkState, Std.ExtDHashMap.get?_insert]
  x10 := by simp [mkState, Std.ExtDHashMap.get?_insert]
  x11 := by simp [mkState, Std.ExtDHashMap.get?_insert]
  x12 := by simp [mkState, Std.ExtDHashMap.get?_insert]
  x13 := by simp [mkState, Std.ExtDHashMap.get?_insert]
  x14 := by simp [mkState, Std.ExtDHashMap.get?_insert]
  x15 := by simp [mkState, Std.ExtDHashMap.get?_insert]
  x16 := by simp [mkState, Std.ExtDHashMap.get?_insert]
  x17 := by simp [mkState, Std.ExtDHashMap.get?_insert]
  x18 := by simp [mkState, Std.ExtDHashMap.get?_insert]
  x19 := by simp [mkState, Std.ExtDHashMap.get?_insert]
  x20 := by simp [mkState, Std.ExtDHashMap.get?_insert]
  x21 := by simp [mkState, Std.ExtDHashMap.get?_insert]
  x22 := by simp [mkState, Std.ExtDHashMap.get?_insert]
  x23 := by simp [mkState, Std.ExtDHashMap.get?_insert]
  x24 := by simp [mkState, Std.ExtDHashMap.get?_insert]
  x25 := by simp [mkState, Std.ExtDHashMap.get?_insert]
  x26 := by simp [mkState, Std.ExtDHashMap.get?_insert]
  x27 := by simp [mkState, Std.ExtDHashMap.get?_insert]
  x28 := by simp [mkState, Std.ExtDHashMap.get?_insert]
  x29 := by simp [mkState, Std.ExtDHashMap.get?_insert]
  x30 := by simp [mkState, Std.ExtDHashMap.get?_insert]
  x31 := by simp [mkState, Std.ExtDHashMap.get?_insert]

end IntxRV
