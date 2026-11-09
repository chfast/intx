import IntxRV.Env
import IntxRV.RunM
import IntxRV.Words
/-!
# The theorems with memory are not vacuous

`RunsM` assumes an environment `EnvM S val` in which the words of the buffers are ordinary memory
(`WordOk`), present in the memory and outside the code. `envM_exists` builds such an environment:
a machine with 4 KiB of RAM at 0x80000000 and no other memory. `api_nonvacuous` shows that the
assumptions of a specification hold there: `NonVacuous`, proved by `rv_nonvacuous` with the
buffers of the arguments at 0x80000000, 0x80000040, ... (Checks/IntxRVApi.lean).
-/

open Sail Sail.ConcurrencyInterfaceV1 PreSail
open LeanRV64D LeanRV64D.Functions LeanRV64D.Defs

namespace IntxRV

/-- The RAM region of the environment. -/
def ram : PMA_Region where
  base := 0x80000000#64
  size := 0x1000#64
  attributes := { (default : PMA) with readable := true, writable := true }
  include_in_device_tree := false

/-- The registers of the environment: those of `envVal` and the RAM region. -/
def envValM (r : Register) : RegisterType r :=
  match r with
  | .misa => 0x1000#64
  | .cur_privilege => .Machine
  | .elp => 0#1
  | .pma_regions => [ram]
  | .pmpcfg_n => Vector.replicate 64 0#8
  | _ => default

/-- The bytes of the RAM, all zero. -/
def ramMem : Mem := (List.range 0x1000).foldl (fun m i => m.insert (0x80000000 + i) 0#8) ∅

theorem mem_foldl_insert (l : List Nat) (m : Mem) (k : Nat)
    (hk : (∃ i ∈ l, k = 0x80000000 + i) ∨ k ∈ m) :
    k ∈ l.foldl (fun m i => m.insert (0x80000000 + i) 0#8) m := by
  induction l generalizing m with
  | nil => simpa using hk
  | cons i l ih =>
    simp only [List.foldl_cons]
    apply ih
    rcases hk with ⟨j, hj, rfl⟩ | hk
    · rcases List.mem_cons.mp hj with rfl | hj
      · right; simp
      · left; exact ⟨j, hj, rfl⟩
    · right; simp [hk]

theorem mem_ramMem (k : Nat) (h1 : 0x80000000 ≤ k) (h2 : k < 0x80001000) : k ∈ ramMem :=
  mem_foldl_insert _ _ _ (.inl ⟨k - 0x80000000, List.mem_range.mpr (by omega), by omega⟩)

theorem pmpcfg_zero (i : Nat) : _get_Pmpcfg_ent_A (Vector.replicate 64 0#8)[i]! = 0#2 := by
  by_cases h : i < 64 <;> simp [h] <;> decide

theorem range_subset_ram (a : BitVec 64) (h1 : 0x80000000 ≤ a.toNat)
    (h2 : a.toNat + 8 ≤ 0x80001000) : range_subset a 8#64 0x80000000#64 0x1000#64 = true := by
  simp only [range_subset, zopz0zIzJ_u, BitVec.toNatInt, Int.ofNat_eq_natCast, Int.ofNat_le,
    decide_eq_true_eq, Bool.and_eq_true]
  bv_omega

theorem matching_ram (a : BitVec 64) (h1 : 0x80000000 ≤ a.toNat)
    (h2 : a.toNat + 8 ≤ 0x80001000) : matching_pma_region [ram] (.Physaddr a) 8 = some ram := by
  have hz : zero_extend (m := 64) (bits_of_physaddr (.Physaddr a)) = a := by
    apply BitVec.eq_of_toNat_eq
    simp (config := { decide := true }) [zero_extend, Sail.BitVec.zeroExtend, bits_of_physaddr]
  have ht : (to_bits (l := 64) 8 : BitVec 64) = 8#64 := by decide
  simp only [matching_pma_region, matching_pma_region_bits_range, hz, ht]
  have := range_subset_ram a h1 h2
  simp only [ram] at this ⊢
  simp [this]

set_option maxRecDepth 100000 in
/-- An environment with the RAM region: the words in the RAM are ordinary memory. -/
theorem envM_exists : ∃ (S : SailState) (val : (r : Register) → RegisterType r), EnvM S val ∧
    S.mem = ramMem ∧ ∀ a : BitVec 64, 0x80000000 ≤ a.toNat → a.toNat + 8 ≤ 0x80001000 →
      a.toNat % 8 = 0 → WordOk val a ∧ Present S.mem a := by
  refine ⟨{ (default : SailState) with regs := regMap envValM allRegisters, mem := ramMem },
    envValM, ⟨⟨fun r => regMap_get? envValM allRegisters r ∅ (fun k => by simp)
      (Or.inl (mem_allRegisters r)), rfl, by decide, Or.inl rfl⟩, rfl, by decide, by decide,
      pmpcfg_zero⟩, rfl, fun a h1 h2 h3 => ⟨⟨h3, ⟨ram, matching_ram a h1 h2, rfl, rfl⟩, ?_, ?_,
      ?_⟩, fun k hk => mem_ramMem _ (by omega) (by omega)⟩⟩
  · simp only [clint_base_toNat, clint_size_toNat]; omega
  · simp only [sig_base_toNat, sig_size_toNat]; omega
  · intro b hb; cases hb

/-- The assumptions of `RunsM code bufs pre` hold for some environment, registers and memory (the
code at 0x1000). -/
def NonVacuous (code : Code) (bufs : Regs → List (BitVec 64)) (pre : Regs → Mem → Prop) : Prop :=
  ∃ (S : SailState) (val : (r : Register) → RegisterType r) (x : Regs), EnvM S val ∧
    (∀ a ∈ bufs x, WordOk val a ∧ Present S.mem a ∧
      (a.toNat + 8 ≤ 0x1000 ∨ 0x1000 + 4 * code.length ≤ a.toNat)) ∧ pre x S.mem

/-- The registers with the buffers of the arguments in the RAM, 64 bytes for each of a0 to a3, and
the stack pointer sp at the end of the RAM. -/
def ramArgs (i : BitVec 5) : BitVec 64 :=
  if 10 ≤ i.toNat ∧ i.toNat < 14 then 0x80000000#64 + 0x40#64 * (i.toNat - 10 : Nat)
  else if i = 2 then 0x80001000#64 else 0

/-- Proves `NonVacuous code bufs pre` with the RAM of `envM_exists` and `ramArgs`; `ls` are the
definitions of `bufs` and `pre`. -/
macro "rv_nonvacuous" " using " "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (
  obtain ⟨S, val, e, -, hw⟩ := envM_exists
  refine ⟨S, val, ramArgs, e, ?_, ?_⟩
  · simp (config := { decide := true }) only [ramArgs, bufWords, List.forall_mem_append,
      List.forall_mem_cons, List.forall_mem_nil, and_true, $ls,*]
    repeat' apply And.intro
    all_goals first
      | exact (hw _ (by decide) (by decide) (by decide)).1
      | exact (hw _ (by decide) (by decide) (by decide)).2
      | simp (config := { decide := true }) [$ls,*]
  · simp (config := { decide := true }) [ramArgs, IntxRV.Buf, IntxRV.Disjoint, $ls,*]))

end IntxRV
