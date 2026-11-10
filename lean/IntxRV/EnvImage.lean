import IntxRV.EnvM
import IntxRV.Image
/-!
# The theorems of the image are not vacuous

`NonVacuousI` says that the assumptions of `RunsI` hold for some environment, registers, memory
and address of the image: the environment of `envM_exists` with the data of the image stored in
its RAM at 0x80000400 (`storeWords`), and registers that the proof of the function chooses.
-/

open Sail Sail.ConcurrencyInterfaceV1 PreSail
open LeanRV64D LeanRV64D.Functions LeanRV64D.Defs

namespace IntxRV

/-- The memory `m` with the words `ws` stored from the address `a`. -/
def storeWords (m : Mem) (a : Nat) : List (BitVec 64) → Mem
  | [] => m
  | w :: ws => storeWords (memStore m a w) (a + 8) ws

theorem memWord_storeWords_of_le {b : Nat} : ∀ {m : Mem} {a : Nat} (ws : List (BitVec 64)),
    b + 8 ≤ a → memWord (storeWords m a ws) b = memWord m b
  | _, _, [], _ => rfl
  | m, a, w :: ws, h => by
    rw [storeWords, memWord_storeWords_of_le ws (by omega),
      memWord_memStore_of_ne _ _ _ _ (by omega)]

theorem holdsData_storeWords : ∀ {m : Mem} {a : BitVec 64} (ws : List (BitVec 64)),
    a.toNat + 8 * ws.length ≤ 2 ^ 64 → HoldsData (storeWords m a.toNat ws) a ws
  | _, _, [], _ => trivial
  | m, a, w :: ws, h => by
    simp only [List.length_cons] at h
    refine ⟨?_, ?_⟩
    · rw [storeWords, memWord_storeWords_of_le ws (by omega), memWord_memStore_self]
    · cases ws with
      | nil => trivial
      | cons w' ws =>
        simp only [List.length_cons] at h
        have h8 : (a + 8).toNat = a.toNat + 8 := by bv_omega
        rw [storeWords, ← h8]
        exact holdsData_storeWords (w' :: ws) (by simp; omega)

theorem present_storeWords {b : BitVec 64} : ∀ {m : Mem} {a : Nat} (ws : List (BitVec 64)),
    Present m b → Present (storeWords m a ws) b
  | _, _, [], h => h
  | _, _, _ :: ws, h => present_storeWords ws (present_memStore h _ _)

theorem exists_of_mem_bufWords {a : BitVec 64} : ∀ {b : BitVec 64} {n : Nat},
    a ∈ bufWords b n → ∃ i < n, a = b + BitVec.ofNat 64 (8 * i)
  | _, 0, h => absurd h (by simp [bufWords])
  | b, n + 1, h => by
    simp only [bufWords, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨0, by omega, by simp⟩
    · obtain ⟨i, hi, rfl⟩ := exists_of_mem_bufWords h
      refine ⟨i + 1, by omega, ?_⟩
      rw [BitVec.add_assoc]; congr 1; rw [Nat.mul_succ, Nat.add_comm, BitVec.ofNat_add]; rfl

/-- The assumptions of `RunsI code entry data off bufs pre` hold for some environment, registers,
memory and address `base` of the image. -/
def NonVacuousI (code : Code) (data : List (BitVec 64)) (off : Nat)
    (bufs : Regs → List (BitVec 64)) (pre : Regs → Mem → Prop) : Prop :=
  ∃ (S : SailState) (val : (r : Register) → RegisterType r) (x : Regs) (base : BitVec 64),
    EnvM S val ∧ base &&& 7 = 0 ∧ 4 * code.length ≤ off ∧
    base.toNat + off + 8 * data.length ≤ 2 ^ 64 ∧
    (∀ a ∈ bufs x, WordOk val a ∧ Present S.mem a ∧
      (a.toNat + 8 ≤ base.toNat ∨ base.toNat + off + 8 * data.length ≤ a.toNat)) ∧
    (∀ a ∈ dataWords base off data.length, WordOk val a ∧ Present S.mem a) ∧
    HoldsData S.mem (base + BitVec.ofNat 64 off) data ∧ pre x S.mem

/-- `NonVacuousI` from the data stored at 0x80000400 in the RAM of `envM_exists` and the registers
`x`: the buffers must be words of the RAM outside the data, and `pre` must hold. -/
theorem nonVacuousI_of {code : Code} {data : List (BitVec 64)} {off : Nat}
    {bufs : Regs → List (BitVec 64)} {pre : Regs → Mem → Prop} (x : Regs)
    (hc : 4 * code.length ≤ off) (ho : off % 8 = 0) (hoff : off ≤ 0x80000400)
    (hd : 8 * data.length ≤ 0x800)
    (hb : ∀ a ∈ bufs x, 0x80000000 ≤ a.toNat ∧ a.toNat + 8 ≤ 0x80001000 ∧
      a.toNat % 8 = 0 ∧ (a.toNat + 8 ≤ 0x80000400 - off ∨ 0x80000400 + 8 * data.length ≤ a.toNat))
    (hpre : ∀ m, pre x m) :
    NonVacuousI code data off bufs pre := by
  obtain ⟨S, val, e, hm, hw⟩ := envM_exists
  have hbase : (BitVec.ofNat 64 (0x80000400 - off)).toNat = 0x80000400 - off := by
    rw [BitVec.toNat_ofNat]; omega
  have hdat : BitVec.ofNat 64 (0x80000400 - off) + BitVec.ofNat 64 off = 0x80000400#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hbase, BitVec.toNat_ofNat]
    simp; omega
  refine ⟨{ S with mem := storeWords S.mem 0x80000400 data }, val, x,
    BitVec.ofNat 64 (0x80000400 - off), e.with_mem _, ?_, hc, ?_,
    fun a ha => ?_, fun a ha => ?_, ?_, hpre _⟩
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, hbase, show BitVec.toNat (7 : BitVec 64) = 2 ^ 3 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, show BitVec.toNat (0 : BitVec 64) = 0 from rfl]
    omega
  · rw [hbase]; omega
  · obtain ⟨h1, h2, h3, h4⟩ := hb a ha
    exact ⟨(hw a h1 h2 h3).1, present_storeWords _ (hw a h1 h2 h3).2, by rw [hbase]; omega⟩
  · rw [dataWords, hdat] at ha
    obtain ⟨i, hi, rfl⟩ := exists_of_mem_bufWords ha
    have hn : (0x80000400#64 + BitVec.ofNat 64 (8 * i)).toNat = 0x80000400 + 8 * i := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; simp; omega
    exact ⟨(hw _ (by omega) (by omega) (by omega)).1,
      present_storeWords _ (hw _ (by omega) (by omega) (by omega)).2⟩
  · rw [hdat]
    exact holdsData_storeWords (a := 0x80000400#64) data (by simp; omega)

end IntxRV
