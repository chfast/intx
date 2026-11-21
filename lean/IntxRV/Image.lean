import IntxRV.Reach
import IntxRV.Step
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.IntervalCases
/-!
# Functions in an image

A function that calls other functions or reads constant data is proved in its image, the function
linked with what it reaches (`Gen.<p>_image_code`, see `scripts/rv_gen.py`): the code at `base`
and the read-only data `data` (64-bit words) at `base + off`. `RunsI code entry data off bufs pre post` is
`RunsM` for the function that starts at the instruction `entry` of the image: the data is in the
memory, ordinary memory (`WordOk`), and the buffers are outside the image.
-/

open Sail Sail.ConcurrencyInterfaceV1 PreSail
open LeanRV64D LeanRV64D.Functions LeanRV64D.Defs

namespace IntxRV

/-- The addresses of the `n` words of the data at `base + off`. -/
def dataWords (base : BitVec 64) (off n : Nat) : List (BitVec 64) :=
  bufWords (base + BitVec.ofNat 64 off) n

/-- The memory `m` holds the words `data` at `a`. -/
def HoldsData (m : Mem) (a : BitVec 64) : List (BitVec 64) → Prop
  | [] => True
  | w :: ws => memWord m a.toNat = w ∧ HoldsData m (a + 8) ws

/-- The function at the instruction `entry` of the image `code` with the data `data` at `off`
computes `post` from the registers and the memory satisfying `pre`, with the loads and stores of
the words at the addresses `bufs x` and the loads of the data. As `RunsM`: for every environment
`EnvM` in which the words of the buffers and of the data are ordinary memory and present in the
memory, the data at `base + off` and the buffers outside the image, the Sail model runs the
function from `pcAt base entry` until it returns to `ret` and nothing else changes. -/
def RunsI (code : Code) (entry : Nat) (data : List (BitVec 64)) (off : Nat)
    (bufs : Regs → List (BitVec 64)) (pre : Regs → Mem → Prop)
    (post : Regs → Mem → Regs → Mem → Prop) : Prop :=
  ∀ (S : SailState) (val : (r : Register) → RegisterType r), EnvM S val →
  ∀ (base ret : BitVec 64), base &&& 7 = 0 → ret &&& 3 = 0 → 4 * code.length ≤ off →
    off + 8 * data.length ≤ (ret - base).toNat → base.toNat + off + 8 * data.length ≤ 2 ^ 64 →
  ∀ (s : SailState) (npc : BitVec 64) (x : Regs), Inv S s (pcAt base entry) npc x → x 1#5 = ret →
    (∀ a ∈ bufs x, WordOk val a ∧ Present S.mem a ∧
      (a.toNat + 8 ≤ base.toNat ∨ base.toNat + off + 8 * data.length ≤ a.toNat)) →
    (∀ a ∈ dataWords base off data.length, WordOk val a ∧ Present S.mem a) →
    HoldsData S.mem (base + BitVec.ofNat 64 off) data →
    pre x S.mem →
    ∃ n s' npc' x', run code base ret n s = .ok true s' ∧
      Inv { S with mem := s'.mem } s' ret npc' x' ∧ post x S.mem x' s'.mem

/-- The word `i` of the buffer at `a`. -/
theorem mem_bufWords {n i : Nat} (h : i < n) : ∀ {a : BitVec 64},
    a + BitVec.ofNat 64 (8 * i) ∈ bufWords a n := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    intro a
    cases i with
    | zero => simp [bufWords]
    | succ i =>
      have := @ih i (by omega) (a + 8)
      simp only [bufWords, List.mem_cons]
      right
      rwa [show a + BitVec.ofNat 64 (8 * (i + 1)) = a + 8 + BitVec.ofNat 64 (8 * i) by
        rw [BitVec.add_assoc]; congr 1; rw [Nat.mul_succ, Nat.add_comm, BitVec.ofNat_add]; rfl]

/-- The data word `i`. -/
theorem holdsData_get {m : Mem} : ∀ {data : List (BitVec 64)} {a : BitVec 64},
    HoldsData m a data → ∀ {i : Nat} (hi : i < data.length),
      memWord m (a + BitVec.ofNat 64 (8 * i)).toNat = data[i]
  | [], _, _, _, hi => absurd hi (by simp)
  | w :: ws, a, ⟨h0, h⟩, i, hi => by
    cases i with
    | zero => simpa using h0
    | succ i =>
      have := holdsData_get h (i := i) (by simpa using hi)
      rw [show a + BitVec.ofNat 64 (8 * (i + 1)) = a + 8 + BitVec.ofNat 64 (8 * i) by
        rw [BitVec.add_assoc]; congr 1; rw [Nat.mul_succ, Nat.add_comm, BitVec.ofNat_add]; rfl]
      simpa using this

/-- The low half of a word. -/
theorem memHalf_lo (m : Mem) (b : Nat) : memHalf m b = (memWord m b).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [memHalf, memWord, BitVec.getLsbD_setWidth, BitVec.getLsbD_append]
  simp (config := { decide := true }) [hi]
  split_ifs <;> first | rfl | omega

/-- The high half of a word. -/
theorem memHalf_hi (m : Mem) (b : Nat) :
    memHalf m (b + 4) = (memWord m b >>> 32).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [memHalf, memWord, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_append, Nat.add_assoc]
  simp (config := { decide := true }) [hi]
  split_ifs <;> first | omega | rfl | (congr 1 <;> omega)

/-- The byte `j` of a word. -/
theorem memByte_word (m : Mem) (b j : Nat) (hj : j < 8) :
    memByte m (b + j) = (memWord m b >>> (8 * j)).setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [memByte, memWord, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
  interval_cases j <;>
  · simp (config := { decide := true }) [hi]
    try (split_ifs <;> first | omega | (rw [BitVec.getLsbD_eq_getElem (by omega)]; congr 1; omega))

/-- The byte `i` of the data: the byte `i % 8` of the word `i / 8`. -/
theorem memByte_data {m : Mem} {a : BitVec 64} {data : List (BitVec 64)} (hh : HoldsData m a data)
    (hno : a.toNat + 8 * data.length ≤ 2 ^ 64) {i : Nat} (hi : i < 8 * data.length) :
    memByte m (a + BitVec.ofNat 64 i).toNat =
      (data[i / 8]'(by omega) >>> (8 * (i % 8))).setWidth 8 := by
  have e : (a + BitVec.ofNat 64 i).toNat = (a + BitVec.ofNat 64 (8 * (i / 8))).toNat + i % 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : i < 2 ^ 64), Nat.mod_eq_of_lt (by omega : 8 * (i / 8) < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  rw [e, memByte_word _ _ _ (Nat.mod_lt _ (by decide)), holdsData_get hh (by omega)]

theorem and_not7_add (a : BitVec 64) (ha : a.toNat % 8 = 0) (i : Nat) (hno : a.toNat + i < 2 ^ 64) :
    (a + BitVec.ofNat 64 i) &&& ~~~7#64 = a + BitVec.ofNat 64 (8 * (i / 8)) := by
  have e1 : (a + BitVec.ofNat 64 i).toNat = a.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64),
      Nat.mod_eq_of_lt hno]
  have e2 : (a + BitVec.ofNat 64 (8 * (i / 8))).toNat = a.toNat + 8 * (i / 8) := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8 * (i / 8) < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega)]
  apply BitVec.eq_of_toNat_eq
  rw [toNat_and_not7, e1, e2]
  omega

/-- The word of the byte `i` of the data is a word of the data: `lbu` of the data may read it. -/
theorem byte_mem_dataWords {base : BitVec 64} {off n i : Nat} (hb : base &&& 7 = 0)
    (ho : off % 8 = 0) (hno : base.toNat + off + 8 * n ≤ 2 ^ 64) (hi : i < 8 * n) :
    (base + BitVec.ofNat 64 off + BitVec.ofNat 64 i) &&& 0xfffffffffffffff8#64 ∈
      dataWords base off n := by
  have hb8 : base.toNat % 8 = 0 := by
    have := congrArg BitVec.toNat hb
    rwa [BitVec.toNat_and, show (7 : BitVec 64).toNat = 2 ^ 3 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, show (0 : BitVec 64).toNat = 0 from rfl] at this
  have hbo : (base + BitVec.ofNat 64 off).toNat = base.toNat + off := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : off < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega)]
  rw [show (0xfffffffffffffff8#64 : BitVec 64) = ~~~7#64 by decide, and_not7_add _ (by omega) i
    (by omega)]
  exact mem_bufWords (by omega : i / 8 < n)

/-- `RunsI` from the `Reach` of the return address from the entry. -/
theorem runsI_of_reach {code : Code} {prog : List instruction} {entry : Nat}
    {data : List (BitVec 64)} {off : Nat} {bufs : Regs → List (BitVec 64)}
    {pre : Regs → Mem → Prop} {post : Regs → Mem → Regs → Mem → Prop} (hd : Decodes code prog)
    (h : ∀ base ret : BitVec 64, base &&& 7 = 0 → ret &&& 3 = 0 → 4 * code.length ≤ off →
      off + 8 * data.length ≤ (ret - base).toNat → base.toNat + off + 8 * data.length ≤ 2 ^ 64 →
      ∀ (x : Regs) (m : Mem), x 1#5 = ret →
      (∀ a ∈ bufs x, a.toNat + 8 ≤ base.toNat ∨ base.toNat + off + 8 * data.length ≤ a.toNat) →
      HoldsData m (base + BitVec.ofNat 64 off) data → pre x m →
      Reach (bufs x ++ dataWords base off data.length) prog base (pcAt base entry) x m ret
        (post x m)) :
    RunsI code entry data off bufs pre post := by
  intro S val e base ret hb hr hc hl hw s npc x hs hx hbuf hdat hhold hpre
  have hb3 : base &&& 3 = 0 := by
    have := congrArg (· &&& 3#64) hb
    simpa [BitVec.and_assoc] using this
  obtain ⟨k, x', m', hk, hq⟩ := h base ret hb hr hc hl hw x S.mem hx
    (fun a ha => (hbuf a ha).2.2) hhold hpre
  have hl' : 4 * prog.length ≤ (ret - base).toNat := by rw [← hd.1]; omega
  have ha := arunM_of_stepsM hl' k _ x x' S.mem m' hk
  have hA : ∀ a ∈ bufs x ++ dataWords base off data.length, WordOk val a ∧ Present S.mem a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact ⟨(hbuf a ha).1, (hbuf a ha).2.1⟩
    · exact hdat a ha
  obtain ⟨s', npc', hrun, hm, hs'⟩ := run_simM hd (fun a h => (hA a h).1) hb3 hr (k + 1) S s _ npc
    x x' m' e (fun a h => (hA a h).2) hs ha
  subst hm
  exact ⟨k + 1, s', npc', x', hrun, hs', hq⟩

end IntxRV
