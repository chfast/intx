import IntxRV.Reach
import IntxRV.Step
import Mathlib.Tactic.SplitIfs
/-!
# Functions in an image

The functions that call other functions or read constant data are proved in the image of all the
functions linked together (`Gen.image_code`, see `scripts/rv_gen.py`): the code at `base` and the
read-only data `data` (64-bit words) at `base + off`. `RunsI code entry data off bufs pre post` is
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
