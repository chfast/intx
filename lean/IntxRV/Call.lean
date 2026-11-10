import IntxRV.Image
/-!
# Calls

A function in the image calls another one by `auipc ra` and `jalr ra`. The proof of the callee
on its own code (`Reach` from its start to its return address in `ra`) is a proof in the image:
`Reach.lift` moves it to the offset of the callee in the image (`Gen.<f>_in_image`), and
`Reach.mono_bufs` to the larger list of the words that the caller may access. `Reach.call` runs the
call in the caller: the callee from its entry to the return address, then the rest of the caller
from the registers and the memory that the callee leaves.
-/

open LeanRV64D.Defs

namespace IntxRV

theorem execM_mono {A A' : List (BitVec 64)} (hA : ∀ a ∈ A, a ∈ A') {i : instruction}
    {pc pc' : BitVec 64} {x x' : Regs} {m m' : Mem} (h : execM A i pc x m = some (pc', x', m')) :
    execM A' i pc x m = some (pc', x', m') := by
  unfold execM at h ⊢
  split at h
  · split at h
    · rename_i hc; rw [if_pos ⟨hc.1, hc.2.1, hA _ hc.2.2⟩]; exact h
    · split at h
      · rename_i _ hc
        rw [if_neg (by simp [hc.1]), if_pos ⟨hc.1, hc.2.1, hc.2.2.imp (hA _) (hA _)⟩]; exact h
      · contradiction
  · split at h
    · rename_i hc; rw [if_pos ⟨hc.1, hA _ hc.2⟩]; exact h
    · contradiction
  · exact h

theorem stepsM_mono {A A' : List (BitVec 64)} (hA : ∀ a ∈ A, a ∈ A') {prog : List instruction}
    {base : BitVec 64} :
    ∀ (k : Nat) (pc : BitVec 64) (x : Regs) (m : Mem) {r : BitVec 64 × Regs × Mem},
      stepsM A prog base k pc x m = some r → stepsM A' prog base k pc x m = some r
  | 0, _, _, _, _, h => h
  | k + 1, pc, x, m, r, h => by
    simp only [stepsM] at h ⊢
    cases hf : fetch prog base pc with
    | none => simp [hf] at h
    | some i =>
      simp only [hf] at h ⊢
      cases hi : execM A i pc x m with
      | none => simp [hi] at h
      | some s =>
        obtain ⟨pc', x', m'⟩ := s
        simp only [hi] at h
        simp only [execM_mono hA hi]
        exact stepsM_mono hA k pc' x' m' h

/-- The words `A` that a run may access can grow. -/
theorem Reach.mono_bufs {A A' : List (BitVec 64)} (hA : ∀ a ∈ A, a ∈ A')
    {prog : List instruction} {base pc tgt : BitVec 64} {x : Regs} {m : Mem}
    {Q : Regs → Mem → Prop} (h : Reach A prog base pc x m tgt Q) :
    Reach A' prog base pc x m tgt Q := by
  obtain ⟨k, x', m', hk, hq⟩ := h
  exact ⟨k, x', m', stepsM_mono hA k pc x m hk, hq⟩

theorem pcAt_pcAt (base : BitVec 64) (o k : Nat) : pcAt (pcAt base o) k = pcAt base (o + k) := by
  simp only [pcAt, BitVec.add_assoc]
  congr 1
  rw [Nat.mul_add, BitVec.ofNat_add]

/-- An instruction of `sub`, the instructions of `prog` from the index `o`, is the instruction of
`prog` at its address. -/
theorem fetch_sub {prog sub : List instruction} {o : Nat}
    (hs : (prog.drop o).take sub.length = sub) {base pc : BitVec 64} {i : instruction}
    (hp : 4 * prog.length < 2 ^ 64) (hf : fetch sub (pcAt base o) pc = some i) :
    fetch prog base pc = some i := by
  unfold fetch at hf ⊢
  split at hf
  · rename_i ha
    have hlt := (List.getElem?_eq_some_iff.mp hf).1
    have hle : o + sub.length ≤ prog.length := by
      have := congrArg List.length hs
      simp only [List.length_take, List.length_drop] at this
      omega
    have hj : ((pc - pcAt base o) >>> 2).toNat < sub.length := hlt
    have hd : pc - base = (pc - pcAt base o) + BitVec.ofNat 64 (4 * o) := by
      simp only [pcAt]; bv_omega
    have h3 : (pc - pcAt base o).toNat % 4 = 0 := by
      have := congrArg BitVec.toNat ha
      simp only [BitVec.toNat_and, show BitVec.toNat (3 : BitVec 64) = 2 ^ 2 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod] at this
      simpa using this
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at hj hf
    clear hlt
    have hidx : ((pc - base) >>> 2).toNat = o + (pc - pcAt base o).toNat / 4 := by
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hd, BitVec.toNat_add,
        BitVec.toNat_ofNat]
      have := (pc - pcAt base o).isLt
      rw [Nat.mod_eq_of_lt (by omega : 4 * o < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
      omega
    have hf' : prog[o + (pc - pcAt base o).toNat / 4]? = some i := by
      have hj' : (pc - pcAt base o).toNat / 4 < sub.length := by simpa using hj
      rw [show (2 : Nat) ^ 2 = 4 from rfl] at hf
      rw [← hs, List.getElem?_take_of_lt (by simpa using hj'), List.getElem?_drop] at hf
      exact hf
    rw [if_pos, hidx]
    · exact hf'
    · rw [hd]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_ofNat,
        show BitVec.toNat (3 : BitVec 64) = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
        show BitVec.toNat (0 : BitVec 64) = 0 from rfl]
      omega
  · contradiction

theorem stepsM_sub {A : List (BitVec 64)} {prog sub : List instruction} {o : Nat}
    (hs : (prog.drop o).take sub.length = sub) {base : BitVec 64} (hp : 4 * prog.length < 2 ^ 64) :
    ∀ (k : Nat) (pc : BitVec 64) (x : Regs) (m : Mem) {r : BitVec 64 × Regs × Mem},
      stepsM A sub (pcAt base o) k pc x m = some r → stepsM A prog base k pc x m = some r
  | 0, _, _, _, _, h => h
  | k + 1, pc, x, m, r, h => by
    simp only [stepsM] at h ⊢
    cases hf : fetch sub (pcAt base o) pc with
    | none => simp [hf] at h
    | some i =>
      simp only [hf] at h
      simp only [fetch_sub hs hp hf]
      cases hi : execM A i pc x m with
      | none => simp [hi] at h
      | some s =>
        obtain ⟨pc', x', m'⟩ := s
        simp only [hi] at h ⊢
        exact stepsM_sub hs hp k pc' x' m' h

/-- A run of the instructions `sub` that are the instructions of `prog` from the index `o` is a
run of `prog`. -/
theorem Reach.lift {A : List (BitVec 64)} {prog sub : List instruction} {o : Nat}
    (hs : (prog.drop o).take sub.length = sub) {base pc tgt : BitVec 64} {x : Regs} {m : Mem}
    {Q : Regs → Mem → Prop} (hp : 4 * prog.length < 2 ^ 64)
    (h : Reach A sub (pcAt base o) pc x m tgt Q) : Reach A prog base pc x m tgt Q := by
  obtain ⟨k, x', m', hk, hq⟩ := h
  exact ⟨k, x', m', stepsM_sub hs hp k pc x m hk, hq⟩

/-- A call: the callee runs from its entry `e` to the return address `pcAt base r` in ra, then the
caller continues from there. -/
theorem Reach.call {A : List (BitVec 64)} {prog : List instruction} {base tgt : BitVec 64}
    {e r : Nat} {x : Regs} {m : Mem} {Q : Regs → Mem → Prop} {R : Regs → Mem → Prop}
    (hcallee : Reach A prog base (pcAt base e) x m (pcAt base r) R)
    (hcont : ∀ x' m', R x' m' → Reach A prog base (pcAt base r) x' m' tgt Q) :
    Reach A prog base (pcAt base e) x m tgt Q :=
  Reach.trans hcallee hcont

end IntxRV
