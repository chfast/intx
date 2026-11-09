import IntxRV.RunM
/-!
# Reaching an address

`Reach A prog base pc x m tgt Q`: running the instructions `prog` at `base` by `execM` from the
address `pc`, the registers `x` and the memory `m` reaches the address `tgt` in some steps, with
registers and memory satisfying `Q`. The proofs of long functions are chains of `Reach` from cut
point to cut point (`Reach.trans`): a straight segment of instructions is proved by running it as
`arunM` with the cut point as the return address (`reach_of_arunM`), and a call by the `Reach` of
the function called. `runsM_of_reach` proves `RunsM` from the `Reach` of the return address.
-/

open LeanRV64D.Defs

namespace IntxRV

/-- `k` steps of `execM` from `pc`, fetching the instructions from `prog` at `base`. -/
def stepsM (A : List (BitVec 64)) (prog : List instruction) (base : BitVec 64) :
    Nat → BitVec 64 → Regs → Mem → Option (BitVec 64 × Regs × Mem)
  | 0, pc, x, m => some (pc, x, m)
  | k + 1, pc, x, m => match fetch prog base pc with
    | none => none
    | some i => match execM A i pc x m with
      | none => none
      | some (pc', x', m') => stepsM A prog base k pc' x' m'

/-- From `pc`, `x` and `m` the run reaches `tgt` with the registers and the memory in `Q`. -/
def Reach (A : List (BitVec 64)) (prog : List instruction) (base pc : BitVec 64) (x : Regs)
    (m : Mem) (tgt : BitVec 64) (Q : Regs → Mem → Prop) : Prop :=
  ∃ k x' m', stepsM A prog base k pc x m = some (tgt, x', m') ∧ Q x' m'

theorem stepsM_add {A : List (BitVec 64)} {prog : List instruction} {base : BitVec 64} :
    ∀ (k₁ k₂ : Nat) (pc : BitVec 64) (x : Regs) (m : Mem),
      stepsM A prog base (k₁ + k₂) pc x m =
        (stepsM A prog base k₁ pc x m).bind fun s => stepsM A prog base k₂ s.1 s.2.1 s.2.2
  | 0, _, _, _, _ => by simp [stepsM]
  | k₁ + 1, k₂, pc, x, m => by
    rw [show k₁ + 1 + k₂ = (k₁ + k₂) + 1 by omega]
    simp only [stepsM]
    split
    · rfl
    · split
      · rfl
      · exact stepsM_add k₁ k₂ _ _ _

theorem Reach.refl {A : List (BitVec 64)} {prog : List instruction} {base pc : BitVec 64}
    {x : Regs} {m : Mem} {Q : Regs → Mem → Prop} (h : Q x m) : Reach A prog base pc x m pc Q :=
  ⟨0, x, m, rfl, h⟩

theorem Reach.trans {A : List (BitVec 64)} {prog : List instruction} {base pc mid tgt : BitVec 64}
    {x : Regs} {m : Mem} {Q R : Regs → Mem → Prop} (h : Reach A prog base pc x m mid Q)
    (h' : ∀ x' m', Q x' m' → Reach A prog base mid x' m' tgt R) :
    Reach A prog base pc x m tgt R := by
  obtain ⟨k, x', m', hk, hq⟩ := h
  obtain ⟨k', x'', m'', hk', hr⟩ := h' x' m' hq
  exact ⟨k + k', x'', m'', by rw [stepsM_add, hk]; exact hk', hr⟩

theorem Reach.mono {A : List (BitVec 64)} {prog : List instruction} {base pc tgt : BitVec 64}
    {x : Regs} {m : Mem} {Q R : Regs → Mem → Prop} (h : Reach A prog base pc x m tgt Q)
    (hq : ∀ x' m', Q x' m' → R x' m') : Reach A prog base pc x m tgt R := by
  obtain ⟨k, x', m', hk, h⟩ := h
  exact ⟨k, x', m', hk, hq x' m' h⟩

/-- A run of `arunM` to `tgt` reaches it. -/
theorem stepsM_of_arunM {A : List (BitVec 64)} {prog : List instruction} {base tgt : BitVec 64} :
    ∀ (n : Nat) (pc : BitVec 64) (x x' : Regs) (m m' : Mem),
      arunM A prog base tgt n pc x m = some (x', m') →
      ∃ k, stepsM A prog base k pc x m = some (tgt, x', m')
  | 0, _, _, _, _, _, h => by simp [arunM] at h
  | n + 1, pc, x, x', m, m', h => by
    unfold arunM at h
    by_cases hp : pc = tgt
    · rw [if_pos hp] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨0, by rw [hp]; rfl⟩
    · rw [if_neg hp] at h
      split at h
      · contradiction
      · rename_i i hf
        split at h
        · contradiction
        · rename_i pc' x'' m'' hi
          obtain ⟨k, hk⟩ := stepsM_of_arunM n pc' x'' x' m'' m' h
          exact ⟨k + 1, by simp [stepsM, hf, hi, hk]⟩

/-- A segment proved by running it as `arunM` with the cut point `tgt` as the return address. -/
theorem reach_of_arunM {A : List (BitVec 64)} {prog : List instruction} {base pc tgt : BitVec 64}
    {x : Regs} {m : Mem} {Q : Regs → Mem → Prop}
    (h : ∃ n x' m', arunM A prog base tgt n pc x m = some (x', m') ∧ Q x' m') :
    Reach A prog base pc x m tgt Q := by
  obtain ⟨n, x', m', ha, hq⟩ := h
  obtain ⟨k, hk⟩ := stepsM_of_arunM n pc x x' m m' ha
  exact ⟨k, x', m', hk, hq⟩

/-- The address of an instruction of `prog` at `base` is not `ret`, past the code. -/
theorem fetch_ne_ret {α : Type} {prog : List α} {base ret pc : BitVec 64} {i : α}
    (hl : 4 * prog.length ≤ (ret - base).toNat) (hf : fetch prog base pc = some i) : pc ≠ ret := by
  rintro rfl
  unfold fetch at hf
  split at hf
  · rename_i ha
    have hlt := (List.getElem?_eq_some_iff.mp hf).1
    rw [BitVec.toNat_ushiftRight] at hlt
    have h3 : (pc - base).toNat % 4 = 0 := by
      have := congrArg BitVec.toNat ha
      simp only [BitVec.toNat_and, show BitVec.toNat (3 : BitVec 64) = 2 ^ 2 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod] at this
      simpa using this
    simp only [Nat.shiftRight_eq_div_pow] at hlt
    omega
  · contradiction

/-- The steps that reach `ret`, past the code, are a run of `arunM` to it. -/
theorem arunM_of_stepsM {A : List (BitVec 64)} {prog : List instruction} {base ret : BitVec 64}
    (hl : 4 * prog.length ≤ (ret - base).toNat) :
    ∀ (k : Nat) (pc : BitVec 64) (x x' : Regs) (m m' : Mem),
      stepsM A prog base k pc x m = some (ret, x', m') →
      arunM A prog base ret (k + 1) pc x m = some (x', m')
  | 0, pc, x, x', m, m', h => by
    simp only [stepsM, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp [arunM]
  | k + 1, pc, x, x', m, m', h => by
    unfold stepsM at h
    split at h
    · contradiction
    · rename_i i hf
      split at h
      · contradiction
      · rename_i pc' x'' m'' hi
        unfold arunM
        rw [if_neg (fetch_ne_ret hl hf), hf]
        simp only [hi]
        exact arunM_of_stepsM hl k pc' x'' x' m'' m' h

/-- `RunsM` from the `Reach` of the return address from the start of the code. -/
theorem runsM_of_reach {code : Code} {prog : List instruction} {bufs : Regs → List (BitVec 64)}
    {pre : Regs → Mem → Prop} {post : Regs → Mem → Regs → Mem → Prop} (hd : Decodes code prog)
    (h : ∀ base ret : BitVec 64, base &&& 3 = 0 → ret &&& 3 = 0 →
      4 * code.length ≤ (ret - base).toNat → ∀ (x : Regs) (m : Mem), x 1#5 = ret → pre x m →
      Reach (bufs x) prog base base x m ret (post x m)) :
    RunsM code bufs pre post := by
  refine runsM_of_arunM hd fun base ret hb hr hl x m hx hp => ?_
  obtain ⟨k, x', m', hk, hq⟩ := h base ret hb hr hl x m hx hp
  exact ⟨k + 1, x', m', arunM_of_stepsM (hd.1 ▸ hl) k base x x' m m' hk, hq⟩

end IntxRV
