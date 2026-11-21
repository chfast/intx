import IntxRV.Run
/-!
# Decoding

`DecodesTo w i`: the decoder of the Sail model (`ext_decode`) decodes the word `w` to the
instruction `i`. The decoder reads the state: its guards check that extensions are enabled (`misa`
for M, the landing pads of Zicfilp for the privilege level). The tactic `rv_decode` evaluates the
decoder on the word in the environment.
-/

open Sail Sail.ConcurrencyInterfaceV1 PreSail
open LeanRV64D LeanRV64D.Functions LeanRV64D.Defs

namespace IntxRV

/-- The Sail model decodes the word `w` to the instruction `i` in every environment. -/
def DecodesTo (w : BitVec 32) (i : instruction) : Prop :=
  ∀ (S s : SailState) (val : (r : Register) → RegisterType r) (pc npc : BitVec 64) (x : Regs),
    Env S val → Inv S s pc npc x → ext_decode w s = .ok i s

theorem decodes_of {code : Code} {prog : List instruction} (hl : code.length = prog.length)
    (h : ∀ k (hk : k < code.length) (hk' : k < prog.length), DecodesTo code[k] prog[k]) :
    Decodes code prog :=
  ⟨hl, fun k hk hk' S s val pc npc x e hi => h k hk hk' S s val pc npc x e hi⟩

theorem decodes_nil : Decodes [] [] :=
  decodes_of rfl fun _ hk => absurd hk (by simp)

theorem decodes_cons {w : BitVec 32} {i : instruction} {code : Code} {prog : List instruction}
    (h : DecodesTo w i) (t : Decodes code prog) : Decodes (w :: code) (i :: prog) := by
  refine decodes_of (by simp [t.1]) fun k hk hk' => ?_
  cases k with
  | zero => exact h
  | succ k =>
    intro S s val pc npc x e hi
    exact t.2 k (by simpa using hk) (by simpa using hk') S s val pc npc x e hi

theorem decodes_append {c₁ c₂ : Code} {p₁ p₂ : List instruction} (h₁ : Decodes c₁ p₁)
    (h₂ : Decodes c₂ p₂) : Decodes (c₁ ++ c₂) (p₁ ++ p₂) := by
  refine decodes_of (by simp [h₁.1, h₂.1]) fun k hk hk' => ?_
  intro S s val pc npc x e hi
  by_cases hl : k < c₁.length
  · rw [List.getElem_append_left hl, List.getElem_append_left (h₁.1 ▸ hl)]
    exact h₁.2 k hl (h₁.1 ▸ hl) S s val pc npc x e hi
  · rw [List.getElem_append_right (by omega), List.getElem_append_right (by rw [← h₁.1]; omega)]
    simp only [List.length_append] at hk hk'
    have h := h₂.2 (k - c₁.length) (by omega) (by rw [← h₂.1]; omega) S s val pc npc x e hi
    simp only [h₁.1] at h ⊢
    exact h

/-- Proves `DecodesTo w i` for a word `w` by evaluating the decoder. -/
macro "rv_decode" : tactic => `(tactic| (
  intro S s val pc npc x e h
  obtain ⟨b, hb⟩ := get_xLPE_env e h
  unfold ext_decode
  delta encdec_backwards
  simp (config := { decide := true }) only [bind, EStateM.bind, pure, pure_bind', pure_apply',
    ite_apply', Sail.BitVec.extractLsb, BitVec.extractLsb, if_true, if_false, currentlyEnabled,
    hartSupports, Bool.true_and, Bool.false_and, Bool.and_false, Bool.and_true, Bool.and_eq_true,
    and_false, false_and, Bool.or_false, Bool.false_or, Bool.or_true, readReg_env e h, isRunReg,
    LeanRV64D.readReg, hb, e.misa_M, encdec_reg_backwards, encdec_mul_op_backwards,
    encdec_bop_backwards, encdec_iop_backwards, encdec_uop_backwards, Nat.reduceAdd, Nat.reduceSub,
    BitVec.reduceExtractLsb', Int.reduceToNat, Int.reduceSub, Functions.regidx_bit_width]
  try rfl))

end IntxRV
