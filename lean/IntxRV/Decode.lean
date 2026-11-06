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
