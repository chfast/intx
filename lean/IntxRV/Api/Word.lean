import IntxRV.Gen.Api
import IntxRV.Tactic
import Intx.Proofs.Div
/-!
# The proofs of the word functions

`umul()`, `addc()` and `udivrem_2by1()` take and return their values in registers. `rv_run`
proves that the machine code computes the model of `Intx.Model`, and the specification follows
from the proofs of the model: `umul_spec`, `addc_spec` and `udivrem_2by1_v_spec`.
-/

-- rv_run evaluates the runs with simp, and passes it lemmas some paths do not use.
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace IntxRV.Api
open IntxRV IntxRV.Gen Intx Intx.Model

theorem umul.model : Runs umul_code umul.pre fun x x' =>
    x'.get 10#5 = (Model.umul (.ofBitVec (x 10#5)) (.ofBitVec (x 11#5))).lo.toBitVec ∧
    x'.get 11#5 = (Model.umul (.ofBitVec (x 10#5)) (.ofBitVec (x 11#5))).hi.toBitVec ∧
    ∀ i ∈ calleeSaved, x' i = x i := by
  rv_run umul_decodes with umul_code umul_prog using []

theorem umul.proof : umul.spec :=
  umul.model.mono (fun _ h => h) fun x _ _ ⟨h0, h1, hc⟩ =>
    ⟨by simpa [h0, h1] using umul_spec (.ofBitVec (x 10#5)) (.ofBitVec (x 11#5)), hc⟩

/-- With the `bool` argument `c` in a2, the `bool` result is 0 or 1 in a1. -/
theorem addc.model (c : Bool) : Runs addc_code (fun x => x 12#5 = if c then 1 else 0)
    fun x x' =>
      x'.get 10#5 = (Model.addc (.ofBitVec (x 10#5)) (.ofBitVec (x 11#5)) c).1.toBitVec ∧
      x'.get 11#5 = (if (Model.addc (.ofBitVec (x 10#5)) (.ofBitVec (x 11#5)) c).2 then 1 else 0) ∧
      ∀ i ∈ calleeSaved, x' i = x i := by
  rv_run addc_decodes with addc_code addc_prog using [Model.addc]

theorem addc.proof : addc.spec := by
  intro S val e base ret hb hr hl s npc x hs hx hp
  have hc : x 12#5 = if decide (x 12#5 = 1) then 1 else 0 := by
    rcases hp with h | h <;> rw [h] <;> rfl
  obtain ⟨n, s', npc', x', hrun, hs', h0, h1, hcs⟩ :=
    addc.model (decide (x 12#5 = 1)) S val e base ret hb hr hl s npc x hs hx hc
  refine ⟨n, s', npc', x', hrun, hs', ?_, ?_, hcs⟩
  · have := addc_spec (.ofBitVec (x 10#5)) (.ofBitVec (x 11#5)) (decide (x 12#5 = 1))
    rw [h0, h1]
    clear hc hp hcs h0 h1
    split <;> simp_all
  · rw [h1]
    split <;> simp

theorem addc.nonvacuous : ∃ x, addc.pre x := ⟨fun _ => 0, Or.inl rfl⟩

/-- The `uint128` argument `u` is in a1:a0, the divisor `d` in a2 and the reciprocal `v` in a3;
the quotient is returned in a0 and the remainder in a1. -/
theorem udivrem_2by1.model : Runs udivrem_2by1_code (fun _ => True) fun x x' =>
    x'.get 10#5 = (udivrem_2by1_v ⟨.ofBitVec (x 10#5), .ofBitVec (x 11#5)⟩ (.ofBitVec (x 12#5))
      (.ofBitVec (x 13#5))).1.toBitVec ∧
    x'.get 11#5 = (udivrem_2by1_v ⟨.ofBitVec (x 10#5), .ofBitVec (x 11#5)⟩ (.ofBitVec (x 12#5))
      (.ofBitVec (x 13#5))).2.toBitVec ∧
    ∀ i ∈ calleeSaved, x' i = x i := by
  rv_run udivrem_2by1_decodes with udivrem_2by1_code udivrem_2by1_prog using [udivrem_2by1_v]

theorem udivrem_2by1.proof : udivrem_2by1.spec :=
  udivrem_2by1.model.mono (fun _ _ => trivial) fun x _ ⟨hd, hu, hv⟩ ⟨h0, h1, hc⟩ => by
    simp only at hd hu hv ⊢
    have hdl := (x 12#5).isLt
    have hlo := (x 10#5).isLt
    have hq : 2 ^ 64 ≤ (2 ^ 128 - 1) / (x 12#5).toNat :=
      (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    have hv1 : (2 ^ 64 + (x 13#5).toNat) * (x 12#5).toNat < 2 ^ 128 := by
      have := Nat.div_mul_le_self (2 ^ 128 - 1) (x 12#5).toNat
      rw [show 2 ^ 64 + (x 13#5).toNat = (2 ^ 128 - 1) / (x 12#5).toNat by omega]
      omega
    have hv2 : 2 ^ 128 ≤ (2 ^ 64 + (x 13#5).toNat + 1) * (x 12#5).toNat := by
      have := Nat.lt_mul_div_succ (2 ^ 128 - 1) (show 0 < (x 12#5).toNat by omega)
      rw [show 2 ^ 64 + (x 13#5).toNat = (2 ^ 128 - 1) / (x 12#5).toNat by omega, Nat.mul_comm]
      omega
    have := udivrem_2by1_v_spec ⟨.ofBitVec (x 10#5), .ofBitVec (x 11#5)⟩ (.ofBitVec (x 12#5))
      (.ofBitVec (x 13#5)) hd (by simp; omega) hv1 hv2
    refine ⟨?_, ?_, hc⟩ <;> simp_all [U128.toNat]

theorem udivrem_2by1.nonvacuous : ∃ x, udivrem_2by1.pre x :=
  ⟨fun i => if i = 12#5 then 0x8000000000000000#64 else if i = 13#5 then -1#64 else 0, by
    simp (config := { decide := true }) [udivrem_2by1.pre]⟩

end IntxRV.Api
