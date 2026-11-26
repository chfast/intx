import IntxRV.Gen.Api.udivrem_2by1
import IntxRV.Tactic
import Intx.Proofs.Div
/-!
# `udivrem_2by1()`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Divides u by the normalized d with its reciprocal v (Moller and Granlund, Algorithm 4).
/// @pre 2^63 ≤ d
/// @pre u < d * 2^64
/// @pre v = (2^128 - 1) / d - 2^64
/// @post result.quot = u / d
/// @post result.rem = u % d
constexpr div_result<uint64_t> udivrem_2by1(uint128 u, uint64_t d, uint64_t v) noexcept
```

`udivrem_2by1.spec` states it for the RV64 machine code of `udivrem_2by1` in `IntxRV/Api.cpp`
(generated in `IntxRV/Gen/Api/`, see `IntxRV/README.md`). `rv_run` proves that the machine code
computes the model `udivrem_2by1_v`, and the specification follows from its proof
`udivrem_2by1_v_spec` with the bounds that the reciprocal `v` gives.
-/

-- rv_run evaluates the runs with simp, and passes it lemmas some paths do not use.
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace IntxRV.Api
open IntxRV IntxRV.Gen Intx Intx.Model

/-- The `uint128` argument `u` is in a1:a0, the divisor `d` in a2 and the reciprocal `v` in a3;
the quotient is returned in a0 and the remainder in a1. -/
theorem udivrem_2by1.model (hdec : udivrem_2by1.decodes) :
    Runs udivrem_2by1_code (fun _ => True) fun x x' =>
      x'.get 10#5 = (udivrem_2by1_v ⟨.ofBitVec (x 10#5), .ofBitVec (x 11#5)⟩ (.ofBitVec (x 12#5))
        (.ofBitVec (x 13#5))).1.toBitVec ∧
      x'.get 11#5 = (udivrem_2by1_v ⟨.ofBitVec (x 10#5), .ofBitVec (x 11#5)⟩ (.ofBitVec (x 12#5))
        (.ofBitVec (x 13#5))).2.toBitVec ∧
      ∀ i ∈ calleeSaved, x' i = x i := by
  rv_run hdec with udivrem_2by1_code udivrem_2by1_prog using [udivrem_2by1_v]

theorem udivrem_2by1.proof_of_decodes (hdec : udivrem_2by1.decodes) : udivrem_2by1.spec :=
  (udivrem_2by1.model hdec).mono (fun _ _ => trivial) fun x _ ⟨hd, hu, hv⟩ ⟨h0, h1, hc⟩ => by
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
