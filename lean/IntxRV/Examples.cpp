// intx: extended precision integer library.
// Copyright 2026 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

// The intx functions whose RV64 machine code is verified against the Sail RISC-V model.
//
// A [[gnu::used]] pointer to a function makes the compiler emit its out-of-line copy (in its own
// section, with -ffunction-sections). scripts/rv_gen.py extracts the machine code of these
// functions to IntxRV/Gen/Code.lean and the lean blocks of this file to IntxRV/Examples.lean.
// The first theorem of a block states that the machine code computes the model of the function
// (Intx.Model) on the argument registers a0 (x10), a1 (x11), ... and returns it in a0 and a1;
// the second derives the specification of the function from the proofs of the model.

#include <intx/intx.hpp>

using intx::uint128;

[[gnu::used]] constexpr auto* umul =
    static_cast<uint128 (*)(uint64_t, uint64_t) noexcept>(&intx::umul);
/* lean
theorem umul_rv : Runs umul_code (fun _ => True) fun x x' =>
    x'.get 10#5 = (Model.umul (.ofBitVec (x 10#5)) (.ofBitVec (x 11#5))).lo.toBitVec ∧
    x'.get 11#5 = (Model.umul (.ofBitVec (x 10#5)) (.ofBitVec (x 11#5))).hi.toBitVec ∧
    ∀ i ∈ calleeSaved, x' i = x i := by
  rv_run umul_decodes with umul_code umul_prog using []

/-- `umul(x, y)` returns the 128-bit product `x * y` in a1:a0. -/
theorem umul_rv_spec : Runs umul_code (fun _ => True) fun x x' =>
    (x'.get 10#5).toNat + 2 ^ 64 * (x'.get 11#5).toNat = (x 10#5).toNat * (x 11#5).toNat :=
  umul_rv.mono (fun _ h => h) fun x _ _ ⟨h0, h1, _⟩ => by
    simpa [h0, h1] using umul_spec (.ofBitVec (x 10#5)) (.ofBitVec (x 11#5))
*/

[[gnu::used]] constexpr auto* addc =
    static_cast<intx::result_with_carry<uint64_t> (*)(uint64_t, uint64_t, bool) noexcept>(
        &intx::addc);
/* lean
/-- The `bool` argument is 0 or 1 in a2, the `bool` result 0 or 1 in a1. -/
theorem addc_rv (c : Bool) : Runs addc_code (fun x => x 12#5 = if c then 1 else 0) fun x x' =>
    x'.get 10#5 = (Model.addc (.ofBitVec (x 10#5)) (.ofBitVec (x 11#5)) c).1.toBitVec ∧
    x'.get 11#5 = (if (Model.addc (.ofBitVec (x 10#5)) (.ofBitVec (x 11#5)) c).2 then 1 else 0) ∧
    ∀ i ∈ calleeSaved, x' i = x i := by
  rv_run addc_decodes with addc_code addc_prog using [Model.addc]

/-- `addc(x, y, c)` returns the sum `x + y + c` in a1:a0. -/
theorem addc_rv_spec (c : Bool) : Runs addc_code (fun x => x 12#5 = if c then 1 else 0)
    fun x x' => (x'.get 10#5).toNat + 2 ^ 64 * (x'.get 11#5).toNat =
      (x 10#5).toNat + (x 11#5).toNat + c.toNat :=
  (addc_rv c).mono (fun _ h => h) fun x _ _ ⟨h0, h1, _⟩ => by
    have := addc_spec (.ofBitVec (x 10#5)) (.ofBitVec (x 11#5)) c
    rw [h0, h1]
    split <;> simp_all
*/

[[gnu::used]] constexpr auto* udivrem_2by1 =
    static_cast<intx::div_result<uint64_t> (*)(uint128, uint64_t, uint64_t) noexcept>(
        &intx::udivrem_2by1);
/* lean
/-- The `uint128` argument `u` is in a1:a0, the divisor `d` in a2 and the reciprocal `v` in a3;
the quotient is returned in a0 and the remainder in a1. -/
theorem udivrem_2by1_rv : Runs udivrem_2by1_code (fun _ => True) fun x x' =>
    x'.get 10#5 = (udivrem_2by1_v ⟨.ofBitVec (x 10#5), .ofBitVec (x 11#5)⟩ (.ofBitVec (x 12#5))
      (.ofBitVec (x 13#5))).1.toBitVec ∧
    x'.get 11#5 = (udivrem_2by1_v ⟨.ofBitVec (x 10#5), .ofBitVec (x 11#5)⟩ (.ofBitVec (x 12#5))
      (.ofBitVec (x 13#5))).2.toBitVec ∧
    ∀ i ∈ calleeSaved, x' i = x i := by
  rv_run udivrem_2by1_decodes with udivrem_2by1_code udivrem_2by1_prog using [udivrem_2by1_v]

/-- `udivrem_2by1(u, d, v)` returns the quotient and the remainder of `u / d` for a normalized
`d`, `u` less than `d * 2^64` and the reciprocal `v` of `d`. -/
theorem udivrem_2by1_rv_spec : Runs udivrem_2by1_code
    (fun x => 2 ^ 63 ≤ (x 12#5).toNat ∧ (x 11#5).toNat < (x 12#5).toNat ∧
      (2 ^ 64 + (x 13#5).toNat) * (x 12#5).toNat < 2 ^ 128 ∧
      2 ^ 128 ≤ (2 ^ 64 + (x 13#5).toNat + 1) * (x 12#5).toNat)
    fun x x' =>
      (x'.get 10#5).toNat = ((x 10#5).toNat + 2 ^ 64 * (x 11#5).toNat) / (x 12#5).toNat ∧
      (x'.get 11#5).toNat = ((x 10#5).toNat + 2 ^ 64 * (x 11#5).toNat) % (x 12#5).toNat :=
  udivrem_2by1_rv.mono (fun _ _ => trivial) fun x _ ⟨hd, hu, hv1, hv2⟩ ⟨h0, h1, _⟩ => by
    have := udivrem_2by1_v_spec ⟨.ofBitVec (x 10#5), .ofBitVec (x 11#5)⟩ (.ofBitVec (x 12#5))
      (.ofBitVec (x 13#5)) hd hu hv1 hv2
    simpa [h0, h1, U128.toNat] using this
*/
