import IntxRV.Gen.Api
import IntxRV.Arith
/-!
# `operator uint8_t` of `uint256`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Explicit converting operator for all builtin integral types.
/// @post result % 2^(8 * sizeof(Int)) = self % 2^(8 * sizeof(Int))
/// @note FV: not proved for Int = bool, which operator bool serves.
template <typename Int>
constexpr explicit operator Int() const noexcept
    requires(std::is_integral_v<Int>)
```

`to_u8_256.spec` states it for the RV64 machine code of `to_u8_256` in `IntxRV/Api.cpp` (generated
in `IntxRV/Gen/Api.lean`, see `IntxRV/README.md`). The function loads the low byte with `lbu`, the
byte 0 of the low word (`byteAt_memWord`, `IntxRV/Bytes.lean`).
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 4000000

theorem to_u8_256.proof : to_u8_256.spec :=
  runsM_of_reach to_u8_256_decodes fun base ret _ hr _ x m hx1 hpre => by
    simp only [to_u8_256.pre, to_u8_256.bufs, Buf] at hpre ⊢
    simp (disch := decide) only [Regs.eq_get x] at hpre hx1 ⊢
    subst hx1
    refine Reach.start ?_
    refine Reach.step (by decide) rfl ?_
    simp only [StepGoal, Nat.reduceAdd, BitVec.reduceSignExtend]
    refine ⟨and_not7_mem_bufWords hpre.1 (by decide : 0 < 8 * 4), fun w hw => ?_⟩
    rv_exec
    try rv_val
    try simp only [update_aligned hr]
    refine Reach.refl ?_
    simp only [to_u8_256.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    simp (disch := decide) only [Regs.eq_get x]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    simp only [Defn] at *
    subst_vars
    have h := byteAt_memWord m (x.get 10#5).toNat 0 (by decide)
    rw [Nat.add_zero] at h
    refine ⟨?_, ?_, trivial, ?_⟩
    · rw [BitVec.add_zero, ← h, BitVec.toNat_setWidth, toNat_byteAt]
      simp only [words, Nat.mul_zero, Nat.add_zero, Nat.reduceMul, Nat.reducePow]
      omega
    · rw [BitVec.add_zero, ← h, BitVec.toNat_setWidth, toNat_byteAt]
      omega
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte, BitVec.ofNat_eq_ofNat]
      simp (disch := decide) only [Regs.eq_get x, and_self]

end IntxRV.Api
