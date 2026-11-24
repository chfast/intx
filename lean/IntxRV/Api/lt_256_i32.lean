import IntxRV.Gen.Api
import IntxRV.Arith
import IntxRV.Conv
/-!
# `operator<` of `uint256` and `int`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Compares with a builtin integer of up to 64 bits as with its uint conversion, which goes
/// through uint64_t, so -1 compares as 2^64 - 1.
/// @post result <-> (x : Int) < (y : Int) % 2 ^ 64
template <std::same_as<uint> U, std::integral T>
    requires(sizeof(T) <= sizeof(uint64_t))
friend constexpr bool operator<(const U& x, T y) noexcept
```

`lt_256_i32.spec` states it for the RV64 machine code of `lt_256_i32` in `IntxRV/Api.cpp` (generated
in `IntxRV/Gen/Api.lean`, see `IntxRV/README.md`). The function compares the low word with the
register of y and tests the high words for 0 (`words4_lt_iff`, `IntxRV/Conv.lean`); y modulo 2^64 is
the register (`toInt_emod`).
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 4000000

theorem lt_256_i32.proof : lt_256_i32.spec :=
  runsM_of_reach lt_256_i32_decodes fun base ret _ hr _ x m hx1 hpre => by
    simp only [lt_256_i32.pre, lt_256_i32.bufs, Buf, Disjoint] at hpre ⊢
    simp (disch := decide) only [Regs.eq_get x] at hpre hx1 ⊢
    subst hx1
    refine Reach.start ?_
    rv_exec
    rv_val
    simp only [update_aligned hr]
    refine Reach.refl ?_
    simp only [lt_256_i32.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    simp (disch := decide) only [Regs.eq_get x]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    simp only [Defn] at *
    subst_vars
    simp only [BitVec.ofNat_eq_ofNat] at *
    refine ⟨?_, ite_and_ite_cases _ _, trivial, ?_⟩
    · rw [decide_eq_true_eq, ite_and_ite_eq_one, toInt_emod, Int.ofNat_lt]
      simp only [words, Nat.mul_zero, Nat.add_zero, BitVec.add_assoc, BitVec.reduceAdd,
        words4_lt_iff, BitVec.or_eq_zero_iff]
      tauto
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte, BitVec.ofNat_eq_ofNat,
        and_self, and_true, true_and]
      simp (disch := decide) only [Regs.eq_get x, and_self]

end IntxRV.Api
