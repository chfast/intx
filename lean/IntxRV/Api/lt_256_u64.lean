import IntxRV.Gen.Api
import IntxRV.Arith
import IntxRV.Conv
/-!
# `operator<` of `uint256` and `uint64_t`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Compares with a builtin integer of up to 64 bits as with its uint conversion, which goes
/// through uint64_t, so -1 compares as 2^64 - 1.
/// @post result <-> (x : Int) < (y : Int) % 2 ^ 64
template <std::same_as<uint> U, std::integral T>
    requires(sizeof(T) <= sizeof(uint64_t))
friend constexpr bool operator<(const U& x, T y) noexcept
```

`lt_256_u64.spec` states it for the RV64 machine code of `lt_256_u64` in `IntxRV/Api.cpp` (generated
in `IntxRV/Gen/Api.lean`, see `IntxRV/README.md`). The function compares the low word with y and
tests the high words for 0 (`words4_lt_iff`, `IntxRV/Conv.lean`).
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 4000000

theorem lt_256_u64.proof : lt_256_u64.spec :=
  runsM_of_reach lt_256_u64_decodes fun base ret _ hr _ x m hx1 hpre => by
    simp only [lt_256_u64.pre, lt_256_u64.bufs, Buf] at hpre ⊢
    simp (disch := decide) only [Regs.eq_get x] at hpre hx1 ⊢
    subst hx1
    refine Reach.start ?_
    rv_exec
    rv_val
    simp only [update_aligned hr]
    refine Reach.refl ?_
    simp only [lt_256_u64.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    simp (disch := decide) only [Regs.eq_get x]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    simp only [Defn] at *
    subst_vars
    simp only [BitVec.ofNat_eq_ofNat] at *
    refine ⟨?_, ite_and_ite_cases _ _, trivial, ?_⟩
    · rw [decide_eq_true_eq, ite_and_ite_eq_one,
        show ((x.get 11#5).toNat : Int) % 2 ^ 64 = (x.get 11#5).toNat by
          have := (x.get 11#5).isLt; omega,
        Int.ofNat_lt]
      simp only [words, Nat.mul_zero, Nat.add_zero, BitVec.add_assoc, BitVec.reduceAdd,
        words4_lt_iff, BitVec.or_eq_zero_iff]
      tauto
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
      simp (disch := decide) only [Regs.eq_get x, and_self]

end IntxRV.Api
