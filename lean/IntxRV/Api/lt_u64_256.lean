import IntxRV.Gen.Api.lt_u64_256
import IntxRV.Arith
import IntxRV.Conv
/-!
# `operator<` of `uint64_t` and `uint256`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Compares a builtin integer of up to 64 bits with y, as its uint conversion.
/// @post result ↔ (x : ℤ) % 2^64 < (y : ℤ)
template <std::same_as<uint> U, std::integral T>
    requires(sizeof(T) <= sizeof(uint64_t))
friend constexpr bool operator<(T x, const U& y) noexcept
```

`lt_u64_256.spec` states it for the RV64 machine code of `lt_u64_256` in `IntxRV/Api.cpp` (generated
in `IntxRV/Gen/Api/`, see `IntxRV/README.md`). The function compares x with the low word and
tests the high words for 0 (`lt_words4_iff`, `IntxRV/Conv.lean`).
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 4000000

theorem lt_u64_256.proof_of_decodes (hdec : lt_u64_256.decodes) : lt_u64_256.spec :=
  runsM_of_reach hdec fun base ret _ hr _ x m hx1 hpre => by
    simp only [lt_u64_256.pre, lt_u64_256.bufs, Buf] at hpre ⊢
    simp (disch := decide) only [Regs.eq_get x] at hpre hx1 ⊢
    subst hx1
    refine Reach.start ?_
    rv_exec
    rv_val
    simp only [update_aligned hr]
    refine Reach.refl ?_
    simp only [lt_u64_256.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    simp (disch := decide) only [Regs.eq_get x]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    simp only [Defn] at *
    subst_vars
    simp only [BitVec.ofNat_eq_ofNat] at *
    refine ⟨?_, ite_or_ite_cases _ _, trivial, ?_⟩
    · rw [decide_eq_true_eq, ite_or_ite_eq_one,
        show ((x.get 10#5).toNat : Int) % 2 ^ 64 = (x.get 10#5).toNat by
          have := (x.get 10#5).isLt; omega,
        Int.ofNat_lt, zero_lt_iff_ne_zero]
      simp only [words, Nat.mul_zero, Nat.add_zero, BitVec.add_assoc, BitVec.reduceAdd,
        lt_words4_iff, ne_eq, BitVec.or_eq_zero_iff]
      tauto
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
      simp (disch := decide) only [Regs.eq_get x, and_self]

end IntxRV.Api
