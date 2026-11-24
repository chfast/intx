import IntxRV.Gen.Api
import IntxRV.Arith
import IntxRV.Conv
/-!
# `operator int64_t` of `uint256`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Explicit converting operator for all builtin integral types.
/// @post result % 2 ^ (8 * sizeof(Int)) = self % 2 ^ (8 * sizeof(Int))
template <typename Int>
constexpr explicit operator Int() const noexcept
    requires(std::is_integral_v<Int>)
```

`to_i64_256.spec` states it for the RV64 machine code of `to_i64_256` in `IntxRV/Api.cpp` (generated
in `IntxRV/Gen/Api.lean`, see `IntxRV/README.md`). The function loads the low word: its bits are the
result as a signed integer modulo 2^64 (`toInt_emod`, `IntxRV/Conv.lean`).
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 4000000

theorem to_i64_256.proof : to_i64_256.spec :=
  runsM_of_reach to_i64_256_decodes fun base ret _ hr _ x m hx1 hpre => by
    simp only [to_i64_256.pre, to_i64_256.bufs, Buf, Disjoint] at hpre ⊢
    simp (disch := decide) only [Regs.eq_get x] at hpre hx1 ⊢
    subst hx1
    refine Reach.start ?_
    rv_exec
    rv_val
    simp only [update_aligned hr]
    refine Reach.refl ?_
    simp only [to_i64_256.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    simp (disch := decide) only [Regs.eq_get x]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    simp only [Defn] at *
    subst_vars
    refine ⟨?_, trivial, ?_⟩
    · simp only [Nat.reduceMul, toInt_emod, words, Nat.mul_zero, Nat.add_zero]
      omega
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte, BitVec.ofNat_eq_ofNat,
        and_self, and_true, true_and]
      simp (disch := decide) only [Regs.eq_get x, and_self]

end IntxRV.Api
