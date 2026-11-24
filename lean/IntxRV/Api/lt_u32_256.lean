import IntxRV.Gen.Api
import IntxRV.Arith
import IntxRV.Conv
/-!
# `operator<` of `unsigned` and `uint256`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Compares a builtin integer of up to 64 bits as its uint conversion with y.
/// @post result <-> (x : Int) % 2 ^ 64 < (y : Int)
template <std::same_as<uint> U, std::integral T>
    requires(sizeof(T) <= sizeof(uint64_t))
friend constexpr bool operator<(T x, const U& y) noexcept
```

`lt_u32_256.spec` states it for the RV64 machine code of `lt_u32_256` in `IntxRV/Api.cpp` (generated
in `IntxRV/Gen/Api.lean`, see `IntxRV/README.md`). The function compares the low 32 bits of the
register of x (`slli`, `srli`) with the low word and tests the high words for 0 (`lt_words4_iff`,
`IntxRV/Conv.lean`).
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 4000000

theorem lt_u32_256.proof : lt_u32_256.spec :=
  runsM_of_reach lt_u32_256_decodes fun base ret _ hr _ x m hx1 hpre => by
    simp only [lt_u32_256.pre, lt_u32_256.bufs, Buf] at hpre ⊢
    simp (disch := decide) only [Regs.eq_get x] at hpre hx1 ⊢
    subst hx1
    refine Reach.start ?_
    rv_exec
    rv_val
    simp only [update_aligned hr]
    refine Reach.refl ?_
    simp only [lt_u32_256.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    simp (disch := decide) only [Regs.eq_get x]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    simp only [Defn] at *
    subst_vars
    simp only [BitVec.ofNat_eq_ofNat] at *
    refine ⟨?_, ite_or_ite_cases _ _, trivial, ?_⟩
    · have hz : ((x.get 10#5 <<< 32) >>> 32).toNat = (x.get 10#5).toNat % 2 ^ 32 := by
        simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
          Nat.shiftRight_eq_div_pow]
        omega
      have key :
          (((x.get 10#5).toNat % 2 ^ 32 : Nat) : Int) % 2 ^ 64 < (words m (x.get 11#5) 4 : Int) ↔
          (x.get 10#5 <<< 32 >>> 32).toNat < words m (x.get 11#5) 4 := by
        rw [hz]; omega
      rw [decide_eq_true_eq, ite_or_ite_eq_one, zero_lt_iff_ne_zero]
      refine Iff.trans ?_ key.symm
      simp only [words, Nat.mul_zero, Nat.add_zero, BitVec.add_assoc, BitVec.reduceAdd,
        lt_words4_iff, ne_eq, BitVec.or_eq_zero_iff]
      tauto
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
      simp (disch := decide) only [Regs.eq_get x, and_self]

end IntxRV.Api
