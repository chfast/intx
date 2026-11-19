import IntxRV.Gen.Api
import IntxRV.Arith
import IntxRV.Image
import IntxRV.Clz
import Mathlib.Tactic.Ring
import IntxRV.Bits
/-!
# `bit_test()` of `uint256`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Tests the bit of x at bit_index.
/// @pre bit_index < N
/// @post result <-> x.testBit bit_index
template <unsigned N>
constexpr bool bit_test(const uint<N>& x, size_t bit_index) noexcept
```

`bit_test_256.spec` states it for the RV64 machine code of `bit_test_256` in `IntxRV/Api.cpp`
(generated in `IntxRV/Gen/Api.lean`, see `IntxRV/README.md`). The function loads the word of the bit
at an address computed from the bit index (`shr3_and`). `rv_exec` runs the instructions, and
`testBit_words` (`IntxRV/Bits.lean`) gives the bit of the number.
-/

set_option maxRecDepth 100000
-- The paths use different lemmas of the same simp calls.
set_option linter.unusedSimpArgs false

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 4000000 in
theorem bit_test_256.reach (base : BitVec 64) (x : Regs) (m : Mem) (hra : x.get 1#5 &&& 3 = 0)
    (hpre : bit_test_256.pre x m) :
    Reach (bit_test_256.bufs x) bit_test_256_prog base (pcAt base 0) x m (x.get 1#5)
      (bit_test_256.post x m) := by
  simp only [bit_test_256.pre, bit_test_256.bufs, Buf] at hpre ⊢
  simp (disch := decide) only [Regs.eq_get x] at hpre ⊢
  rv_exec
  refine Reach.step (by decide) rfl ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  simp only [Defn] at *
  subst_vars
  have hi : (x.get 11#5).toNat / 64 < 4 := by omega
  rw [shr3_and]
  refine ⟨mem_bufWords hi, fun w hw => ?_⟩
  rv_exec
  rv_val
  simp only [update_aligned hra]
  refine Reach.refl ?_
  simp only [bit_test_256.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, and_true, true_and]
  simp (disch := decide) only [Regs.eq_get x]
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  simp only [Defn] at *
  subst_vars
  rw [testBit_words m 4 _ _ (by omega)]
  refine ⟨by simp [shr_and_one_eq_one], and_one_cases _, ?_⟩
  simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte, BitVec.ofNat_eq_ofNat,
    and_self, and_true, true_and]
  simp (disch := decide) only [Regs.eq_get x, and_self]

theorem bit_test_256.proof : bit_test_256.spec :=
  runsM_of_reach bit_test_256_decodes fun base ret _ hr _ x m hx1 hpre => by
    have hx : x.get 1#5 = ret := by rw [← Regs.eq_get x (by decide)]; exact hx1
    have h := bit_test_256.reach base x m (hx ▸ hr) hpre
    rwa [pcAt_zero, hx] at h

end IntxRV.Api
