import IntxRV.Gen.Api.umul_256
import IntxRV.Umul256
/-!
# `umul()` of `uint256`

The specification, from `include/intx/intx.hpp`:

```cpp
/// The full product.
/// @post result = x * y
template <unsigned N>
constexpr uint<2 * N> umul(const uint<N>& x, const uint<N>& y) noexcept
```

`umul_256.spec` states it for the RV64 machine code of `umul_256` in `IntxRV/Api.cpp` (generated in
`IntxRV/Gen/Api/`, see `IntxRV/README.md`). The function saves the callee-saved registers on
the stack, computes the 16 products of the words with `mul` and `mulhu`, and adds them with `mac()`
as `add` and `sltu`, with some words spilled to the stack. `rv_exec` runs its 162 instructions,
without branches. `umul256_words` (`IntxRV/Umul256.lean`) gives the product from the definitions of
the values of the run, which `apply` and `assumption` find by the names of the stored words.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

/-- The run of `umul()` of `uint256` from any address of its code, for its calls. -/
theorem umul_256.reach (base : BitVec 64) (x : Regs) (m : Mem) (hra : x.get 1#5 &&& 3 = 0)
    (hpre : umul_256.pre x m) :
    Reach (umul_256.bufs x) umul_256_prog base (pcAt base 0) x m (x.get 1#5)
      (umul_256.post x m) := by
  simp only [umul_256.pre, umul_256.bufs, Buf, Disjoint] at hpre ⊢
  simp (disch := decide) only [Regs.eq_get x] at hpre ⊢
  rv_exec
  rv_copies
  rv_val
  simp only [update_aligned hra]
  refine Reach.refl ?_
  simp only [umul_256.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  simp (disch := decide) only [Regs.eq_get x]
  refine ⟨?_, ?_, ?_⟩
  · simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
      Nat.add_zero]
    simp (disch := first | bv_omega | fail) only [memWord_memStore_self, memWord_memStore_of_ne]
    rv_loads
    apply umul256_words
    all_goals assumption
  · simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore,
      unchangedExcept2_refl]
  · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte, BitVec.ofNat_eq_ofNat,
      and_self, and_true, true_and]
    simp (disch := decide) only [Regs.eq_get x, and_self]

theorem umul_256.proof_of_decodes (hdec : umul_256.decodes) : umul_256.spec :=
  runsM_of_reach hdec fun base ret _ hr _ x m hx1 hpre => by
    have hx : x.get 1#5 = ret := by rw [← Regs.eq_get x (by decide)]; exact hx1
    have h := umul_256.reach base x m (hx ▸ hr) hpre
    rwa [pcAt_zero, hx] at h

end IntxRV.Api
