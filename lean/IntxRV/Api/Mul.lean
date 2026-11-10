import IntxRV.Gen.Api
import IntxRV.Arith
/-!
# The proof of `umul()` of `uint256`

The function saves the callee-saved registers on the stack and computes the 512-bit product by
the products of the words with `mul` and `mulhu`, and the sums of their words with the carries
by `sltu`. `rv_exec` runs its 162 instructions one by one; `rv_arith` proves the product from the
words and the carries.
-/

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

namespace IntxRV.Api
open IntxRV IntxRV.Gen

/-- The run from the start of the code to the return address in ra. -/
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
    rw [mul_words4]
    rv_arith
  · simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore, unchangedExcept2_refl]
  · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte, BitVec.ofNat_eq_ofNat,
      and_self, and_true, true_and]
    simp (disch := decide) only [Regs.eq_get x, and_self]

theorem umul_256.proof : umul_256.spec :=
  runsM_of_reach umul_256_decodes fun base ret _ hr _ x m hx1 hpre => by
    have hx : x.get 1#5 = ret := by rw [← Regs.eq_get x (by decide)]; exact hx1
    have h := umul_256.reach base x m (hx ▸ hr) hpre
    rwa [pcAt_zero, hx] at h

end IntxRV.Api
