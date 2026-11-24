import IntxRV.Gen.Api
import IntxRV.Arith
/-!
# `be::unsafe::store()` of `uint256`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Overload for uint256.
/// @pre dst.size() = 32
/// @post bigEndian dst = x
inline void store(uint8_t* dst, const uint256& x) noexcept
```

`be_store_256.spec` states it for the RV64 machine code of `be_store_256` in `IntxRV/Api.cpp`
(generated in `IntxRV/Gen/Api.lean`, see `IntxRV/README.md`). The function saves 13 registers in its
frame, loads the 4 words and stores their 32 bytes with `sb`, the most significant first: the
addresses as numbers from the buffers and the frame (`toNat_add_ofNat`, `toNat_add_frame`,
`IntxRV/Bytes.lean`) for `omega`, the byte stored of a word shifted right by 8k is `byteAt` of the
word, and `bigEndian_byteAt32` gives the number.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem be_store_256.proof : be_store_256.spec :=
  runsM_of_reach be_store_256_decodes fun base ret _ hr _ x m hx1 hpre => by
    simp only [be_store_256.pre, be_store_256.bufs, BufBytes, Buf, Disjoint] at hpre ⊢
    simp (disch := decide) only [Regs.eq_get x] at hpre hx1 ⊢
    subst hx1
    have hA : ∀ k, k < 32 → (x.get 10#5 + BitVec.ofNat 64 k).toNat = (x.get 10#5).toNat + k :=
      fun k hk => toNat_add_ofNat _ k (by omega)
    have hB : ∀ k, k < 32 → (x.get 11#5 + BitVec.ofNat 64 k).toNat = (x.get 11#5).toNat + k :=
      fun k hk => toNat_add_ofNat _ k (by omega)
    have hS : ∀ c : BitVec 64, 2 ^ 64 - 112 ≤ c.toNat →
        (x.get 2#5 + c).toNat = (x.get 2#5 - 112#64).toNat + (c.toNat + 112 - 2 ^ 64) :=
      fun c hc => toNat_add_frame _ c 112 hc (by decide) (by omega)
    refine Reach.start ?_
    rv_exec
    simp (disch := first | decide | omega) only [hA, hB, hS, BitVec.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd] at *
    simp (disch := omega) only [memWord_memStoreByte_of_ne, memWord_memStore_self,
      memWord_memStore_of_ne] at *
    rv_val
    simp only [Defn] at *
    subst_vars
    try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    simp only [update_aligned hr]
    refine Reach.refl ?_
    simp only [be_store_256.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    simp (disch := decide) only [Regs.eq_get x]
    refine ⟨?_, ?_, ?_⟩
    · simp only [bytes, bytesAt, Nat.add_assoc, Nat.reduceAdd]
      simp (config := { decide := true }) only [memByte_memStoreByte_add,
        memByte_memStoreByte_add_zero, memByte_memStoreByte_zero_add, memByte_memStoreByte_self,
        ↓reduceIte]
      simp (disch := decide) only [setWidth_ushiftRight_eq_byteAt, Nat.reduceDiv]
      simp only [setWidth_eq_byteAt]
      rw [bigEndian_byteAt32]
      simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
        Nat.add_zero]
      simp (disch := first | decide | omega) only [hB, Nat.reducePow]
    · simp (disch := omega) only [unchangedExcept2_memStoreByte, unchangedExcept2_memStore,
        unchangedExcept2_refl]
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte, BitVec.ofNat_eq_ofNat,
        and_self, and_true, true_and]
      simp (disch := decide) only [Regs.eq_get x, and_self]

end IntxRV.Api
