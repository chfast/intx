import IntxRV.Gen.Api
import IntxRV.Arith
import IntxRV.Conv
/-!
# `be::trunc()` of `uint256` to `evmc::address`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Stores the truncated value of an uint in the .bytes field of an object of type T.
/// @post bigEndian result.bytes = x % 2 ^ (8 * sizeof(T))
template <typename T, unsigned N>
inline T trunc(const uint<N>& x) noexcept
```

`be_trunc_address.spec` states it for the RV64 machine code of `be_trunc_address` in
`IntxRV/Api.cpp` (generated in `IntxRV/Gen/Api.lean`, see `IntxRV/README.md`). The function saves 3
registers in its frame, loads the low 3 words and stores the low 20 bytes with `sb` to the result:
the addresses as numbers from the buffers and the frame (`toNat_add_ofNat`, `toNat_add_frame`,
`IntxRV/Bytes.lean`) for `omega`, and `bigEndian_byteAt20` gives the number modulo 2^160
(`words4_mod160`, `IntxRV/Conv.lean`).
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem be_trunc_address.proof : be_trunc_address.spec :=
  runsM_of_reach be_trunc_address_decodes fun base ret _ hr _ x m hx1 hpre => by
    simp only [be_trunc_address.pre, be_trunc_address.bufs, BufBytes, Buf, Disjoint] at hpre ⊢
    simp (disch := decide) only [Regs.eq_get x] at hpre hx1 ⊢
    subst hx1
    have hA : ∀ k, k < 20 → (x.get 10#5 + BitVec.ofNat 64 k).toNat = (x.get 10#5).toNat + k :=
      fun k hk => toNat_add_ofNat _ k (by omega)
    have hB : ∀ k, k < 32 → (x.get 11#5 + BitVec.ofNat 64 k).toNat = (x.get 11#5).toNat + k :=
      fun k hk => toNat_add_ofNat _ k (by omega)
    have hS : ∀ c : BitVec 64, 2 ^ 64 - 32 ≤ c.toNat →
        (x.get 2#5 + c).toNat = (x.get 2#5 - 32#64).toNat + (c.toNat + 32 - 2 ^ 64) :=
      fun c hc => toNat_add_frame _ c 32 hc (by decide) (by omega)
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
    simp only [be_trunc_address.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    simp (disch := decide) only [Regs.eq_get x]
    refine ⟨?_, ?_, ?_⟩
    · simp only [bytes, bytesAt, Nat.add_assoc, Nat.reduceAdd]
      simp (config := { decide := true }) only [memByte_memStoreByte_add,
        memByte_memStoreByte_add_zero, memByte_memStoreByte_zero_add, memByte_memStoreByte_self,
        ↓reduceIte]
      simp (disch := decide) only [setWidth_ushiftRight_eq_byteAt, Nat.reduceDiv]
      simp only [setWidth_eq_byteAt]
      rw [bigEndian_byteAt20]
      simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
        Nat.add_zero]
      rw [words4_mod160]
      simp (disch := first | decide | omega) only [hB, Nat.reducePow]
    · simp (disch := omega) only [unchangedExcept2_memStoreByte, unchangedExcept2_memStore,
        unchangedExcept2_refl]
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte, BitVec.ofNat_eq_ofNat,
        true_and]
      simp (disch := decide) only [Regs.eq_get x, and_self]

end IntxRV.Api
