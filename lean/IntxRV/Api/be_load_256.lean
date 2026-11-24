import IntxRV.Gen.Api
import IntxRV.Arith
/-!
# `be::unsafe::load<uint256>()`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Loads an uint value from a buffer. The user must make sure
/// that the provided buffer is big enough. Therefore, marked "unsafe".
/// @pre src.size() = sizeof(IntT)
/// @post result = bigEndian src
template <typename IntT>
inline IntT load(const uint8_t* src) noexcept
```

`be_load_256.spec` states it for the RV64 machine code of `be_load_256` in `IntxRV/Api.cpp`
(generated in `IntxRV/Gen/Api.lean`, see `IntxRV/README.md`). The function saves 13 registers in its
frame, loads the 32 bytes with `lbu`, swaps each 8 into a word with shifts, masks and ors and stores
the words to the result: the addresses as numbers from the buffers and the frame (`toNat_add_ofNat`,
`toNat_add_frame`, `IntxRV/Bytes.lean`) for `omega`, and `rv_bytes` for each word
(`bigEndian_bytesAt32`).
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem be_load_256.proof : be_load_256.spec :=
  runsM_of_reach be_load_256_decodes fun base ret _ hr _ x m hx1 hpre => by
    simp only [be_load_256.pre, be_load_256.bufs, BufBytes, Buf, Disjoint] at hpre ⊢
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
    try simp (disch := omega) only [memByte_memStore_of_ne, memWord_memStore_self,
      memWord_memStore_of_ne] at *
    rv_val
    simp only [Defn] at *
    subst_vars
    try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    simp only [update_aligned hr]
    refine Reach.refl ?_
    simp only [be_load_256.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    simp (disch := decide) only [Regs.eq_get x]
    refine ⟨?_, ?_, ?_⟩
    · simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
        Nat.add_zero]
      simp (disch := first | decide | omega) only [hA, Nat.reducePow]
      simp (disch := omega) only [memWord_memStore_self, memWord_memStore_of_ne]
      rw [bytes, bigEndian_bytesAt32]
      simp only [bytesAt, Nat.add_assoc, Nat.reduceAdd]
      apply words4_congr <;> rv_bytes
    · simp (disch := omega) only [unchangedExcept2_memStore, unchangedExcept2_refl]
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte, BitVec.ofNat_eq_ofNat,
        and_self, and_true, true_and]
      simp (disch := decide) only [Regs.eq_get x, and_self]

end IntxRV.Api
