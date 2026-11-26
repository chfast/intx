import IntxRV.Gen.Api.be_store_u64
import IntxRV.Arith
/-!
# `be::unsafe::store()` of `uint64_t`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Stores an integer value at the provided pointer in big-endian order. The user must make sure
/// that the provided buffer is big enough to fit the value. Therefore, marked "unsafe".
/// @pre dst.size() = sizeof(T)
/// @post bigEndian dst = x
template <typename T>
inline void store(uint8_t* dst, const T& x) noexcept
```

`be_store_u64.spec` states it for the RV64 machine code of `be_store_u64` in `IntxRV/Api.cpp`
(generated in `IntxRV/Gen/Api/`, see `IntxRV/README.md`). The function stores the 8 bytes of x
with `sb`, the most significant first: the byte stored of x shifted right by 8k is `byteAt x k`
(`IntxRV/Bytes.lean`), and `bigEndian_byteAt` gives the number.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 4000000

theorem be_store_u64.proof_of_decodes (hdec : be_store_u64.decodes) : be_store_u64.spec :=
  runsM_of_reach hdec fun base ret _ hr _ x m hx1 hpre => by
    simp only [be_store_u64.pre, be_store_u64.bufs, BufBytes] at hpre ⊢
    simp (disch := decide) only [Regs.eq_get x] at hpre hx1 ⊢
    subst hx1
    refine Reach.start ?_
    rv_exec
    try rv_val
    simp only [update_aligned hr]
    refine Reach.refl ?_
    simp only [be_store_u64.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    simp (disch := decide) only [Regs.eq_get x]
    try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    try simp only [Defn] at *
    try subst_vars
    refine ⟨?_, ?_, ?_⟩
    · simp only [bytes, bytesAt, Nat.add_assoc, Nat.reduceAdd]
      simp (disch := omega) only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow,
        Nat.mod_eq_of_lt]
      simp (config := { decide := true }) only [memByte_memStoreByte_add,
        memByte_memStoreByte_add_zero, memByte_memStoreByte_zero_add, memByte_memStoreByte_self,
        ↓reduceIte]
      simp (disch := decide) only [setWidth_ushiftRight_eq_byteAt, Nat.reduceDiv]
      rw [setWidth_eq_byteAt]
      exact bigEndian_byteAt _
    · simp (disch := omega) only [unchangedExcept_memStoreByte, unchangedExcept_refl,
        BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.mod_eq_of_lt]
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte, BitVec.ofNat_eq_ofNat]
      simp (disch := decide) only [Regs.eq_get x, and_self]

end IntxRV.Api
