import IntxRV.Gen.Api
import IntxRV.Arith
/-!
# `be::unsafe::load<uint64_t>()`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Loads an uint value from a buffer. The user must make sure
/// that the provided buffer is big enough. Therefore, marked "unsafe".
/// @pre src.size() = sizeof(IntT)
/// @post result = bigEndian src
template <typename IntT>
inline IntT load(const uint8_t* src) noexcept
```

`be_load_u64.spec` states it for the RV64 machine code of `be_load_u64` in `IntxRV/Api.cpp`
(generated in `IntxRV/Gen/Api.lean`, see `IntxRV/README.md`). The function loads the 8 bytes with
`lbu` and swaps them into the result with shifts, masks and ors: `rv_bytes` (`IntxRV/Bytes.lean`)
compares the bytes of the result with the bytes of the buffer.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 4000000

theorem be_load_u64.proof : be_load_u64.spec :=
  runsM_of_reach be_load_u64_decodes fun base ret _ hr _ x m hx1 hpre => by
    simp only [be_load_u64.pre, be_load_u64.bufs, BufBytes] at hpre ⊢
    simp (disch := decide) only [Regs.eq_get x] at hpre hx1 ⊢
    subst hx1
    refine Reach.start ?_
    rv_exec
    rv_val
    simp only [update_aligned hr]
    refine Reach.refl ?_
    simp only [be_load_u64.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    simp (disch := decide) only [Regs.eq_get x]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    simp only [Defn] at *
    subst_vars
    refine ⟨?_, trivial, ?_⟩
    · rw [bytes, ← toNat_beWord _ (by simp [bytesAt])]
      congr 1
      simp only [bytesAt, Nat.add_assoc, Nat.reduceAdd]
      simp (disch := omega) only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow,
        Nat.reduceMod, Nat.mod_eq_of_lt]
      rv_bytes
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte, BitVec.ofNat_eq_ofNat,
        and_self, and_true, true_and]
      simp (disch := decide) only [Regs.eq_get x, and_self]

end IntxRV.Api
