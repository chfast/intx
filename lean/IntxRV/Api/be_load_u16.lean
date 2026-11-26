import IntxRV.Gen.Api.be_load_u16
import IntxRV.Arith
/-!
# `be::unsafe::load<uint16_t>()`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Loads an uint value from a buffer. The user must make sure
/// that the provided buffer is big enough. Therefore, marked "unsafe".
/// @pre src.size() = sizeof(IntT)
/// @post result = bigEndian src
template <typename IntT>
inline IntT load(const uint8_t* src) noexcept
```

`be_load_u16.spec` states it for the RV64 machine code of `be_load_u16` in `IntxRV/Api.cpp`
(generated in `IntxRV/Gen/Api/`, see `IntxRV/README.md`). The function loads the 2 bytes with
`lbu` and ors the first shifted by 8 with the second: `rv_bytes` (`IntxRV/Bytes.lean`) compares the
bytes of the result with the bytes of the buffer.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 4000000

theorem be_load_u16.proof_of_decodes (hdec : be_load_u16.decodes) : be_load_u16.spec :=
  runsM_of_reach hdec fun base ret _ hr _ x m hx1 hpre => by
    simp only [be_load_u16.pre, be_load_u16.bufs, BufBytes] at hpre ⊢
    simp (disch := decide) only [Regs.eq_get x] at hpre hx1 ⊢
    subst hx1
    refine Reach.start ?_
    rv_exec
    try rv_val
    simp only [update_aligned hr]
    refine Reach.refl ?_
    simp only [be_load_u16.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    simp (disch := decide) only [Regs.eq_get x]
    try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    try simp only [Defn] at *
    try subst_vars
    have hw : ((memByte m (x.get 10#5).toNat).setWidth 64 <<< 8 |||
        (memByte m (x.get 10#5 + 1#64).toNat).setWidth 64) =
        beWord [memByte m (x.get 10#5).toNat, memByte m ((x.get 10#5).toNat + 1)] := by
      simp (disch := omega) only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow,
        Nat.mod_eq_of_lt]
      rv_bytes
    refine ⟨?_, ?_, trivial, ?_⟩
    · rw [hw, toNat_beWord _ (by simp)]
      simp only [bytes, bytesAt]
    · rw [hw, toNat_beWord _ (by simp)]
      exact lt_of_lt_of_eq (bigEndian_lt _) (by simp)
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte, BitVec.ofNat_eq_ofNat]
      simp (disch := decide) only [Regs.eq_get x, and_self]

end IntxRV.Api
