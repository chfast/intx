import IntxRV.Gen.Api.be_load_u32
import IntxRV.Arith
/-!
# `be::unsafe::load<uint32_t>()`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Loads an uint value from a buffer. The user must make sure
/// that the provided buffer is big enough. Therefore, marked "unsafe".
/// @pre src.size() = sizeof(IntT)
/// @post result = bigEndian src
template <typename IntT>
inline IntT load(const uint8_t* src) noexcept
```

`be_load_u32.spec` states it for the RV64 machine code of `be_load_u32` in `IntxRV/Api.cpp`
(generated in `IntxRV/Gen/Api/`, see `IntxRV/README.md`). The function loads the low byte with
`lb` and masks it, and shifts the top byte with `slliw`, so the result is the 32-bit value
sign-extended, as the calling convention requires (`signExtend_or`, `IntxRV/Bytes.lean`);
`setWidth32_eq_of_byteAt` compares its low 4 bytes with the bytes of the buffer.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 4000000

theorem be_load_u32.proof_of_decodes (hdec : be_load_u32.decodes) : be_load_u32.spec :=
  runsM_of_reach hdec fun base ret _ hr _ x m hx1 hpre => by
    simp only [be_load_u32.pre, be_load_u32.bufs, BufBytes] at hpre ⊢
    simp (disch := decide) only [Regs.eq_get x] at hpre hx1 ⊢
    subst hx1
    refine Reach.start ?_
    rv_exec
    try rv_val
    simp only [update_aligned hr]
    refine Reach.refl ?_
    simp only [be_load_u32.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    simp (disch := decide) only [Regs.eq_get x]
    try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    try simp only [Defn] at *
    try subst_vars
    simp only [shiftiwopVal_slliw, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, bytes, bytesAt,
      Nat.add_assoc, Nat.reduceAdd] at *
    simp (disch := omega) only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow,
      Nat.mod_eq_of_lt] at *
    generalize memByte m (x.get 10#5).toNat = b0 at *
    generalize memByte m ((x.get 10#5).toNat + 1) = b1 at *
    generalize memByte m ((x.get 10#5).toNat + 2) = b2 at *
    generalize memByte m ((x.get 10#5).toNat + 3) = b3 at *
    have ha :
        (b1.setWidth 64 <<< 16 ||| (b2.setWidth 64 <<< 8 ||| b3.signExtend 64 &&& 255#64)).toNat <
          2 ^ 31 := by
      have h1 : (b1.setWidth 64 <<< 16).toNat < 2 ^ 31 := by
        have := b1.isLt
        rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq]; omega
      have h2 : (b2.setWidth 64 <<< 8).toNat < 2 ^ 31 := by
        have := b2.isLt
        rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq]; omega
      have h3 : (b3.signExtend 64 &&& 255#64).toNat < 2 ^ 31 := by
        rw [BitVec.toNat_and]
        exact lt_of_le_of_lt (Nat.and_le_right) (by decide)
      rw [BitVec.toNat_or, BitVec.toNat_or]
      exact Nat.or_lt_two_pow h1 (Nat.or_lt_two_pow h2 h3)
    rw [BitVec.or_assoc]
    have hw : ((b0.setWidth 64).setWidth 32 <<< 24).signExtend 64 |||
        (b1.setWidth 64 <<< 16 ||| (b2.setWidth 64 <<< 8 ||| b3.signExtend 64 &&& 255#64)) =
        BitVec.signExtend 64 (BitVec.setWidth 32
          (((b0.setWidth 64).setWidth 32 <<< 24).signExtend 64 |||
            (b1.setWidth 64 <<< 16 ||| (b2.setWidth 64 <<< 8 ||| b3.signExtend 64 &&& 255#64)))) :=
      signExtend_or _ _ ha
    refine ⟨?_, hw, trivial, ?_⟩
    · have h32 := setWidth32_eq_of_byteAt
        (((b0.setWidth 64).setWidth 32 <<< 24).signExtend 64 |||
          (b1.setWidth 64 <<< 16 ||| (b2.setWidth 64 <<< 8 ||| b3.signExtend 64 &&& 255#64)))
        (beWord [b0, b1, b2, b3]) (by
          intro k hk
          simp only [beWord, List.foldl]
          interval_cases k <;> rv_bytes_simp)
      have h := congrArg BitVec.toNat h32
      simp only [BitVec.toNat_setWidth, toNat_beWord [b0, b1, b2, b3] (by simp)] at h
      rw [h, Nat.mod_eq_of_lt (lt_of_lt_of_eq (bigEndian_lt [b0, b1, b2, b3]) (by simp))]
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte, BitVec.ofNat_eq_ofNat]
      simp (disch := decide) only [Regs.eq_get x, and_self]

end IntxRV.Api
