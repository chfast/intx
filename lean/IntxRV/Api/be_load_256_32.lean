import IntxRV.Gen.Api
import IntxRV.Memcpy
import IntxRV.Arith
import IntxRV.Call
import IntxRV.EnvImage

/-!
# `be::load<uint256>()` from `uint8_t[32]`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Loads an integer value from bytes of big-endian order.
/// If the size of bytes is smaller than the result, the value is zero-extended.
/// @post result = bigEndian src
template <typename T, unsigned M>
inline T load(const uint8_t (&src)[M]) noexcept
```

`be_load_256_32.spec` states it for the RV64 machine code of the image of `be_load_256_32` in
`IntxRV/Api.cpp` (generated in `IntxRV/Gen/Api.lean`, see `IntxRV/README.md`). The function copies
the 32 bytes to the result with `memcpy()`, by its proof `memcpy.reach` (`IntxRV/Memcpy.lean`),
loads them back as words, swaps them with shifts, masks and ors and stores them: `memWord_memCopy`
reads the words of the source, and `rv_bytes` (`IntxRV/Bytes.lean`) proves each word by its bytes.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem be_load_256_32.proof : be_load_256_32.spec := by
  apply runsI_of_reach be_load_256_32_image_decodes
  intro base ret hb hr _ _ _ x m hx1 _ _ hpre
  have hb3 : base &&& 3 = 0 := by
    have := congrArg (· &&& 3#64) hb
    simpa [BitVec.and_assoc] using this
  simp only [be_load_256_32.pre, be_load_256_32.bufs, Buf, BufBytes, Disjoint] at hpre ⊢
  simp (disch := decide) only [Regs.eq_get x] at hpre hx1 ⊢
  simp only [be_load_256_32_entry, show be_load_256_32_image_data.length = 0 from rfl,
    show be_load_256_32_image_dataOff = 504 from rfl] at *
  subst hx1
  rv_exec
  rv_val
  rw [show pcAt base 9 + 428#64 = pcAt base 116 by simp only [pcAt]; bv_omega,
    update_aligned (by simp only [pcAt]; exact aligned_add hb3 (by decide))]
  refine Reach.call_sub (r := 11) be_load_256_32_image_memcpy_in (by decide)
    (memcpy.reach _ _ _ ?_ ?_ ?_ ?_ ?_ ?_) ?_ (fun a h => h) ?_
  all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  · simp only [pcAt]; exact aligned_add hb3 (by decide)
  · omega
  · omega
  · omega
  · intro i hi
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inr (and_not7_mem_bufWords hpre.1.1 (by omega))))
  · intro i hi
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (mem_bufBytes hi)))
  · intro x2 m2 ⟨hm2, h10, hsaved⟩
    subst hm2
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hsaved
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte,
      BitVec.ofNat_eq_ofNat] at hsaved
    simp (disch := decide) only [Regs.eq_get x, Regs.eq_get x2] at hsaved
    obtain ⟨h2, h3, h4, h8, h9, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩ := hsaved
    rw [← regs_set_of_get' (by decide) h8, ← regs_set_of_get' (by decide) h2]
    have hA : ∀ k, k < 32 → (x.get 10#5 + BitVec.ofNat 64 k).toNat = (x.get 10#5).toNat + k :=
      fun k hk => toNat_add_ofNat _ k (by omega)
    have hS : ∀ c : BitVec 64, 2 ^ 64 - 48 ≤ c.toNat →
        (x.get 2#5 + c).toNat = (x.get 2#5 - 48#64).toNat + (c.toNat + 48 - 2 ^ 64) :=
      fun c hc => toNat_add_frame _ c 48 hc (by decide) (by omega)
    rv_exec
    simp (disch := first | decide | omega) only [hA, hS, BitVec.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd] at *
    simp (disch := omega) only [memWord_memStore_self, memWord_memStore_of_ne, memWord_memCopy,
      memWord_memCopy_of_disjoint, Nat.add_sub_cancel_left, Nat.sub_self, Nat.add_zero] at *
    rv_val
    simp only [Defn] at *
    subst_vars
    try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    simp only [update_aligned hr]
    refine Reach.refl ?_
    simp only [be_load_256_32.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
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
    · simp (disch := omega) only [unchangedExcept2_memStore, unchangedExcept2_memCopy,
        unchangedExcept2_refl]
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte, BitVec.ofNat_eq_ofNat]
      simp (disch := decide) only [Regs.eq_get x2, h3, h4, h21,
        h22, h23, h24, h25, h26, h27, and_self]

theorem be_load_256_32.nonvacuous :
    NonVacuousI be_load_256_32_image_code be_load_256_32_image_data be_load_256_32_image_dataOff
      be_load_256_32.bufs be_load_256_32.pre :=
  nonVacuousI_of (fun i => if i = 10#5 then 0x80000800#64 else if i = 11#5 then 0x80000900#64
      else if i = 2#5 then 0x80001000#64 else 0)
    (by decide) (by decide) (by decide) (by decide)
    (by simp only [be_load_256_32.bufs, bufWords, bufBytes, List.cons_append, List.nil_append,
          List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        simp (config := { decide := true }) only [])
    (fun _ => by simp only [be_load_256_32.pre, Buf, BufBytes, Disjoint]; decide)

end IntxRV.Api
