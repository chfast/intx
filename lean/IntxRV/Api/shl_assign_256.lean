import IntxRV.Gen.Api
import IntxRV.Api.shl_256
import IntxRV.Arith
import IntxRV.Call
import IntxRV.Bytes
import IntxRV.EnvImage
import IntxRV.Conv
import IntxRV.Shift

/-!
# `operator<<=` of `uint256`

The specification, from `include/intx/intx.hpp`:

```cpp
/// The shift left by shift modulo 2^N.
/// @post self = old(self) * 2 ^ shift % 2 ^ N
constexpr uint& operator<<=(uint shift) noexcept { return *this = *this << shift; }
```

`shl_assign_256.spec` states it for the RV64 machine code of the image of `shl_assign_256` in
`IntxRV/Api.cpp` (generated in `IntxRV/Gen/Api.lean`, see `IntxRV/README.md`). The function tests
the high words of the shift: if one is not 0, it stores 0 to a temporary in its frame, the shift of
2^64 or more giving 0 (`shl_val_ge` (`IntxRV/Shift.lean`)); else it calls `operator<<` by `uint64_t`
(`IntxRV/Api/shl_256.lean`) by its proof, with the low word of the shift, the object and the
temporary as the result. Then it copies the temporary to the object. The frame of the callee is in
the frame of the caller (`UnchangedExcept2.trans_in`, `IntxRV/Bytes.lean`).
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem shl_assign_256.proof : shl_assign_256.spec := by
  apply runsI_of_reach shl_assign_256_image_decodes
  intro base ret hb hr _ _ _ x m hx1 _ _ hpre
  have hb3 : base &&& 3 = 0 := by
    have := congrArg (· &&& 3#64) hb
    simpa [BitVec.and_assoc] using this
  simp only [shl_assign_256.pre, shl_assign_256.bufs, Buf, Disjoint] at hpre ⊢
  simp (disch := decide) only [Regs.eq_get x] at hpre hx1 ⊢
  simp only [shl_assign_256_entry, show shl_assign_256_image_data.length = 0 from rfl,
    show shl_assign_256_image_dataOff = 400 from rfl] at *
  subst hx1
  have hA : ∀ k, k < 32 → (x.get 10#5 + BitVec.ofNat 64 k).toNat = (x.get 10#5).toNat + k :=
    fun k hk => toNat_add_ofNat _ k (by omega)
  have hB : ∀ k, k < 32 → (x.get 11#5 + BitVec.ofNat 64 k).toNat = (x.get 11#5).toNat + k :=
    fun k hk => toNat_add_ofNat _ k (by omega)
  have hS : ∀ c : BitVec 64, 2 ^ 64 - 48 ≤ c.toNat →
      (x.get 2#5 + c).toNat = (x.get 2#5 - 48#64).toNat + (c.toNat + 48 - 2 ^ 64) :=
    fun c hc => toNat_add_frame _ c 48 hc (by decide) (by omega)
  have hsp : x.get 2#5 + 18446744073709551568#64 = x.get 2#5 - 48#64 := by
    rw [BitVec.sub_eq_add_neg]; rfl
  rv_exec
  · simp (disch := first | decide | omega) only [hA, hB, hS, BitVec.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd] at *
    try simp (disch := omega) only [memWord_memStore_self, memWord_memStore_of_ne] at *
    rv_val
    simp only [Defn] at *
    subst_vars
    try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    simp only [update_aligned hr]
    refine Reach.refl ?_
    simp only [shl_assign_256.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    simp (disch := decide) only [Regs.eq_get x]
    refine ⟨?_, ?_, ?_⟩
    · simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
        Nat.add_zero]
      simp (disch := first | decide | omega) only [hA, hB, Nat.reducePow]
      simp (disch := omega) only [memWord_memStore_self, memWord_memStore_of_ne]
      simp only [BitVec.ofNat_eq_ofNat, BitVec.or_eq_zero_iff, not_and_or] at *
      simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.zero_mod, Nat.mul_zero,
        Nat.add_zero] at *
      rw [show (115792089237316195423570985008687907853269984665640564039457584007913129639936 :
        Nat) = 2 ^ 256 by norm_num]
      apply shl_val_ge
      omega
    · simp (disch := omega) only [unchangedExcept2_memStore, unchangedExcept2_refl]
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte, BitVec.ofNat_eq_ofNat]
      simp (disch := decide) only [Regs.eq_get x, and_self]
  · rv_val
    simp only [Defn] at *
    subst_vars
    simp only [bne_eq_false_iff_eq, BitVec.ofNat_eq_ofNat, BitVec.or_eq_zero_iff] at *
    obtain ⟨⟨hy16, hy8⟩, hy24⟩ := ‹(_ ∧ _) ∧ _›
    rw [show pcAt base 13 + 76#64 = pcAt base 32 by simp only [pcAt]; bv_omega,
      update_aligned (by simp only [pcAt]; exact aligned_add hb3 (by decide))]
    refine Reach.call_sub (r := 15) shl_assign_256_image_shl_256_in (by decide)
      (shl_256.reach _ _ _ ?_ ?_) ?_ ?_ ?_
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      simp only [pcAt]
      exact aligned_add hb3 (by decide)
    · simp only [shl_256.pre, Buf, Disjoint]
      simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
      simp (disch := decide) only [hsp]
      omega
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · intro a ha
      simp only [shl_256.bufs] at ha
      simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at ha
      simp (disch := decide) only [hsp] at ha
      simp only [List.mem_append, bufWords, List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
      rcases ha with ((h | h | h | h) | (h | h | h | h)) <;> simp only [h, true_or, or_true]
    · intro x2 m2 hpost
      simp only [shl_256.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hpost
      simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte,
        BitVec.ofNat_eq_ofNat] at hpost
      simp (disch := decide) only [Regs.eq_get x, Regs.eq_get x2, hsp] at hpost
      obtain ⟨hval, hun, h2, h3, h4, h8, h9, h18, h19, h20, h21, h22, h23, h24, h25, h26,
        h27⟩ := hpost
      rw [← regs_set_of_get' (by decide) h8, ← regs_set_of_get' (by decide) h2]
      rv_exec
      simp only [hsp] at *
      simp (disch := first | decide | omega) only [hA, hB, hS, BitVec.toNat_ofNat, Nat.reducePow,
        Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd] at *
      have hT : ∀ k, k < 48 →
          (x.get 2#5 - 48#64 + BitVec.ofNat 64 k).toNat = (x.get 2#5 - 48#64).toNat + k :=
        fun k hk => toNat_add_ofNat _ k (by omega)
      simp (disch := first | decide | omega) only [hT] at *
      simp (disch := omega) only [memWord_of_unchangedExcept hun, memWord_memStore_self,
        memWord_memStore_of_ne] at *
      rv_val
      simp only [Defn] at *
      subst_vars
      try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      simp only [update_aligned hr]
      refine Reach.refl ?_
      simp only [shl_assign_256.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq]
      simp (disch := decide) only [Regs.eq_get x]
      refine ⟨?_, ?_, ?_⟩
      · simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
          Nat.add_zero] at hval ⊢
        simp (disch := first | decide | omega) only [hA, hB, hT, Nat.reducePow] at hval ⊢
        simp (disch := omega) only [memWord_memStore_self, memWord_memStore_of_ne] at hval ⊢
        rw [hval]
        simp only [hy8, hy16, hy24, BitVec.toNat_ofNat, Nat.zero_mod, Nat.mul_zero, Nat.add_zero]
      · simp (disch := omega) only [unchangedExcept2_memStore]
        refine UnchangedExcept2.trans_in ?_ hun (by omega)
        simp (disch := omega) only [unchangedExcept2_memStore, unchangedExcept2_refl]
      · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte, BitVec.ofNat_eq_ofNat]
        simp (disch := decide) only [Regs.eq_get x2, h3, h4, h9, h18, h19, h20, h21,
          h22, h23, h24, h25, h26, h27, BitVec.sub_add_cancel, and_self]

theorem shl_assign_256.nonvacuous :
    NonVacuousI shl_assign_256_image_code shl_assign_256_image_data shl_assign_256_image_dataOff
      shl_assign_256.bufs shl_assign_256.pre :=
  nonVacuousI_of (fun i => if i = 10#5 then 0x80000800#64 else if i = 11#5 then 0x80000900#64
      else if i = 2#5 then 0x80001000#64 else 0)
    (by decide) (by decide) (by decide) (by decide)
    (by simp only [shl_assign_256.bufs, bufWords, List.cons_append, List.nil_append,
          List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        simp (config := { decide := true }) only [])
    (fun _ => by simp only [shl_assign_256.pre, Buf, Disjoint]; decide)

end IntxRV.Api
