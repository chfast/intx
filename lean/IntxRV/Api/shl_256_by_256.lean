import IntxRV.Gen.Api.shl_256_by_256
import IntxRV.Api.shl_256
import IntxRV.Call
import IntxRV.EnvImage
/-!
# `operator<<` of `uint256` by `uint256`

The specification, from `include/intx/intx.hpp`:

```cpp
/// The shift left modulo 2^N.
/// @post result = x * 2^shift % 2^N
friend constexpr uint operator<<(const uint& x, const uint& shift) noexcept
```

`shl_256_by_256.spec` states it for the RV64 machine code of `shl_256_by_256` in `IntxRV/Api.cpp`
(generated in `IntxRV/Gen/Api/`, see `IntxRV/README.md`). The instance has `[[gnu::flatten]]`,
but clang inlines one level only: the code tests the high words of the shift and calls the operator
by `uint64_t` with the low word. The callee in the image has the code of `shl_256`
(`Gen.shl_256_by_256_image_shl_256_in`), so `Reach.call_sub` runs it by `shl_256.reach`.

If a high word is not zero, the shift is at least 2^64 and the code stores 0 (`shl_val_ge`).
Otherwise it saves ra in a frame of 16 bytes below sp, calls the operator and returns its result.
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace IntxRV.Api
open IntxRV IntxRV.Gen

theorem shl_256_by_256.proof_of_decodes (hdec : shl_256_by_256.decodes) : shl_256_by_256.spec := by
  apply runsI_of_reach hdec
  intro base ret hb hr _ _ _ x m hx1 _ _ hpre
  have hb3 : base &&& 3 = 0 := by
    have := congrArg (· &&& 3#64) hb
    simpa [BitVec.and_assoc] using this
  simp only [shl_256_by_256.pre, shl_256_by_256.bufs, Buf, Disjoint] at hpre ⊢
  simp (disch := decide) only [Regs.eq_get x] at hpre hx1 ⊢
  simp only [shl_256_by_256_entry, show shl_256_by_256_image_data.length = 0 from rfl,
    show shl_256_by_256_image_dataOff = 344 from rfl] at *
  subst hx1
  iterate 5 rv_step
  rv_step
  · -- A high word of the shift is not zero: the result is 0.
    rv_exec
    simp only [Defn] at *
    subst_vars
    rv_val
    simp only [update_aligned hr]
    refine Reach.refl ?_
    simp only [shl_256_by_256.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    simp (disch := decide) only [Regs.eq_get x]
    refine ⟨?_, ?_, ?_⟩
    · simp (config := { decide := true }) (disch := first | bv_omega | fail) only [words,
        BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero,
        memWord_memStore_self, memWord_memStore_of_ne, Nat.mul_zero, Nat.add_zero,
        BitVec.toNat_zero]
      apply shl_val_ge
      simp only [BitVec.ofNat_eq_ofNat, BitVec.or_eq_zero_iff, not_and_or] at *
      simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.zero_mod] at *
      omega
    · simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore,
        unchangedExcept2_refl]
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte, BitVec.ofNat_eq_ofNat,
        and_self, and_true, true_and]
      simp (disch := decide) only [Regs.eq_get x, and_self]
  · -- The call of the operator by uint64_t with the low word of the shift.
    iterate 4 rv_step
    rv_step
    rv_val
    simp only [Defn] at *
    subst_vars
    simp only [bne_eq_false_iff_eq, BitVec.ofNat_eq_ofNat, BitVec.or_eq_zero_iff] at *
    obtain ⟨⟨h16, h8⟩, h24⟩ := ‹(_ ∧ _) ∧ _›
    rw [show pcAt base 9 + 40#64 = pcAt base 19 by simp only [pcAt]; bv_omega,
      update_aligned (by simp only [pcAt]; exact aligned_add hb3 (by decide))]
    refine Reach.call_sub (r := 11) shl_256_by_256_image_shl_256_in (by decide)
      (shl_256.reach _ _ _ ?_ ?_) ?_ ?_ ?_
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      simp only [pcAt]
      exact aligned_add hb3 (by decide)
    · simp only [shl_256.pre, Buf, Disjoint]
      simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte, BitVec.ofNat_eq_ofNat]
      simp (disch := decide) only [Regs.eq_get x]
      omega
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · intro a ha
      simp only [shl_256.bufs] at ha
      simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte,
        BitVec.ofNat_eq_ofNat] at ha
      simp (disch := decide) only [Regs.eq_get x] at ha
      simp only [List.mem_append] at ha ⊢
      tauto
    · -- After the call: the return to the caller.
      intro x2 m2 hpost
      obtain ⟨hval, hun, hsaved⟩ := hpost
      simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte,
        BitVec.ofNat_eq_ofNat] at hval hun
      simp (disch := decide) only [Regs.eq_get x] at hval hun
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hsaved
      simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte,
        BitVec.ofNat_eq_ofNat] at hsaved
      simp (disch := decide) only [Regs.eq_get x] at hsaved
      have h2 : x2.get 2#5 = x.get 2#5 + 18446744073709551600#64 := by
        rw [← Regs.eq_get x2 (by decide)]; exact hsaved.1
      refine Reach.step (by decide) rfl ?_
      simp only [StepGoal, Nat.reduceAdd]
      refine ⟨?_, fun w hw => ?_⟩
      · rw [h2]; rv_mem
      rw [h2] at hw
      rv_val at hw
      rw [memWord_of_unchangedExcept hun _ (by bv_omega), memWord_memStore_self] at hw
      unfold Defn at hw
      subst hw
      rv_step
      rv_step
      rv_val
      simp only [update_aligned hr, h2, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero]
      refine Reach.refl ?_
      simp only [shl_256_by_256.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq]
      simp (disch := decide) only [Regs.eq_get x]
      refine ⟨?_, ?_, ?_⟩
      · have e11 : words (memStore m (x.get 2#5 + 18446744073709551608#64).toNat (x.get 1#5))
            (x.get 11#5) 4 = words m (x.get 11#5) 4 := by
          simp (disch := first | bv_omega | fail) only [words, BitVec.add_assoc, BitVec.reduceAdd,
            show (8 : BitVec 64) = 8#64 from rfl, memWord_memStore_of_ne]
        have e12 : words m (x.get 12#5) 4 = (memWord m (x.get 12#5).toNat).toNat := by
          simp only [words, BitVec.add_assoc, BitVec.reduceAdd,
            show (8 : BitVec 64) = 8#64 from rfl, h8, h16, h24, BitVec.toNat_ofNat, Nat.zero_mod,
            Nat.mul_zero, Nat.add_zero]
        rw [hval, e11, e12]
      · exact UnchangedExcept2.trans
          ((unchangedExcept2_memStore _ _ (by bv_omega)).mpr (unchangedExcept2_refl _ _ _ _ _)) hun
      · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte,
          BitVec.ofNat_eq_ofNat]
        simp only [hsaved, and_self]
theorem shl_256_by_256.nonvacuous :
    NonVacuousI shl_256_by_256_image_code shl_256_by_256_image_data shl_256_by_256_image_dataOff
      shl_256_by_256.bufs shl_256_by_256.pre :=
  nonVacuousI_of (fun i => if i = 10#5 then 0x80000800#64 else if i = 11#5 then 0x80000900#64
      else if i = 12#5 then 0x80000a00#64 else if i = 2#5 then 0x80001000#64 else 0)
    (by decide) (by decide) (by decide) (by decide)
    (by simp only [shl_256_by_256.bufs, bufWords, List.cons_append, List.nil_append,
          List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        simp (config := { decide := true }) only [↓reduceIte])
    (fun _ => by simp only [shl_256_by_256.pre, Buf, Disjoint]; decide)

end IntxRV.Api
