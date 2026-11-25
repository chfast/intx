import IntxRV.Api.udivrem_512_256
import IntxRV.Api.umul_256
import IntxRV.Gen.Api.mulmod_256
/-!
# `mulmod()` of `uint256`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Computes (x * y) % mod with the 512-bit product. A modulus of 0 gives 0.
/// @post result = if mod = 0 then 0 else x * y % mod
constexpr uint256 mulmod(const uint256& x, const uint256& y, const uint256& mod) noexcept
```

`mulmod_256.spec` states it for the RV64 machine code of `mulmod_256` in `IntxRV/Api.cpp`
(generated in `IntxRV/Gen/Api/`, see `IntxRV/README.md`). The code saves ra, s0 and s1 in a
frame of 192 bytes, calls `umul()` with the product at sp + 8 and `udivrem<512, 256>()` with the
result at sp + 72, and copies the remainder to the result. The callees in the image run by
`umul_256.reach` and by `udivrem_512_256.reach` with the immediates of the address of the table in
this image (`Gen.mulmod_256_image_udivrem_512_256_in`).
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

theorem mulmod_256.proof_of_decodes (hdec : mulmod_256.decodes) : mulmod_256.spec := by
  apply runsI_of_reach hdec
  intro base ret hb hr _ _ hw x m hx1 hbufs hhold hpre
  rw [show mulmod_256_image_dataOff = 6016 from rfl] at hw hhold hbufs ⊢
  rw [show mulmod_256_image_data.length = 256 from rfl] at hw hbufs ⊢
  have hb3 : base &&& 3 = 0 := by
    have := congrArg (· &&& 3#64) hb
    simpa [BitVec.and_assoc] using this
  have hx : x.get 1#5 = ret := by rw [← Regs.eq_get x (by decide)]; exact hx1
  have hst := buf_outside (x 2#5 - 432#64) base 54 6016 (8 * 256) (by norm_num)
    (hbufs _ (List.mem_append_right _ (mem_bufWords_zero (by norm_num))))
    (hbufs _ (List.mem_append_right _ (mem_bufWords (by norm_num))))
    (by simp only [mulmod_256.pre, Buf] at hpre; exact hpre.2.2.2.2.2.2.2.1.2) (by norm_num)
  have hTr := buf_outside (x 10#5) base 4 6016 (8 * 256) (by norm_num)
    (hbufs _ (List.mem_append_left _ (List.mem_append_right _ (mem_bufWords_zero (by norm_num)))))
    (hbufs _ (List.mem_append_left _ (List.mem_append_right _ (mem_bufWords (by norm_num)))))
    (by simp only [mulmod_256.pre, Buf] at hpre; exact hpre.1.2) (by norm_num)
  have hpre0 := hpre
  simp only [mulmod_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre hst hTr
  obtain ⟨⟨hra, hrn⟩, ⟨hxa, hxn⟩, ⟨hya, hyn⟩, ⟨hma, hmn⟩, hdrx, hdry, hdrm, ⟨hsa, hsn⟩, hdsx,
    hdsy, hdsm, hdsr⟩ := hpre
  have hT : (base + BitVec.ofNat 64 6016).toNat = base.toNat + 6016 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  simp only [mulmod_256.bufs]
  simp (disch := decide) only [Regs.eq_get x]
  rw [show mulmod_256_entry = 0 from rfl, dataWords, ← hx]
  rv_exec_cut 27
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.reduceSignExtend]
  rw [show pcAt base 7 + 80#64 = pcAt base 27 by simp only [pcAt]; bv_omega,
    update_aligned (pcAt_aligned hb3 27)]
  generalize hM : memStore (memStore (memStore m _ _) _ _) _ _ = M
  have hwx : words M (x.get 11#5) 4 = words m (x.get 11#5) 4 := by
    rw [← hM, words_memStore_of_disjoint _ _ _ _ _ (by omega) (by bv_omega),
      words_memStore_of_disjoint _ _ _ _ _ (by omega) (by bv_omega),
      words_memStore_of_disjoint _ _ _ _ _ (by omega) (by bv_omega)]
  have hwy : words M (x.get 12#5) 4 = words m (x.get 12#5) 4 := by
    rw [← hM, words_memStore_of_disjoint _ _ _ _ _ (by omega) (by bv_omega),
      words_memStore_of_disjoint _ _ _ _ _ (by omega) (by bv_omega),
      words_memStore_of_disjoint _ _ _ _ _ (by omega) (by bv_omega)]
  have hwm : words M (x.get 13#5) 4 = words m (x.get 13#5) 4 := by
    rw [← hM, words_memStore_of_disjoint _ _ _ _ _ (by omega) (by bv_omega),
      words_memStore_of_disjoint _ _ _ _ _ (by omega) (by bv_omega),
      words_memStore_of_disjoint _ _ _ _ _ (by omega) (by bv_omega)]
  have hmM : UnchangedExcept2 m M (x.get 10#5) 32 (x.get 2#5 - 432#64) 432 := by
    rw [← hM]
    simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
    exact unchangedExcept2_refl _ _ _ _ _
  refine Reach.call_sub (r := 9) mulmod_256_image_umul_256_in (by decide)
    (umul_256.reach (pcAt base mulmod_256_image_umul_256_offset) _ _ ?_ ?_) ?_ ?_ ?_
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    exact pcAt_aligned hb3 9
  · simp only [umul_256.pre, Buf, Disjoint]
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    simp (disch := decide) only [Regs.eq_get x]
    repeat' apply And.intro
    all_goals bv_omega
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · intro a ha
    simp only [umul_256.bufs] at ha
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at ha
    simp (disch := decide) only [Regs.eq_get x] at ha
    simp only [List.mem_append] at ha ⊢
    rcases ha with ((h | h) | h) | h
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))
    · rw [show x.get 2#5 + 18446744073709551432#64 = x.get 2#5 - 432#64 +
        BitVec.ofNat 64 (8 * 31) by bv_omega] at h
      exact Or.inl (Or.inr (mem_bufWords_of_offset (by norm_num) h))
    · rw [show x.get 2#5 + 18446744073709551424#64 - 160#64 = x.get 2#5 - 432#64 +
        BitVec.ofNat 64 (8 * 10) by bv_omega] at h
      exact Or.inl (Or.inr (mem_bufWords_of_offset (by norm_num) h))
  intro x3 m3 hpost
  obtain ⟨hprod, hunc3, hsaved3⟩ := hpost
  simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at hprod hunc3
  simp (disch := decide) only [Regs.eq_get x] at hprod hunc3
  rw [hwx, hwy] at hprod
  have h23 : x3.get 2#5 = x.get 2#5 + 18446744073709551424#64 := by
    rw [get_of_calleeSaved hsaved3 (by decide)]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  have h83 : x3.get 8#5 = x.get 13#5 := by
    rw [get_of_calleeSaved hsaved3 (by decide)]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  have h93 : x3.get 9#5 = x.get 10#5 := by
    rw [get_of_calleeSaved hsaved3 (by decide)]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  -- The memory after `umul()`: changed only in the frame.
  have hm3 : UnchangedExcept2 m m3 (x.get 10#5) 32 (x.get 2#5 - 432#64) 432 :=
    fun k ha hb => (hunc3 k (by bv_omega) (by bv_omega)).trans (hmM k ha hb)
  have hwm3 : words m3 (x.get 13#5) 4 = words m (x.get 13#5) 4 :=
    words_of_unchangedExcept2 hm3 4 _ (by omega) (by omega) (by omega)
  have hhold3 : HoldsData m3 (base + BitVec.ofNat 64 6016) mulmod_256_image_data :=
    holdsData_of_unchangedExcept2 hm3 _ _
      (by rw [hT, show mulmod_256_image_data.length = 256 from rfl]; omega)
      (by rw [hT, show mulmod_256_image_data.length = 256 from rfl]; omega)
      (by rw [hT, show mulmod_256_image_data.length = 256 from rfl]; omega) hhold
  rw [← regs_set_of_get' (by decide) h23, ← regs_set_of_get' (by decide) h83,
    ← regs_set_of_get' (by decide) h93]
  rv_exec_cut 189
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.reduceSignExtend]
  rw [show pcAt base 12 + 708#64 = pcAt base 189 by simp only [pcAt]; bv_omega,
    update_aligned (pcAt_aligned hb3 189)]
  have hsp : x.get 2#5 + 18446744073709551424#64 - 240#64 = x.get 2#5 - 432#64 := by bv_omega
  refine Reach.call_sub (r := 14) mulmod_256_image_udivrem_512_256_in (by decide)
    (udivrem_512_256.reach 0x1#20 0xe14#12 0x1#20 0xa4c#12 0x0#20 0x60c#12 0x0#20 0x2f8#12
      (pcAt base mulmod_256_image_udivrem_512_256_offset) (base + 6016#64) _ _ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ hhold3 ?_) ?_ ?_ ?_
  all_goals try (simp only [mulmod_256_image_udivrem_512_256_offset, pcAt, BitVec.reduceAppend,
      BitVec.reduceSignExtend]; bv_omega)
  · exact pcAt_aligned hb3 _
  · rw [hT]; omega
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    exact pcAt_aligned hb3 14
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    rw [hT]; bv_omega
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    rw [hsp, hT]; bv_omega
  · simp only [udivrem_512_256.pre, Buf, Disjoint]
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    rw [hsp]
    repeat' apply And.intro
    all_goals bv_omega
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · intro a ha
    simp only [udivrem_512_256.bufs] at ha
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at ha
    rw [hsp] at ha
    simp only [List.mem_append] at ha ⊢
    rcases ha with ((((h | h) | h) | h) | h)
    · rw [show x.get 2#5 + 18446744073709551432#64 = x.get 2#5 - 432#64 +
        BitVec.ofNat 64 (8 * 31) by bv_omega] at h
      exact Or.inl (Or.inr (mem_bufWords_of_offset (by norm_num) h))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    · rw [show x.get 2#5 + 18446744073709551496#64 = x.get 2#5 - 432#64 +
        BitVec.ofNat 64 (8 * 39) by bv_omega] at h
      exact Or.inl (Or.inr (mem_bufWords_of_offset (by norm_num) h))
    · exact Or.inl (Or.inr (mem_bufWords_of_le (by norm_num) h))
    · exact Or.inr h
  · intro x5 m5 hpost
    obtain ⟨-, hrem, hunc5, hsaved5⟩ := hpost
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at hrem hunc5
    rw [hprod, hwm3, hsp] at *
    have h25 : x5.get 2#5 = x.get 2#5 + 18446744073709551424#64 := by
      rw [get_of_calleeSaved hsaved5 (by decide)]
      simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    have h95 : x5.get 9#5 = x.get 10#5 := by
      rw [get_of_calleeSaved hsaved5 (by decide)]
      simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    -- The saved registers in the frame of 192 bytes, outside the frames of the callees.
    have hsv : ∀ c : BitVec 64, (x.get 2#5 - 432#64).toNat + 408 ≤ (x.get 2#5 + c).toNat →
        (x.get 2#5 + c).toNat + 8 ≤ (x.get 2#5 - 432#64).toNat + 432 →
        memWord m5 (x.get 2#5 + c).toNat = memWord M (x.get 2#5 + c).toNat := fun c h1 h2 => by
      rw [memWord_of_unchangedExcept2 hunc5 _ (by bv_omega) (by bv_omega),
        memWord_of_unchangedExcept2 hunc3 _ (by bv_omega) (by bv_omega)]
    have hra5 := hsv 18446744073709551608#64 (by bv_omega) (by bv_omega)
    have hs05 := hsv 18446744073709551600#64 (by bv_omega) (by bv_omega)
    have hs15 := hsv 18446744073709551592#64 (by bv_omega) (by bv_omega)
    rw [← hM] at hra5 hs05 hs15
    simp (disch := first | bv_omega | fail) only [memWord_memStore_self, memWord_memStore_of_ne]
      at hra5 hs05 hs15
    rw [← regs_set_of_get' (by decide) h25, ← regs_set_of_get' (by decide) h95]
    rv_exec
    rename_i w0 hw0 w1 hw1 w2 hw2 w3 hw3 wra hwra ws0 hws0 ws1 hws1
    rw [hra5] at hwra
    rw [hs05] at hws0
    rw [hs15] at hws1
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.reduceSignExtend,
      BitVec.add_zero]
    rw [hwra.eq, update_aligned (hx ▸ hr)]
    refine Reach.refl ?_
    simp only [mulmod_256.post]
    simp (disch := decide) only [Regs.eq_get x]
    refine ⟨?_, ?_, ?_⟩
    · simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrem
      rw [← hrem]
      simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
        Nat.add_zero]
      simp (disch := first | bv_omega | fail) only [memWord_memStore_self, memWord_memStore_of_ne]
      rw [hw0.eq, hw1.eq, hw2.eq, hw3.eq]
    · simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
      exact fun k ha hb => (hunc5 k (by bv_omega) (by omega)).trans (hm3 k ha hb)
    · intro r hr'
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
      all_goals first
        | exact (Regs.eq_get x (by decide)).symm
        | (rw [Regs.eq_get x (by decide)]; first | exact hws0.eq | exact hws1.eq)
        | (rw [Regs.eq_get x5 (by decide), get_of_calleeSaved hsaved5 (by decide)]
           simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
           rw [get_of_calleeSaved hsaved3 (by decide)]
           simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
           rw [Regs.eq_get x (by decide)])

/-- The registers of the nonvacuous instance: x, y, the modulus, the result and the frame of 432
bytes above the data. -/
theorem mulmod_256.nonvacuous :
    NonVacuousI mulmod_256_image_code mulmod_256_image_data mulmod_256_image_dataOff
      mulmod_256.bufs mulmod_256.pre :=
  nonVacuousI_of (fun i => if i = 10#5 then 0x80000C60#64 else if i = 11#5 then 0x80000C00#64
      else if i = 12#5 then 0x80000C20#64 else if i = 13#5 then 0x80000C40#64
      else if i = 2#5 then 0x80000E30#64 else 0)
    (by decide) (by decide) (by decide) (by decide)
    (by rw [show mulmod_256_image_dataOff = 6016 from rfl,
          show mulmod_256_image_data.length = 256 from rfl]
        simp only [mulmod_256.bufs, ↓reduceIte, BitVec.reduceEq, BitVec.reduceSub, bufWords,
          List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq]
        repeat' apply And.intro
        all_goals decide)
    (fun _ => by simp only [mulmod_256.pre, Buf, Disjoint]; decide)

end IntxRV.Api
