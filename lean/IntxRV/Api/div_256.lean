import IntxRV.Div256Op
import IntxRV.Gen.Api.div_256
/-!
# `operator/` of `uint256`

The specification, from `include/intx/intx.hpp`:

```cpp
/// The quotient. A division by 0 gives 0.
/// @post result = x / y
friend constexpr uint operator/(const uint& x, const uint& y) noexcept
```

`div_256.spec` states it for the RV64 machine code of `div_256` in `IntxRV/Api.cpp`
(generated in `IntxRV/Gen/Api/`, see `IntxRV/README.md`). The code saves ra and s0 in a frame
of 80 bytes, calls `udivrem<256, 256>()` with the result at sp and copies the quotient to the
result. The callee in the image has the code of `udivrem_256` and its callees, with the immediates
of the address of the table in this image (`Gen.div_256_image_udivrem_256_in`), so `Reach.call_sub`
runs it by `udivrem_256.reach`. The memory after the call is in `IntxRV/Div256Op.lean`.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem div_256.proof_of_decodes (hdec : div_256.decodes) : div_256.spec := by
  apply runsI_of_reach hdec
  intro base ret hb hr _ _ hw x m hx1 hbufs hhold hpre
  rw [show div_256_image_dataOff = 5344 from rfl] at hw hhold hbufs ⊢
  rw [show div_256_image_data.length = 256 from rfl] at hw hbufs ⊢
  have hb3 : base &&& 3 = 0 := by
    have := congrArg (· &&& 3#64) hb
    simpa [BitVec.and_assoc] using this
  have hx : x.get 1#5 = ret := by rw [← Regs.eq_get x (by decide)]; exact hx1
  have hst := buf_outside (x 2#5 - 128#64) base 16 5344 (8 * 256) (by norm_num)
    (hbufs _ (List.mem_append_right _ (mem_bufWords_zero (by norm_num))))
    (hbufs _ (List.mem_append_right _ (mem_bufWords (by norm_num))))
    (by simp only [div_256.pre, Buf] at hpre; exact hpre.2.2.2.2.2.1.2) (by norm_num)
  have hpre0 := hpre
  simp only [div_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre hst
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr⟩ := hpre
  have hT : (base + BitVec.ofNat 64 5344).toNat = base.toNat + 5344 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  simp only [div_256.bufs]
  simp (disch := decide) only [Regs.eq_get x]
  rw [show div_256_entry = 0 from rfl, dataWords, ← hx]
  rv_exec_cut 19
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  rw [show pcAt base 5 + BitVec.signExtend 64 56#12 = pcAt base 19 by
      simp only [pcAt, BitVec.reduceSignExtend]; bv_omega,
    update_aligned (by simp only [pcAt]; exact aligned_add hb3 (by decide))]
  have hsp : x.get 2#5 + 18446744073709551536#64 - 48#64 = x.get 2#5 - 128#64 := by bv_omega
  refine Reach.call_sub (r := 7) div_256_image_udivrem_256_in (by decide)
    (udivrem_256.reach 0x1#20 0x2d0#12 0x1#20 0xf08#12 0x1#20 0x994#12 0x0#20 0x688#12 0x0#20
      0x31c#12 (pcAt base div_256_image_udivrem_256_offset) (base + 5344#64) _ _ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?_ ?_ ?_
  all_goals try (simp only [div_256_image_udivrem_256_offset, pcAt, BitVec.reduceAppend,
      BitVec.reduceSignExtend]; bv_omega)
  · simp only [div_256_image_udivrem_256_offset, pcAt]; exact aligned_add hb3 (by decide)
  · rw [hT]; omega
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    simp only [pcAt]; exact aligned_add hb3 (by decide)
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    rw [hT]; bv_omega
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    rw [hsp, hT]; bv_omega
  · simp (disch := first | (rw [hT]; bv_omega) | fail) only [holdsData_table_memStore]
    exact hhold
  · simp only [udivrem_256.pre, Buf, Disjoint]
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    simp (disch := decide) only [Regs.eq_get x]
    rw [hsp]
    repeat' apply And.intro
    all_goals bv_omega
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · intro a ha
    simp only [udivrem_256.bufs] at ha
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at ha
    simp (disch := decide) only [Regs.eq_get x] at ha
    rw [hsp] at ha
    simp only [List.mem_append] at ha ⊢
    rcases ha with ((((h | h) | h) | h) | h)
    · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    · rw [show x.get 2#5 + 18446744073709551536#64 = x.get 2#5 - 128#64 +
        BitVec.ofNat 64 (8 * 6) by bv_omega] at h
      exact Or.inl (Or.inr (mem_bufWords_of_offset (by norm_num) h))
    · exact Or.inl (Or.inr (mem_bufWords_of_le (by norm_num) h))
    · exact Or.inr h
  · intro x3 m3 hpost
    obtain ⟨hq, -, hunc, hsaved⟩ := hpost
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at hq hunc
    simp (disch := decide) only [Regs.eq_get x] at hq hunc
    rw [hsp] at hunc
    rw [div_frame_words m (x.get 2#5) (x.get 1#5) (x.get 8#5) (x.get 11#5) hun hdsu hsn,
      div_frame_words m (x.get 2#5) (x.get 1#5) (x.get 8#5) (x.get 12#5) hvn hdsv hsn] at hq
    obtain ⟨hra3, hs03, hm3⟩ := div_frame_mem m m3 (x.get 10#5) (x.get 2#5) (x.get 1#5)
      (x.get 8#5) hrn hsn hdsr hunc
    have h23 : x3.get 2#5 = x.get 2#5 + 18446744073709551536#64 := by
      rw [← Regs.eq_get x3 (by decide), hsaved 2#5 (by decide)]
      simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    have h83 : x3.get 8#5 = x.get 10#5 := by
      rw [← Regs.eq_get x3 (by decide), hsaved 8#5 (by decide)]
      simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    have hcs3 : ∀ i ∈ calleeSaved, i ≠ 2#5 → i ≠ 8#5 → x3 i = x i := by
      intro i hi h2i h8i
      rw [hsaved i hi]
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] <;>
        first
          | exact absurd rfl h2i
          | exact absurd rfl h8i
    clear hsaved
    rw [← regs_set_of_get (by decide) h23, ← regs_set_of_get (by decide) h83]
    rv_exec
    simp only [Defn] at *
    subst_vars
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.reduceSignExtend,
      BitVec.add_zero]
    rw [hra3, hs03, update_aligned (hx ▸ hr)]
    refine Reach.refl ?_
    simp only [div_256.post]
    simp (disch := decide) only [Regs.eq_get x]
    refine ⟨?_, ?_, ?_⟩
    · rw [← hq, words4_unfold, words4_unfold]
      simp (disch := first | bv_omega | fail) only [BitVec.add_assoc, BitVec.reduceAdd,
        memWord_memStore_self, memWord_memStore_of_ne]
    · simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
      exact hm3
    · intro i hi
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] <;>
        first
          | exact (Regs.eq_get x (by decide)).symm
          | exact hcs3 _ (by decide) (by decide) (by decide)
/-- The registers of the nonvacuous instance: the result, x and y above the data, and the frame
below sp. -/
theorem div_256.nonvacuous :
    NonVacuousI div_256_image_code div_256_image_data div_256_image_dataOff div_256.bufs
      div_256.pre :=
  nonVacuousI_of (fun i => if i = 10#5 then 0x80000C00#64 else if i = 11#5 then 0x80000C20#64
      else if i = 12#5 then 0x80000C40#64 else if i = 2#5 then 0x80000D00#64 else 0)
    (by decide) (by decide) (by decide) (by decide)
    (by rw [show div_256_image_dataOff = 5344 from rfl,
          show div_256_image_data.length = 256 from rfl]
        simp only [div_256.bufs, ↓reduceIte, BitVec.reduceEq, BitVec.reduceSub, bufWords,
          List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq]
        repeat' apply And.intro
        all_goals decide)
    (fun _ => by simp only [div_256.pre, Buf, Disjoint]; decide)

end IntxRV.Api
