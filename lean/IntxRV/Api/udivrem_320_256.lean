import IntxRV.Div320Disp
/-!
# `udivrem()` of `uint320` by `uint256`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Divides u by v. A division by 0 gives 0 as the quotient and the remainder.
/// @post result.quot = u / v
/// @post result.rem = if v = 0 then 0 else u % v
template <unsigned M, unsigned N>
constexpr div_result<uint<M>, uint<N>> udivrem(const uint<M>& u, const uint<N>& v) noexcept
```

`udivrem_320_256.spec` states it for the RV64 machine code of `udivrem_320_256` in
`IntxRV/Api.cpp`, the division in `addmod()`. The function saves ra and s0 to s4 in a frame of 48
bytes (`U320Frame`) and dispatches on the top words of u and v (`u320_main`,
`IntxRV/Div320Disp.lean`): it calls `udivrem_top1<3>()` or `udivrem_top2<4>()` for v ≥ 2^192, and
`udivrem_top1<2>()`, `udivrem_top2<3>()` or `udivrem_top2<3, true>()` for 2^128 ≤ v < 2^192 by the
top words (`IntxRV/Div320Top.lean`); for v < 2^128 and u ≥ 2^192 it zeroes the result with `memset()`
and calls `udivrem_by2()` of 4 quotient words or `udivrem_by1()` of 5 words, and otherwise it counts
the significant words of u and v, returns 0 and u if u < v, and calls `udivrem_by1()` or
`udivrem_by2()` with max(m, 2) or max(m, 3) words of u (`IntxRV/Div320By.lean`) or
`udivrem_knuth<320, 256>()` with the m words (`IntxRV/Div320K.lean`). Each callee runs by its proof
for the immediates of the address of the table (`Reach.call_sub`), and all the paths end in the
epilogue at the instruction 142 (`u320_epi`, `IntxRV/Div320.lean`). The proofs run the code of the
image with the instructions of the callees nested to the right (`p320_eq`): the fetch of an
instruction then does not reduce them.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

set_option hygiene false in
/-- The frame after the prologue of `udivrem<320, 256>()`. -/
local macro "u320_pro_frame" : tactic => `(tactic| (
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  all_goals try (simp (disch := first | bv_omega | fail) only [memWord_memStore_self,
    memWord_memStore_of_ne]; done)
  · simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
    exact unchangedExcept2_refl _ _ _ _ _
  · intro r hr' hn
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte] at hn ⊢))

/-- The run of `udivrem<320, 256>()` and its callees for any immediates of the address `T` of the
table of the reciprocal in the callees (`udivrem_320_256_progAt`), with the result and the frame of
336 bytes below sp outside the table. -/
theorem udivrem_320_256.reach (hi0 : BitVec 20) (lo0 : BitVec 12) (hi1 : BitVec 20)
    (lo1 : BitVec 12) (hi2 : BitVec 20) (lo2 : BitVec 12) (hi3 : BitVec 20) (lo3 : BitVec 12)
    (hi4 : BitVec 20) (lo4 : BitVec 12) (hi5 : BitVec 20) (lo5 : BitVec 12) (hi6 : BitVec 20)
    (lo6 : BitVec 12) (hi7 : BitVec 20) (lo7 : BitVec 12) (hi8 : BitVec 20) (lo8 : BitVec 12)
    (hi9 : BitVec 20) (lo9 : BitVec 12) (base T : BitVec 64) (x : Regs) (m : Mem)
    (hT0 : pcAt (pcAt base 182) 5 + ((hi0 ++ 0x000#12).signExtend 64 + lo0.signExtend 64) = T)
    (hT1 : pcAt (pcAt base 375) 5 + ((hi1 ++ 0x000#12).signExtend 64 + lo1.signExtend 64) = T)
    (hT2 : pcAt (pcAt base 618) 54 + ((hi2 ++ 0x000#12).signExtend 64 + lo2.signExtend 64) = T)
    (hT3 : pcAt (pcAt base 932) 50 + ((hi3 ++ 0x000#12).signExtend 64 + lo3.signExtend 64) = T)
    (hT4 : pcAt (pcAt base 1275) 65 + ((hi4 ++ 0x000#12).signExtend 64 + lo4.signExtend 64) = T)
    (hT5 : pcAt (pcAt base 1457) 64 + ((hi5 ++ 0x000#12).signExtend 64 + lo5.signExtend 64) = T)
    (hT6 : pcAt (pcAt base 1661) 87 + ((hi6 ++ 0x000#12).signExtend 64 + lo6.signExtend 64) = T)
    (hT7 : pcAt (pcAt base 1948) 107 + ((hi7 ++ 0x000#12).signExtend 64 + lo7.signExtend 64) = T)
    (hT8 : pcAt (pcAt base 2273) 84 + ((hi8 ++ 0x000#12).signExtend 64 + lo8.signExtend 64) = T)
    (hT9 : pcAt (pcAt base 2585) 184 + ((hi9 ++ 0x000#12).signExtend 64 + lo9.signExtend 64) = T)
    (hb3 : base &&& 3 = 0) (hw : T.toNat + 8 * 256 ≤ 2 ^ 64) (hr : x.get 1#5 &&& 3 = 0)
    (hTr : (x.get 10#5).toNat + 72 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hTs : (x.get 2#5 - 336#64).toNat + 336 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 336#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hpre : udivrem_320_256.pre x m) :
    Reach (udivrem_320_256.bufs x ++ bufWords T 256)
      (udivrem_320_256_progAt hi0 lo0 hi1 lo1 hi2 lo2 hi3 lo3 hi4 lo4 hi5 lo5 hi6 lo6 hi7 lo7 hi8
        lo8 hi9 lo9) base (pcAt base 0) x m (x.get 1#5) (udivrem_320_256.post x m) := by
  have hpre0 := hpre
  simp only [udivrem_320_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr⟩ := hpre
  simp only [udivrem_320_256.bufs]
  simp (disch := decide) only [Regs.eq_get x]
  generalize hDe : bufWords T 256 = D
  have hD : ∀ a ∈ bufWords T 256, a ∈ D := fun _ h => hDe ▸ h
  clear hDe
  show Reach (u320Bufs x D) _ _ _ _ _ _ _
  rw [p320_eq]
  rv_exec_cut 7
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.reduceSignExtend,
    BitVec.add_assoc, BitVec.reduceAdd]
  generalize hM1 : memStore (memStore (memStore (memStore (memStore (memStore m _ _) _ _) _ _) _ _)
    _ _) _ _ = M1
  have hF1 : U320Frame x m (x.set 2#5 (x.get 2#5 + 18446744073709551568#64)) M1 := by
    rw [← hM1]; u320_pro_frame
  exact u320_main base x m hb3 hr hpre0 hw hTr hTs hhold hD hT0 hT1 hT2 hT3 hT4 hT5 hT6 hT7 hT8 hT9
    _ _ hF1 (by simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte])
    (by simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte])
    (by simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte])

theorem udivrem_320_256.proof_of_decodes (hdec : udivrem_320_256.decodes) :
    udivrem_320_256.spec := by
  apply runsI_of_reach hdec
  intro base ret hb hr _ _ hw x m hx1 hbufs hhold hpre
  rw [show udivrem_320_256_image_dataOff = 12016 from rfl] at hw hhold hbufs ⊢
  rw [show udivrem_320_256_image_data.length = 256 from rfl] at hw hbufs ⊢
  have hb3 : base &&& 3 = 0 := by
    have := congrArg (· &&& 3#64) hb
    simpa [BitVec.and_assoc] using this
  have hx : x.get 1#5 = ret := by rw [← Regs.eq_get x (by decide)]; exact hx1
  have hpre' := hpre
  simp only [udivrem_320_256.pre, Buf] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  have hTr := buf_outside (x 10#5) base 9 12016 (8 * 256) (by norm_num)
    (hbufs _ (List.mem_append_left _ (List.mem_append_right _ (mem_bufWords_zero (by norm_num)))))
    (hbufs _ (List.mem_append_left _ (List.mem_append_right _ (mem_bufWords (by norm_num)))))
    (by rw [Regs.eq_get x (by decide)]; exact hpre'.1.2) (by norm_num)
  have hTs := buf_outside (x 2#5 - 336#64) base 42 12016 (8 * 256) (by norm_num)
    (hbufs _ (List.mem_append_right _ (mem_bufWords_zero (by norm_num))))
    (hbufs _ (List.mem_append_right _ (mem_bufWords (by norm_num))))
    (by rw [Regs.eq_get x (by decide)]; exact hpre'.2.2.2.2.2.1.2) (by norm_num)
  rw [Regs.eq_get x (by decide)] at hTr hTs
  have hT : (base + BitVec.ofNat 64 12016).toNat = base.toNat + 12016 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [show udivrem_320_256_entry = udivrem_320_256_image_udivrem_320_256_offset from rfl, dataWords,
    ← hx]
  refine Reach.lift udivrem_320_256_image_udivrem_320_256_in (by decide) ?_
  have h := udivrem_320_256.reach 0x3#20 0xc04#12 0x3#20 0x900#12 0x2#20 0x470#12 0x2#20 0xf98#12 0x2#20 0xa00#12 0x1#20 0x72c#12 0x1#20 0x3a0#12 0x1#20 0xed4#12 0x1#20 0xa1c#12 0x0#20 0x3ac#12
    (pcAt base udivrem_320_256_image_udivrem_320_256_offset) _ x m
    (by simp only [udivrem_320_256_image_udivrem_320_256_offset, pcAt, BitVec.reduceAppend,
      BitVec.reduceSignExtend]; bv_omega)
    (by simp only [udivrem_320_256_image_udivrem_320_256_offset, pcAt, BitVec.reduceAppend,
      BitVec.reduceSignExtend]; bv_omega)
    (by simp only [udivrem_320_256_image_udivrem_320_256_offset, pcAt, BitVec.reduceAppend,
      BitVec.reduceSignExtend]; bv_omega)
    (by simp only [udivrem_320_256_image_udivrem_320_256_offset, pcAt, BitVec.reduceAppend,
      BitVec.reduceSignExtend]; bv_omega)
    (by simp only [udivrem_320_256_image_udivrem_320_256_offset, pcAt, BitVec.reduceAppend,
      BitVec.reduceSignExtend]; bv_omega)
    (by simp only [udivrem_320_256_image_udivrem_320_256_offset, pcAt, BitVec.reduceAppend,
      BitVec.reduceSignExtend]; bv_omega)
    (by simp only [udivrem_320_256_image_udivrem_320_256_offset, pcAt, BitVec.reduceAppend,
      BitVec.reduceSignExtend]; bv_omega)
    (by simp only [udivrem_320_256_image_udivrem_320_256_offset, pcAt, BitVec.reduceAppend,
      BitVec.reduceSignExtend]; bv_omega)
    (by simp only [udivrem_320_256_image_udivrem_320_256_offset, pcAt, BitVec.reduceAppend,
      BitVec.reduceSignExtend]; bv_omega)
    (by simp only [udivrem_320_256_image_udivrem_320_256_offset, pcAt, BitVec.reduceAppend,
      BitVec.reduceSignExtend]; bv_omega)
    (by simp only [udivrem_320_256_image_udivrem_320_256_offset, pcAt]; exact aligned_add hb3 (by decide))
    (by rw [hT]; omega) (hx ▸ hr) (by rw [hT]; omega) (by rw [hT]; omega) hhold hpre
  rwa [pcAt_zero] at h

/-- The registers of the nonvacuous instance: the result, u, v and the frame of 336 bytes above
the data. -/
theorem udivrem_320_256.nonvacuous :
    NonVacuousI udivrem_320_256_image_code udivrem_320_256_image_data udivrem_320_256_image_dataOff
      udivrem_320_256.bufs udivrem_320_256.pre :=
  nonVacuousI_of (fun i => if i = 10#5 then 0x80000C00#64 else if i = 11#5 then 0x80000C48#64
      else if i = 12#5 then 0x80000C70#64 else if i = 2#5 then 0x80000DE0#64 else 0)
    (by decide) (by decide) (by decide) (by decide)
    (by rw [show udivrem_320_256_image_dataOff = 12016 from rfl,
          show udivrem_320_256_image_data.length = 256 from rfl]
        simp only [udivrem_320_256.bufs, ↓reduceIte, BitVec.reduceEq, BitVec.reduceSub, bufWords,
          List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq]
        repeat' apply And.intro
        all_goals decide)
    (fun _ => by simp only [udivrem_320_256.pre, Buf, Disjoint]; decide)

end IntxRV.Api
