import IntxRV.SDiv
/-!
# `sdivrem()` of `uint256`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Divides u by v as signed numbers. A division by 0 gives 0 as the quotient and the remainder.
/// @post result.quot = Int.toNat ((signed N u).tdiv (signed N v) % 2^N)
/// @post result.rem = if v = 0 then 0 else Int.toNat ((signed N u).tmod (signed N v) % 2^N)
template <unsigned N>
constexpr div_result<uint<N>> sdivrem(const uint<N>& u, const uint<N>& v) noexcept
```

`sdivrem_256.spec` states it for the RV64 machine code of `sdivrem_256` in `IntxRV/Api.cpp`. The
function saves ra and s0 to s3 in a frame of 112 bytes (`SDFrame`, `IntxRV/SDiv.lean`), copies u
and v to the frame or negates them there by their signs (`sd_main`), calls `udivrem<256, 256>()`
on the magnitudes by its proof (`sd_call`), negates the quotient in the result for different signs
(`sd_quot`) and the remainder for a negative u (`sd_rem`). The negations are `neg4_words`
(`IntxRV/Neg.lean`); `sdivrem_quot` and `sdivrem_rem` give the truncated signed division from the
division of the magnitudes.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

set_option hygiene false in
/-- The frame after the prologue of `sdivrem()`. -/
local macro "sd_pro_frame" : tactic => `(tactic| (
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  all_goals try (simp (disch := first | bv_omega | fail) only [memWord_memStore_self,
    memWord_memStore_of_ne]; done)
  · simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
    exact unchangedExcept2_refl _ _ _ _ _
  · intro r hr' hn
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte] at hn ⊢))

/-- The run of `sdivrem()` and its callees with the result and the frame of 160 bytes below sp
outside the table. -/
theorem sdivrem_256.reach (base T : BitVec 64) (x : Regs) (m : Mem)
    (hT0 : pcAt (pcAt (pcAt base 131) 108) 5 + ((0x1#20 ++ 0x000#12).signExtend 64 +
      (0x2d0#12).signExtend 64) = T)
    (hT1 : pcAt (pcAt (pcAt base 131) 301) 54 + ((0x1#20 ++ 0x000#12).signExtend 64 +
      (0xf08#12).signExtend 64) = T)
    (hT2 : pcAt (pcAt (pcAt base 131) 615) 89 + ((0x1#20 ++ 0x000#12).signExtend 64 +
      (0x994#12).signExtend 64) = T)
    (hT3 : pcAt (pcAt (pcAt base 131) 824) 75 + ((0x0#20 ++ 0x000#12).signExtend 64 +
      (0x688#12).signExtend 64) = T)
    (hT4 : pcAt (pcAt (pcAt base 131) 1033) 85 + ((0x0#20 ++ 0x000#12).signExtend 64 +
      (0x31c#12).signExtend 64) = T)
    (hb3 : base &&& 3 = 0) (hw : T.toNat + 8 * 256 ≤ 2 ^ 64) (hr : x.get 1#5 &&& 3 = 0)
    (hTr : (x.get 10#5).toNat + 64 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hTs : (x.get 2#5 - 160#64).toNat + 160 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 160#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hpre : sdivrem_256.pre x m) :
    Reach (sdivrem_256.bufs x ++ bufWords T 256) sdivrem_256_image_prog base (pcAt base 0) x m
      (x.get 1#5) (sdivrem_256.post x m) := by
  -- `omega` does not see the addresses of the table.
  replace hT0 := PLift.up hT0
  replace hT1 := PLift.up hT1
  replace hT2 := PLift.up hT2
  replace hT3 := PLift.up hT3
  replace hT4 := PLift.up hT4
  have hpre0 := hpre
  simp only [sdivrem_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr⟩ := hpre
  simp only [sdivrem_256.bufs]
  simp (disch := decide) only [Regs.eq_get x]
  generalize hDe : bufWords T 256 = D
  have hD : ∀ a ∈ bufWords T 256, a ∈ D := fun _ h => hDe ▸ h
  clear hDe
  show Reach (sdBufs x D) _ _ _ _ _ _ _
  rw [ps_eq]
  rv_exec_cut 6
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.reduceSignExtend,
    BitVec.add_assoc, BitVec.reduceAdd]
  generalize hM1 : memStore (memStore (memStore (memStore (memStore m _ _) _ _) _ _) _ _) _ _ = M1
  have hF1 : SDFrame x m (x.set 2#5 (x.get 2#5 + 18446744073709551504#64)) M1 := by
    rw [← hM1]; sd_pro_frame
  exact sd_main base T x m hb3 hr hpre0 hw hTr hTs hhold hD hT0.down hT1.down hT2.down hT3.down
    hT4.down
    _ _ hF1 (by simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte])
    (by simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte])
    (by simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte])

theorem sdivrem_256.proof_of_decodes (hdec : sdivrem_256.decodes) : sdivrem_256.spec := by
  apply runsI_of_reach hdec
  intro base ret hb hr _ _ hw x m hx1 hbufs hhold hpre
  rw [show sdivrem_256_image_dataOff = 5792 from rfl] at hw hhold hbufs ⊢
  rw [show sdivrem_256_image_data.length = 256 from rfl] at hw hbufs ⊢
  have hb3 : base &&& 3 = 0 := by
    have := congrArg (· &&& 3#64) hb
    simpa [BitVec.and_assoc] using this
  have hx : x.get 1#5 = ret := by rw [← Regs.eq_get x (by decide)]; exact hx1
  have hpre' := hpre
  simp only [sdivrem_256.pre, Buf] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  have hTr := buf_outside (x 10#5) base 8 5792 (8 * 256) (by norm_num)
    (hbufs _ (List.mem_append_left _ (List.mem_append_right _ (mem_bufWords_zero (by norm_num)))))
    (hbufs _ (List.mem_append_left _ (List.mem_append_right _ (mem_bufWords (by norm_num)))))
    (by rw [Regs.eq_get x (by decide)]; exact hpre'.1.2) (by norm_num)
  have hTs := buf_outside (x 2#5 - 160#64) base 20 5792 (8 * 256) (by norm_num)
    (hbufs _ (List.mem_append_right _ (mem_bufWords_zero (by norm_num))))
    (hbufs _ (List.mem_append_right _ (mem_bufWords (by norm_num))))
    (by rw [Regs.eq_get x (by decide)]; exact hpre'.2.2.2.2.2.1.2) (by norm_num)
  rw [Regs.eq_get x (by decide)] at hTr hTs
  have hT : (base + BitVec.ofNat 64 5792).toNat = base.toNat + 5792 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [show sdivrem_256_entry = 0 from rfl, dataWords, ← hx]
  exact sdivrem_256.reach base _ x m
    (by simp only [pcAt, BitVec.reduceAppend, BitVec.reduceSignExtend]; bv_omega)
    (by simp only [pcAt, BitVec.reduceAppend, BitVec.reduceSignExtend]; bv_omega)
    (by simp only [pcAt, BitVec.reduceAppend, BitVec.reduceSignExtend]; bv_omega)
    (by simp only [pcAt, BitVec.reduceAppend, BitVec.reduceSignExtend]; bv_omega)
    (by simp only [pcAt, BitVec.reduceAppend, BitVec.reduceSignExtend]; bv_omega)
    hb3 (by rw [hT]; omega) (hx ▸ hr) (by rw [hT]; omega) (by rw [hT]; omega) hhold hpre

/-- The registers of the nonvacuous instance: the result, u, v and the frame of 160 bytes above
the data. -/
theorem sdivrem_256.nonvacuous :
    NonVacuousI sdivrem_256_image_code sdivrem_256_image_data sdivrem_256_image_dataOff
      sdivrem_256.bufs sdivrem_256.pre :=
  nonVacuousI_of (fun i => if i = 10#5 then 0x80000C00#64 else if i = 11#5 then 0x80000C40#64
      else if i = 12#5 then 0x80000C60#64 else if i = 2#5 then 0x80000D20#64 else 0)
    (by decide) (by decide) (by decide) (by decide)
    (by rw [show sdivrem_256_image_dataOff = 5792 from rfl,
          show sdivrem_256_image_data.length = 256 from rfl]
        simp only [sdivrem_256.bufs, ↓reduceIte, BitVec.reduceEq, BitVec.reduceSub, bufWords,
          List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq]
        repeat' apply And.intro
        all_goals decide)
    (fun _ => by simp only [sdivrem_256.pre, Buf, Disjoint]; decide)

end IntxRV.Api
