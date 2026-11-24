import IntxRV.AddModFast
/-!
# `addmod()` of `uint256`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Computes (x + y) % mod without the overflow of x + y. A modulus of 0 gives 0.
/// @post result = if mod = 0 then 0 else (x + y) % mod
constexpr uint256 addmod(const uint256& x, const uint256& y, const uint256& mod) noexcept
```

`addmod_256.spec` states it for the RV64 machine code of `addmod_256` in `IntxRV/Api.cpp`. The
function saves ra and s0 to s3 in a frame of 160 bytes (`AMFrame`, `IntxRV/AddMod.lean`) and
dispatches on the top words of x, y and the modulus (`am_main`, `IntxRV/AddModFast.lean`). For a
modulus below 2^192 or a top word of x or y above the top word of the modulus, it stores the sum
of 5 words in the frame and calls `udivrem<320, 256>()` (`am_slow`, `am_call`), which runs by its
proof for the immediates of the address of the table (`Reach.call_sub`), and copies the remainder
to the result. Otherwise x and y are less than twice the modulus: it subtracts the modulus from
each unless it borrows (`am_x`, `am_y`), adds the two remainders and subtracts the modulus from
the sum unless the sum does not carry and the subtraction borrows (`am_sum`). Both paths end in the
epilogue at the instruction 55 (`am_epi`). The proofs run the code of the image with the
instructions of the callees nested to the right (`pa_eq`).
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

set_option hygiene false in
/-- The frame after the prologue of `addmod()`. -/
local macro "am_pro_frame" : tactic => `(tactic| (
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

/-- The run of `addmod()` and its callees with the result and the frame of 496 bytes below sp
outside the table. -/
theorem addmod_256.reach (base T : BitVec 64) (x : Regs) (m : Mem)
    (hT0 : pcAt (pcAt (pcAt base 158) 182) 5 + ((0x3#20 ++ 0x000#12).signExtend 64 +
      (0xc04#12).signExtend 64) = T)
    (hT1 : pcAt (pcAt (pcAt base 158) 375) 5 + ((0x3#20 ++ 0x000#12).signExtend 64 +
      (0x900#12).signExtend 64) = T)
    (hT2 : pcAt (pcAt (pcAt base 158) 618) 54 + ((0x2#20 ++ 0x000#12).signExtend 64 +
      (0x470#12).signExtend 64) = T)
    (hT3 : pcAt (pcAt (pcAt base 158) 932) 50 + ((0x2#20 ++ 0x000#12).signExtend 64 +
      (0xf98#12).signExtend 64) = T)
    (hT4 : pcAt (pcAt (pcAt base 158) 1275) 65 + ((0x2#20 ++ 0x000#12).signExtend 64 +
      (0xa00#12).signExtend 64) = T)
    (hT5 : pcAt (pcAt (pcAt base 158) 1457) 64 + ((0x1#20 ++ 0x000#12).signExtend 64 +
      (0x72c#12).signExtend 64) = T)
    (hT6 : pcAt (pcAt (pcAt base 158) 1661) 87 + ((0x1#20 ++ 0x000#12).signExtend 64 +
      (0x3a0#12).signExtend 64) = T)
    (hT7 : pcAt (pcAt (pcAt base 158) 1948) 107 + ((0x1#20 ++ 0x000#12).signExtend 64 +
      (0xed4#12).signExtend 64) = T)
    (hT8 : pcAt (pcAt (pcAt base 158) 2273) 84 + ((0x1#20 ++ 0x000#12).signExtend 64 +
      (0xa1c#12).signExtend 64) = T)
    (hT9 : pcAt (pcAt (pcAt base 158) 2585) 184 + ((0x0#20 ++ 0x000#12).signExtend 64 +
      (0x3ac#12).signExtend 64) = T)
    (hb3 : base &&& 3 = 0) (hw : T.toNat + 8 * 256 ≤ 2 ^ 64) (hr : x.get 1#5 &&& 3 = 0)
    (hTr : (x.get 10#5).toNat + 32 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hTs : (x.get 2#5 - 496#64).toNat + 496 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 496#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hpre : addmod_256.pre x m) :
    Reach (addmod_256.bufs x ++ bufWords T 256) addmod_256_image_prog base (pcAt base 0) x m
      (x.get 1#5) (addmod_256.post x m) := by
  -- `omega` does not see the addresses of the table.
  replace hT0 := PLift.up hT0
  replace hT1 := PLift.up hT1
  replace hT2 := PLift.up hT2
  replace hT3 := PLift.up hT3
  replace hT4 := PLift.up hT4
  replace hT5 := PLift.up hT5
  replace hT6 := PLift.up hT6
  replace hT7 := PLift.up hT7
  replace hT8 := PLift.up hT8
  replace hT9 := PLift.up hT9
  have hpre0 := hpre
  simp only [addmod_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hxa, hxn⟩, ⟨hya, hyn⟩, ⟨hma, hmn⟩, hdrx, hdry, hdrm, ⟨hsa, hsn⟩, hdsx,
    hdsy, hdsm, hdsr⟩ := hpre
  simp only [addmod_256.bufs]
  simp (disch := decide) only [Regs.eq_get x]
  generalize hDe : bufWords T 256 = D
  have hD : ∀ a ∈ bufWords T 256, a ∈ D := fun _ h => hDe ▸ h
  clear hDe
  show Reach (amBufs x D) _ _ _ _ _ _ _
  rw [pa_eq]
  rv_exec_cut 6
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.reduceSignExtend,
    BitVec.add_assoc, BitVec.reduceAdd]
  generalize hM1 : memStore (memStore (memStore (memStore (memStore m _ _) _ _) _ _) _ _) _ _ = M1
  have hF1 : AMFrame x m (x.set 2#5 (x.get 2#5 + 18446744073709551456#64)) M1 := by
    rw [← hM1]; am_pro_frame
  exact am_main base T x m hb3 hr hpre0 hw hTr hTs hhold hD hT0.down hT1.down hT2.down hT3.down
    hT4.down hT5.down hT6.down hT7.down hT8.down hT9.down
    _ _ hF1 (by simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte])
    (by simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte])
    (by simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte])
    (by simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte])

theorem addmod_256.proof : addmod_256.spec := by
  apply runsI_of_reach addmod_256_image_decodes
  intro base ret hb hr _ _ hw x m hx1 hbufs hhold hpre
  rw [show addmod_256_image_dataOff = 12648 from rfl] at hw hhold hbufs ⊢
  rw [show addmod_256_image_data.length = 256 from rfl] at hw hbufs ⊢
  have hb3 : base &&& 3 = 0 := by
    have := congrArg (· &&& 3#64) hb
    simpa [BitVec.and_assoc] using this
  have hx : x.get 1#5 = ret := by rw [← Regs.eq_get x (by decide)]; exact hx1
  have hpre' := hpre
  simp only [addmod_256.pre, Buf] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  have hTr := buf_outside (x 10#5) base 4 12648 (8 * 256) (by norm_num)
    (hbufs _ (List.mem_append_left _ (List.mem_append_right _ (mem_bufWords_zero (by norm_num)))))
    (hbufs _ (List.mem_append_left _ (List.mem_append_right _ (mem_bufWords (by norm_num)))))
    (by rw [Regs.eq_get x (by decide)]; exact hpre'.1.2) (by norm_num)
  have hTs := buf_outside (x 2#5 - 496#64) base 62 12648 (8 * 256) (by norm_num)
    (hbufs _ (List.mem_append_right _ (mem_bufWords_zero (by norm_num))))
    (hbufs _ (List.mem_append_right _ (mem_bufWords (by norm_num))))
    (by rw [Regs.eq_get x (by decide)]; exact hpre'.2.2.2.2.2.2.2.1.2) (by norm_num)
  rw [Regs.eq_get x (by decide)] at hTr hTs
  have hT : (base + BitVec.ofNat 64 12648).toNat = base.toNat + 12648 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [show addmod_256_entry = 0 from rfl, dataWords, ← hx]
  exact addmod_256.reach base _ x m
    (by simp only [pcAt, BitVec.reduceAppend, BitVec.reduceSignExtend]; bv_omega)
    (by simp only [pcAt, BitVec.reduceAppend, BitVec.reduceSignExtend]; bv_omega)
    (by simp only [pcAt, BitVec.reduceAppend, BitVec.reduceSignExtend]; bv_omega)
    (by simp only [pcAt, BitVec.reduceAppend, BitVec.reduceSignExtend]; bv_omega)
    (by simp only [pcAt, BitVec.reduceAppend, BitVec.reduceSignExtend]; bv_omega)
    (by simp only [pcAt, BitVec.reduceAppend, BitVec.reduceSignExtend]; bv_omega)
    (by simp only [pcAt, BitVec.reduceAppend, BitVec.reduceSignExtend]; bv_omega)
    (by simp only [pcAt, BitVec.reduceAppend, BitVec.reduceSignExtend]; bv_omega)
    (by simp only [pcAt, BitVec.reduceAppend, BitVec.reduceSignExtend]; bv_omega)
    (by simp only [pcAt, BitVec.reduceAppend, BitVec.reduceSignExtend]; bv_omega)
    hb3 (by rw [hT]; omega) (hx ▸ hr) (by rw [hT]; omega) (by rw [hT]; omega) hhold hpre

/-- The registers of the nonvacuous instance: the result, x, y, the modulus and the frame of 496
bytes above the data. -/
theorem addmod_256.nonvacuous :
    NonVacuousI addmod_256_image_code addmod_256_image_data addmod_256_image_dataOff
      addmod_256.bufs addmod_256.pre :=
  nonVacuousI_of (fun i => if i = 10#5 then 0x80000C00#64 else if i = 11#5 then 0x80000C20#64
      else if i = 12#5 then 0x80000C40#64 else if i = 13#5 then 0x80000C60#64
      else if i = 2#5 then 0x80000E70#64 else 0)
    (by decide) (by decide) (by decide) (by decide)
    (by rw [show addmod_256_image_dataOff = 12648 from rfl,
          show addmod_256_image_data.length = 256 from rfl]
        simp only [addmod_256.bufs, ↓reduceIte, BitVec.reduceEq, BitVec.reduceSub, bufWords,
          List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq]
        repeat' apply And.intro
        all_goals decide)
    (fun _ => by simp only [addmod_256.pre, Buf, Disjoint]; decide)

end IntxRV.Api
