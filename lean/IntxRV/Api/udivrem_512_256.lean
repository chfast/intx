import IntxRV.Div512Top
/-!
# `udivrem()` of `uint512` by `uint256`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Divides u by v. A division by 0 gives 0 as the quotient and the remainder.
/// @post result.quot = u / v
/// @post result.rem = if v = 0 then 0 else u % v
template <unsigned M, unsigned N>
constexpr div_result<uint<M>, uint<N>> udivrem(const uint<M>& u, const uint<N>& v) noexcept
```

`udivrem_512_256.spec` states it for the RV64 machine code of `udivrem_512_256` in
`IntxRV/Api.cpp`, the division in `mulmod()`. The function saves ra and s0 to s5 in a frame of 160
bytes (`U512Frame`), counts the significant words n of v from the top and m of u (`u512_scan`), and
dispatches on them (`u512_dispatch`, `IntxRV/Div512Top.lean`): it returns 0 and u if u < v, and
otherwise zeroes the result with `memset()` and calls `udivrem_by1()` or `udivrem_by2()`
(`IntxRV/Div512By.lean`), or normalizes the divisor inline, u with `shl<9, 8>()`, and calls
`udivrem_knuth_normalized<3>()` or `udivrem_knuth_normalized<4>()` (`IntxRV/Div512K3.lean`,
`IntxRV/Div512K4.lean`). Each callee runs by its proof for the immediates of the address of the
table (`Reach.call_sub`, `Reach.call_sub_at`), and all the paths end in the epilogue at the
instruction 327 (`u512_epi`, `IntxRV/Div512.lean`).
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

set_option hygiene false in
/-- The frame after the prologue of `udivrem<512, 256>()`. -/
local macro "u512_pro_frame" : tactic => `(tactic| (
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  all_goals try (simp (disch := first | bv_omega | fail) only [memWord_memStore_self,
    memWord_memStore_of_ne]; done)
  · simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
    exact unchangedExcept2_refl _ _ _ _ _
  · intro r hr' hn
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte,
        List.mem_cons, List.not_mem_nil, or_false, not_true_eq_false, not_false_eq_true] at hn ⊢))

set_option hygiene false in
/-- The side goals of the dispatch and the count of u after the count of v. -/
local macro "u512_top_side" : tactic => `(tactic| (
  all_goals first
    | done
    | (exact U512Frame.regs hF1 (by simp (config := { decide := true }) only [Regs.get_set,
        ↓reduceIte]) (by u512_cs))
    | (simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; done)
    | exact words_lt _ _ _
    | assumption
    | (intro h; simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; done)
    | (intro h; exact absurd h (by decide))
    | (rw [hw4]; bv_omega)
    | (left; rfl)
    | (right; simp only [Nat.reduceSub, Nat.reduceMul]; assumption)))

set_option hygiene false in
/-- The exit of the count of the words of v with `k` words at 54 (u[7] ≠ 0) or 29 (u[7] = 0). -/
local macro "u512_top" k:num : tactic => `(tactic| first
  | (refine u512_dispatch base x m hb3 hr hpre0 hw hTr hTs hhold hD hT0.down hT1.down hT2.down
      hT3.down _ _ ?_ ?_ ?_ ?_ $k (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ 8 (by norm_num)
      (by norm_num) ?_ ?_ ?_
     u512_top_side
     done)
  | (refine u512_scan base x m hb3 hr hpre0 hw hTr hTs hhold hD hT0.down hT1.down hT2.down
      hT3.down _ _ ?_ ?_ ?_ ?_ $k (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_
     u512_top_side
     done))

/-- The run of `udivrem<512, 256>()` and its callees for any immediates of the address `T` of the
table of the reciprocal in the callees (`udivrem_512_256_progAt`), with the result and the frame of
240 bytes below sp outside the table. -/
theorem udivrem_512_256.reach (hi0 : BitVec 20) (lo0 : BitVec 12) (hi1 : BitVec 20)
    (lo1 : BitVec 12) (hi2 : BitVec 20) (lo2 : BitVec 12) (hi3 : BitVec 20) (lo3 : BitVec 12)
    (base T : BitVec 64) (x : Regs) (m : Mem)
    (hT0 : pcAt (pcAt base 409) 5 + ((hi0 ++ 0x000#12).signExtend 64 + lo0.signExtend 64) = T)
    (hT1 : pcAt (pcAt base 602) 54 + ((hi1 ++ 0x000#12).signExtend 64 + lo1.signExtend 64) = T)
    (hT2 : pcAt (pcAt base 916) 12 + ((hi2 ++ 0x000#12).signExtend 64 + lo2.signExtend 64) = T)
    (hT3 : pcAt (pcAt base 1091) 34 + ((hi3 ++ 0x000#12).signExtend 64 + lo3.signExtend 64) = T)
    (hb3 : base &&& 3 = 0) (hw : T.toNat + 8 * 256 ≤ 2 ^ 64) (hr : x.get 1#5 &&& 3 = 0)
    (hTr : (x.get 10#5).toNat + 96 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hTs : (x.get 2#5 - 240#64).toNat + 240 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 240#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hpre : udivrem_512_256.pre x m) :
    Reach (udivrem_512_256.bufs x ++ bufWords T 256)
      (udivrem_512_256_progAt hi0 lo0 hi1 lo1 hi2 lo2 hi3 lo3) base (pcAt base 0) x m
      (x.get 1#5) (udivrem_512_256.post x m) := by
  have hpre0 := hpre
  simp only [udivrem_512_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr⟩ := hpre
  simp only [udivrem_512_256.bufs]
  simp (disch := decide) only [Regs.eq_get x]
  generalize hDe : bufWords T 256 = D
  have hD : ∀ a ∈ bufWords T 256, a ∈ D := fun _ h => hDe ▸ h
  clear hDe
  show Reach (u512Bufs x D) _ _ _ _ _ _ _
  -- `omega` and `subst_vars` do not see the address of the table.
  replace hT0 := PLift.up hT0
  replace hT1 := PLift.up hT1
  replace hT2 := PLift.up hT2
  replace hT3 := PLift.up hT3
  have hw4 : words m (x.get 12#5) 4 = (memWord m (x.get 12#5).toNat).toNat + 2 ^ 64 *
      ((memWord m (x.get 12#5 + 8#64).toNat).toNat + 2 ^ 64 *
        ((memWord m (x.get 12#5 + 16#64).toNat).toNat + 2 ^ 64 *
          (memWord m (x.get 12#5 + 24#64).toNat).toNat)) := by
    simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
      Nat.add_zero]
  have hv0l := (memWord m (x.get 12#5).toNat).isLt
  have hv1l := (memWord m (x.get 12#5 + 8#64).toNat).isLt
  have hv2l := (memWord m (x.get 12#5 + 16#64).toNat).isLt
  rv_exec_cut 8
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.reduceSignExtend,
    BitVec.add_assoc, BitVec.reduceAdd]
  generalize hM1 : memStore (memStore (memStore (memStore (memStore (memStore (memStore m _ _) _ _)
    _ _) _ _) _ _) _ _) _ _ = M1
  have hF1 : U512Frame x m (x.set 2#5 (x.get 2#5 + 18446744073709551456#64)) M1 := by
    rw [← hM1]; u512_pro_frame
  have hu56 := hF1.memWord_u hpre0 56#64 (by decide)
  have hv8 := hF1.memWord_v hpre0 8#64 (by decide)
  have hv16 := hF1.memWord_v hpre0 16#64 (by decide)
  have hv24 := hF1.memWord_v hpre0 24#64 (by decide)
  rv_exec_cut 29 54
  all_goals rv_subst
  all_goals simp only [hu56, hv8, hv16, hv24] at *
  all_goals try simp only [sltu_zero_add_one]
  all_goals try split_ifs
  all_goals first | u512_top 4 | u512_top 3 | u512_top 2 | u512_top 1

theorem udivrem_512_256.proof : udivrem_512_256.spec := by
  apply runsI_of_reach udivrem_512_256_image_decodes
  intro base ret hb hr _ _ hw x m hx1 hbufs hhold hpre
  rw [show udivrem_512_256_image_dataOff = 5264 from rfl] at hw hhold hbufs ⊢
  rw [show udivrem_512_256_image_data.length = 256 from rfl] at hw hbufs ⊢
  have hb3 : base &&& 3 = 0 := by
    have := congrArg (· &&& 3#64) hb
    simpa [BitVec.and_assoc] using this
  have hx : x.get 1#5 = ret := by rw [← Regs.eq_get x (by decide)]; exact hx1
  have hpre' := hpre
  simp only [udivrem_512_256.pre, Buf] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  have hTr := buf_outside (x 10#5) base 12 5264 (8 * 256) (by norm_num)
    (hbufs _ (List.mem_append_left _ (List.mem_append_right _ (mem_bufWords_zero (by norm_num)))))
    (hbufs _ (List.mem_append_left _ (List.mem_append_right _ (mem_bufWords (by norm_num)))))
    (by rw [Regs.eq_get x (by decide)]; exact hpre'.1.2) (by norm_num)
  have hTs := buf_outside (x 2#5 - 240#64) base 30 5264 (8 * 256) (by norm_num)
    (hbufs _ (List.mem_append_right _ (mem_bufWords_zero (by norm_num))))
    (hbufs _ (List.mem_append_right _ (mem_bufWords (by norm_num))))
    (by rw [Regs.eq_get x (by decide)]; exact hpre'.2.2.2.2.2.1.2) (by norm_num)
  rw [Regs.eq_get x (by decide)] at hTr hTs
  have hT : (base + BitVec.ofNat 64 5264).toNat = base.toNat + 5264 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [show udivrem_512_256_entry = udivrem_512_256_image_udivrem_512_256_offset from rfl, dataWords,
    ← hx]
  refine Reach.lift udivrem_512_256_image_udivrem_512_256_in (by decide) ?_
  have h := udivrem_512_256.reach 0x1#20 0xe18#12 0x1#20 0xa50#12 0x0#20 0x610#12 0x0#20 0x2fc#12
    (pcAt base udivrem_512_256_image_udivrem_512_256_offset) _ x m
    (by simp only [udivrem_512_256_image_udivrem_512_256_offset, pcAt, BitVec.reduceAppend,
      BitVec.reduceSignExtend]; bv_omega)
    (by simp only [udivrem_512_256_image_udivrem_512_256_offset, pcAt, BitVec.reduceAppend,
      BitVec.reduceSignExtend]; bv_omega)
    (by simp only [udivrem_512_256_image_udivrem_512_256_offset, pcAt, BitVec.reduceAppend,
      BitVec.reduceSignExtend]; bv_omega)
    (by simp only [udivrem_512_256_image_udivrem_512_256_offset, pcAt, BitVec.reduceAppend,
      BitVec.reduceSignExtend]; bv_omega)
    (by simp only [udivrem_512_256_image_udivrem_512_256_offset, pcAt]; exact aligned_add hb3 (by decide))
    (by rw [hT]; omega) (hx ▸ hr) (by rw [hT]; omega) (by rw [hT]; omega) hhold hpre
  rwa [pcAt_zero] at h

/-- The registers of the nonvacuous instance: the result, u, v and the frame of 240 bytes above
the data. -/
theorem udivrem_512_256.nonvacuous :
    NonVacuousI udivrem_512_256_image_code udivrem_512_256_image_data udivrem_512_256_image_dataOff
      udivrem_512_256.bufs udivrem_512_256.pre :=
  nonVacuousI_of (fun i => if i = 10#5 then 0x80000C00#64 else if i = 11#5 then 0x80000C60#64
      else if i = 12#5 then 0x80000CA0#64 else if i = 2#5 then 0x80000DB0#64 else 0)
    (by decide) (by decide) (by decide) (by decide)
    (by rw [show udivrem_512_256_image_dataOff = 5264 from rfl,
          show udivrem_512_256_image_data.length = 256 from rfl]
        simp only [udivrem_512_256.bufs, ↓reduceIte, BitVec.reduceEq, BitVec.reduceSub, bufWords,
          List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq]
        repeat' apply And.intro
        all_goals decide)
    (fun _ => by simp only [udivrem_512_256.pre, Buf, Disjoint]; decide)

end IntxRV.Api
