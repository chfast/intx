import IntxRV.DivTopE
/-!
# `internal::udivrem_top2<3, true>()` of `uint320` by `uint256`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Divides u by v when the quotient fits in two words: v has TOP significant words
/// and u has one more word, or two more words with the top one less than v[TOP - 1].
/// With EQUAL (TOP 3 only) the top word of u may also equal v[TOP - 1]: the quotient has then
/// up to 129 bits.
///
/// The quotient is estimated from the top 2 words of the normalized divisor with two 3/2
/// divisions and corrected with the remainder, computed from the remainder of the 3/2 divisions
/// and the low words of the original (not normalized) operands.
/// The word v[TOP - 1] must not be zero.
/// @pre 2 ^ (64 * (TOP - 1)) <= v
/// @pre v < 2 ^ (64 * TOP)
/// @pre u / 2 ^ (64 * (TOP + 1)) < v / 2 ^ (64 * (TOP - 1)) + EQUAL
/// @post result.quot = u / v
/// @post result.rem = u % v
template <size_t TOP, bool EQUAL = false, unsigned M, unsigned N>
constexpr div_result<uint<M>, uint<N>> udivrem_top2(const uint<M>& u, const uint<N>& v) noexcept
```

`udivrem_top2_3_equal_320.spec` states it for the RV64 machine code of `udivrem_top2_3_equal_320`
in `IntxRV/Api.cpp`, the instance that `udivrem<320, 256>()` calls for a divisor of 3 words when the
top word of the numerator equals v[2]: the numerator has the word u[4] at most v[2] (`topE_ue`).
The normalization is that of the instance without EQUAL (`IntxRV/Api/udivrem_top2_3_320.lean`);
the two paths meet at 81 (`topE_main`). The blocks are in `IntxRV/DivTopE.lean`. The function saves
s0 to s4 in a frame of 48 bytes. `udivrem_top2_3_equal_320.reach` is the run for any immediates of
the address of the table.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- The run of `udivrem_top2<3, true, 320, 256>()` for any immediates `hi` and `lo` of the address
`T` of the table of the reciprocal, with the frame of 48 bytes below sp outside the table. -/
theorem udivrem_top2_3_equal_320.reach (hi : BitVec 20) (lo : BitVec 12) (base T : BitVec 64)
    (x : Regs) (m : Mem)
    (hT : pcAt base 107 + ((hi ++ 0x000#12).signExtend 64 + lo.signExtend 64) = T)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64) (hr : x.get 1#5 &&& 3 = 0)
    (hstk : (x.get 2#5 - 48#64).toNat + 48 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 2#5 - 48#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data)
    (hpre : udivrem_top2_3_equal_320.pre x m) :
    Reach (udivrem_top2_3_equal_320.bufs x ++ bufWords T 256) (udivrem_top2_3_equal_320_progAt hi lo)
      base (pcAt base 0) x m (x.get 1#5) (udivrem_top2_3_equal_320.post x m) := by
  have hpre0 := hpre
  simp only [udivrem_top2_3_equal_320.pre, udivrem_top2_3_equal_320.bufs, Buf] at hpre ⊢
  simp (disch := decide) only [Regs.eq_get x] at hpre ⊢
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr, hv1, hv2,
    hu3⟩ := hpre
  have hv3 := top4_zero m (x.get 12#5) hv2
  have hv2' := top3_ne_zero m (x.get 12#5) hv1 hv3
  have hue := topE_ue m (x.get 11#5) (x.get 12#5) hu3 hv3
  rv_exec_cut 81
  all_goals
    set v2 := memWord m (x.get 12#5 + 16#64).toNat with hv2e
    set v1 := memWord m (x.get 12#5 + 8#64).toNat with hv1e
    set v0 := memWord m (x.get 12#5).toNat with hv0e
    set ue := memWord m (x.get 11#5 + 32#64).toNat with huee
    set u3 := memWord m (x.get 11#5 + 24#64).toNat with hu3e
    set u2 := memWord m (x.get 11#5 + 16#64).toNat with hu2e
    set u1 := memWord m (x.get 11#5 + 8#64).toNat with hu1e
    set u0 := memWord m (x.get 11#5).toNat with hu0e
    rv_copies
    have hv2n : v2 ≠ 0 := fun h => hv2' (by rw [h]; rfl)
    -- The count of the leading zeros of v[2], S.
    have hs := clz_ite v2
    rw [if_neg hv2n, swarClz_expand, smear_expand] at hs
    rv_fold hs
    rv_fold hs
    subst hs
    have hL64 : v2.toNat.log2 < 64 := (Nat.log2_lt hv2').mpr v2.isLt
    have hSt : (BitVec.ofNat 64 (63 - v2.toNat.log2)).toNat = 63 - v2.toNat.log2 :=
      ofNat_S_toNat (by omega)
    have hS1 : v2.toNat * 2 ^ (63 - v2.toNat.log2) < 2 ^ 64 := by
      have := Nat.lt_log2_self (n := v2.toNat)
      calc v2.toNat * 2 ^ (63 - v2.toNat.log2)
          < 2 ^ (v2.toNat.log2 + 1) * 2 ^ (63 - v2.toNat.log2) :=
            Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos _)
        _ = 2 ^ 64 := by rw [← pow_add]; congr 1; omega
    have hS63 : 2 ^ 63 ≤ v2.toNat * 2 ^ (63 - v2.toNat.log2) := by
      have := Nat.log2_self_le hv2'
      calc 2 ^ 63 = 2 ^ v2.toNat.log2 * 2 ^ (63 - v2.toNat.log2) := by
            rw [← pow_add]; congr 1; omega
        _ ≤ _ := Nat.mul_le_mul_right _ this
    have hVw : words m (x.get 12#5) 4 = v0.toNat + 2 ^ 64 * (v1.toNat + 2 ^ 64 * v2.toNat) :=
      (words_v3 m (x.get 12#5) hv3).symm
    have hUw : words m (x.get 11#5) 5 = u0.toNat + 2 ^ 64 * (u1.toNat + 2 ^ 64 * (u2.toNat +
        2 ^ 64 * (u3.toNat + 2 ^ 64 * ue.toNat))) := by
      simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
        Nat.add_zero]
      rfl
    -- u[4] <= v[2] < 2^(64 - S): the shifted u has 5 words.
    have hueQ : ue.toNat < 2 ^ (64 - (63 - v2.toNat.log2)) := by
      have hP : 2 ^ (63 - v2.toNat.log2) * 2 ^ (64 - (63 - v2.toNat.log2)) = 2 ^ 64 := by
        rw [← pow_add]; congr 1; omega
      by_contra hc
      have := Nat.mul_le_mul_right (2 ^ (63 - v2.toNat.log2)) (Nat.le_of_not_lt hc)
      rw [Nat.mul_comm (2 ^ (64 - _)), hP] at this
      have : ue.toNat * 2 ^ (63 - v2.toNat.log2) ≤ v2.toNat * 2 ^ (63 - v2.toNat.log2) :=
        Nat.mul_le_mul_right _ hue
      omega
  -- s ≠ 0: the normalized words by the funnel shifts.
  all_goals first
    | (rv_lacks ¬BitVec.ofNat 64 (63 - v2.toNat.log2) = 0#64; skip)
    | (rv_get hne : ¬BitVec.ofNat 64 (63 - v2.toNat.log2) = 0#64
       have hS0 := ofNat_S_ne (by omega) hne
       have hd0 := toNat_fshl_code v1 v0 (BitVec.ofNat 64 (63 - v2.toNat.log2)) (by rw [hSt]; omega)
       have hd1 := toNat_fshl_code v2 v1 (BitVec.ofNat 64 (63 - v2.toNat.log2)) (by rw [hSt]; omega)
       have ht3 := toNat_fshl_code ue u3 (BitVec.ofNat 64 (63 - v2.toNat.log2)) (by rw [hSt]; omega)
       have ht2 := toNat_fshl_code u3 u2 (BitVec.ofNat 64 (63 - v2.toNat.log2)) (by rw [hSt]; omega)
       have ht1 := toNat_fshl_code u2 u1 (BitVec.ofNat 64 (63 - v2.toNat.log2)) (by rw [hSt]; omega)
       have ht0 := toNat_fshl_code u1 u0 (BitVec.ofNat 64 (63 - v2.toNat.log2)) (by rw [hSt]; omega)
       rv_fold hd0
       rv_fold hd0
       rv_fold hd1
       rv_fold hd1
       rv_fold ht3
       rv_fold ht3
       rv_fold ht2
       rv_fold ht2
       rv_fold ht1
       rv_fold ht1
       rv_fold ht0
       rv_fold ht0
       conv at hd0 => rhs; rw [hSt]
       conv at hd1 => rhs; rw [hSt]
       conv at ht3 => rhs; rw [hSt]
       conv at ht2 => rhs; rw [hSt]
       conv at ht1 => rhs; rw [hSt]
       conv at ht0 => rhs; rw [hSt]
       refine topE_main hi lo base T x m hT hw hr hstk hhold hpre0 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
       · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
       · intro r hr
         simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
         obtain ⟨h5, h6, h7, h11, h13, h14, h15, h16, h17, h28, h29, h30, -⟩ := hr
         simp (config := { decide := true }) only [Regs.set_apply, h5, h6, h7, h11, h13, h14, h15,
           h16, h17, h28, h29, h30, ↓reduceIte]
       all_goals simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
       all_goals try first | exact hv0e | exact hu0e
       · rw [hSt]; omega
       · rw [hSt, hd0, hd1, hVw, norm2_low _ _ _ _ v1.isLt v0.isLt (by omega) ?_,
           div_low_word _ _ _ (by omega)]
         have := fshl_lt (by omega) v1.isLt hS1
         have hP : 2 ^ (63 - v2.toNat.log2) * 2 ^ (64 - (63 - v2.toNat.log2)) = 2 ^ 64 := by
           rw [← pow_add]; congr 1; omega
         have : v1.toNat * 2 ^ (63 - v2.toNat.log2) < 2 ^ 64 * 2 ^ (63 - v2.toNat.log2) :=
           Nat.mul_lt_mul_of_pos_right v1.isLt (Nat.two_pow_pos _)
         have hv2Q : v2.toNat < 2 ^ (64 - (63 - v2.toNat.log2)) := by
           by_contra hc
           have := Nat.mul_le_mul_right (2 ^ (63 - v2.toNat.log2)) (Nat.le_of_not_lt hc)
           rw [Nat.mul_comm (2 ^ (64 - _)), hP] at this
           omega
         have hv2P : (v2.toNat + 1) * 2 ^ (63 - v2.toNat.log2) ≤ 2 ^ 64 := by
           rw [← hP, Nat.mul_comm (2 ^ (63 - _))]
           exact Nat.mul_le_mul_right _ hv2Q
         nlinarith
       · rw [hd1]; exact norm2_hi (d0 := v1.toNat) (by omega) v1.isLt hS1 hS63
       · rw [hSt, ht0, ht1, ht2, ht3, hUw, norm5_words _ _ _ _ _ _ u0.isLt u1.isLt u2.isLt u3.isLt
           hueQ (by omega), div_low_word _ _ _ (by omega)])
  -- s = 0: the words not shifted.
  all_goals
    rv_get hz : BitVec.ofNat 64 (63 - v2.toNat.log2) = 0#64
    have hS0 := ofNat_S_eq (by omega) hz
    have hd63 : 2 ^ 63 ≤ v2.toNat := by rw [hS0] at hS63; simpa using hS63
    refine topE_main hi lo base T x m hT hw hr hstk hhold hpre0 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨h5, h6, h7, -, h13, h14, h15, h16, h17, h28, h29, -, -⟩ := hr
      simp (config := { decide := true }) only [Regs.set_apply, h5, h6, h7, h13, h14, h15, h16,
        h17, h28, h29, ↓reduceIte]
    all_goals simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    all_goals try first | exact hv0e | exact hu0e
    · rw [hSt]; omega
    · rw [hSt, hS0, hVw, div_low_word _ _ _ (by omega), Nat.div_eq_of_lt v0.isLt]
      simp
    · exact hd63
    · rw [hSt, hS0, hUw, div_low_word _ _ _ (by omega), Nat.div_eq_of_lt u0.isLt]
      simp

theorem udivrem_top2_3_equal_320.proof : udivrem_top2_3_equal_320.spec := by
  apply runsI_of_reach udivrem_top2_3_equal_320_image_decodes
  intro base ret _ hr _ _ hw x m hx1 hbufs hhold hpre
  rw [show udivrem_top2_3_equal_320_image_dataOff = 1304 from rfl] at hw hhold hbufs ⊢
  rw [show udivrem_top2_3_equal_320_image_data.length = 256 from rfl] at hw hbufs ⊢
  have hx : x.get 1#5 = ret := by rw [← Regs.eq_get x (by decide)]; exact hx1
  have hpre' := hpre
  simp only [udivrem_top2_3_equal_320.pre, Buf] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  have hst := frame48_outside (x 2#5) base 1304 (8 * 256)
    (hbufs _ (List.mem_append_right _ (mem_bufWords_zero (by norm_num))))
    (hbufs _ (List.mem_append_right _ (mem_bufWords (by norm_num))))
    (by rw [Regs.eq_get x (by decide)]; exact hpre'.2.2.2.2.2.1.2) (by norm_num)
  rw [Regs.eq_get x (by decide)] at hst
  rw [show udivrem_top2_3_equal_320_entry =
      udivrem_top2_3_equal_320_image_udivrem_top2_3_equal_320_offset from rfl, dataWords, ← hx]
  refine Reach.lift udivrem_top2_3_equal_320_image_udivrem_top2_3_equal_320_in (by decide) ?_
  have hT : (base + BitVec.ofNat 64 1304).toNat = base.toNat + 1304 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have h := udivrem_top2_3_equal_320.reach 0x0#20 0x36c#12
    (pcAt base udivrem_top2_3_equal_320_image_udivrem_top2_3_equal_320_offset) _ x m
    (by simp only [udivrem_top2_3_equal_320_image_udivrem_top2_3_equal_320_offset, pcAt,
      BitVec.reduceAppend, BitVec.reduceSignExtend]; bv_omega)
    (by rw [hT]; omega) (hx ▸ hr) (by rw [hT]; omega) hhold hpre
  rwa [pcAt_zero] at h

/-- The registers of the nonvacuous instance: the result, u = 2^256 and v = 2^128 above the data,
with u[4] equal to v[2], and the frame below sp. -/
theorem udivrem_top2_3_equal_320.nonvacuous :
    NonVacuousI udivrem_top2_3_equal_320_image_code udivrem_top2_3_equal_320_image_data
      udivrem_top2_3_equal_320_image_dataOff udivrem_top2_3_equal_320.bufs
      udivrem_top2_3_equal_320.pre :=
  nonVacuousI_of_args (fun i => if i = 10#5 then 0x80000D20#64 else if i = 11#5 then 0x80000D68#64
      else if i = 12#5 then 0x80000D90#64 else if i = 2#5 then 0x80000DE0#64 else 0)
    0x80000D68 [0, 0, 0, 0, 1, 0, 0, 1, 0]
    (by decide) (by decide) (by decide) (by decide)
    (by rw [show udivrem_top2_3_equal_320_image_dataOff = 1304 from rfl,
          show udivrem_top2_3_equal_320_image_data.length = 256 from rfl]
        simp only [udivrem_top2_3_equal_320.bufs, ↓reduceIte, BitVec.reduceEq, BitVec.reduceSub,
          bufWords, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq]
        repeat' apply And.intro
        all_goals decide)
    (by decide)
    (fun m => by
      simp only [udivrem_top2_3_equal_320.pre, Buf, Disjoint, words, ↓reduceIte, BitVec.reduceEq,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, BitVec.toNat_ofNat,
        Nat.reducePow, Nat.reduceMod, Nat.mul_zero, Nat.add_zero]
      simp (disch := decide) only [memWord_storeWords_getD]
      decide)

end IntxRV.Api
