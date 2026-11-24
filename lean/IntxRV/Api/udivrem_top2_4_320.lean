import IntxRV.DivTop24
/-!
# `internal::udivrem_top2<4>()` of `uint320` by `uint256`

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
/// @pre 2^(64 * (TOP - 1)) ≤ v
/// @pre v < 2^(64 * TOP)
/// @pre u / 2^(64 * (TOP + 1)) < v / 2^(64 * (TOP - 1)) + EQUAL
/// @post result.quot = u / v
/// @post result.rem = u % v
template <size_t TOP, bool EQUAL = false, unsigned M, unsigned N>
constexpr div_result<uint<M>, uint<N>> udivrem_top2(const uint<M>& u, const uint<N>& v) noexcept
```

`udivrem_top2_4_320.spec` states it for the RV64 machine code of `udivrem_top2_4_320` in
`IntxRV/Api.cpp`, the instance that `udivrem<320, 256>()` calls for a divisor of 4 words when u[4]
is not less than v[3]. The numerator has no word above the significant words of v, so the top
digit of the normalized u is u[4] shifted right, less than the top word of the normalized v. The
function normalizes the top words of u and v with the count of the leading zeros of v[3]; the two
paths meet at 78 (`top24_main`). The blocks are in `IntxRV/DivTop24.lean`. The function saves s0 to
s3 in a frame of 32 bytes. `udivrem_top2_4_320.reach` is the run for any immediates of the address
of the table.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- The run of `udivrem_top2<4, false, 320, 256>()` for any immediates `hi` and `lo` of the address
`T` of the table of the reciprocal, with the frame of 32 bytes below sp outside the table. -/
theorem udivrem_top2_4_320.reach (hi : BitVec 20) (lo : BitVec 12) (base T : BitVec 64)
    (x : Regs) (m : Mem)
    (hT : pcAt base 84 + ((hi ++ 0x000#12).signExtend 64 + lo.signExtend 64) = T)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64) (hr : x.get 1#5 &&& 3 = 0)
    (hstk : (x.get 2#5 - 32#64).toNat + 32 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 2#5 - 32#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hpre : udivrem_top2_4_320.pre x m) :
    Reach (udivrem_top2_4_320.bufs x ++ bufWords T 256) (udivrem_top2_4_320_progAt hi lo) base
      (pcAt base 0) x m (x.get 1#5) (udivrem_top2_4_320.post x m) := by
  have hpre0 := hpre
  simp only [udivrem_top2_4_320.pre, udivrem_top2_4_320.bufs, Buf] at hpre ⊢
  simp (disch := decide) only [Regs.eq_get x] at hpre ⊢
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr, hv1, hv2,
    hu3⟩ := hpre
  have hv3n := top4_ne_zero m (x.get 12#5) hv1
  rv_exec_cut 78
  all_goals
    set v3 := memWord m (x.get 12#5 + 24#64).toNat with hv3e
    set v2 := memWord m (x.get 12#5 + 16#64).toNat with hv2e
    set v1 := memWord m (x.get 12#5 + 8#64).toNat with hv1e
    set v0 := memWord m (x.get 12#5).toNat with hv0e
    set u4 := memWord m (x.get 11#5 + 32#64).toNat with hu4e
    set u3 := memWord m (x.get 11#5 + 24#64).toNat with hu3e
    set u2 := memWord m (x.get 11#5 + 16#64).toNat with hu2e
    set u1 := memWord m (x.get 11#5 + 8#64).toNat with hu1e
    set u0 := memWord m (x.get 11#5).toNat with hu0e
    rv_copies
    have hv3' : v3.toNat ≠ 0 := fun h => hv3n (BitVec.eq_of_toNat_eq (by simpa using h))
    -- The count of the leading zeros of v[3], S.
    have hs := clz_ite v3
    rw [if_neg hv3n, swarClz_expand, smear_expand] at hs
    rv_fold hs
    rv_fold hs
    subst hs
    have hL64 : v3.toNat.log2 < 64 := (Nat.log2_lt hv3').mpr v3.isLt
    have hSt : (BitVec.ofNat 64 (63 - v3.toNat.log2)).toNat = 63 - v3.toNat.log2 :=
      ofNat_S_toNat (by omega)
    have hS1 : v3.toNat * 2 ^ (63 - v3.toNat.log2) < 2 ^ 64 := by
      have := Nat.lt_log2_self (n := v3.toNat)
      calc v3.toNat * 2 ^ (63 - v3.toNat.log2)
          < 2 ^ (v3.toNat.log2 + 1) * 2 ^ (63 - v3.toNat.log2) :=
            Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos _)
        _ = 2 ^ 64 := by rw [← pow_add]; congr 1; omega
    have hS63 : 2 ^ 63 ≤ v3.toNat * 2 ^ (63 - v3.toNat.log2) := by
      have := Nat.log2_self_le hv3'
      calc 2 ^ 63 = 2 ^ v3.toNat.log2 * 2 ^ (63 - v3.toNat.log2) := by
            rw [← pow_add]; congr 1; omega
        _ ≤ _ := Nat.mul_le_mul_right _ this
    have hVw : words m (x.get 12#5) 4 =
        v0.toNat + 2 ^ 64 * (v1.toNat + 2 ^ 64 * (v2.toNat + 2 ^ 64 * v3.toNat)) :=
      words4_unfold m _
    have hUw : words m (x.get 11#5) 5 = u0.toNat + 2 ^ 64 * (u1.toNat + 2 ^ 64 * (u2.toNat +
        2 ^ 64 * (u3.toNat + 2 ^ 64 * u4.toNat))) := by
      simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
        Nat.add_zero]
      rfl
    have hP : 2 ^ (63 - v3.toNat.log2) * 2 ^ (64 - (63 - v3.toNat.log2)) = 2 ^ 64 := by
      rw [← pow_add]; congr 1; omega
  -- s ≠ 0: the normalized words by the funnel shifts.
  all_goals first
    | (rv_lacks ¬BitVec.ofNat 64 (63 - v3.toNat.log2) = 0#64; skip)
    | (rv_get hne : ¬BitVec.ofNat 64 (63 - v3.toNat.log2) = 0#64
       have hS0 := ofNat_S_ne (by omega) hne
       have hd0 := toNat_fshl_code v2 v1 (BitVec.ofNat 64 (63 - v3.toNat.log2)) (by rw [hSt]; omega)
       have hd1 := toNat_fshl_code v3 v2 (BitVec.ofNat 64 (63 - v3.toNat.log2)) (by rw [hSt]; omega)
       have ht2 := toNat_fshl_code u4 u3 (BitVec.ofNat 64 (63 - v3.toNat.log2)) (by rw [hSt]; omega)
       have ht1 := toNat_fshl_code u3 u2 (BitVec.ofNat 64 (63 - v3.toNat.log2)) (by rw [hSt]; omega)
       have ht0 := toNat_fshl_code u2 u1 (BitVec.ofNat 64 (63 - v3.toNat.log2)) (by rw [hSt]; omega)
       have ht3 : (u4 >>> ((BitVec.signExtend 64 (BitVec.setWidth 32 0#64 -
           BitVec.setWidth 32 (BitVec.ofNat 64 (63 - v3.toNat.log2)))).toNat % 64)).toNat =
           u4.toNat / 2 ^ (64 - (63 - v3.toNat.log2)) := by
         rw [top24_neg_amt _ (by omega), BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
           Nat.mod_eq_of_lt (by omega)]
       rv_fold hd0
       rv_fold hd0
       rv_fold hd1
       rv_fold hd1
       rv_fold ht2
       rv_fold ht2
       rv_fold ht1
       rv_fold ht1
       rv_fold ht0
       rv_fold ht0
       rv_fold ht3
       rv_fold ht3
       conv at hd0 => rhs; rw [hSt]
       conv at hd1 => rhs; rw [hSt]
       conv at ht2 => rhs; rw [hSt]
       conv at ht1 => rhs; rw [hSt]
       conv at ht0 => rhs; rw [hSt]
       refine top24_main hi lo base T x m hT hw hr hstk hhold hpre0 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
         ?_ ?_
       all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
       · intro i hi
         simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
         rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
           rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
       · rw [hSt]; omega
       · rw [hSt, hd0, hd1, hVw, top24_div128 _ _ _ v0.isLt (by omega),
           norm2_low _ _ _ _ v2.isLt v1.isLt (by omega) ?_, div_low_word _ _ _ (by omega)]
         have : v2.toNat * 2 ^ (63 - v3.toNat.log2) < 2 ^ 64 * 2 ^ (63 - v3.toNat.log2) :=
           Nat.mul_lt_mul_of_pos_right v2.isLt (Nat.two_pow_pos _)
         have hv3Q : v3.toNat < 2 ^ (64 - (63 - v3.toNat.log2)) := by
           by_contra hc
           have := Nat.mul_le_mul_right (2 ^ (63 - v3.toNat.log2)) (Nat.le_of_not_lt hc)
           rw [Nat.mul_comm (2 ^ (64 - _)), hP] at this
           omega
         have hv3P : (v3.toNat + 1) * 2 ^ (63 - v3.toNat.log2) ≤ 2 ^ 64 := by
           rw [← hP, Nat.mul_comm (2 ^ (63 - _))]
           exact Nat.mul_le_mul_right _ hv3Q
         nlinarith
       · rw [hd1]; exact norm2_hi (d0 := v2.toNat) (by omega) v2.isLt hS1 hS63
       · have hn5 := norm5_words u1.toNat u2.toNat u3.toNat u4.toNat 0 (63 - v3.toNat.log2)
           u1.isLt u2.isLt u3.isLt u4.isLt (Nat.two_pow_pos _) (by omega)
         simp only [Nat.zero_mul, Nat.zero_add, Nat.mul_zero, Nat.add_zero] at hn5
         rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) u4.isLt)] at hn5
         rw [hSt, ht0, ht1, ht2, ht3, hn5, hUw, top24_div128 _ _ _ u0.isLt (by omega),
           div_low_word _ _ _ (by omega)]
       · rw [ht3, hd1]
         have h63 := norm2_hi (d0 := v2.toNat) (by omega) v2.isLt hS1 hS63
         have : u4.toNat / 2 ^ (64 - (63 - v3.toNat.log2)) < 2 ^ (63 - v3.toNat.log2) := by
           rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), hP]
           exact u4.isLt
         have : 2 ^ (63 - v3.toNat.log2) ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) (by omega)
         omega)
  -- s = 0: the words not shifted.
  all_goals
    rv_get hz : BitVec.ofNat 64 (63 - v3.toNat.log2) = 0#64
    have hS0 := ofNat_S_eq (by omega) hz
    have hd63 : 2 ^ 63 ≤ v3.toNat := by rw [hS0] at hS63; simpa using hS63
    refine top24_main hi lo base T x m hT hw hr hstk hhold hpre0 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · intro i hi
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    · rw [hSt]; omega
    · rw [hSt, hS0, hVw, top24_div128 _ _ _ v0.isLt (by omega), Nat.sub_zero,
        Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt v1.isLt, Nat.zero_add]
    · exact hd63
    · rw [hSt, hS0, hUw, top24_div128 _ _ _ u0.isLt (by omega), Nat.sub_zero,
        Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt u1.isLt, Nat.zero_add]
      simp
    · simp only [BitVec.toNat_ofNat, Nat.zero_mod]
      omega

theorem udivrem_top2_4_320.proof : udivrem_top2_4_320.spec := by
  apply runsI_of_reach udivrem_top2_4_320_image_decodes
  intro base ret _ hr _ _ hw x m hx1 hbufs hhold hpre
  rw [show udivrem_top2_4_320_image_dataOff = 1248 from rfl] at hw hhold hbufs ⊢
  rw [show udivrem_top2_4_320_image_data.length = 256 from rfl] at hw hbufs ⊢
  have hx : x.get 1#5 = ret := by rw [← Regs.eq_get x (by decide)]; exact hx1
  have hpre' := hpre
  simp only [udivrem_top2_4_320.pre, Buf] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  have hst := frame32_outside (x 2#5) base 1248 (8 * 256)
    (hbufs _ (List.mem_append_right _ (mem_bufWords_zero (by norm_num))))
    (hbufs _ (List.mem_append_right _ (mem_bufWords (by norm_num))))
    (by rw [Regs.eq_get x (by decide)]; exact hpre'.2.2.2.2.2.1.2) (by norm_num)
  rw [Regs.eq_get x (by decide)] at hst
  rw [show udivrem_top2_4_320_entry = udivrem_top2_4_320_image_udivrem_top2_4_320_offset from rfl,
    dataWords, ← hx]
  refine Reach.lift udivrem_top2_4_320_image_udivrem_top2_4_320_in (by decide) ?_
  have hT : (base + BitVec.ofNat 64 1248).toNat = base.toNat + 1248 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have h := udivrem_top2_4_320.reach 0x0#20 0x390#12
    (pcAt base udivrem_top2_4_320_image_udivrem_top2_4_320_offset) _ x m
    (by simp only [udivrem_top2_4_320_image_udivrem_top2_4_320_offset, pcAt, BitVec.reduceAppend,
      BitVec.reduceSignExtend]; bv_omega)
    (by rw [hT]; omega) (hx ▸ hr) (by rw [hT]; omega) hhold hpre
  rwa [pcAt_zero] at h

set_option exponentiation.threshold 320 in
/-- The registers of the nonvacuous instance: the result, u = 2^256 and v = 2^192 above the data, and
the frame below sp. -/
theorem udivrem_top2_4_320.nonvacuous :
    NonVacuousI udivrem_top2_4_320_image_code udivrem_top2_4_320_image_data
      udivrem_top2_4_320_image_dataOff udivrem_top2_4_320.bufs udivrem_top2_4_320.pre :=
  nonVacuousI_of_args (fun i => if i = 10#5 then 0x80000D00#64 else if i = 11#5 then 0x80000D48#64
      else if i = 12#5 then 0x80000D70#64 else if i = 2#5 then 0x80000DB0#64 else 0)
    0x80000D48 [0, 0, 0, 0, 1, 0, 0, 0, 1]
    (by decide) (by decide) (by decide) (by decide)
    (by rw [show udivrem_top2_4_320_image_dataOff = 1248 from rfl,
          show udivrem_top2_4_320_image_data.length = 256 from rfl]
        simp only [udivrem_top2_4_320.bufs, ↓reduceIte, BitVec.reduceEq, BitVec.reduceSub,
          bufWords, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq]
        repeat' apply And.intro
        all_goals decide)
    (by decide)
    (fun m => by
      simp only [udivrem_top2_4_320.pre, Buf, Disjoint, words, ↓reduceIte, BitVec.reduceEq,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, BitVec.toNat_ofNat,
        Nat.reducePow, Nat.reduceMod, Nat.mul_zero, Nat.add_zero]
      simp (disch := decide) only [memWord_storeWords_getD]
      decide)

end IntxRV.Api
