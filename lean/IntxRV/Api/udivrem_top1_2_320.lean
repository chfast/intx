import IntxRV.DivTop1
import IntxRV.Gen.Api.udivrem_top1_2_320
/-!
# `internal::udivrem_top1()` of `uint320` by `uint256`, the top word 2

The specification, from `include/intx/intx.hpp`:

```cpp
/// Divides u by v when the quotient fits in a single word: v has TOP + 1 significant words
/// and u has at most one more significant word, which is less than v[TOP].
///
/// The quotient is estimated from the top word of the normalized divisor with 2/1 division
/// and corrected with the remainder computed on the original (not normalized) operands.
/// The word v[TOP] must not be zero.
/// @pre 2^(64 * TOP) ≤ v
/// @pre v < 2^(64 * (TOP + 1))
/// @pre u / 2^(64 * (TOP + 1)) < v / 2^(64 * TOP)
/// @post result.quot = u / v
/// @post result.rem = u % v
template <size_t TOP, unsigned M, unsigned N>
constexpr div_result<uint<M>, uint<N>> udivrem_top1(const uint<M>& u, const uint<N>& v) noexcept
```

`udivrem_top1_2_320.spec` states it for the RV64 machine code of `udivrem_top1_2_320` in
`IntxRV/Api.cpp`, the instance that `udivrem<320, 256>()` calls for a divisor of 3 words. The
numerator is wider than the divisor: u[4] is 0 and u[3] is less than v[2] (`top1_2_320_ue`), there
is no return for u < v, and the remainder is computed from u without a copy. The function
normalizes the top words of v with the count of the leading zeros of v[2], computes the reciprocal
of the top word with the table of the image (`recip2BV_spec`), estimates the quotient from u[3],
u[2] and u[1] with the inlined `udivrem_2by1()` (`div2by1BVc_spec`), not less than the quotient
(`top1_est`), subtracts q * v from the 3 words of u below u[3] (`submul3_words`) and runs the
correction loop while the borrow is not 0 (`top1_2_320_tail`), as the instance of `uint256`
(`IntxRV/Api/udivrem_top1_2.lean`, `IntxRV/DivTop1.lean`). `udivrem_top1_2_320.reach` is the run
for any immediates of the address of the table.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- The result of a division of 5 words by 4 words stored as the quotient `q` of one word and the
remainder `a` of 3 words. -/
theorem words_ret9 (m : Mem) (r q a0 a1 a2 z : BitVec 64) (hz : z = 0#64)
    (hr : r.toNat + 72 ≤ 2 ^ 64)
    (m' : Mem) (hm : m' = memStore (memStore (memStore (memStore (memStore (memStore (memStore
      (memStore (memStore m r.toNat q) (r + 8#64).toNat z) (r + 16#64).toNat z)
      (r + 24#64).toNat z) (r + 32#64).toNat z) (r + 40#64).toNat a0) (r + 48#64).toNat a1)
      (r + 56#64).toNat a2) (r + 64#64).toNat z) :
    words m' r 5 = q.toNat ∧
      words m' (r + 40#64) 4 = a0.toNat + 2 ^ 64 * (a1.toNat + 2 ^ 64 * a2.toNat) ∧
      UnchangedExcept m m' r 72 := by
  subst hm hz
  refine ⟨?_, ?_, ?_⟩
  · simp (disch := first | bv_omega | fail) only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd, memWord_memStore_self, memWord_memStore_of_ne, BitVec.toNat_ofNat,
      Nat.zero_mod, Nat.mul_zero, Nat.add_zero]
  · simp (disch := first | bv_omega | fail) only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd, memWord_memStore_self, memWord_memStore_of_ne, BitVec.toNat_ofNat,
      Nat.zero_mod, Nat.mul_zero, Nat.add_zero]
  · simp (disch := first | bv_omega | fail) only [unchangedExcept_memStore,
      unchangedExcept_refl]

/-- The end of `udivrem_top1<2>()` of `uint320` by `uint256` from 154: the stores of the quotient
in a1 and the remainder in `a4:a3:a2`, and the return. -/
theorem top1_2_320_exit {hi : BitVec 20} {lo : BitVec 12} {D : List (BitVec 64)}
    (base : BitVec 64) (x : Regs) (m : Mem)
    (hpre : udivrem_top1_2_320.pre x m) (hr : x.get 1#5 &&& 3 = 0) (x' : Regs)
    (h10 : x'.get 10#5 = x.get 10#5) (h1 : x'.get 1#5 = x.get 1#5)
    (hcs : ∀ i ∈ calleeSaved, x' i = x i)
    (hqr : (x'.get 11#5).toNat = words m (x.get 11#5) 5 / words m (x.get 12#5) 4 ∧
      (x'.get 12#5).toNat + 2 ^ 64 * ((x'.get 13#5).toNat + 2 ^ 64 * (x'.get 14#5).toNat) =
        words m (x.get 11#5) 5 % words m (x.get 12#5) 4) :
    Reach (bufWords (x.get 11#5) 5 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 9 ++ D)
      (udivrem_top1_2_320_progAt hi lo) base (pcAt base 154) x' m (x.get 1#5)
      (udivrem_top1_2_320.post x m) := by
  have hpre' := hpre
  simp only [udivrem_top1_2_320.pre, Buf] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hra, hrn⟩, -⟩ := hpre'
  rw [← h10]
  have hrn' : (x'.get 10#5).toNat + 72 ≤ 2 ^ 64 := h10 ▸ hrn
  rv_exec
  rv_val
  rw [h1, update_aligned hr]
  refine Reach.refl ?_
  have hz : x'.get 0#5 = 0#64 := by rw [show (0#5 : BitVec 5) = 0 from rfl, Regs.get_zero]; rfl
  have hw := words_ret9 m (x'.get 10#5) (x'.get 11#5) (x'.get 12#5) (x'.get 13#5) (x'.get 14#5)
    (x'.get 0#5) hz hrn' _ rfl
  simp only [udivrem_top1_2_320.post]
  simp (disch := decide) only [Regs.eq_get x]
  rw [← h10]
  refine ⟨?_, ?_, hw.2.2, ?_⟩
  · rw [hw.1, hqr.1]
  · rw [hw.2.1, hqr.2]
  · intro i hi
    rw [Regs.set_apply, if_pos (by decide)]
    exact hcs i hi

/-- The registers at the head of the correction loop of `udivrem_top1<2>()` of `uint320` by
`uint256`, at 165: `t2:a3:a4 + q * v = u + 2^192 * borrow`, with the quotient `q` in a1, the
borrow in t0, not 0, and the words of v in `a7:t1:a6`; `n` the excess of `q`. -/
def top1_2_320Loop (x : Regs) (m : Mem) (n : Nat) (x' : Regs) (m' : Mem) : Prop :=
  m' = m ∧ x'.get 10#5 = x.get 10#5 ∧ x'.get 1#5 = x.get 1#5 ∧ (∀ i ∈ calleeSaved, x' i = x i) ∧
    (x'.get 16#5).toNat + 2 ^ 64 * ((x'.get 6#5).toNat + 2 ^ 64 * (x'.get 17#5).toNat) =
      words m (x.get 12#5) 4 ∧
    (x'.get 15#5).toNat + 2 ^ 64 * ((x'.get 13#5).toNat + 2 ^ 64 * (x'.get 14#5).toNat) +
      (x'.get 11#5).toNat * words m (x.get 12#5) 4 =
      words m (x.get 11#5) 5 + 2 ^ 192 * (x'.get 5#5).toNat ∧
    x'.get 5#5 ≠ 0#64 ∧ n = (x'.get 11#5).toNat - words m (x.get 11#5) 5 / words m (x.get 12#5) 4

/-- The correction loop of `udivrem_top1<2>()` of `uint320` by `uint256` from 165. -/
theorem top1_2_320_loop {hi : BitVec 20} {lo : BitVec 12} {D : List (BitVec 64)}
    (base : BitVec 64) (x : Regs) (m : Mem)
    (hpre : udivrem_top1_2_320.pre x m) (hr : x.get 1#5 &&& 3 = 0) :
    ∀ n x' m', top1_2_320Loop x m n x' m' →
    Reach (bufWords (x.get 11#5) 5 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 9 ++ D)
      (udivrem_top1_2_320_progAt hi lo) base (pcAt base 165) x' m' (x.get 1#5)
      (udivrem_top1_2_320.post x m) := by
  apply Reach.loop (top1_2_320Loop x m)
  intro n x' m' h ih
  obtain ⟨hm, h10, h1, hcs, hv, hsm, hb, hn⟩ := h
  rw [hm]
  have hlt := top1_q_gt (words3_lt _ _ _) hsm
    (fun h0 => hb (BitVec.eq_of_toNat_eq (by simpa using h0)))
  rv_step
  rv_exec_cut 154 165
  -- The borrow is 0: the end.
  all_goals first
    | (rv_not_at 154; skip)
    | (refine top1_2_320_exit base x m hpre hr _ ?_ ?_ ?_ ?_
       · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h10
       · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h1
       · refine calleeSaved_of hcs _ ?_
         intro i hi
         simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
         rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
           rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
       · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
         apply top1_2_body_exit
         all_goals assumption)
  -- The borrow is not 0: the next correction.
  all_goals
    refine ih _ (top1_body_k hlt hn) _ _ ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · exact h10
    · exact h1
    · refine calleeSaved_of hcs _ ?_
      intro i hi
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    · exact hv
    · apply top1_2_body_sm
      all_goals assumption
    · assumption

/-- The end of `udivrem_top1<2>()` of `uint320` by `uint256` from the test of the borrow at 152:
`t2:a3:a4 + q * v = u + 2^192 * borrow` with the quotient estimate `q` in a1 not less than
`u / v`, and the words v[0] in a6 and v[2] in a7. -/
theorem top1_2_320_tail {hi : BitVec 20} {lo : BitVec 12} {D : List (BitVec 64)}
    (base : BitVec 64) (x : Regs) (m : Mem)
    (hpre : udivrem_top1_2_320.pre x m) (hr : x.get 1#5 &&& 3 = 0) (x' : Regs)
    (h10 : x'.get 10#5 = x.get 10#5) (h1 : x'.get 1#5 = x.get 1#5)
    (h12 : x'.get 12#5 = x.get 12#5) (hcs : ∀ i ∈ calleeSaved, x' i = x i)
    (hv : (x'.get 16#5).toNat + 2 ^ 64 * ((memWord m (x.get 12#5 + 8#64).toNat).toNat +
      2 ^ 64 * (x'.get 17#5).toNat) = words m (x.get 12#5) 4)
    (hsm : (x'.get 15#5).toNat + 2 ^ 64 * ((x'.get 13#5).toNat + 2 ^ 64 * (x'.get 14#5).toNat) +
      (x'.get 11#5).toNat * words m (x.get 12#5) 4 =
      words m (x.get 11#5) 5 + 2 ^ 192 * (x'.get 5#5).toNat)
    (hq : words m (x.get 11#5) 5 / words m (x.get 12#5) 4 ≤ (x'.get 11#5).toNat) :
    Reach (bufWords (x.get 11#5) 5 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 9 ++ D)
      (udivrem_top1_2_320_progAt hi lo) base (pcAt base 152) x' m (x.get 1#5)
      (udivrem_top1_2_320.post x m) := by
  have hpre' := hpre
  simp only [udivrem_top1_2_320.pre, Buf] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨-, -, -, -, -, hv1, -, -⟩ := hpre'
  have hV : 0 < words m (x.get 12#5) 4 := by
    have : 0 < 2 ^ (64 * 2) := by positivity
    omega
  have hz0 : x'.get 0#5 = 0#64 := by rw [show (0#5 : BitVec 5) = 0 from rfl, Regs.get_zero]; rfl
  rw [← h12]
  rv_step
  rv_exec_cut 154 165
  all_goals simp only [hz0, bne_eq_false_iff_eq] at *
  -- The borrow is 0: no correction.
  all_goals first
    | (rv_not_at 154; skip)
    | (rw [h12]
       refine top1_2_320_exit base x m hpre hr _ ?_ ?_ ?_ ?_
       · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h10
       · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h1
       · refine calleeSaved_of hcs _ ?_
         intro i hi
         simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
         rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
           rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
       · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
         exact top1_tail_exit hV hsm (by assumption) hq)
  -- The borrow is not 0: the load of v[1] and the correction loop.
  all_goals
    rw [h12]
    simp only [Defn] at *
    subst_vars
    rw [h12] at *
    refine top1_2_320_loop base x m hpre hr _ _ _ ⟨rfl, ?_, ?_, ?_, ?_, hsm, by assumption, rfl⟩
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · exact h10
    · exact h1
    · refine calleeSaved_of hcs _ ?_
      intro i hi
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    · exact hv

/-- The words of u above the top word of v: u[4] is 0 and u[3] is less than v[2]. -/
theorem top1_2_320_ue (m : Mem) (u v : BitVec 64)
    (h : words m u 5 / 2 ^ (64 * (2 + 1)) < words m v 4 / 2 ^ (64 * 2))
    (h3 : memWord m (v + 24#64).toNat = 0#64) :
    memWord m (u + 32#64).toNat = 0#64 ∧
      (memWord m (u + 24#64).toNat).toNat < (memWord m (v + 16#64).toNat).toNat := by
  simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
    Nat.add_zero] at h
  rw [h3, BitVec.toNat_ofNat, Nat.zero_mod] at h
  have := (memWord m u.toNat).isLt
  have := (memWord m (u + 8#64).toNat).isLt
  have := (memWord m (u + 16#64).toNat).isLt
  have := (memWord m (u + 24#64).toNat).isLt
  have := (memWord m v.toNat).isLt
  have := (memWord m (v + 8#64).toNat).isLt
  have := (memWord m (v + 16#64).toNat).isLt
  refine ⟨BitVec.eq_of_toNat_eq ?_, ?_⟩
  · simp only [BitVec.toNat_ofNat, Nat.zero_mod]
    omega
  · omega

/-- The words of a 5-word number with the top word 0. -/
theorem words5_eq_4 (m : Mem) (a : BitVec 64) (h : memWord m (a + 32#64).toNat = 0#64) :
    words m a 5 = words m a 4 := by
  simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
    Nat.add_zero, h]
  simp

/-- The run of `udivrem_top1<2>()` of `uint320` by `uint256` for any immediates `hi` and `lo` of
the address `T` of the table of the reciprocal. -/
theorem udivrem_top1_2_320.reach (hi : BitVec 20) (lo : BitVec 12) (base T : BitVec 64)
    (x : Regs) (m : Mem)
    (hT : pcAt base 65 + ((hi ++ 0x000#12).signExtend 64 + lo.signExtend 64) = T)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64) (hr : x.get 1#5 &&& 3 = 0)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hpre : udivrem_top1_2_320.pre x m) :
    Reach (udivrem_top1_2_320.bufs x ++ bufWords T 256) (udivrem_top1_2_320_progAt hi lo) base
      (pcAt base 0) x m (x.get 1#5) (udivrem_top1_2_320.post x m) := by
  have hpre0 := hpre
  simp only [udivrem_top1_2_320.pre, udivrem_top1_2_320.bufs, Buf] at hpre ⊢
  simp (disch := decide) only [Regs.eq_get x] at hpre ⊢
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, hv1, hv2, hu3⟩ := hpre
  simp only [Disjoint] at hdru hdrv
  have hv3 := top4_zero m (x.get 12#5) hv2
  have hv2' := top3_ne_zero m (x.get 12#5) hv1 hv3
  obtain ⟨hu4, hue⟩ := top1_2_320_ue m (x.get 11#5) (x.get 12#5) hu3 hv3
  have hU54 := words5_eq_4 m (x.get 11#5) hu4
  rv_exec_cut 152
  -- The words v[2], v[1], u[3], u[2] and u[1] by names.
  all_goals
    set v2 := memWord m (x.get 12#5 + 16#64).toNat with hv2e
    set v1 := memWord m (x.get 12#5 + 8#64).toNat with hv1e
    set ue := memWord m (x.get 11#5 + 24#64).toNat with huee
    set u2 := memWord m (x.get 11#5 + 16#64).toNat with hu2e
    set u1 := memWord m (x.get 11#5 + 8#64).toNat with hu1e
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
  -- The normalized top word vt of v, the funnel shift of v[2] and v[1] for s ≠ 0.
  all_goals first
    | (rv_lacks ¬BitVec.ofNat 64 (63 - v2.toNat.log2) = 0#64; skip)
    | (have h1 := toNat_fshl_code v2 v1 (BitVec.ofNat 64 (63 - v2.toNat.log2)) (by rw [hSt]; omega)
       rv_fold h1
       rv_fold h1
       rw [hSt] at h1
       have hdn63 := norm2_hi (d0 := v1.toNat) (by omega) v1.isLt hS1 hS63
       rw [← h1] at hdn63)
  all_goals first
    | (rv_lacks BitVec.ofNat 64 (63 - v2.toNat.log2) = 0#64; skip)
    | (rv_get hz : BitVec.ofNat 64 (63 - v2.toNat.log2) = 0#64
       have hS0 := ofNat_S_eq (by omega) hz
       have hdn63 : 2 ^ 63 ≤ v2.toNat := by rw [hS0] at hS63; simpa using hS63)
  -- The table entry of vt: the low half.
  all_goals
    simp only [hT] at *
    refine Reach.step (by decide) (by rv_fetch) ?_
    simp only [StepGoal, Nat.reduceAdd]
    rv_val
    have ha := table_addr_by1 _ T hdn63
    rv_fold ha
    have hix := index_lt_256 hdn63
    rw [ha]
    refine ⟨Or.inl (List.mem_append_right _ (mem_bufWords hix)), fun wL hwL => ?_⟩
    try simp (disch := bv_omega) only [memHalf_memStore_of_ne] at hwL
    rw [memHalf_lo, holdsData_get hhold
        (by rw [show reciprocal_2by1_image_data.length = 256 from rfl]; exact hix),
      ← List.getD_eq_getElem _ 0, image_data_get _ hix] at hwL
    rv_exec_cut 152
    -- The high half.
    refine Reach.step (by decide) (by rv_fetch) ?_
    simp only [StepGoal, Nat.reduceAdd]
    rv_val
    have hah := table_addr_by1_hi _ T hdn63
    rv_fold hah
    rw [hah]
    refine ⟨Or.inr (by
      rw [show ∀ a : BitVec 64, a + 4 - 4#64 = a from fun a => by bv_omega]
      exact List.mem_append_right _ (mem_bufWords hix)), fun wH hwH => ?_⟩
    try simp (disch := bv_omega) only [memHalf_memStore_of_ne] at hwH
    rw [table_entry_add4 T hdn63 hw, memHalf_hi, holdsData_get hhold
        (by rw [show reciprocal_2by1_image_data.length = 256 from rfl]; exact hix),
      ← List.getD_eq_getElem _ 0, image_data_get _ hix] at hwH
    rv_exec_cut 152
  -- The reciprocal of vt.
  all_goals
    rv_cse
    obtain ⟨hL, hH⟩ := table_LH hdn63 hwL hwH
    have hv := recip2BV_spec _ wL wH hdn63 hL hH
    simp only [recip2BV] at hv
    rv_fold hv
    rv_fold hv
  all_goals simp only [zopz0zI_u_eq, decide_eq_true_eq, decide_eq_false_iff_not] at *
  -- The quotient estimate: s ≠ 0.
  all_goals first
    | (rv_lacks ¬BitVec.ofNat 64 (63 - v2.toNat.log2) = 0#64; skip)
    | (rv_get hne : ¬BitVec.ofNat 64 (63 - v2.toNat.log2) = 0#64
       have hS0 := ofNat_S_ne (by omega) hne
       have hhi := toNat_fshl_code ue u2 (BitVec.ofNat 64 (63 - v2.toNat.log2)) (by rw [hSt]; omega)
       have hlo := toNat_fshl_code u2 u1 (BitVec.ofNat 64 (63 - v2.toNat.log2)) (by rw [hSt]; omega)
       conv at hhi => rhs; rw [hSt]
       conv at hlo => rhs; rw [hSt]
       have hue1 : ue.toNat * 2 ^ (63 - v2.toNat.log2) < 2 ^ 64 :=
         Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.le_of_lt hue)) hS1
       rw [Nat.mod_eq_of_lt (fshl_lt (by omega) u2.isLt hue1)] at hhi
       have hs := div2by1BVc_spec ((ue <<< ((BitVec.ofNat 64 (63 - v2.toNat.log2)).toNat % 64)) |||
           ((u2 >>> 1) >>> ((BitVec.ofNat 64 (63 - v2.toNat.log2) ^^^
             18446744073709551615#64).toNat % 64)))
         ((u2 <<< ((BitVec.ofNat 64 (63 - v2.toNat.log2)).toNat % 64)) |||
           ((u1 >>> 1) >>> ((BitVec.ofNat 64 (63 - v2.toNat.log2) ^^^
             18446744073709551615#64).toNat % 64))) _ _ hdn63
         (by rw [hhi, h1]; exact top1_2_hi_lt (by omega) u2.isLt v1.isLt hue hS1) hv
       simp only [div2by1BVc] at hs
       rv_fold hs
       rv_fold hs
       try simp (disch := assumption) only [if_pos, if_neg] at hs
       rv_fold hs
       try (simp only [BitVec.add_assoc] at hs; rv_fold hs)
       rv_fold hhi
       rv_fold hhi
       rv_fold hlo
       rv_fold hlo
       rw [hhi, hlo, top1_2_ut _ _ _ _ (by omega) u1.isLt, h1,
         Nat.mod_eq_of_lt (fshl_lt (by omega) v1.isLt hS1)] at hs)
  -- s = 0.
  all_goals first
    | (rv_lacks BitVec.ofNat 64 (63 - v2.toNat.log2) = 0#64; skip)
    | (have hs := div2by1BVc_spec ue u2 _ _ hdn63 hue hv
       simp only [div2by1BVc] at hs
       rv_fold hs
       rv_fold hs
       try simp (disch := assumption) only [if_pos, if_neg] at hs
       rv_fold hs
       try (simp only [BitVec.add_assoc] at hs; rv_fold hs)
       have hN : (2 ^ 64 * ue.toNat + u2.toNat) / v2.toNat =
           ((u2.toNat + 2 ^ 64 * ue.toNat) * 2 ^ (63 - v2.toNat.log2) +
             u1.toNat / 2 ^ (64 - (63 - v2.toNat.log2))) /
           (v2.toNat * 2 ^ (63 - v2.toNat.log2) + v1.toNat / 2 ^ (64 - (63 - v2.toNat.log2))) := by
         rw [hS0, Nat.div_eq_of_lt u1.isLt, Nat.div_eq_of_lt v1.isLt]
         simp only [Nat.pow_zero, Nat.mul_one, Nat.add_zero]
         rw [Nat.add_comm (2 ^ 64 * _)]
       rw [hN] at hs)
  -- The estimate is not less than the quotient.
  all_goals
    have hest := top1_est (U := words m (x.get 11#5) 4) (V := words m (x.get 12#5) 4) (by omega)
      (words4_lt_top3 m (x.get 11#5)) (words4_ge_top3 m (x.get 12#5))
      (Nat.lt_of_lt_of_le (by norm_num) (Nat.le_add_right_of_le hS63)) hs
  -- The submul() and the correction.
  all_goals
    have hv3n : (memWord m (x.get 12#5 + 24#64).toNat).toNat = 0 := by rw [hv3]; rfl
    have hest' := hest
    have hV0 : 0 < words m (x.get 12#5) 4 := by
      have : 0 < 2 ^ (64 * 2) := by positivity
      omega
    simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
      Nat.add_zero, hv3n] at hest' hV0
    rv_fold hest'
    rv_fold hV0
    try rw [← hu1e] at hest' hV0
    try rw [← hu2e] at hest' hV0
    try rw [← huee] at hest' hV0
    try rw [← hv1e] at hest' hV0
    refine top1_2_320_tail base x m hpre0 hr _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · intro i hi
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] <;>
        exact (Regs.eq_get x (by decide)).symm
    · simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
        Nat.add_zero, hv3n]
      rv_loads
      rfl
    · rw [hU54]
      simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
        Nat.add_zero, hv3n]
      rv_loads
      try rw [← hu1e]
      try rw [← hu2e]
      try rw [← huee]
      try rw [← hv1e]
      apply submul3_words
      all_goals assumption
    · rw [hU54]; exact hest

theorem udivrem_top1_2_320.proof_of_decodes (hdec : udivrem_top1_2_320.decodes) :
    udivrem_top1_2_320.spec := by
  apply runsI_of_reach hdec
  intro base ret _ hr _ _ hw x m hx1 _ hhold hpre
  rw [show udivrem_top1_2_320_image_dataOff = 728 from rfl] at hw hhold ⊢
  rw [show udivrem_top1_2_320_image_data.length = 256 from rfl] at hw ⊢
  have hx : x.get 1#5 = ret := by rw [← Regs.eq_get x (by decide)]; exact hx1
  rw [show udivrem_top1_2_320_entry = udivrem_top1_2_320_image_udivrem_top1_2_320_offset from rfl,
    dataWords, ← hx]
  refine Reach.lift udivrem_top1_2_320_image_udivrem_top1_2_320_in (by decide) ?_
  have h := udivrem_top1_2_320.reach 0x0#20 0x1d4#12
    (pcAt base udivrem_top1_2_320_image_udivrem_top1_2_320_offset) _ x m
    (by simp only [udivrem_top1_2_320_image_udivrem_top1_2_320_offset, pcAt, BitVec.reduceAppend,
      BitVec.reduceSignExtend]; bv_omega)
    (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (hx ▸ hr) hhold hpre
  rwa [pcAt_zero] at h

/-- The registers of the nonvacuous instance: the result, u = 0 and v = 2^128 above the data. -/
theorem udivrem_top1_2_320.nonvacuous :
    NonVacuousI udivrem_top1_2_320_image_code udivrem_top1_2_320_image_data
      udivrem_top1_2_320_image_dataOff udivrem_top1_2_320.bufs udivrem_top1_2_320.pre :=
  nonVacuousI_of_args (fun i => if i = 10#5 then 0x80000C00#64 else if i = 11#5 then 0x80000C48#64
      else if i = 12#5 then 0x80000C70#64 else 0)
    0x80000C48 [0, 0, 0, 0, 0, 0, 0, 1, 0]
    (by decide) (by decide) (by decide) (by decide)
    (by rw [show udivrem_top1_2_320_image_dataOff = 728 from rfl,
          show udivrem_top1_2_320_image_data.length = 256 from rfl]
        simp only [udivrem_top1_2_320.bufs, ↓reduceIte, BitVec.reduceEq, bufWords,
          List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq]
        repeat' apply And.intro
        all_goals decide)
    (by decide)
    (fun m => by
      simp only [udivrem_top1_2_320.pre, Buf, Disjoint, words, ↓reduceIte, BitVec.reduceEq,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.toNat_ofNat,
        Nat.reducePow, Nat.reduceMod, Nat.mul_zero, Nat.add_zero]
      simp (disch := decide) only [memWord_storeWords_getD]
      decide)

end IntxRV.Api
