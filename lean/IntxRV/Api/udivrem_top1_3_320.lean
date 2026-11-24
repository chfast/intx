import IntxRV.DivTop1
/-!
# `internal::udivrem_top1()` of `uint320` by `uint256`, the top word 3

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

`udivrem_top1_3_320.spec` states it for the RV64 machine code of `udivrem_top1_3_320` in
`IntxRV/Api.cpp`, the instance that `udivrem<320, 256>()` calls for a divisor of 4 words. The
numerator has the word u[4] above the divisor, less than v[3] (`top1_3_320_ue`), and there is no
return for u < v. The function normalizes the top words of v with the count of the leading zeros
of v[3], computes the reciprocal of the top word with the table of the image (`recip2BV_spec`),
estimates the quotient from u[4], u[3] and u[2] with the inlined `udivrem_2by1()`
(`div2by1BVc_spec`), not less than the quotient (`top1_est`), subtracts q * v from the 4 words of u
below u[4] and u[4] from the borrow (`submul4ue_words`), and runs the correction loop while the
borrow is not 0 (`top1_3_320_tail`), as the instance of `uint256` (`IntxRV/Api/udivrem_top1_3.lean`,
`IntxRV/DivTop1.lean`). It saves s0 and s1, which `submul()` uses, in a frame of 16 bytes.
`udivrem_top1_3_320.reach` is the run for any immediates of the address of the table.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- The word u[4] of u above the top word of v is less than it. -/
theorem top1_3_320_ue (m : Mem) (u v : BitVec 64)
    (h : words m u 5 / 2 ^ (64 * (3 + 1)) < words m v 4 / 2 ^ (64 * 3)) :
    (memWord m (u + 32#64).toNat).toNat < (memWord m (v + 24#64).toNat).toNat := by
  simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
    Nat.add_zero] at h
  have := (memWord m u.toNat).isLt
  have := (memWord m (u + 8#64).toNat).isLt
  have := (memWord m (u + 16#64).toNat).isLt
  have := (memWord m (u + 24#64).toNat).isLt
  have := (memWord m (u + 32#64).toNat).isLt
  have := (memWord m v.toNat).isLt
  have := (memWord m (v + 8#64).toNat).isLt
  have := (memWord m (v + 16#64).toNat).isLt
  have := (memWord m (v + 24#64).toNat).isLt
  omega

/-- A 5-word number is less than its top three words and one, times 2^128. -/
theorem words5_lt_top3 (m : Mem) (a : BitVec 64) :
    words m a 5 < ((memWord m (a + 16#64).toNat).toNat + 2 ^ 64 *
      ((memWord m (a + 24#64).toNat).toNat + 2 ^ 64 * (memWord m (a + 32#64).toNat).toNat) + 1) *
      2 ^ 128 := by
  simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
    Nat.add_zero]
  have := (memWord m a.toNat).isLt
  have := (memWord m (a + 8#64).toNat).isLt
  omega

set_option maxHeartbeats 4000000 in
/-- `submul()` of 4 words in the RV64 code of `udivrem_top1<3>()` of `uint320` by `uint256`, less
the word `ue` of u above them: the words `r` of `u - q * v` and the borrow `w`, from the
definitions of the values (as `submul4_words`), for an estimate `q` not less than the quotient. -/
theorem submul4ue_words {u0 u1 u2 u3 ue v0 v1 v2 v3 q p0 h0 p1 h1 p2 s1 a2 c1 s2 h2 r0 b0 d1 e1 r1
    f1 b1 p3 a3 c2 s3 h3 d2 e2 r2 c3 d3 f2 g b2 e3 r3 f3 b3 t w : BitVec 64}
    (hw : Defn w (t + b3)) (ht : Defn t (c3 + g)) (hg : Defn g (h3 - ue))
    (hb3 : Defn b3 (e3 ||| f3))
    (hf3 : Defn f3 (if d3 < r3 then 1#64 else 0#64)) (he3 : Defn e3 (if u3 < d3 then 1#64 else 0#64))
    (hr3 : Defn r3 (d3 - b2)) (hd3 : Defn d3 (u3 - s3)) (hb2 : Defn b2 (e2 ||| f2))
    (hf2 : Defn f2 (if d2 < r2 then 1#64 else 0#64)) (he2 : Defn e2 (if u2 < d2 then 1#64 else 0#64))
    (hr2 : Defn r2 (d2 - b1)) (hd2 : Defn d2 (u2 - s2)) (hb1 : Defn b1 (e1 ||| f1))
    (hf1 : Defn f1 (if d1 < r1 then 1#64 else 0#64)) (he1 : Defn e1 (if u1 < d1 then 1#64 else 0#64))
    (hr1 : Defn r1 (d1 - b0)) (hd1 : Defn d1 (u1 - s1))
    (hb0 : Defn b0 (if u0 < r0 then 1#64 else 0#64)) (hr0 : Defn r0 (u0 - p0))
    (hc3 : Defn c3 (if s3 < p3 then 1#64 else 0#64)) (hh3 : Defn h3 (mulhu v3 q))
    (hs3 : Defn s3 (a3 + c2)) (ha3 : Defn a3 (p3 + h2)) (hp3 : Defn p3 (v3 * q))
    (hc2 : Defn c2 (if s2 < p2 then 1#64 else 0#64)) (hh2 : Defn h2 (mulhu v2 q))
    (hs2 : Defn s2 (a2 + c1)) (ha2 : Defn a2 (p2 + h1)) (hp2 : Defn p2 (v2 * q))
    (hc1 : Defn c1 (if s1 < p1 then 1#64 else 0#64)) (hs1 : Defn s1 (p1 + h0))
    (hh1 : Defn h1 (mulhu v1 q)) (hp1 : Defn p1 (v1 * q)) (hh0 : Defn h0 (mulhu v0 q))
    (hp0 : Defn p0 (v0 * q))
    (hq : (u0.toNat + 2 ^ 64 * (u1.toNat + 2 ^ 64 * (u2.toNat + 2 ^ 64 * (u3.toNat +
      2 ^ 64 * ue.toNat)))) / (v0.toNat + 2 ^ 64 * (v1.toNat + 2 ^ 64 * (v2.toNat +
        2 ^ 64 * v3.toNat))) ≤ q.toNat)
    (hV0 : 0 < v0.toNat + 2 ^ 64 * (v1.toNat + 2 ^ 64 * (v2.toNat + 2 ^ 64 * v3.toNat))) :
    r0.toNat + 2 ^ 64 * (r1.toNat + 2 ^ 64 * (r2.toNat + 2 ^ 64 * r3.toNat)) +
        q.toNat * (v0.toNat + 2 ^ 64 * (v1.toNat + 2 ^ 64 * (v2.toNat + 2 ^ 64 * v3.toNat))) =
      u0.toNat + 2 ^ 64 * (u1.toNat + 2 ^ 64 * (u2.toNat + 2 ^ 64 * (u3.toNat +
        2 ^ 64 * ue.toNat))) + 2 ^ 256 * w.toNat := by
  have k1 := defn_mulhu_le hh1
  have k2 := defn_mulhu_le hh2
  have k3 := defn_mulhu_le hh3
  have l1 := defn_bit_le hc1
  have l2 := defn_bit_le hc2
  have l3 := defn_bit_le hc3
  have lb0 := defn_bit_le hb0
  obtain ⟨n1, lb1⟩ := defn_sub_borrow hd1 he1 hr1 hf1 hb1 lb0
  obtain ⟨n2, lb2⟩ := defn_sub_borrow hd2 he2 hr2 hf2 hb2 lb1
  obtain ⟨n3, lb3⟩ := defn_sub_borrow hd3 he3 hr3 hf3 hb3 lb2
  have hS := submul4_nat (g3 := c3.toNat + h3.toNat) (defn_mul_mulhu hp0 hh0)
    (defn_mul_mulhu hp1 hh1) (defn_mul_mulhu hp2 hh2) (defn_mul_mulhu hp3 hh3)
    (defn_carry_left hs1 hc1) (defn_carry3 ha2 hs2 hc2 (by omega))
    (defn_carry3 ha3 hs3 hc3 (by omega)) rfl (defn_sub_borrow0 hr0 hb0) n1 n2 n3
  have hd : q.toNat * (v0.toNat + 2 ^ 64 * (v1.toNat + 2 ^ 64 * (v2.toNat + 2 ^ 64 * v3.toNat))) =
      v0.toNat * q.toNat + 2 ^ 64 * (v1.toNat * q.toNat + 2 ^ 64 * (v2.toNat * q.toNat +
        2 ^ 64 * (v3.toNat * q.toNat))) := by ring
  -- The borrow word: c3 + (h3 - ue) + b3 modulo 2^64.
  have hwn : w.toNat = (c3.toNat + h3.toNat + b3.toNat + (2 ^ 64 - ue.toNat)) % 2 ^ 64 := by
    rw [hw.eq, ht.eq, hg.eq, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_sub]
    have := ue.isLt; have := h3.isLt; omega
  have hqv : q.toNat * (v0.toNat + 2 ^ 64 * (v1.toNat + 2 ^ 64 * (v2.toNat + 2 ^ 64 * v3.toNat))) ≤
      (2 ^ 64 - 1) * (2 ^ 256 - 1) := by
    have := v0.isLt; have := v1.isLt; have := v2.isLt; have := v3.isLt
    exact Nat.mul_le_mul (by have := q.isLt; omega) (by omega)
  have hV : v0.toNat + 2 ^ 64 * (v1.toNat + 2 ^ 64 * (v2.toNat + 2 ^ 64 * v3.toNat)) < 2 ^ 256 := by
    have := v0.isLt; have := v1.isLt; have := v2.isLt; have := v3.isLt; omega
  have hR : r0.toNat + 2 ^ 64 * (r1.toNat + 2 ^ 64 * (r2.toNat + 2 ^ 64 * r3.toNat)) < 2 ^ 256 := by
    have := r0.isLt; have := r1.isLt; have := r2.isLt; have := r3.isLt; omega
  have := u0.isLt; have := u1.isLt; have := u2.isLt; have := u3.isLt
  -- The estimate is not less than the quotient: q * v > u - v.
  generalize hUe : u0.toNat + 2 ^ 64 * (u1.toNat + 2 ^ 64 * (u2.toNat + 2 ^ 64 * (u3.toNat +
    2 ^ 64 * ue.toNat))) = U at *
  have hU4 : U = u0.toNat + 2 ^ 64 * (u1.toNat + 2 ^ 64 * (u2.toNat + 2 ^ 64 * u3.toNat)) +
      2 ^ 256 * ue.toNat := by rw [← hUe]; ring
  generalize hVe : v0.toNat + 2 ^ 64 * (v1.toNat + 2 ^ 64 * (v2.toNat + 2 ^ 64 * v3.toNat)) = V
    at *
  have hdm := Nat.div_add_mod' U V
  have hml := Nat.mod_lt U hV0
  have hle : U / V * V ≤ q.toNat * V := Nat.mul_le_mul_right _ hq
  rw [hd] at hqv
  rw [← hd] at hS
  generalize q.toNat * V = QV at *
  generalize U / V * V = DV at *
  generalize r0.toNat + 2 ^ 64 * (r1.toNat + 2 ^ 64 * (r2.toNat + 2 ^ 64 * r3.toNat)) = R at *
  generalize u0.toNat + 2 ^ 64 * (u1.toNat + 2 ^ 64 * (u2.toNat + 2 ^ 64 * u3.toNat)) = U4 at *
  have hS3 : c3.toNat + h3.toNat + b3.toNat < 2 ^ 64 := by omega
  have hge : ue.toNat ≤ c3.toNat + h3.toNat + b3.toNat := by omega
  have : w.toNat = c3.toNat + h3.toNat + b3.toNat - ue.toNat := by rw [hwn]; omega
  omega

/-- The result of a division of 5 words by 4 words stored as the quotient `q` of one word and the
remainder `a` of 4 words. -/
theorem words_ret9r (m : Mem) (r q a0 a1 a2 a3 z : BitVec 64) (hz : z = 0#64)
    (hr : r.toNat + 72 ≤ 2 ^ 64)
    (m' : Mem) (hm : m' = memStore (memStore (memStore (memStore (memStore (memStore (memStore
      (memStore (memStore m r.toNat q) (r + 8#64).toNat z) (r + 16#64).toNat z)
      (r + 24#64).toNat z) (r + 32#64).toNat z) (r + 40#64).toNat a0) (r + 48#64).toNat a1)
      (r + 56#64).toNat a2) (r + 64#64).toNat a3) :
    words m' r 5 = q.toNat ∧
      words m' (r + 40#64) 4 = a0.toNat + 2 ^ 64 * (a1.toNat + 2 ^ 64 * (a2.toNat +
        2 ^ 64 * a3.toNat)) ∧
      UnchangedExcept m m' r 72 := by
  subst hm hz
  refine ⟨?_, ?_, ?_⟩
  · simp (disch := first | bv_omega | fail) only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd, memWord_memStore_self, memWord_memStore_of_ne, BitVec.toNat_ofNat,
      Nat.zero_mod, Nat.mul_zero, Nat.add_zero]
  · simp (disch := first | bv_omega | fail) only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd, memWord_memStore_self, memWord_memStore_of_ne, Nat.mul_zero,
      Nat.add_zero]
  · simp (disch := first | bv_omega | fail) only [unchangedExcept_memStore,
      unchangedExcept_refl]

/-- The end of `udivrem_top1<3>()` of `uint320` by `uint256` from 172: the stores of the quotient
in a1 and the remainder in `t0:a4:a3:t1`, and the return. -/
theorem top1_3_320_exit {hi : BitVec 20} {lo : BitVec 12} {D : List (BitVec 64)}
    (base : BitVec 64) (x : Regs) (m : Mem)
    (hpre : udivrem_top1_3_320.pre x m) (hr : x.get 1#5 &&& 3 = 0) (x' : Regs) (m' : Mem)
    (h10 : x'.get 10#5 = x.get 10#5) (h1 : x'.get 1#5 = x.get 1#5)
    (hcs : ∀ i ∈ calleeSaved, x' i = x i)
    (hm : UnchangedExcept2 m m' (x.get 10#5) 72 (x.get 2#5 - 16#64) 16)
    (hqr : (x'.get 11#5).toNat = words m (x.get 11#5) 5 / words m (x.get 12#5) 4 ∧
      (x'.get 6#5).toNat + 2 ^ 64 * ((x'.get 13#5).toNat + 2 ^ 64 * ((x'.get 14#5).toNat +
        2 ^ 64 * (x'.get 5#5).toNat)) = words m (x.get 11#5) 5 % words m (x.get 12#5) 4) :
    Reach (bufWords (x.get 11#5) 5 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 9 ++
        bufWords (x.get 2#5 - 16#64) 2 ++ D) (udivrem_top1_3_320_progAt hi lo) base
      (pcAt base 172) x' m' (x.get 1#5) (udivrem_top1_3_320.post x m) := by
  have hpre' := hpre
  simp only [udivrem_top1_3_320.pre, Buf] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hra, hrn⟩, -⟩ := hpre'
  rw [← h10]
  have hrn' : (x'.get 10#5).toNat + 72 ≤ 2 ^ 64 := h10 ▸ hrn
  rv_exec
  rv_val
  rw [h1, update_aligned hr]
  refine Reach.refl ?_
  have hz : x'.get 0#5 = 0#64 := by rw [show (0#5 : BitVec 5) = 0 from rfl, Regs.get_zero]; rfl
  have hw := words_ret9r m' (x'.get 10#5) (x'.get 11#5) (x'.get 6#5) (x'.get 13#5) (x'.get 14#5)
    (x'.get 5#5) (x'.get 0#5) hz hrn' _ rfl
  simp only [udivrem_top1_3_320.post]
  simp (disch := decide) only [Regs.eq_get x]
  rw [← h10] at hm ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hw.1, hqr.1]
  · rw [hw.2.1, hqr.2]
  · simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
    exact hm
  · intro i hi
    rw [Regs.set_apply, if_pos (by decide)]
    exact hcs i hi

/-- The registers and the memory at the head of the correction loop of `udivrem_top1<3>()` of
`uint320` by `uint256`, at 182: `t2:a3:a4:t0 + q * v = u + 2^256 * borrow`, with the quotient
`q` in a1, the borrow in t3, not 0, and the words of v in `a5:a6:a7:a2`; `n` the excess of `q`. -/
def top1_3_320Loop (x : Regs) (m : Mem) (n : Nat) (x' : Regs) (m' : Mem) : Prop :=
  x'.get 10#5 = x.get 10#5 ∧ x'.get 1#5 = x.get 1#5 ∧ (∀ i ∈ calleeSaved, x' i = x i) ∧
    UnchangedExcept2 m m' (x.get 10#5) 72 (x.get 2#5 - 16#64) 16 ∧
    (x'.get 15#5).toNat + 2 ^ 64 * ((x'.get 16#5).toNat + 2 ^ 64 * ((x'.get 17#5).toNat +
      2 ^ 64 * (x'.get 12#5).toNat)) = words m (x.get 12#5) 4 ∧
    (x'.get 7#5).toNat + 2 ^ 64 * ((x'.get 13#5).toNat + 2 ^ 64 * ((x'.get 14#5).toNat +
      2 ^ 64 * (x'.get 5#5).toNat)) + (x'.get 11#5).toNat * words m (x.get 12#5) 4 =
      words m (x.get 11#5) 5 + 2 ^ 256 * (x'.get 28#5).toNat ∧
    x'.get 28#5 ≠ 0#64 ∧ n = (x'.get 11#5).toNat - words m (x.get 11#5) 5 / words m (x.get 12#5) 4

/-- The correction loop of `udivrem_top1<3>()` of `uint320` by `uint256` from 182. -/
theorem top1_3_320_loop {hi : BitVec 20} {lo : BitVec 12} {D : List (BitVec 64)}
    (base : BitVec 64) (x : Regs) (m : Mem)
    (hpre : udivrem_top1_3_320.pre x m) (hr : x.get 1#5 &&& 3 = 0) :
    ∀ n x' m', top1_3_320Loop x m n x' m' →
    Reach (bufWords (x.get 11#5) 5 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 9 ++
        bufWords (x.get 2#5 - 16#64) 2 ++ D) (udivrem_top1_3_320_progAt hi lo) base
      (pcAt base 182) x' m' (x.get 1#5) (udivrem_top1_3_320.post x m) := by
  apply Reach.loop (top1_3_320Loop x m)
  intro n x' m' h ih
  obtain ⟨h10, h1, hcs, hm, hv, hsm, hb, hn⟩ := h
  have hlt := top1_q_gt (words4_lt _ _ _ _) hsm
    (fun h0 => hb (BitVec.eq_of_toNat_eq (by simpa using h0)))
  rv_step
  rv_exec_cut 172 182
  -- The borrow is 0: the end.
  all_goals first
    | (rv_not_at 172; skip)
    | (refine top1_3_320_exit base x m hpre hr _ _ ?_ ?_ ?_ hm ?_
       · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h10
       · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h1
       · refine calleeSaved_of hcs _ ?_
         intro i hi
         simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
         rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
           rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
       · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
         apply top1_body_exit
         all_goals assumption)
  -- The borrow is not 0: the next correction.
  all_goals
    refine ih _ (top1_body_k hlt hn) _ _ ⟨?_, ?_, ?_, hm, ?_, ?_, ?_, rfl⟩
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · exact h10
    · exact h1
    · refine calleeSaved_of hcs _ ?_
      intro i hi
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    · exact hv
    · apply top1_body_sm
      all_goals assumption
    · assumption

/-- The end of `udivrem_top1<3>()` of `uint320` by `uint256` from the test of the borrow at 170:
`t2:a3:a4:t0 + q * v = u + 2^256 * borrow` with the quotient estimate `q` in a1 not less than
`u / v`. -/
theorem top1_3_320_tail {hi : BitVec 20} {lo : BitVec 12} {D : List (BitVec 64)}
    (base : BitVec 64) (x : Regs) (m : Mem)
    (hpre : udivrem_top1_3_320.pre x m) (hr : x.get 1#5 &&& 3 = 0) (x' : Regs) (m' : Mem)
    (h10 : x'.get 10#5 = x.get 10#5) (h1 : x'.get 1#5 = x.get 1#5)
    (hcs : ∀ i ∈ calleeSaved, x' i = x i)
    (hm : UnchangedExcept2 m m' (x.get 10#5) 72 (x.get 2#5 - 16#64) 16)
    (hv : (x'.get 15#5).toNat + 2 ^ 64 * ((x'.get 16#5).toNat + 2 ^ 64 * ((x'.get 17#5).toNat +
      2 ^ 64 * (x'.get 12#5).toNat)) = words m (x.get 12#5) 4)
    (hsm : (x'.get 7#5).toNat + 2 ^ 64 * ((x'.get 13#5).toNat + 2 ^ 64 * ((x'.get 14#5).toNat +
      2 ^ 64 * (x'.get 5#5).toNat)) + (x'.get 11#5).toNat * words m (x.get 12#5) 4 =
      words m (x.get 11#5) 5 + 2 ^ 256 * (x'.get 28#5).toNat)
    (hq : words m (x.get 11#5) 5 / words m (x.get 12#5) 4 ≤ (x'.get 11#5).toNat) :
    Reach (bufWords (x.get 11#5) 5 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 9 ++
        bufWords (x.get 2#5 - 16#64) 2 ++ D) (udivrem_top1_3_320_progAt hi lo) base
      (pcAt base 170) x' m' (x.get 1#5) (udivrem_top1_3_320.post x m) := by
  have hpre' := hpre
  simp only [udivrem_top1_3_320.pre] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  have hV : 0 < words m (x.get 12#5) 4 := by
    have := hpre'.2.2.2.2.2.2.2.2.2.1; have : 0 < 2 ^ (64 * 3) := by positivity
    omega
  have hz0 : x'.get 0#5 = 0#64 := by rw [show (0#5 : BitVec 5) = 0 from rfl, Regs.get_zero]; rfl
  rv_step
  rv_exec_cut 172 182
  all_goals simp only [hz0, bne_eq_false_iff_eq] at *
  -- The borrow is 0: no correction.
  all_goals first
    | (rv_not_at 172; skip)
    | (refine top1_3_320_exit base x m hpre hr _ _ ?_ ?_ ?_ hm ?_
       · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h10
       · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h1
       · refine calleeSaved_of hcs _ ?_
         intro i hi
         simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
         rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
           rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
       · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
         exact top1_tail_exit hV hsm (by assumption) hq)
  -- The borrow is not 0: the correction loop.
  all_goals
    exact top1_3_320_loop base x m hpre hr _ _ _ ⟨h10, h1, hcs, hm, hv, hsm, by assumption, rfl⟩

/-- The stores of s0 and s1 below sp are in the stack frame of `udivrem_top1<3>()` of `uint320`
by `uint256`. -/
theorem unchangedExcept2_s0s1 (m : Mem) (r sp v w : BitVec 64)
    (hs : (sp - 16#64).toNat + 16 ≤ 2 ^ 64) :
    UnchangedExcept2 m (memStore (memStore m (sp + 18446744073709551608#64).toNat v)
      (sp + 18446744073709551600#64).toNat w) r 72 (sp - 16#64) 16 := by
  rw [unchangedExcept2_memStore _ _ (Or.inr ⟨by bv_omega, by bv_omega⟩),
    unchangedExcept2_memStore _ _ (Or.inr ⟨by bv_omega, by bv_omega⟩)]
  exact unchangedExcept2_refl _ _ _ _ _

/-- The run of `udivrem_top1<3>()` of `uint320` by `uint256` for any immediates `hi` and `lo` of
the address `T` of the table of the reciprocal. -/
theorem udivrem_top1_3_320.reach (hi : BitVec 20) (lo : BitVec 12) (base T : BitVec 64)
    (x : Regs) (m : Mem)
    (hT : pcAt base 64 + ((hi ++ 0x000#12).signExtend 64 + lo.signExtend 64) = T)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64) (hr : x.get 1#5 &&& 3 = 0)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hpre : udivrem_top1_3_320.pre x m) :
    Reach (udivrem_top1_3_320.bufs x ++ bufWords T 256) (udivrem_top1_3_320_progAt hi lo) base
      (pcAt base 0) x m (x.get 1#5) (udivrem_top1_3_320.post x m) := by
  have hpre0 := hpre
  simp only [udivrem_top1_3_320.pre, udivrem_top1_3_320.bufs, Buf] at hpre ⊢
  simp (disch := decide) only [Regs.eq_get x] at hpre ⊢
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr, hv1, hv2,
    hu3⟩ := hpre
  simp only [Disjoint] at hdru hdrv hdsu hdsv hdsr
  have hv3 := top4_ne_zero m (x.get 12#5) hv1
  have hv3' : (memWord m (x.get 12#5 + 24#64).toNat).toNat ≠ 0 :=
    fun h => hv3 (BitVec.eq_of_toNat_eq (by simpa using h))
  have hue := top1_3_320_ue m (x.get 11#5) (x.get 12#5) hu3
  rv_exec_cut 170
  -- The words v[3], v[2], u[4], u[3] and u[2] by names.
  all_goals
    set v3 := memWord m (x.get 12#5 + 24#64).toNat with hv3e
    set v2 := memWord m (x.get 12#5 + 16#64).toNat with hv2e
    set ue := memWord m (x.get 11#5 + 32#64).toNat with huee
    set u3 := memWord m (x.get 11#5 + 24#64).toNat with hu3e
    set u2 := memWord m (x.get 11#5 + 16#64).toNat with hu2e
    rv_copies
    have hv3n : v3 ≠ 0 := fun h => hv3' (by rw [h]; rfl)
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
  -- The normalized top word vt of v, the funnel shift of v[3] and v[2] for s ≠ 0.
  all_goals first
    | (rv_lacks ¬BitVec.ofNat 64 (63 - v3.toNat.log2) = 0#64; skip)
    | (have h1 := toNat_fshl_code v3 v2 (BitVec.ofNat 64 (63 - v3.toNat.log2)) (by rw [hSt]; omega)
       rv_fold h1
       rv_fold h1
       rw [hSt] at h1
       have hdn63 := norm2_hi (d0 := v2.toNat) (by omega) v2.isLt hS1 hS63
       rw [← h1] at hdn63)
  all_goals first
    | (rv_lacks BitVec.ofNat 64 (63 - v3.toNat.log2) = 0#64; skip)
    | (rv_get hz : BitVec.ofNat 64 (63 - v3.toNat.log2) = 0#64
       have hS0 := ofNat_S_eq (by omega) hz
       have hdn63 : 2 ^ 63 ≤ v3.toNat := by rw [hS0] at hS63; simpa using hS63)
  -- The table entry of vt: the low half.
  all_goals
    simp only [hT] at *
    refine Reach.step (by decide) rfl ?_
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
    rv_exec_cut 170
    -- The high half.
    refine Reach.step (by decide) rfl ?_
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
    rv_exec_cut 170
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
    | (rv_lacks ¬BitVec.ofNat 64 (63 - v3.toNat.log2) = 0#64; skip)
    | (rv_get hne : ¬BitVec.ofNat 64 (63 - v3.toNat.log2) = 0#64
       have hS0 := ofNat_S_ne (by omega) hne
       have hhi := toNat_fshl_code ue u3 (BitVec.ofNat 64 (63 - v3.toNat.log2)) (by rw [hSt]; omega)
       have hlo := toNat_fshl_code u3 u2 (BitVec.ofNat 64 (63 - v3.toNat.log2)) (by rw [hSt]; omega)
       conv at hhi => rhs; rw [hSt]
       conv at hlo => rhs; rw [hSt]
       have hue1 : ue.toNat * 2 ^ (63 - v3.toNat.log2) < 2 ^ 64 :=
         Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.le_of_lt hue)) hS1
       rw [Nat.mod_eq_of_lt (fshl_lt (by omega) u3.isLt hue1)] at hhi
       have hs := div2by1BVc_spec ((ue <<< ((BitVec.ofNat 64 (63 - v3.toNat.log2)).toNat % 64)) |||
           ((u3 >>> 1) >>> ((BitVec.ofNat 64 (63 - v3.toNat.log2) ^^^
             18446744073709551615#64).toNat % 64)))
         ((u3 <<< ((BitVec.ofNat 64 (63 - v3.toNat.log2)).toNat % 64)) |||
           ((u2 >>> 1) >>> ((BitVec.ofNat 64 (63 - v3.toNat.log2) ^^^
             18446744073709551615#64).toNat % 64))) _ _ hdn63
         (by rw [hhi, h1]; exact top1_2_hi_lt (by omega) u3.isLt v2.isLt hue hS1) hv
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
       rw [hhi, hlo, top1_2_ut _ _ _ _ (by omega) u2.isLt, h1,
         Nat.mod_eq_of_lt (fshl_lt (by omega) v2.isLt hS1)] at hs)
  -- s = 0.
  all_goals first
    | (rv_lacks BitVec.ofNat 64 (63 - v3.toNat.log2) = 0#64; skip)
    | (have hs := div2by1BVc_spec ue u3 _ _ hdn63 hue hv
       simp only [div2by1BVc] at hs
       rv_fold hs
       rv_fold hs
       try simp (disch := assumption) only [if_pos, if_neg] at hs
       rv_fold hs
       try (simp only [BitVec.add_assoc] at hs; rv_fold hs)
       have hN : (2 ^ 64 * ue.toNat + u3.toNat) / v3.toNat =
           ((u3.toNat + 2 ^ 64 * ue.toNat) * 2 ^ (63 - v3.toNat.log2) +
             u2.toNat / 2 ^ (64 - (63 - v3.toNat.log2))) /
           (v3.toNat * 2 ^ (63 - v3.toNat.log2) + v2.toNat / 2 ^ (64 - (63 - v3.toNat.log2))) := by
         rw [hS0, Nat.div_eq_of_lt u2.isLt, Nat.div_eq_of_lt v2.isLt]
         simp only [Nat.pow_zero, Nat.mul_one, Nat.add_zero]
         rw [Nat.add_comm (2 ^ 64 * _)]
       rw [hN] at hs)
  -- The estimate is not less than the quotient.
  all_goals
    have hest := top1_est (U := words m (x.get 11#5) 5) (V := words m (x.get 12#5) 4) (by omega)
      (words5_lt_top3 m (x.get 11#5)) (words4_ge_top2 m (x.get 12#5))
      (Nat.lt_of_lt_of_le (by norm_num) (Nat.le_add_right_of_le hS63)) hs
  -- The submul() and the correction.
  all_goals
    have hest' := hest
    have hV0 : 0 < words m (x.get 12#5) 4 := by
      have : 0 < 2 ^ (64 * 3) := by positivity
      omega
    simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
      Nat.add_zero] at hest' hV0
    rv_fold hest'
    rv_fold hV0
    try rw [← hu2e] at hest' hV0
    try rw [← hu3e] at hest' hV0
    try rw [← huee] at hest' hV0
    try rw [← hv2e] at hest' hV0
    try rw [← hv3e] at hest' hV0
    refine top1_3_320_tail base x m hpre0 hr _ _ ?_ ?_ ?_ (unchangedExcept2_s0s1 _ _ _ _ _ hsn)
      ?_ ?_ ?_
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · intro i hi
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] <;>
        exact (Regs.eq_get x (by decide)).symm
    · simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
        Nat.add_zero]
      rv_loads
      rfl
    · simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
        Nat.add_zero]
      rv_loads
      try rw [← hu2e]
      try rw [← hu3e]
      try rw [← huee]
      try rw [← hv2e]
      try rw [← hv3e]
      apply submul4ue_words
      all_goals assumption
    · exact hest

theorem udivrem_top1_3_320.proof : udivrem_top1_3_320.spec := by
  apply runsI_of_reach udivrem_top1_3_320_image_decodes
  intro base ret _ hr _ _ hw x m hx1 _ hhold hpre
  rw [show udivrem_top1_3_320_image_dataOff = 816 from rfl] at hw hhold ⊢
  rw [show udivrem_top1_3_320_image_data.length = 256 from rfl] at hw ⊢
  have hx : x.get 1#5 = ret := by rw [← Regs.eq_get x (by decide)]; exact hx1
  rw [show udivrem_top1_3_320_entry = udivrem_top1_3_320_image_udivrem_top1_3_320_offset from rfl,
    dataWords, ← hx]
  refine Reach.lift udivrem_top1_3_320_image_udivrem_top1_3_320_in (by decide) ?_
  have h := udivrem_top1_3_320.reach 0x0#20 0x230#12
    (pcAt base udivrem_top1_3_320_image_udivrem_top1_3_320_offset) _ x m
    (by simp only [udivrem_top1_3_320_image_udivrem_top1_3_320_offset, pcAt, BitVec.reduceAppend,
      BitVec.reduceSignExtend]; bv_omega)
    (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (hx ▸ hr) hhold hpre
  rwa [pcAt_zero] at h

/-- The registers of the nonvacuous instance: the result, u = 0 and v = 2^192 above the data, and
the frame below sp. -/
theorem udivrem_top1_3_320.nonvacuous :
    NonVacuousI udivrem_top1_3_320_image_code udivrem_top1_3_320_image_data
      udivrem_top1_3_320_image_dataOff udivrem_top1_3_320.bufs udivrem_top1_3_320.pre :=
  nonVacuousI_of_args (fun i => if i = 10#5 then 0x80000C00#64 else if i = 11#5 then 0x80000C48#64
      else if i = 12#5 then 0x80000C70#64 else if i = 2#5 then 0x80000CB0#64 else 0)
    0x80000C48 [0, 0, 0, 0, 0, 0, 0, 0, 1]
    (by decide) (by decide) (by decide) (by decide)
    (by rw [show udivrem_top1_3_320_image_dataOff = 816 from rfl,
          show udivrem_top1_3_320_image_data.length = 256 from rfl]
        simp only [udivrem_top1_3_320.bufs, ↓reduceIte, BitVec.reduceEq, BitVec.reduceSub,
          bufWords, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq]
        repeat' apply And.intro
        all_goals decide)
    (by decide)
    (fun m => by
      simp only [udivrem_top1_3_320.pre, Buf, Disjoint, words, ↓reduceIte, BitVec.reduceEq,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, BitVec.toNat_ofNat,
        Nat.reducePow, Nat.reduceMod, Nat.mul_zero, Nat.add_zero]
      simp (disch := decide) only [memWord_storeWords_getD]
      decide)

end IntxRV.Api
