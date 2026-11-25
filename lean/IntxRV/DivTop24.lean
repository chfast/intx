import IntxRV.DivTopE
import IntxRV.Gen.Api.udivrem_top2_4_320

/-!
# The blocks of `udivrem_top2<4>()` of `uint320` by `uint256`

The divisor has 4 significant words: below the top 128 bits of the normalized divisor are 2 words of
v, and the remainder has 4 words. The code has the two 2-word `submul()` of the quotient words,
which clang interleaves (`top24_submul_words`), and a correction loop with a 4-word addition
(`top24_loop`). The two divisions of 3 by 2 words, the stores of the result and the frame of 32
bytes are as in `IntxRV/DivTop2_320.lean`, in other registers.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- The first inlined `udivrem_3by2()` of `udivrem_top2<4>()` of `uint320`, from 139 to 169 (with
the correction out of line): `t2:a7:t1` by `a5:a6` (a5 high) with the reciprocal in t3, to the
quotient in a7 and the remainder in `t2:t1` (t2 high), with t4 0. -/
theorem top24_div_top {A : List (BitVec 64)} {hi : BitVec 20} {lo : BitVec 12} (base : BitVec 64)
    (x : Regs) (m : Mem)
    (hd : 2 ^ 127 ≤ (x.get 16#5).toNat + 2 ^ 64 * (x.get 15#5).toNat)
    (hu : (x.get 7#5).toNat * 2 ^ 64 + (x.get 17#5).toNat <
      (x.get 16#5).toNat + 2 ^ 64 * (x.get 15#5).toNat)
    (hv : (x.get 28#5).toNat =
      (2 ^ 192 - 1) / ((x.get 16#5).toNat + 2 ^ 64 * (x.get 15#5).toNat) - 2 ^ 64) :
    Reach A (udivrem_top2_4_320_progAt hi lo) base (pcAt base 139) x m (pcAt base 169)
      (fun x' m' => m' = m ∧ x'.get 29#5 = 0#64 ∧ Div3Out x x' ((x.get 7#5).toNat * 2 ^ 128 +
        (x.get 17#5).toNat * 2 ^ 64 + (x.get 6#5).toNat)
        ((x.get 16#5).toNat + 2 ^ 64 * (x.get 15#5).toNat) 17#5 6#5 7#5
        [6#5, 7#5, 8#5, 17#5, 29#5, 30#5, 31#5]) := by
  rv_exec
  all_goals
    beta_reduce
    simp only [Div3Out]
    rv_cse
    have hs := div3by2BV_spec (x.get 7#5) (x.get 17#5) (x.get 6#5) (x.get 16#5) (x.get 15#5)
      (x.get 28#5) hd hu hv
    simp only [div3by2BV] at hs
    rv_fold hs
    rv_fold hs
    simp only [zopz0zI_u_eq, decide_eq_true_eq, decide_eq_false_iff_not, beq_eq_false_iff_ne,
      ne_eq] at *
    rv_conds
    simp (disch := assumption) only [if_pos, if_neg] at hs
    rv_fold hs
    rv_fold hs
    constructor
    · first | rfl | trivial
    constructor
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      exact hs.1
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      exact hs.2
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp (config := { decide := true }) only [Regs.set_apply, hr, ↓reduceIte]

/-- The second inlined `udivrem_3by2()` of `udivrem_top2<4>()` of `uint320`, from 169 to 200 (with
the correction out of line): `t2:t1:t0` by `a5:a6` with the reciprocal in t3 and t4 0, to the
quotient in t0 and the remainder in `t2:t1`. -/
theorem top24_div_low {A : List (BitVec 64)} {hi : BitVec 20} {lo : BitVec 12} (base : BitVec 64)
    (x : Regs) (m : Mem)
    (hd : 2 ^ 127 ≤ (x.get 16#5).toNat + 2 ^ 64 * (x.get 15#5).toNat)
    (hu : (x.get 7#5).toNat * 2 ^ 64 + (x.get 6#5).toNat <
      (x.get 16#5).toNat + 2 ^ 64 * (x.get 15#5).toNat)
    (hv : (x.get 28#5).toNat =
      (2 ^ 192 - 1) / ((x.get 16#5).toNat + 2 ^ 64 * (x.get 15#5).toNat) - 2 ^ 64)
    (h29 : x.get 29#5 = 0#64) :
    Reach A (udivrem_top2_4_320_progAt hi lo) base (pcAt base 169) x m (pcAt base 200)
      (fun x' m' => m' = m ∧ Div3Out x x' ((x.get 7#5).toNat * 2 ^ 128 +
        (x.get 6#5).toNat * 2 ^ 64 + (x.get 5#5).toNat)
        ((x.get 16#5).toNat + 2 ^ 64 * (x.get 15#5).toNat) 5#5 6#5 7#5
        [5#5, 6#5, 7#5, 15#5, 16#5, 28#5, 29#5, 30#5, 31#5]) := by
  rv_exec
  all_goals
    beta_reduce
    simp only [Div3Out]
    rv_cse
    rw [h29] at *
    have hs := div3by2BVz_spec (x.get 7#5) (x.get 6#5) (x.get 5#5) (x.get 16#5) (x.get 15#5)
      (x.get 28#5) hd hu hv
    simp only [div3by2BVz] at hs
    rv_fold hs
    rv_fold hs
    simp only [zopz0zI_u_eq, decide_eq_true_eq, decide_eq_false_iff_not, beq_eq_false_iff_ne,
      ne_eq] at *
    rv_conds
    simp (disch := assumption) only [if_pos, if_neg] at hs
    rv_fold hs
    rv_fold hs
    constructor
    · first | rfl | trivial
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      exact hs.1
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      exact hs.2
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp (config := { decide := true }) only [Regs.set_apply, hr, ↓reduceIte]

/-- The result of `udivrem_top2<4>()` of `uint320` stored as the quotient `q1:q0` and the
remainder `a`. -/
theorem words_ret9q2r4 (m : Mem) (r q0 q1 a0 a1 a2 a3 z : BitVec 64) (hz : z = 0#64)
    (hr : r.toNat + 72 ≤ 2 ^ 64)
    (m' : Mem) (hm : m' = memStore (memStore (memStore (memStore (memStore (memStore (memStore
      (memStore (memStore m r.toNat q0) (r + 8#64).toNat q1) (r + 16#64).toNat z)
      (r + 24#64).toNat z) (r + 32#64).toNat z) (r + 40#64).toNat a0) (r + 48#64).toNat a1)
      (r + 56#64).toNat a2) (r + 64#64).toNat a3) :
    words m' r 5 = q0.toNat + 2 ^ 64 * q1.toNat ∧
      words m' (r + 40#64) 4 =
        a0.toNat + 2 ^ 64 * (a1.toNat + 2 ^ 64 * (a2.toNat + 2 ^ 64 * a3.toNat)) ∧
      UnchangedExcept m m' r 72 := by
  subst hm hz
  refine ⟨?_, ?_, ?_⟩
  · simp (disch := first | bv_omega | fail) only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd, memWord_memStore_self, memWord_memStore_of_ne, BitVec.toNat_ofNat,
      Nat.zero_mod, Nat.mul_zero, Nat.add_zero]
  · simp (disch := first | bv_omega | fail) only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd, memWord_memStore_self, memWord_memStore_of_ne, Nat.mul_zero, Nat.add_zero]
  · simp (disch := first | bv_omega | fail) only [unchangedExcept_memStore,
      unchangedExcept_refl]

/-- The end of `udivrem_top2<4>()` of `uint320` from 262: the stores of the quotient in `a7:t4` and
the remainder in `a4:a3:a1:a2`, and the return. -/
theorem top24_exit {hi : BitVec 20} {lo : BitVec 12} (base T : BitVec 64) (x : Regs) (m : Mem)
    (hpre : udivrem_top2_4_320.pre x m) (hr : x.get 1#5 &&& 3 = 0) (x' : Regs) (m' : Mem)
    (h10 : x'.get 10#5 = x.get 10#5) (h1 : x'.get 1#5 = x.get 1#5)
    (hcs : ∀ i ∈ calleeSaved, x' i = x i)
    (hm : UnchangedExcept2 m m' (x.get 10#5) 72 (x.get 2#5 - 32#64) 32)
    (hqr : (x'.get 29#5).toNat + 2 ^ 64 * (x'.get 17#5).toNat =
        words m (x.get 11#5) 5 / words m (x.get 12#5) 4 ∧
      (x'.get 12#5).toNat + 2 ^ 64 * ((x'.get 11#5).toNat + 2 ^ 64 * ((x'.get 13#5).toNat +
        2 ^ 64 * (x'.get 14#5).toNat)) = words m (x.get 11#5) 5 % words m (x.get 12#5) 4) :
    Reach (bufWords (x.get 11#5) 5 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 9 ++
        bufWords (x.get 2#5 - 32#64) 4 ++ bufWords T 256) (udivrem_top2_4_320_progAt hi lo) base
      (pcAt base 262) x' m' (x.get 1#5) (udivrem_top2_4_320.post x m) := by
  have hpre' := hpre
  simp only [udivrem_top2_4_320.pre, Buf] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hra, hrn⟩, -⟩ := hpre'
  rw [← h10]
  have hrn' : (x'.get 10#5).toNat + 72 ≤ 2 ^ 64 := h10 ▸ hrn
  rv_exec
  rv_val
  rw [h1, update_aligned hr]
  refine Reach.refl ?_
  have hz : x'.get 0#5 = 0#64 := by rw [show (0#5 : BitVec 5) = 0 from rfl, Regs.get_zero]; rfl
  have hw := words_ret9q2r4 m' (x'.get 10#5) (x'.get 29#5) (x'.get 17#5) (x'.get 12#5)
    (x'.get 11#5) (x'.get 13#5) (x'.get 14#5) _ hz hrn' _ rfl
  simp only [udivrem_top2_4_320.post]
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

/-- The addition of 4 words in the correction loop of `udivrem_top2<4>()`: the words `n` of
`r + v` and the carry out of them as a condition. -/
theorem add4c_words {r0 r1 r2 r3 v0 v1 v2 v3 n0 c0 a1 e1 n1 f1 c1 a2 e2 n2 f2 c2 a3 n3 : BitVec 64}
    (hn0 : Defn n0 (r0 + v0)) (hc0 : Defn c0 (if n0 < r0 then 1#64 else 0#64))
    (ha1 : Defn a1 (r1 + v1)) (he1 : Defn e1 (if a1 < r1 then 1#64 else 0#64))
    (hn1 : Defn n1 (a1 + c0)) (hf1 : Defn f1 (if n1 < a1 then 1#64 else 0#64))
    (hc1 : Defn c1 (e1 ||| f1))
    (ha2 : Defn a2 (r2 + v2)) (he2 : Defn e2 (if a2 < r2 then 1#64 else 0#64))
    (hn2 : Defn n2 (a2 + c1)) (hf2 : Defn f2 (if n2 < a2 then 1#64 else 0#64))
    (hc2 : Defn c2 (e2 ||| f2)) (ha3 : Defn a3 (r3 + v3)) (hn3 : Defn n3 (a3 + c2)) :
    n0.toNat + 2 ^ 64 * (n1.toNat + 2 ^ 64 * (n2.toNat + 2 ^ 64 * n3.toNat)) +
        2 ^ 256 * (if a3 < r3 ∨ n3 < a3 then 1 else 0) =
      r0.toNat + 2 ^ 64 * (r1.toNat + 2 ^ 64 * (r2.toNat + 2 ^ 64 * r3.toNat)) +
        (v0.toNat + 2 ^ 64 * (v1.toNat + 2 ^ 64 * (v2.toNat + 2 ^ 64 * v3.toNat))) := by
  have e0 := defn_carry_left hn0 hc0
  have l0 := defn_bit_le hc0
  obtain ⟨e1', l1⟩ := defn_add_carry ha1 he1 hn1 hf1 hc1 l0
  obtain ⟨e2', l2⟩ := defn_add_carry ha2 he2 hn2 hf2 hc2 l1
  rw [hn3.eq, ha3.eq]
  have := r3.isLt; have := v3.isLt
  have h1 : (r3 + v3).toNat = (r3.toNat + v3.toNat) % 2 ^ 64 := BitVec.toNat_add _ _
  have h2 : (r3 + v3 + c2).toNat = ((r3 + v3).toNat + c2.toNat) % 2 ^ 64 := BitVec.toNat_add _ _
  by_cases d1 : r3 + v3 < r3 <;> by_cases d2 : r3 + v3 + c2 < r3 + v3 <;>
    simp only [d1, d2, true_or, or_true, or_self, ↓reduceIte] <;>
    simp only [BitVec.lt_def] at d1 d2 <;> omega

theorem add4c_carry {r0 r1 r2 r3 v0 v1 v2 v3 n0 c0 a1 e1 n1 f1 c1 a2 e2 n2 f2 c2 a3 n3 : BitVec 64}
    (hn0 : Defn n0 (r0 + v0)) (hc0 : Defn c0 (if n0 < r0 then 1#64 else 0#64))
    (ha1 : Defn a1 (r1 + v1)) (he1 : Defn e1 (if a1 < r1 then 1#64 else 0#64))
    (hn1 : Defn n1 (a1 + c0)) (hf1 : Defn f1 (if n1 < a1 then 1#64 else 0#64))
    (hc1 : Defn c1 (e1 ||| f1))
    (ha2 : Defn a2 (r2 + v2)) (he2 : Defn e2 (if a2 < r2 then 1#64 else 0#64))
    (hn2 : Defn n2 (a2 + c1)) (hf2 : Defn f2 (if n2 < a2 then 1#64 else 0#64))
    (hc2 : Defn c2 (e2 ||| f2)) (ha3 : Defn a3 (r3 + v3)) (hn3 : Defn n3 (a3 + c2))
    (hc : a3 < r3 ∨ n3 < a3) :
    n0.toNat + 2 ^ 64 * (n1.toNat + 2 ^ 64 * (n2.toNat + 2 ^ 64 * n3.toNat)) + 2 ^ 256 =
      r0.toNat + 2 ^ 64 * (r1.toNat + 2 ^ 64 * (r2.toNat + 2 ^ 64 * r3.toNat)) +
        (v0.toNat + 2 ^ 64 * (v1.toNat + 2 ^ 64 * (v2.toNat + 2 ^ 64 * v3.toNat))) := by
  have h := add4c_words hn0 hc0 ha1 he1 hn1 hf1 hc1 ha2 he2 hn2 hf2 hc2 ha3 hn3
  rwa [if_pos hc, Nat.mul_one] at h

theorem add4c_nocarry {r0 r1 r2 r3 v0 v1 v2 v3 n0 c0 a1 e1 n1 f1 c1 a2 e2 n2 f2 c2 a3 n3 : BitVec 64}
    (hn0 : Defn n0 (r0 + v0)) (hc0 : Defn c0 (if n0 < r0 then 1#64 else 0#64))
    (ha1 : Defn a1 (r1 + v1)) (he1 : Defn e1 (if a1 < r1 then 1#64 else 0#64))
    (hn1 : Defn n1 (a1 + c0)) (hf1 : Defn f1 (if n1 < a1 then 1#64 else 0#64))
    (hc1 : Defn c1 (e1 ||| f1))
    (ha2 : Defn a2 (r2 + v2)) (he2 : Defn e2 (if a2 < r2 then 1#64 else 0#64))
    (hn2 : Defn n2 (a2 + c1)) (hf2 : Defn f2 (if n2 < a2 then 1#64 else 0#64))
    (hc2 : Defn c2 (e2 ||| f2)) (ha3 : Defn a3 (r3 + v3)) (hn3 : Defn n3 (a3 + c2))
    (h1 : ¬a3 < r3) (h2 : ¬n3 < a3) :
    n0.toNat + 2 ^ 64 * (n1.toNat + 2 ^ 64 * (n2.toNat + 2 ^ 64 * n3.toNat)) =
      r0.toNat + 2 ^ 64 * (r1.toNat + 2 ^ 64 * (r2.toNat + 2 ^ 64 * r3.toNat)) +
        (v0.toNat + 2 ^ 64 * (v1.toNat + 2 ^ 64 * (v2.toNat + 2 ^ 64 * v3.toNat))) := by
  have h := add4c_words hn0 hc0 ha1 he1 hn1 hf1 hc1 ha2 he2 hn2 hf2 hc2 ha3 hn3
  rwa [if_neg (by tauto), Nat.mul_zero, Nat.add_zero] at h

/-- The quotient estimate is too large if `R + q v = u + 2^256` with `R < 2^256`. -/
theorem top24_q_gt {R q U V : Nat} (hR : R < 2 ^ 256) (h : R + q * V = U + 2 ^ 256) :
    U / V < q := top1_q_gt (b := 1) hR (by rw [h]; ring) (by norm_num)

/-- The quotient and the remainder after the last correction of `udivrem_top2<4>()`. -/
theorem top24_exit_nat {R' q' R q U V : Nat} (h : R' + 2 ^ 256 = R + V) (hd : q' + 1 = q)
    (hsm : R + q * V = U + 2 ^ 256) (hR : R < 2 ^ 256) : q' = U / V ∧ R' = U % V := by
  have : q * V = q' * V + V := by rw [← hd]; ring
  exact div_mod_of_lt (by omega) (by omega)

/-- The invariant of the loop of `udivrem_top2<4>()` after a correction without a carry. -/
theorem top24_cont_nat {R' q' R q U V : Nat} (h : R' = R + V) (hd : q' + 1 = q)
    (hsm : R + q * V = U + 2 ^ 256) : R' + q' * V = U + 2 ^ 256 := by
  have : q * V = q' * V + V := by rw [← hd]; ring
  omega

/-- The registers and the memory at the head of the correction loop of `udivrem_top2<4>()` of
`uint320`, at 274: `a4:a3:a1:t2 + q * v = u + 2^256`, with the quotient `q` in `a7:t0` and the
words of v in `t3:t1:a6:a5`; `n` the excess of `q`. -/
def top24Loop (x : Regs) (m : Mem) (n : Nat) (x' : Regs) (m' : Mem) : Prop :=
  x'.get 10#5 = x.get 10#5 ∧ x'.get 1#5 = x.get 1#5 ∧ (∀ i ∈ calleeSaved, x' i = x i) ∧
    UnchangedExcept2 m m' (x.get 10#5) 72 (x.get 2#5 - 32#64) 32 ∧
    (x'.get 15#5).toNat + 2 ^ 64 * ((x'.get 16#5).toNat + 2 ^ 64 * ((x'.get 6#5).toNat +
      2 ^ 64 * (x'.get 28#5).toNat)) = words m (x.get 12#5) 4 ∧
    (x'.get 7#5).toNat + 2 ^ 64 * ((x'.get 11#5).toNat + 2 ^ 64 * ((x'.get 13#5).toNat +
      2 ^ 64 * (x'.get 14#5).toNat)) +
      ((x'.get 5#5).toNat + 2 ^ 64 * (x'.get 17#5).toNat) * words m (x.get 12#5) 4 =
      words m (x.get 11#5) 5 + 2 ^ 256 ∧
    n = (x'.get 5#5).toNat + 2 ^ 64 * (x'.get 17#5).toNat -
      words m (x.get 11#5) 5 / words m (x.get 12#5) 4

/-- The correction loop of `udivrem_top2<4>()` of `uint320` from 274. -/
theorem top24_loop {hi : BitVec 20} {lo : BitVec 12} (base T : BitVec 64) (x : Regs) (m : Mem)
    (hpre : udivrem_top2_4_320.pre x m) (hr : x.get 1#5 &&& 3 = 0) :
    ∀ n x' m', top24Loop x m n x' m' →
    Reach (bufWords (x.get 11#5) 5 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 9 ++
        bufWords (x.get 2#5 - 32#64) 4 ++ bufWords T 256) (udivrem_top2_4_320_progAt hi lo) base
      (pcAt base 274) x' m' (x.get 1#5) (udivrem_top2_4_320.post x m) := by
  apply Reach.loop (top24Loop x m)
  intro n x' m' h ih
  obtain ⟨h10, h1, hcs, hm, hv, hsm, hn⟩ := h
  have hR := words4_lt (x'.get 7#5) (x'.get 11#5) (x'.get 13#5) (x'.get 14#5)
  have hlt := top24_q_gt hR hsm
  rv_step
  rv_exec_cut 262 274
  all_goals try simp only [zopz0zI_u_eq, decide_eq_true_eq, decide_eq_false_iff_not] at *
  all_goals try rv_conds
  -- The sum r + v and the quotient less 1, from the values of the run.
  all_goals
    simp only [Defn] at *
    subst_vars
    have hd := dec2_toNat (q0 := x'.get 5#5) (q1 := x'.get 17#5) rfl rfl
      (Nat.lt_of_le_of_lt (Nat.zero_le _) hlt)
  -- A carry out of r + v: the end.
  all_goals first
    | (rv_not_at 262; skip)
    | (have ha := add4c_carry (r0 := x'.get 7#5) (r1 := x'.get 11#5) (r2 := x'.get 13#5)
         (r3 := x'.get 14#5) (v0 := x'.get 15#5) (v1 := x'.get 16#5) (v2 := x'.get 6#5)
         (v3 := x'.get 28#5) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
         (by tauto)
       rw [hv] at ha
       refine top24_exit base T x m hpre hr _ _ ?_ ?_ ?_ hm ?_
       · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h10
       · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h1
       · refine calleeSaved_of hcs _ ?_
         intro i hi
         simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
         rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
           rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
       · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
         exact top24_exit_nat ha hd hsm hR)
  -- No carry: the next correction.
  all_goals
    have ha := add4c_nocarry (r0 := x'.get 7#5) (r1 := x'.get 11#5) (r2 := x'.get 13#5)
      (r3 := x'.get 14#5) (v0 := x'.get 15#5) (v1 := x'.get 16#5) (v2 := x'.get 6#5)
      (v3 := x'.get 28#5) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (by assumption) (by assumption)
    rw [hv] at ha
    refine ih _ ?_ _ _ ⟨?_, ?_, ?_, hm, ?_, ?_, rfl⟩
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · omega
    · exact h10
    · exact h1
    · refine calleeSaved_of hcs _ ?_
      intro i hi
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    · exact hv
    · exact top24_cont_nat ha hd hsm

/-- Two borrows in a row, `u - m` and then of a bit, are not both 1. -/
theorem borrows_excl {y m u b y' c b' : Nat} (h1 : y + m = u + 2 ^ 64 * b)
    (h2 : y' + c = y + 2 ^ 64 * b') (hm : m < 2 ^ 64) (hy' : y' < 2 ^ 64) (hc : c ≤ 1) :
    b + b' ≤ 1 := by
  omega

/-- `u - s - t - c` with `s + t` less than `2^64` and `c` a bit, computed in 3 steps, and its borrow
from the first 2 steps or the last. -/
theorem sub2_borrow_cond {z2 z1 z u s t c : BitVec 64} (h2 : Defn z2 (u - s)) (h1 : Defn z1 (z2 - t))
    (h : Defn z (z1 - c)) (hst : s.toNat + t.toNat < 2 ^ 64) (hc : c.toNat ≤ 1) :
    z.toNat + s.toNat + t.toNat + c.toNat = u.toNat + 2 ^ 64 * (if u < z1 ∨ z1 < z then 1 else 0) := by
  rw [h.eq, h1.eq, h2.eq]
  have hu := u.isLt
  have e1 : (u - s - t).toNat = (u.toNat + (2 ^ 64 - (s.toNat + t.toNat))) % 2 ^ 64 := by
    rw [BitVec.toNat_sub, BitVec.toNat_sub]; omega
  have e2 : (u - s - t - c).toNat = ((u - s - t).toNat + (2 ^ 64 - c.toNat)) % 2 ^ 64 := by
    rw [BitVec.toNat_sub]; omega
  by_cases c1 : u < u - s - t <;> by_cases c2 : u - s - t < u - s - t - c <;>
    simp only [c1, c2, true_or, or_true, or_self, ↓reduceIte] <;>
    simp only [BitVec.lt_def] at c1 c2 <;> omega

/-- The two 2-word `submul()` of the words of the quotient and their borrows in the RV64 code of
`udivrem_top2<4>()`: the words `R` of `rw - q * vl` and the borrow out of them, from the definitions
of the values. -/
theorem top24_submul_words
    {r0 r1 r2 r3 v0 v1 q0 q1 p00 h00 p10 h10 p01 h01 p11 h11 R0 m1 m2 bw0 cm1 y1 cm2 y2 bm1 y1'
      B1h bm2 B0h bb R1 bq1 bb1 y2' B0 b6 R2 bb2 c z2 z1 R3 : BitVec 64}
    (hp00 : Defn p00 (v0 * q0)) (hh00 : Defn h00 (mulhu v0 q0)) (hp10 : Defn p10 (v1 * q0))
    (hp01 : Defn p01 (v0 * q1)) (hh01 : Defn h01 (mulhu v0 q1)) (hp11 : Defn p11 (v1 * q1))
    (hh11 : Defn h11 (mulhu v1 q1)) (hh10 : Defn h10 (mulhu v1 q0))
    (hR0 : Defn R0 (r0 - p00)) (hm1 : Defn m1 (p10 + h00)) (hm2 : Defn m2 (p11 + h01))
    (hbw0 : Defn bw0 (if r0 < R0 then 1#64 else 0#64))
    (hcm1 : Defn cm1 (if m1 < p10 then 1#64 else 0#64)) (hy1 : Defn y1 (r1 - m1))
    (hcm2 : Defn cm2 (if m2 < p11 then 1#64 else 0#64)) (hy2 : Defn y2 (r2 - m2))
    (hbm1 : Defn bm1 (if r1 < y1 then 1#64 else 0#64)) (hy1' : Defn y1' (y1 - bw0))
    (hB1h : Defn B1h (cm2 + h11)) (hbm2 : Defn bm2 (if r2 < y2 then 1#64 else 0#64))
    (hB0h : Defn B0h (cm1 + h10)) (hbb : Defn bb (if y1 < y1' then 1#64 else 0#64))
    (hR1 : Defn R1 (y1' - p01)) (hbq1 : Defn bq1 (if y1' < R1 then 1#64 else 0#64))
    (hbb1 : Defn bb1 (bm1 ||| bb)) (hy2' : Defn y2' (y2 - bq1)) (hB0 : Defn B0 (B0h + bb1))
    (hb6 : Defn b6 (if y2 < y2' then 1#64 else 0#64)) (hR2 : Defn R2 (y2' - B0))
    (hbb2 : Defn bb2 (bm2 ||| b6)) (hc : Defn c (if y2' < R2 then 1#64 else 0#64))
    (hz2 : Defn z2 (r3 - B1h)) (hz1 : Defn z1 (z2 - bb2)) (hR3 : Defn R3 (z1 - c)) :
    R0.toNat + 2 ^ 64 * (R1.toNat + 2 ^ 64 * (R2.toNat + 2 ^ 64 * R3.toNat)) +
        (q0.toNat + 2 ^ 64 * q1.toNat) * (v0.toNat + 2 ^ 64 * v1.toNat) =
      r0.toNat + 2 ^ 64 * (r1.toNat + 2 ^ 64 * (r2.toNat + 2 ^ 64 * r3.toNat)) +
        2 ^ 256 * (if r3 < z1 ∨ z1 < R3 then 1 else 0) := by
  have m00 := defn_mul_mulhu hp00 hh00
  have m10 := defn_mul_mulhu hp10 hh10
  have m01 := defn_mul_mulhu hp01 hh01
  have m11 := defn_mul_mulhu hp11 hh11
  have k00 := toNat_mul_le v0 q0
  have k10 := toNat_mul_le v1 q0
  have k01 := toNat_mul_le v0 q1
  have k11 := toNat_mul_le v1 q1
  have kh10 := defn_mulhu_le hh10
  have kh11 := defn_mulhu_le hh11
  have lbw0 := defn_bit_le hbw0
  have lcm1 := defn_bit_le hcm1
  have lcm2 := defn_bit_le hcm2
  have lbm1 := defn_bit_le hbm1
  have lbm2 := defn_bit_le hbm2
  have lbb := defn_bit_le hbb
  have lbq1 := defn_bit_le hbq1
  have lb6 := defn_bit_le hb6
  have lc := defn_bit_le hc
  have n0 := defn_sub_borrow0 hR0 hbw0
  have a1 := defn_carry_left hm1 hcm1
  have a2 := defn_carry_left hm2 hcm2
  have s1 := defn_sub_borrow0 hy1 hbm1
  have s2 := defn_sub_borrow0 hy2 hbm2
  have s1' := defn_sub_borrow0 hy1' hbb
  have sR1 := defn_sub_borrow0 hR1 hbq1
  have s2' := defn_sub_borrow0 hy2' hb6
  have sR2 := defn_sub_borrow0 hR2 hc
  have e1 := defn_add_exact hB1h (by clear * - lcm2 kh11; omega)
  have e0 := defn_add_exact hB0h (by clear * - lcm1 kh10; omega)
  have o1 : bb1.toNat = bm1.toNat + bb.toNat := by
    rw [hbb1.eq]
    exact or_bits_toNat lbm1 lbb (borrows_excl s1 s1' m1.isLt y1'.isLt lbw0)
  have o2 : bb2.toNat = bm2.toNat + b6.toNat := by
    rw [hbb2.eq]
    exact or_bits_toNat lbm2 lb6 (borrows_excl s2 s2' m2.isLt y2'.isLt lbq1)
  -- The first submul() of 2 words: rw[0..2) - q0 * vl with the high word B0.
  have hA : R0.toNat + 2 ^ 64 * y1'.toNat + v0.toNat * q0.toNat + 2 ^ 64 * (v1.toNat * q0.toNat) =
      r0.toNat + 2 ^ 64 * r1.toNat + 2 ^ 128 * (B0h.toNat + bb1.toNat) := by
    clear * - n0 m00 m10 a1 s1 s1' e0 o1; omega
  have hB0x := defn_add_exact hB0 (by
    have i0 := R0.isLt; have i1 := y1'.isLt
    clear * - hA k00 k10 i0 i1; omega)
  -- The second submul() of 2 words: rw[1..3) - q1 * vl with the high word B1h + bb2.
  have hB : R1.toNat + 2 ^ 64 * y2'.toNat + v0.toNat * q1.toNat + 2 ^ 64 * (v1.toNat * q1.toNat) =
      y1'.toNat + 2 ^ 64 * r2.toNat + 2 ^ 128 * (B1h.toNat + bb2.toNat) := by
    clear * - sR1 m01 m11 a2 s2 s2' e1 o2; omega
  have hD := sub2_borrow_cond hz2 hz1 hR3 (by
    have i0 := R1.isLt; have i1 := y2'.isLt
    clear * - hB k01 k11 i0 i1; omega) lc
  have hq : (q0.toNat + 2 ^ 64 * q1.toNat) * (v0.toNat + 2 ^ 64 * v1.toNat) =
      v0.toNat * q0.toNat + 2 ^ 64 * (v1.toNat * q0.toNat) + 2 ^ 64 * (v0.toNat * q1.toNat) +
        2 ^ 128 * (v1.toNat * q1.toNat) := by ring
  rw [hq]
  generalize (if r3 < z1 ∨ z1 < R3 then 1 else 0) = b at *
  clear * - hA hB sR2 hB0x hD; omega

theorem top24_submul_nb
    {r0 r1 r2 r3 v0 v1 q0 q1 p00 h00 p10 h10 p01 h01 p11 h11 R0 m1 m2 bw0 cm1 y1 cm2 y2 bm1 y1'
      B1h bm2 B0h bb R1 bq1 bb1 y2' B0 b6 R2 bb2 c z2 z1 R3 : BitVec 64}
    (hp00 : Defn p00 (v0 * q0)) (hh00 : Defn h00 (mulhu v0 q0)) (hp10 : Defn p10 (v1 * q0))
    (hp01 : Defn p01 (v0 * q1)) (hh01 : Defn h01 (mulhu v0 q1)) (hp11 : Defn p11 (v1 * q1))
    (hh11 : Defn h11 (mulhu v1 q1)) (hh10 : Defn h10 (mulhu v1 q0))
    (hR0 : Defn R0 (r0 - p00)) (hm1 : Defn m1 (p10 + h00)) (hm2 : Defn m2 (p11 + h01))
    (hbw0 : Defn bw0 (if r0 < R0 then 1#64 else 0#64))
    (hcm1 : Defn cm1 (if m1 < p10 then 1#64 else 0#64)) (hy1 : Defn y1 (r1 - m1))
    (hcm2 : Defn cm2 (if m2 < p11 then 1#64 else 0#64)) (hy2 : Defn y2 (r2 - m2))
    (hbm1 : Defn bm1 (if r1 < y1 then 1#64 else 0#64)) (hy1' : Defn y1' (y1 - bw0))
    (hB1h : Defn B1h (cm2 + h11)) (hbm2 : Defn bm2 (if r2 < y2 then 1#64 else 0#64))
    (hB0h : Defn B0h (cm1 + h10)) (hbb : Defn bb (if y1 < y1' then 1#64 else 0#64))
    (hR1 : Defn R1 (y1' - p01)) (hbq1 : Defn bq1 (if y1' < R1 then 1#64 else 0#64))
    (hbb1 : Defn bb1 (bm1 ||| bb)) (hy2' : Defn y2' (y2 - bq1)) (hB0 : Defn B0 (B0h + bb1))
    (hb6 : Defn b6 (if y2 < y2' then 1#64 else 0#64)) (hR2 : Defn R2 (y2' - B0))
    (hbb2 : Defn bb2 (bm2 ||| b6)) (hc : Defn c (if y2' < R2 then 1#64 else 0#64))
    (hz2 : Defn z2 (r3 - B1h)) (hz1 : Defn z1 (z2 - bb2)) (hR3 : Defn R3 (z1 - c))
    (hn1 : ¬r3 < z1) (hn2 : ¬z1 < R3) :
    R0.toNat + 2 ^ 64 * (R1.toNat + 2 ^ 64 * (R2.toNat + 2 ^ 64 * R3.toNat)) +
        (q0.toNat + 2 ^ 64 * q1.toNat) * (v0.toNat + 2 ^ 64 * v1.toNat) =
      r0.toNat + 2 ^ 64 * (r1.toNat + 2 ^ 64 * (r2.toNat + 2 ^ 64 * r3.toNat)) := by
  have h := top24_submul_words hp00 hh00 hp10 hp01 hh01 hp11 hh11 hh10 hR0 hm1 hm2 hbw0 hcm1 hy1 hcm2 hy2
    hbm1 hy1' hB1h hbm2 hB0h hbb hR1 hbq1 hbb1 hy2' hB0 hb6 hR2 hbb2 hc hz2 hz1 hR3
  rwa [if_neg (by tauto), Nat.mul_zero, Nat.add_zero] at h

theorem top24_submul_b
    {r0 r1 r2 r3 v0 v1 q0 q1 p00 h00 p10 h10 p01 h01 p11 h11 R0 m1 m2 bw0 cm1 y1 cm2 y2 bm1 y1'
      B1h bm2 B0h bb R1 bq1 bb1 y2' B0 b6 R2 bb2 c z2 z1 R3 : BitVec 64}
    (hp00 : Defn p00 (v0 * q0)) (hh00 : Defn h00 (mulhu v0 q0)) (hp10 : Defn p10 (v1 * q0))
    (hp01 : Defn p01 (v0 * q1)) (hh01 : Defn h01 (mulhu v0 q1)) (hp11 : Defn p11 (v1 * q1))
    (hh11 : Defn h11 (mulhu v1 q1)) (hh10 : Defn h10 (mulhu v1 q0))
    (hR0 : Defn R0 (r0 - p00)) (hm1 : Defn m1 (p10 + h00)) (hm2 : Defn m2 (p11 + h01))
    (hbw0 : Defn bw0 (if r0 < R0 then 1#64 else 0#64))
    (hcm1 : Defn cm1 (if m1 < p10 then 1#64 else 0#64)) (hy1 : Defn y1 (r1 - m1))
    (hcm2 : Defn cm2 (if m2 < p11 then 1#64 else 0#64)) (hy2 : Defn y2 (r2 - m2))
    (hbm1 : Defn bm1 (if r1 < y1 then 1#64 else 0#64)) (hy1' : Defn y1' (y1 - bw0))
    (hB1h : Defn B1h (cm2 + h11)) (hbm2 : Defn bm2 (if r2 < y2 then 1#64 else 0#64))
    (hB0h : Defn B0h (cm1 + h10)) (hbb : Defn bb (if y1 < y1' then 1#64 else 0#64))
    (hR1 : Defn R1 (y1' - p01)) (hbq1 : Defn bq1 (if y1' < R1 then 1#64 else 0#64))
    (hbb1 : Defn bb1 (bm1 ||| bb)) (hy2' : Defn y2' (y2 - bq1)) (hB0 : Defn B0 (B0h + bb1))
    (hb6 : Defn b6 (if y2 < y2' then 1#64 else 0#64)) (hR2 : Defn R2 (y2' - B0))
    (hbb2 : Defn bb2 (bm2 ||| b6)) (hc : Defn c (if y2' < R2 then 1#64 else 0#64))
    (hz2 : Defn z2 (r3 - B1h)) (hz1 : Defn z1 (z2 - bb2)) (hR3 : Defn R3 (z1 - c))
    (hb : r3 < z1 ∨ z1 < R3) :
    R0.toNat + 2 ^ 64 * (R1.toNat + 2 ^ 64 * (R2.toNat + 2 ^ 64 * R3.toNat)) +
        (q0.toNat + 2 ^ 64 * q1.toNat) * (v0.toNat + 2 ^ 64 * v1.toNat) =
      r0.toNat + 2 ^ 64 * (r1.toNat + 2 ^ 64 * (r2.toNat + 2 ^ 64 * r3.toNat)) + 2 ^ 256 := by
  have h := top24_submul_words hp00 hh00 hp10 hp01 hh01 hp11 hh11 hh10 hR0 hm1 hm2 hbw0 hcm1 hy1 hcm2 hy2
    hbm1 hy1' hB1h hbm2 hB0h hbb hR1 hbq1 hbb1 hy2' hB0 hb6 hR2 hbb2 hc hz2 hz1 hR3
  rwa [if_pos hb, Nat.mul_one] at h

/-- The quotient estimate times v from the remainder of `udivrem_top2<4>()`. -/
theorem top24_nat {U V q r0 R vl rw b Q : Nat} (hT : U / Q = q * (V / Q) + r0) (hvl : vl = V % Q)
    (hrw : rw = r0 * Q + U % Q) (hsm : R + q * vl = rw + 2 ^ 256 * b) :
    R + q * V = U + 2 ^ 256 * b := by
  calc R + q * V = R + q * (Q * (V / Q) + V % Q) := by rw [Nat.div_add_mod]
    _ = (R + q * vl) + Q * (q * (V / Q)) := by rw [hvl]; ring
    _ = rw + 2 ^ 256 * b + Q * (q * (V / Q)) := by rw [hsm]
    _ = Q * (q * (V / Q) + r0) + U % Q + 2 ^ 256 * b := by rw [hrw]; ring
    _ = Q * (U / Q) + U % Q + 2 ^ 256 * b := by rw [hT]
    _ = U + 2 ^ 256 * b := by rw [Nat.div_add_mod]

/-- The end of `udivrem_top2<4>()` of `uint320` from the `submul()` of the quotient words at 218:
the remainder `rw = r0 * Q + u mod Q` in `t5:a1:t1:t3`, `v mod Q` in `t4:a5` and the quotient in
`a7:t0`, for the quotient `q` and the remainder `r0` of `u / Q` by `v / Q`; s0 to s3 in the frame. -/
theorem top24_sub {hi : BitVec 20} {lo : BitVec 12} (base T : BitVec 64) (x : Regs) (m : Mem)
    (hpre : udivrem_top2_4_320.pre x m) (hr : x.get 1#5 &&& 3 = 0) (x' : Regs) (m' : Mem)
    (h10 : x'.get 10#5 = x.get 10#5) (h1 : x'.get 1#5 = x.get 1#5)
    (h12 : x'.get 12#5 = x.get 12#5) (h2 : x'.get 2#5 = x.get 2#5 + 18446744073709551584#64)
    (hcs : ∀ i ∈ calleeSaved, i ∉ [2#5, 8#5, 9#5, 18#5, 19#5] → x' i = x i)
    (hf : memWord m' (x.get 2#5 + 18446744073709551608#64).toNat = x.get 8#5 ∧
      memWord m' (x.get 2#5 + 18446744073709551600#64).toNat = x.get 9#5 ∧
      memWord m' (x.get 2#5 + 18446744073709551592#64).toNat = x.get 18#5 ∧
      memWord m' (x.get 2#5 + 18446744073709551584#64).toNat = x.get 19#5)
    (hm : UnchangedExcept2 m m' (x.get 10#5) 72 (x.get 2#5 - 32#64) 32)
    (hv0 : x'.get 15#5 = memWord m (x.get 12#5).toNat)
    (hv1 : x'.get 16#5 = memWord m (x.get 12#5 + 8#64).toNat) (r0 Q : Nat)
    (hD : 0 < words m (x.get 12#5) 4 / Q)
    (hT : words m (x.get 11#5) 5 / Q =
      ((x'.get 5#5).toNat + 2 ^ 64 * (x'.get 17#5).toNat) * (words m (x.get 12#5) 4 / Q) + r0)
    (hr0 : r0 < words m (x.get 12#5) 4 / Q)
    (hvl : (x'.get 15#5).toNat + 2 ^ 64 * (x'.get 29#5).toNat = words m (x.get 12#5) 4 % Q)
    (hrw : (x'.get 28#5).toNat + 2 ^ 64 * ((x'.get 11#5).toNat + 2 ^ 64 * ((x'.get 6#5).toNat +
      2 ^ 64 * (x'.get 30#5).toNat)) = r0 * Q + words m (x.get 11#5) 5 % Q) :
    Reach (bufWords (x.get 11#5) 5 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 9 ++
        bufWords (x.get 2#5 - 32#64) 4 ++ bufWords T 256) (udivrem_top2_4_320_progAt hi lo) base
      (pcAt base 218) x' m' (x.get 1#5) (udivrem_top2_4_320.post x m) := by
  have hpre' := hpre
  simp only [udivrem_top2_4_320.pre, Buf] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr, hv1', hv2,
    hu3⟩ := hpre'
  simp only [Disjoint] at hdrv hdsv
  have hsp : ∀ k ∈ [0, 8, 16, 24], x'.get 2#5 + BitVec.ofNat 64 k ∈
      bufWords (x.get 11#5) 5 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 9 ++
        bufWords (x.get 2#5 - 32#64) 4 ++ bufWords T 256 := by
    intro k hk
    rw [h2]
    exact List.mem_append_left _ (List.mem_append_right _ (frame32_mem _ k hk))
  obtain ⟨hf0, hf1, hf2, hf3⟩ := hf
  have hs0 : memWord m' (x'.get 2#5 + 24#64).toNat = x.get 8#5 := by
    rw [h2, show x.get 2#5 + 18446744073709551584#64 + 24#64 =
      x.get 2#5 + 18446744073709551608#64 by bv_omega]; exact hf0
  have hs1 : memWord m' (x'.get 2#5 + 16#64).toNat = x.get 9#5 := by
    rw [h2, show x.get 2#5 + 18446744073709551584#64 + 16#64 =
      x.get 2#5 + 18446744073709551600#64 by bv_omega]; exact hf1
  have hs2 : memWord m' (x'.get 2#5 + 8#64).toNat = x.get 18#5 := by
    rw [h2, show x.get 2#5 + 18446744073709551584#64 + 8#64 =
      x.get 2#5 + 18446744073709551592#64 by bv_omega]; exact hf2
  have hs3 : memWord m' (x'.get 2#5).toNat = x.get 19#5 := by rw [h2]; exact hf3
  have hV : 0 < words m (x.get 12#5) 4 := by
    have : 0 < 2 ^ (64 * 3) := by positivity
    omega
  have hw2 : memWord m' (x.get 12#5 + 16#64).toNat = memWord m (x.get 12#5 + 16#64).toNat :=
    memWord_of_unchangedExcept2 hm _ (by bv_omega) (by bv_omega)
  have hw3 : memWord m' (x.get 12#5 + 24#64).toNat = memWord m (x.get 12#5 + 24#64).toNat :=
    memWord_of_unchangedExcept2 hm _ (by bv_omega) (by bv_omega)
  rw [← h12]
  rw [← h12] at hsp
  rv_exec_cut 252
  -- The restore of s0 to s3 from the frame.
  refine Reach.step (by decide) rfl ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  refine ⟨hsp 24 (by simp), fun ws0 hws0 => ?_⟩
  refine Reach.step (by decide) rfl ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  refine ⟨hsp 16 (by simp), fun ws1 hws1 => ?_⟩
  refine Reach.step (by decide) rfl ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  refine ⟨hsp 8 (by simp), fun ws2 hws2 => ?_⟩
  refine Reach.step (by decide) rfl ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  refine ⟨by simpa using hsp 0 (by simp), fun ws3 hws3 => ?_⟩
  rw [hs0] at hws0
  rw [hs1] at hws1
  rw [hs2] at hws2
  rw [hs3] at hws3
  rv_exec_cut 262 274
  all_goals try simp only [zopz0zI_u_eq, decide_eq_true_eq, decide_eq_false_iff_not] at *
  all_goals try rv_conds
  all_goals
    simp only [Defn] at *
    subst_vars
    rw [h12]
  -- No borrow: the end.
  all_goals first
    | (rv_not_at 262; skip)
    | (have hs := top24_submul_nb (r0 := x'.get 28#5) (r1 := x'.get 11#5) (r2 := x'.get 6#5)
         (r3 := x'.get 30#5) (v0 := x'.get 15#5) (v1 := x'.get 29#5) (q0 := x'.get 5#5)
         (q1 := x'.get 17#5) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
         rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by assumption)
         (by assumption)
       refine top24_exit base T x m hpre hr _ _ ?_ ?_ ?_ hm ?_
       · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h10
       · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h1
       · intro i hi
         have hcs' := hcs i hi
         simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
         rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
           rfl | rfl
         all_goals simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
         all_goals first
           | exact hcs' (by decide)
           | exact (Regs.eq_get x (by decide)).symm
           | (rw [h2, Regs.eq_get x (by decide)]; bv_omega)
       · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
         exact top2_sub_exit_nat hV hD hT hr0 hvl hrw hs)
  -- A borrow: the words of v and the correction loop.
  all_goals
    have hs := top24_submul_b (r0 := x'.get 28#5) (r1 := x'.get 11#5) (r2 := x'.get 6#5)
      (r3 := x'.get 30#5) (v0 := x'.get 15#5) (v1 := x'.get 29#5) (q0 := x'.get 5#5)
      (q1 := x'.get 17#5) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by tauto)
    refine top24_loop base T x m hpre hr _ _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · exact h10
    · exact h1
    · intro i hi
      have hcs' := hcs i hi
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl
      all_goals simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
      all_goals first
        | exact hcs' (by decide)
        | exact (Regs.eq_get x (by decide)).symm
        | (rw [h2, Regs.eq_get x (by decide)]; bv_omega)
    · exact hm
    · rw [hv0, hv1, hw2, hw3]
      exact (words4_unfold m _).symm
    · exact top24_nat hT hvl hrw (by rw [hs, Nat.mul_one])

/-- A number of at least 2 words modulo `2^(128 - S)`: its low word and the next one modulo
`2^(64 - S)`. -/
theorem mod_two_low (a b r S : Nat) (ha : a < 2 ^ 64) (hS : S ≤ 64) :
    (a + 2 ^ 64 * (b + 2 ^ 64 * r)) % 2 ^ (128 - S) = a + 2 ^ 64 * (b % 2 ^ (64 - S)) := by
  have h : 2 ^ (128 - S) = 2 ^ 64 * 2 ^ (64 - S) := by rw [← pow_add]; congr 1; omega
  rw [h, Nat.mod_mul, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha,
    Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt ha, Nat.zero_add, mod_low _ _ _ hS]

/-- The 4-word remainder of `udivrem_top2<4>()`: `r0 * 2^(128 - S) + u mod 2^(128 - S)`, from u[0],
the shift of `u1 << S` and the words of `r0` right by `S`. -/
theorem top24_rw (u0 u1 r0 S U : Nat) (hS : S < 64)
    (hU : U % 2 ^ (128 - S) = u0 + 2 ^ 64 * (u1 % 2 ^ (64 - S))) :
    u0 + 2 ^ 64 * ((u1 * 2 ^ S % 2 ^ 64 + 2 ^ 64 * r0) / 2 ^ S) =
      r0 * 2 ^ (128 - S) + U % 2 ^ (128 - S) := by
  rw [top2_rw _ _ _ hS, hU,
    show (2 : Nat) ^ (128 - S) = 2 ^ 64 * 2 ^ (64 - S) by rw [← pow_add]; congr 1; omega]
  ring

/-- The end of `udivrem_top2<4>()` of `uint320` after the division of the top digits, from 200: the
quotient `q` in `a7:t0` and the remainder `r0` in `t2:t1` of `u / Q` by `v / Q` for
`Q = 2^(128 - s)`, the shift `s` in a3 and `~s` in a4; s0 to s3 in the frame. -/
theorem top24_shift {hi : BitVec 20} {lo : BitVec 12} (base T : BitVec 64) (x : Regs) (m : Mem)
    (hpre : udivrem_top2_4_320.pre x m) (hr : x.get 1#5 &&& 3 = 0) (x' : Regs) (m' : Mem)
    (h10 : x'.get 10#5 = x.get 10#5) (h1 : x'.get 1#5 = x.get 1#5)
    (h11 : x'.get 11#5 = x.get 11#5) (h12 : x'.get 12#5 = x.get 12#5)
    (h2 : x'.get 2#5 = x.get 2#5 + 18446744073709551584#64)
    (hcs : ∀ i ∈ calleeSaved, i ∉ [2#5, 8#5, 9#5, 18#5, 19#5] → x' i = x i)
    (hf : memWord m' (x.get 2#5 + 18446744073709551608#64).toNat = x.get 8#5 ∧
      memWord m' (x.get 2#5 + 18446744073709551600#64).toNat = x.get 9#5 ∧
      memWord m' (x.get 2#5 + 18446744073709551592#64).toNat = x.get 18#5 ∧
      memWord m' (x.get 2#5 + 18446744073709551584#64).toNat = x.get 19#5)
    (hm : UnchangedExcept2 m m' (x.get 10#5) 72 (x.get 2#5 - 32#64) 32)
    (hS : (x'.get 13#5).toNat < 64) (h14 : x'.get 14#5 = x'.get 13#5 ^^^ 18446744073709551615#64)
    (hD : 0 < words m (x.get 12#5) 4 / 2 ^ (128 - (x'.get 13#5).toNat))
    (hT : words m (x.get 11#5) 5 / 2 ^ (128 - (x'.get 13#5).toNat) =
      ((x'.get 5#5).toNat + 2 ^ 64 * (x'.get 17#5).toNat) *
        (words m (x.get 12#5) 4 / 2 ^ (128 - (x'.get 13#5).toNat)) +
      ((x'.get 6#5).toNat + 2 ^ 64 * (x'.get 7#5).toNat))
    (hr0 : (x'.get 6#5).toNat + 2 ^ 64 * (x'.get 7#5).toNat <
      words m (x.get 12#5) 4 / 2 ^ (128 - (x'.get 13#5).toNat)) :
    Reach (bufWords (x.get 11#5) 5 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 9 ++
        bufWords (x.get 2#5 - 32#64) 4 ++ bufWords T 256) (udivrem_top2_4_320_progAt hi lo) base
      (pcAt base 200) x' m' (x.get 1#5) (udivrem_top2_4_320.post x m) := by
  have hpre' := hpre
  simp only [udivrem_top2_4_320.pre, Buf] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr, -⟩ := hpre'
  simp only [Disjoint] at hdru hdrv hdsu hdsv
  have hv0m : memWord m' (x.get 12#5).toNat = memWord m (x.get 12#5).toNat :=
    memWord_of_unchangedExcept2 hm _ (by bv_omega) (by bv_omega)
  have hv1m : memWord m' (x.get 12#5 + 8#64).toNat = memWord m (x.get 12#5 + 8#64).toNat :=
    memWord_of_unchangedExcept2 hm _ (by bv_omega) (by bv_omega)
  have hu0m : memWord m' (x.get 11#5).toNat = memWord m (x.get 11#5).toNat :=
    memWord_of_unchangedExcept2 hm _ (by bv_omega) (by bv_omega)
  have hu1m : memWord m' (x.get 11#5 + 8#64).toNat = memWord m (x.get 11#5 + 8#64).toNat :=
    memWord_of_unchangedExcept2 hm _ (by bv_omega) (by bv_omega)
  -- The words v mod Q and u mod Q by the low 2 words.
  have hvq : words m (x.get 12#5) 4 % 2 ^ (128 - (x'.get 13#5).toNat) =
      (memWord m (x.get 12#5).toNat).toNat + 2 ^ 64 *
        ((memWord m (x.get 12#5 + 8#64).toNat).toNat % 2 ^ (64 - (x'.get 13#5).toNat)) := by
    rw [words4_unfold]; exact mod_two_low _ _ _ _ (BitVec.isLt _) (by omega)
  have huq : words m (x.get 11#5) 5 % 2 ^ (128 - (x'.get 13#5).toNat) =
      (memWord m (x.get 11#5).toNat).toNat + 2 ^ 64 *
        ((memWord m (x.get 11#5 + 8#64).toNat).toNat % 2 ^ (64 - (x'.get 13#5).toNat)) := by
    simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
      Nat.add_zero]
    exact mod_two_low _ _ _ _ (BitVec.isLt _) (by omega)
  have hz0 : x'.get 0#5 = 0#64 := by rw [show (0#5 : BitVec 5) = 0 from rfl, Regs.get_zero]; rfl
  rw [← h11, ← h12]
  rv_exec_cut 218
  all_goals
    simp only [Defn] at *
    subst_vars
    try simp only [hz0] at *
    try rw [h11]
    try rw [h12]
  all_goals
    refine top24_sub base T x m hpre hr _ _ ?_ ?_ ?_ ?_ ?_ hf hm ?_ ?_
      ((x'.get 6#5).toNat + 2 ^ 64 * (x'.get 7#5).toNat) (2 ^ (128 - (x'.get 13#5).toNat)) hD ?_
      hr0 ?_ ?_
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · exact h10
    · exact h1
    · exact h12
    · exact h2
    · intro i hi hx
      have hcs' := hcs i hi hx
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl
      all_goals simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at hx ⊢
      all_goals exact hcs'
    · exact hv0m
    · exact hv1m
    · exact hT
    · rw [toNat_and_mask _ _ hS, hv0m, hv1m, hvq]
    · rw [hu0m, hu1m]
      first
        | (-- s = 0: the words of u[1] and r0 not shifted.
           rv_get hb : x'.get 13#5 = 0#64
           have h0 : (x'.get 13#5).toNat = 0 := by rw [hb]; rfl
           rw [h0] at huq ⊢
           simp only [Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.ushiftRight_zero, Nat.sub_zero] at huq ⊢
           rw [huq, Nat.mod_eq_of_lt (BitVec.isLt _)]
           ring)
        | (-- s ≠ 0: the words of u[1] << s and r0 shifted right by s.
           rv_get hb : ¬x'.get 13#5 = 0#64
           have hS0 : 0 < (x'.get 13#5).toNat := by
             rcases Nat.eq_zero_or_pos (x'.get 13#5).toNat with h | h
             · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hb
             · exact h
           rw [h14, toNat_fshr_code _ _ _ hS hS0, toNat_fshr_code _ _ _ hS hS0,
             BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hS,
             BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, fshr3_words _ _ _ _ hS,
             top24_rw _ _ _ _ _ hS huq])

/-- The run of `udivrem_top2<4>()` of `uint320` from 78, where the paths of the normalization meet:
the normalized top words of v in `a5:a6` (vt), of u in `t2:a7:t1:t0` (t3:t2:t1:t0), the shift in a3
and its complement in a4. -/
theorem top24_main (hi : BitVec 20) (lo : BitVec 12) (base T : BitVec 64) (x : Regs) (m : Mem)
    (hT : pcAt base 84 + ((hi ++ 0x000#12).signExtend 64 + lo.signExtend 64) = T)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64) (hr : x.get 1#5 &&& 3 = 0)
    (hstk : (x.get 2#5 - 32#64).toNat + 32 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 2#5 - 32#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hpre : udivrem_top2_4_320.pre x m)
    (x' : Regs) (h10 : x'.get 10#5 = x.get 10#5) (h1 : x'.get 1#5 = x.get 1#5)
    (h11 : x'.get 11#5 = x.get 11#5) (h12 : x'.get 12#5 = x.get 12#5)
    (h2 : x'.get 2#5 = x.get 2#5) (hcs : ∀ i ∈ calleeSaved, x' i = x i)
    (hS : (x'.get 13#5).toNat < 64) (h14 : x'.get 14#5 = x'.get 13#5 ^^^ 18446744073709551615#64)
    (hDw : (x'.get 16#5).toNat + 2 ^ 64 * (x'.get 15#5).toNat =
      words m (x.get 12#5) 4 / 2 ^ (128 - (x'.get 13#5).toNat))
    (hd63 : 2 ^ 63 ≤ (x'.get 15#5).toNat)
    (hTw : (x'.get 5#5).toNat + 2 ^ 64 * ((x'.get 6#5).toNat + 2 ^ 64 * ((x'.get 17#5).toNat +
      2 ^ 64 * (x'.get 7#5).toNat)) = words m (x.get 11#5) 5 / 2 ^ (128 - (x'.get 13#5).toNat))
    (hT3 : (x'.get 7#5).toNat < (x'.get 15#5).toNat) :
    Reach (bufWords (x.get 11#5) 5 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 9 ++
        bufWords (x.get 2#5 - 32#64) 4 ++ bufWords T 256) (udivrem_top2_4_320_progAt hi lo) base
      (pcAt base 78) x' m (x.get 1#5) (udivrem_top2_4_320.post x m) := by
  have hpre0 := hpre
  simp only [udivrem_top2_4_320.pre, Buf] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr, hv1, hv2,
    hu3⟩ := hpre
  rw [← h2] at hstk hsn
  rw [← h2]
  rv_exec_cut 139
  simp only [hT] at *
  -- The table entry of vt: the low half.
  refine Reach.step (by decide) rfl ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  have ha := table_addr_by1 _ T hd63
  rv_fold ha
  have hix := index_lt_256 hd63
  rw [ha]
  refine ⟨Or.inl (List.mem_append_right _ (mem_bufWords hix)), fun wL hwL => ?_⟩
  try simp (disch := bv_omega) only [memHalf_memStore_of_ne] at hwL
  rw [memHalf_lo, holdsData_get hhold
      (by rw [show reciprocal_2by1_image_data.length = 256 from rfl]; exact hix),
    ← List.getD_eq_getElem _ 0, image_data_get _ hix] at hwL
  rv_exec_cut 139
  -- The high half.
  refine Reach.step (by decide) rfl ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  have hah := table_addr_by1_hi _ T hd63
  rv_fold hah
  rw [hah]
  refine ⟨Or.inr (by
    rw [show ∀ a : BitVec 64, a + 4 - 4#64 = a from fun a => by bv_omega]
    exact List.mem_append_right _ (mem_bufWords hix)), fun wH hwH => ?_⟩
  try simp (disch := bv_omega) only [memHalf_memStore_of_ne] at hwH
  rw [table_entry_add4 T hd63 hw, memHalf_hi, holdsData_get hhold
      (by rw [show reciprocal_2by1_image_data.length = 256 from rfl]; exact hix),
    ← List.getD_eq_getElem _ 0, image_data_get _ hix] at hwH
  rv_exec_cut 139
  -- The reciprocal of vt.
  rv_cse
  obtain ⟨hL, hH⟩ := table_LH hd63 hwL hwH
  have hv := recip3BV_spec (x'.get 16#5) (x'.get 15#5) wL wH hd63 hL hH
  simp only [recip3BV] at hv
  rw [show (0 : BitVec 64) = 0#64 from rfl] at hv
  rv_fold hv
  rv_fold hv
  have hlt : (x'.get 7#5).toNat * 2 ^ 64 + (x'.get 17#5).toNat <
      (x'.get 16#5).toNat + 2 ^ 64 * (x'.get 15#5).toNat := by
    have := (x'.get 17#5).isLt
    clear * - hT3 this
    omega
  have hD1 : 2 ^ 127 ≤ (x'.get 16#5).toNat + 2 ^ 64 * (x'.get 15#5).toNat := by
    clear * - hd63
    omega
  -- The first division of the top digits t3:t2:t1.
  refine Reach.trans (top24_div_top base _ _ ?_ ?_ ?_) ?_
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    exact hD1
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    exact hlt
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    exact hv
  intro x2 m2 ⟨hm2, h29, hq1, hr1, h02, hfr2⟩
  subst hm2
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte] at hq1 hr1
  have h29' : x2 29#5 = 0#64 := by rw [Regs.eq_get x2 (by decide)]; exact h29
  rw [regs_eq_sets _ x2 _ h02 hfr2]
  simp only [setRegs]
  rw [← Regs.eq_get x2 (by decide : (17#5 : BitVec 5) ≠ 0)] at hq1
  rw [← Regs.eq_get x2 (by decide : (6#5 : BitVec 5) ≠ 0),
    ← Regs.eq_get x2 (by decide : (7#5 : BitVec 5) ≠ 0)] at hr1
  have hX : (x2 7#5).toNat * 2 ^ 64 + (x2 6#5).toNat <
      (x'.get 16#5).toNat + 2 ^ 64 * (x'.get 15#5).toNat := by
    have := Nat.mod_lt ((x'.get 7#5).toNat * 2 ^ 128 + (x'.get 17#5).toNat * 2 ^ 64 +
      (x'.get 6#5).toNat) (Nat.lt_of_lt_of_le (Nat.two_pow_pos 127) hD1)
    calc (x2 7#5).toNat * 2 ^ 64 + (x2 6#5).toNat = (x2 6#5).toNat + 2 ^ 64 * (x2 7#5).toNat := by
          ring
      _ = _ := hr1
      _ < _ := this
  -- The second division of r1:t0 by vt.
  refine Reach.trans (top24_div_low base _ _ ?_ ?_ ?_ ?_) ?_
  all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · exact hD1
  · exact hX
  · exact hv
  · exact h29'
  intro x3 m3 ⟨hm3, hq0, hr0, h03, hfr3⟩
  subst hm3
  try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte] at hq0 hr0
  rw [← Regs.eq_get x3 (by decide : (5#5 : BitVec 5) ≠ 0)] at hq0
  rw [← Regs.eq_get x3 (by decide : (6#5 : BitVec 5) ≠ 0),
    ← Regs.eq_get x3 (by decide : (7#5 : BitVec 5) ≠ 0)] at hr0
  rw [regs_eq_sets _ x3 _ h03 hfr3]
  simp only [setRegs]
  have hdig := top2_digits hTw hq1 hr1 hq0 hr0
  rw [hDw] at hdig
  have hr0D : (x3 6#5).toNat + 2 ^ 64 * (x3 7#5).toNat <
      words m (x.get 12#5) 4 / 2 ^ (128 - (x'.get 13#5).toNat) := by
    rw [hr0, ← hDw]; exact Nat.mod_lt _ (Nat.lt_of_lt_of_le (Nat.two_pow_pos 127) hD1)
  rw [h2]
  obtain ⟨hf0, hf1, hf2, hf3⟩ := frame32_reads m (x.get 2#5) (x'.get 8#5) (x'.get 9#5)
    (x'.get 18#5) (x'.get 19#5)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hf0 hf1 hf2
  refine top24_shift base T x m hpre0 hr _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (unchangedExcept2_frame32_72 _ _ _ _ _ _ _ (h2 ▸ hsn)) ?_ ?_ ?_ ?_ ?_
  all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · exact h10
  · exact h1
  · exact h11
  · exact h12
  · intro i hi hx
    have hcs' := hcs i hi
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    all_goals simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at hx ⊢
    all_goals exact hcs'
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hf0, Regs.eq_get x' (by decide) |>.symm, hcs _ (by decide), Regs.eq_get x (by decide)]
    · rw [hf1, Regs.eq_get x' (by decide) |>.symm, hcs _ (by decide), Regs.eq_get x (by decide)]
    · rw [hf2, Regs.eq_get x' (by decide) |>.symm, hcs _ (by decide), Regs.eq_get x (by decide)]
    · rw [hf3, Regs.eq_get x' (by decide) |>.symm, hcs _ (by decide), Regs.eq_get x (by decide)]
  · exact hS
  · exact h14
  · rw [← hDw]; exact Nat.lt_of_lt_of_le (Nat.two_pow_pos 127) hD1
  · exact hdig
  · exact hr0D

/-- The shift amount `-s` of the 32-bit `subw`. -/
theorem top24_neg_amt : ∀ t < 64, (BitVec.signExtend 64 (BitVec.setWidth 32 0#64 -
    BitVec.setWidth 32 (BitVec.ofNat 64 t))).toNat % 64 = (64 - t) % 64 := by
  decide

/-- A number divided by `2^(128 - S)`: the words above its low word divided by `2^(64 - S)`. -/
theorem top24_div128 (a X S : Nat) (ha : a < 2 ^ 64) (hS : S ≤ 64) :
    (a + 2 ^ 64 * X) / 2 ^ (128 - S) = X / 2 ^ (64 - S) := by
  rw [show (2 : Nat) ^ (128 - S) = 2 ^ 64 * 2 ^ (64 - S) by rw [← pow_add]; congr 1; omega,
    ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt ha,
    Nat.zero_add]

end IntxRV.Api
