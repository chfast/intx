import IntxRV.DivTop2
import IntxRV.Gen.Api.udivrem_top2_3_320

/-!
# The blocks of `udivrem_top2<3>()` of `uint320` by `uint256`

The code of the instance of `udivrem_top2<3>()` that `udivrem<320, 256>()` calls is the code of the
instance of `uint256` (`IntxRV/DivTop2.lean`) after the normalization, 2 instructions later, with
the register t2 for the top digit of the first `udivrem_3by2()` and the stores of a 5-word
quotient. The block lemmas here are those of `IntxRV/DivTop2.lean` for it.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- The first inlined `udivrem_3by2()` of `udivrem_top2<3>()` of `uint320`, from 142 to 172:
`t2:a1:t3` by `a6:a7` with the reciprocal in t4, to the quotient in a1 and the remainder in
`t3:t2`, with t5 0. -/
theorem top2_320_div_top {A : List (BitVec 64)} {hi : BitVec 20} {lo : BitVec 12} (base : BitVec 64)
    (x : Regs) (m : Mem)
    (hd : 2 ^ 127 ≤ (x.get 17#5).toNat + 2 ^ 64 * (x.get 16#5).toNat)
    (hu : (x.get 7#5).toNat * 2 ^ 64 + (x.get 11#5).toNat <
      (x.get 17#5).toNat + 2 ^ 64 * (x.get 16#5).toNat)
    (hv : (x.get 29#5).toNat =
      (2 ^ 192 - 1) / ((x.get 17#5).toNat + 2 ^ 64 * (x.get 16#5).toNat) - 2 ^ 64) :
    Reach A (udivrem_top2_3_320_progAt hi lo) base (pcAt base 142) x m (pcAt base 172) (fun x' m' =>
      m' = m ∧ x'.get 30#5 = 0#64 ∧ Div3Out x x' ((x.get 7#5).toNat * 2 ^ 128 +
        (x.get 11#5).toNat * 2 ^ 64 + (x.get 28#5).toNat)
        ((x.get 17#5).toNat + 2 ^ 64 * (x.get 16#5).toNat) 11#5 7#5 28#5
        [7#5, 8#5, 9#5, 11#5, 28#5, 30#5, 31#5]) := by
  rv_exec
  all_goals
    beta_reduce
    simp only [Div3Out]
    rv_cse
    have hs := div3by2BV_spec (x.get 7#5) (x.get 11#5) (x.get 28#5) (x.get 17#5) (x.get 16#5)
      (x.get 29#5) hd hu hv
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

/-- The second inlined `udivrem_3by2()` of `udivrem_top2<3>()` of `uint320`, from 172 to 208, with
the restore of s0 to s3 from the frame and of sp: `t3:t2:t1` by `a6:a7` with the reciprocal in t4
and t5 0, to the quotient in t1 and the remainder in `t3:t2`. -/
theorem top2_320_div_low {A : List (BitVec 64)} {hi : BitVec 20} {lo : BitVec 12} (base : BitVec 64)
    (x : Regs) (m : Mem)
    (hd : 2 ^ 127 ≤ (x.get 17#5).toNat + 2 ^ 64 * (x.get 16#5).toNat)
    (hu : (x.get 28#5).toNat * 2 ^ 64 + (x.get 7#5).toNat <
      (x.get 17#5).toNat + 2 ^ 64 * (x.get 16#5).toNat)
    (hv : (x.get 29#5).toNat =
      (2 ^ 192 - 1) / ((x.get 17#5).toNat + 2 ^ 64 * (x.get 16#5).toNat) - 2 ^ 64)
    (h30 : x.get 30#5 = 0#64)
    (hsp : ∀ k ∈ [0, 8, 16, 24], (x.get 2#5 + BitVec.ofNat 64 k) ∈ A) :
    Reach A (udivrem_top2_3_320_progAt hi lo) base (pcAt base 172) x m (pcAt base 208) (fun x' m' =>
      m' = m ∧ x'.get 2#5 = x.get 2#5 + 32#64 ∧
      x'.get 8#5 = memWord m (x.get 2#5 + 24#64).toNat ∧
      x'.get 9#5 = memWord m (x.get 2#5 + 16#64).toNat ∧
      x'.get 18#5 = memWord m (x.get 2#5 + 8#64).toNat ∧
      x'.get 19#5 = memWord m (x.get 2#5).toNat ∧
      Div3Out x x' ((x.get 28#5).toNat * 2 ^ 128 + (x.get 7#5).toNat * 2 ^ 64 +
        (x.get 6#5).toNat) ((x.get 17#5).toNat + 2 ^ 64 * (x.get 16#5).toNat) 6#5 7#5 28#5
        [2#5, 6#5, 7#5, 8#5, 9#5, 16#5, 17#5, 18#5, 19#5, 28#5, 29#5, 30#5, 31#5]) := by
  rv_exec
  -- The restore of s0 to s3 from the frame.
  all_goals
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
    rv_exec
  all_goals
    beta_reduce
    simp only [Div3Out]
    rv_cse
    rw [h30] at *
    have hs := div3by2BVz_spec (x.get 28#5) (x.get 7#5) (x.get 6#5) (x.get 17#5) (x.get 16#5)
      (x.get 29#5) hd hu hv
    simp only [div3by2BVz] at hs
    rv_fold hs
    rv_fold hs
    simp only [zopz0zI_u_eq, decide_eq_true_eq, decide_eq_false_iff_not, beq_eq_false_iff_ne,
      ne_eq] at *
    rv_conds
    simp (disch := assumption) only [if_pos, if_neg] at hs
    rv_fold hs
    rv_fold hs
    refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · exact hws0
    · exact hws1
    · exact hws2
    · exact hws3
    · exact hs.1
    · exact hs.2
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp (config := { decide := true }) only [Regs.set_apply, hr, ↓reduceIte]

/-- The result of a division of 5 words by 4 words stored as the quotient `q` of two words and the
remainder `a` of 3 words, in the order of the stores of `udivrem_top2<3>()` of `uint320`. -/
theorem words_ret9q2 (m : Mem) (r q0 q1 a0 a1 a2 z : BitVec 64) (hz : z = 0#64)
    (hr : r.toNat + 72 ≤ 2 ^ 64)
    (m' : Mem) (hm : m' = memStore (memStore (memStore (memStore (memStore (memStore (memStore
      (memStore (memStore m r.toNat q0) (r + 8#64).toNat q1) (r + 16#64).toNat z)
      (r + 24#64).toNat z) (r + 64#64).toNat z) (r + 32#64).toNat z) (r + 40#64).toNat a0)
      (r + 48#64).toNat a1) (r + 56#64).toNat a2) :
    words m' r 5 = q0.toNat + 2 ^ 64 * q1.toNat ∧
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

/-- The end of `udivrem_top2<3>()` of `uint320` from 241: the stores of the quotient in `a1:t2` and
the remainder in `a4:a3:a2`, and the return. -/
theorem top2_320_exit {hi : BitVec 20} {lo : BitVec 12} (base T : BitVec 64) (x : Regs) (m : Mem)
    (hpre : udivrem_top2_3_320.pre x m) (hr : x.get 1#5 &&& 3 = 0) (x' : Regs) (m' : Mem)
    (h10 : x'.get 10#5 = x.get 10#5) (h1 : x'.get 1#5 = x.get 1#5)
    (hcs : ∀ i ∈ calleeSaved, x' i = x i)
    (hm : UnchangedExcept2 m m' (x.get 10#5) 72 (x.get 2#5 - 32#64) 32)
    (hqr : (x'.get 7#5).toNat + 2 ^ 64 * (x'.get 11#5).toNat =
        words m (x.get 11#5) 5 / words m (x.get 12#5) 4 ∧
      (x'.get 12#5).toNat + 2 ^ 64 * ((x'.get 13#5).toNat + 2 ^ 64 * (x'.get 14#5).toNat) =
        words m (x.get 11#5) 5 % words m (x.get 12#5) 4) :
    Reach (bufWords (x.get 11#5) 5 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 9 ++
        bufWords (x.get 2#5 - 32#64) 4 ++ bufWords T 256) (udivrem_top2_3_320_progAt hi lo) base
      (pcAt base 241) x' m' (x.get 1#5) (udivrem_top2_3_320.post x m) := by
  have hpre' := hpre
  simp only [udivrem_top2_3_320.pre, Buf] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hra, hrn⟩, -⟩ := hpre'
  rw [← h10]
  have hrn' : (x'.get 10#5).toNat + 72 ≤ 2 ^ 64 := h10 ▸ hrn
  rv_exec
  rv_val
  rw [h1, update_aligned hr]
  refine Reach.refl ?_
  have hz : x'.get 0#5 = 0#64 := by rw [show (0#5 : BitVec 5) = 0 from rfl, Regs.get_zero]; rfl
  have hw := words_ret9q2 m' (x'.get 10#5) (x'.get 7#5) (x'.get 11#5) (x'.get 12#5) (x'.get 13#5)
    (x'.get 14#5) _ hz hrn' _ rfl
  simp only [udivrem_top2_3_320.post]
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

/-- The registers and the memory at the head of the correction loop of `udivrem_top2<3>()` of
`uint320`, at 254: `a5:a3:a4 + q * v = u + 2^192`, with the quotient `q` in `a1:t1` and the words of
v in `a6:a7:t0`; `n` the excess of `q`. -/
def top2_320Loop (x : Regs) (m : Mem) (n : Nat) (x' : Regs) (m' : Mem) : Prop :=
  x'.get 10#5 = x.get 10#5 ∧ x'.get 1#5 = x.get 1#5 ∧ (∀ i ∈ calleeSaved, x' i = x i) ∧
    UnchangedExcept2 m m' (x.get 10#5) 72 (x.get 2#5 - 32#64) 32 ∧
    (x'.get 16#5).toNat + 2 ^ 64 * ((x'.get 17#5).toNat + 2 ^ 64 * (x'.get 5#5).toNat) =
      words m (x.get 12#5) 4 ∧
    (x'.get 15#5).toNat + 2 ^ 64 * ((x'.get 13#5).toNat + 2 ^ 64 * (x'.get 14#5).toNat) +
      ((x'.get 6#5).toNat + 2 ^ 64 * (x'.get 11#5).toNat) * words m (x.get 12#5) 4 =
      words m (x.get 11#5) 5 + 2 ^ 192 ∧
    n = (x'.get 6#5).toNat + 2 ^ 64 * (x'.get 11#5).toNat -
      words m (x.get 11#5) 5 / words m (x.get 12#5) 4

/-- The correction loop of `udivrem_top2<3>()` of `uint320` from 254. -/
theorem top2_320_loop {hi : BitVec 20} {lo : BitVec 12} (base T : BitVec 64) (x : Regs) (m : Mem)
    (hpre : udivrem_top2_3_320.pre x m) (hr : x.get 1#5 &&& 3 = 0) :
    ∀ n x' m', top2_320Loop x m n x' m' →
    Reach (bufWords (x.get 11#5) 5 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 9 ++
        bufWords (x.get 2#5 - 32#64) 4 ++ bufWords T 256) (udivrem_top2_3_320_progAt hi lo) base
      (pcAt base 254) x' m' (x.get 1#5) (udivrem_top2_3_320.post x m) := by
  apply Reach.loop (top2_320Loop x m)
  intro n x' m' h ih
  obtain ⟨h10, h1, hcs, hm, hv, hsm, hn⟩ := h
  have hR := words3_lt (x'.get 15#5) (x'.get 13#5) (x'.get 14#5)
  have hlt := top2_q_gt hR hsm
  rv_step
  rv_exec_cut 241 254
  all_goals try simp only [zopz0zI_u_eq, decide_eq_true_eq, decide_eq_false_iff_not] at *
  all_goals try rv_conds
  -- The sum r + v and the quotient less 1, from the values of the run.
  all_goals
    simp only [Defn] at *
    subst_vars
    have hd := dec2_toNat (q0 := x'.get 6#5) (q1 := x'.get 11#5) rfl rfl
      (Nat.lt_of_le_of_lt (Nat.zero_le _) hlt)
  -- A carry out of r + v: the end.
  all_goals first
    | (rv_not_at 241; skip)
    | (have ha := add3c_carry (r0 := x'.get 15#5) (r1 := x'.get 13#5) (r2 := x'.get 14#5)
         (v0 := x'.get 16#5) (v1 := x'.get 17#5) (v2 := x'.get 5#5) rfl rfl rfl rfl rfl rfl rfl rfl rfl
         (by tauto)
       rw [hv] at ha
       refine top2_320_exit base T x m hpre hr _ _ ?_ ?_ ?_ hm ?_
       · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h10
       · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h1
       · refine calleeSaved_of hcs _ ?_
         intro i hi
         simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
         rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
           rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
       · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
         exact top2_exit_nat ha hd hsm hR)
  -- No carry: the next correction.
  all_goals
    have ha := add3c_nocarry (r0 := x'.get 15#5) (r1 := x'.get 13#5) (r2 := x'.get 14#5)
      (v0 := x'.get 16#5) (v1 := x'.get 17#5) (v2 := x'.get 5#5) rfl rfl rfl rfl rfl rfl rfl rfl rfl
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
    · exact top2_cont_nat ha hd hsm

/-- The end of `udivrem_top2<3>()` of `uint320` from the `submul()` of the quotient words at 222:
the remainder `rw = r0 * Q + u mod Q` in `a7:t2:a6`, `v mod Q` in a3 and the quotient in `a1:t1`,
for the quotient `q` and the remainder `r0` of `u / Q` by `v / Q`. -/
theorem top2_320_sub {hi : BitVec 20} {lo : BitVec 12} (base T : BitVec 64) (x : Regs) (m : Mem)
    (hpre : udivrem_top2_3_320.pre x m) (hr : x.get 1#5 &&& 3 = 0) (x' : Regs) (m' : Mem)
    (h10 : x'.get 10#5 = x.get 10#5) (h1 : x'.get 1#5 = x.get 1#5)
    (h12 : x'.get 12#5 = x.get 12#5) (hcs : ∀ i ∈ calleeSaved, x' i = x i)
    (hm : UnchangedExcept2 m m' (x.get 10#5) 72 (x.get 2#5 - 32#64) 32) (r0 Q : Nat)
    (hD : 0 < words m (x.get 12#5) 4 / Q)
    (hT : words m (x.get 11#5) 5 / Q =
      ((x'.get 6#5).toNat + 2 ^ 64 * (x'.get 11#5).toNat) * (words m (x.get 12#5) 4 / Q) + r0)
    (hr0 : r0 < words m (x.get 12#5) 4 / Q)
    (hvl : (x'.get 13#5).toNat = words m (x.get 12#5) 4 % Q)
    (hrw : (x'.get 16#5).toNat + 2 ^ 64 * ((x'.get 7#5).toNat + 2 ^ 64 * (x'.get 17#5).toNat) =
      r0 * Q + words m (x.get 11#5) 5 % Q) :
    Reach (bufWords (x.get 11#5) 5 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 9 ++
        bufWords (x.get 2#5 - 32#64) 4 ++ bufWords T 256) (udivrem_top2_3_320_progAt hi lo) base
      (pcAt base 222) x' m' (x.get 1#5) (udivrem_top2_3_320.post x m) := by
  have hpre' := hpre
  simp only [udivrem_top2_3_320.pre, Buf] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr, hv1, hv2,
    hu3⟩ := hpre'
  simp only [Disjoint] at hdrv hdsv
  have hV : 0 < words m (x.get 12#5) 4 := by
    have : 0 < 2 ^ (64 * 2) := by positivity
    omega
  have hv3 := top4_zero m (x.get 12#5) hv2
  have hw0 : memWord m' (x.get 12#5).toNat = memWord m (x.get 12#5).toNat :=
    memWord_of_unchangedExcept2 hm _ (by bv_omega) (by bv_omega)
  have hw1 : memWord m' (x.get 12#5 + 8#64).toNat = memWord m (x.get 12#5 + 8#64).toNat :=
    memWord_of_unchangedExcept2 hm _ (by bv_omega) (by bv_omega)
  have hw2 : memWord m' (x.get 12#5 + 16#64).toNat = memWord m (x.get 12#5 + 16#64).toNat :=
    memWord_of_unchangedExcept2 hm _ (by bv_omega) (by bv_omega)
  rw [← h12]
  rv_exec_cut 241 254
  all_goals try simp only [zopz0zI_u_eq, decide_eq_true_eq, decide_eq_false_iff_not] at *
  all_goals try rv_conds
  all_goals
    simp only [Defn] at *
    subst_vars
    rw [h12]
  -- No borrow: the end.
  all_goals first
    | (rv_not_at 241; skip)
    | (have hs := top2_submul_nb (rw0 := x'.get 16#5) (rw1 := x'.get 7#5) (rw2 := x'.get 17#5)
         (vl := x'.get 13#5) (q0 := x'.get 6#5) (q1 := x'.get 11#5) rfl rfl rfl rfl rfl rfl rfl rfl
         rfl rfl rfl rfl rfl rfl (by assumption) (by assumption)
       refine top2_320_exit base T x m hpre hr _ _ ?_ ?_ ?_ hm ?_
       · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h10
       · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h1
       · refine calleeSaved_of hcs _ ?_
         intro i hi
         simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
         rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
           rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
       · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
         exact top2_sub_exit_nat hV hD hT hr0 hvl hrw hs)
  -- A borrow: the words of v and the correction loop.
  all_goals
    have hs := top2_submul_b (rw0 := x'.get 16#5) (rw1 := x'.get 7#5) (rw2 := x'.get 17#5)
      (vl := x'.get 13#5) (q0 := x'.get 6#5) (q1 := x'.get 11#5) rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl rfl rfl (by tauto)
    refine top2_320_loop base T x m hpre hr _ _ _ ⟨?_, ?_, ?_, hm, ?_, ?_, rfl⟩
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · exact h10
    · exact h1
    · refine calleeSaved_of hcs _ ?_
      intro i hi
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    · rw [hw0, hw1, hw2]
      exact words_v3 m _ hv3
    · exact top2_nat hT hvl hrw (by rw [hs, Nat.mul_one])

/-- The end of `udivrem_top2<3>()` of `uint320` after the division of the top digits, from 208: the
quotient `q` in `a1:t1` and the remainder `r0` in `t3:t2` of `u / Q` by `v / Q` for `Q = 2^(64 -
s)`, the shift `s` in a4 and `~s` in a5, and the words u[0] in t0 and v[0] in a3. -/
theorem top2_320_shift {hi : BitVec 20} {lo : BitVec 12} (base T : BitVec 64) (x : Regs) (m : Mem)
    (hpre : udivrem_top2_3_320.pre x m) (hr : x.get 1#5 &&& 3 = 0) (x' : Regs) (m' : Mem)
    (h10 : x'.get 10#5 = x.get 10#5) (h1 : x'.get 1#5 = x.get 1#5)
    (h12 : x'.get 12#5 = x.get 12#5) (hcs : ∀ i ∈ calleeSaved, x' i = x i)
    (hm : UnchangedExcept2 m m' (x.get 10#5) 72 (x.get 2#5 - 32#64) 32)
    (hS : (x'.get 14#5).toNat < 64) (h15 : x'.get 15#5 = x'.get 14#5 ^^^ 18446744073709551615#64)
    (hv0 : x'.get 13#5 = memWord m (x.get 12#5).toNat)
    (hu0 : x'.get 5#5 = memWord m (x.get 11#5).toNat)
    (hD : 0 < words m (x.get 12#5) 4 / 2 ^ (64 - (x'.get 14#5).toNat))
    (hT : words m (x.get 11#5) 5 / 2 ^ (64 - (x'.get 14#5).toNat) =
      ((x'.get 6#5).toNat + 2 ^ 64 * (x'.get 11#5).toNat) *
        (words m (x.get 12#5) 4 / 2 ^ (64 - (x'.get 14#5).toNat)) +
      ((x'.get 7#5).toNat + 2 ^ 64 * (x'.get 28#5).toNat))
    (hr0 : (x'.get 7#5).toNat + 2 ^ 64 * (x'.get 28#5).toNat <
      words m (x.get 12#5) 4 / 2 ^ (64 - (x'.get 14#5).toNat)) :
    Reach (bufWords (x.get 11#5) 5 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 9 ++
        bufWords (x.get 2#5 - 32#64) 4 ++ bufWords T 256) (udivrem_top2_3_320_progAt hi lo) base
      (pcAt base 208) x' m' (x.get 1#5) (udivrem_top2_3_320.post x m) := by
  -- The words v mod Q and u mod Q by the low words.
  have hvq : words m (x.get 12#5) 4 % 2 ^ (64 - (x'.get 14#5).toNat) =
      (memWord m (x.get 12#5).toNat).toNat % 2 ^ (64 - (x'.get 14#5).toNat) := by
    simp only [words]; exact mod_low _ _ _ (by omega)
  have huq : words m (x.get 11#5) 5 % 2 ^ (64 - (x'.get 14#5).toNat) =
      (memWord m (x.get 11#5).toNat).toNat % 2 ^ (64 - (x'.get 14#5).toNat) := by
    simp only [words]; exact mod_low _ _ _ (by omega)
  have hz0 : x'.get 0#5 = 0#64 := by rw [show (0#5 : BitVec 5) = 0 from rfl, Regs.get_zero]; rfl
  have hPQ : 2 ^ (x'.get 14#5).toNat * 2 ^ (64 - (x'.get 14#5).toNat) = 2 ^ 64 := by
    rw [← pow_add]; congr 1; omega
  rv_exec_cut 222
  all_goals
    simp only [Defn] at *
    subst_vars
    simp only [hz0, BitVec.zero_add] at *
  all_goals
    refine top2_320_sub base T x m hpre hr _ _ ?_ ?_ ?_ ?_ hm
      ((x'.get 7#5).toNat + 2 ^ 64 * (x'.get 28#5).toNat) (2 ^ (64 - (x'.get 14#5).toNat)) hD ?_
      hr0 ?_ ?_
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    all_goals try assumption
    · refine calleeSaved_of hcs _ ?_
      intro i hi
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    · rw [hvq, toNat_and_mask _ _ hS, hv0]
    · rw [huq, ← hu0]
      first
        | (-- s = 0: the words of u[0] and r0 not shifted.
           rv_get hb : x'.get 14#5 = 0#64
           have h0 : (x'.get 14#5).toNat = 0 := by rw [hb]; rfl
           simp only [h0, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.ushiftRight_zero, Nat.sub_zero]
           rw [Nat.mod_eq_of_lt (x'.get 5#5).isLt]
           ring)
        | (-- s ≠ 0: the words of u[0] << s and r0 shifted right by s.
           rv_get hb : ¬x'.get 14#5 = 0#64
           have hS0 : 0 < (x'.get 14#5).toNat := by
             rcases Nat.eq_zero_or_pos (x'.get 14#5).toNat with h | h
             · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hb
             · exact h
           rw [h15, toNat_fshr_code _ _ _ hS hS0, toNat_fshr_code _ _ _ hS hS0,
             BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hS,
             BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, fshr3_words _ _ _ _ hS,
             top2_rw _ _ _ hS])

/-- The word u[4] of u above the top word of v is less than v[2], with v[3] = 0. -/
theorem top2_320_ue (m : Mem) (u v : BitVec 64)
    (h : words m u 5 / 2 ^ (64 * (3 + 1)) < words m v 4 / 2 ^ (64 * (3 - 1)) + 0)
    (h3 : memWord m (v + 24#64).toNat = 0#64) :
    (memWord m (u + 32#64).toNat).toNat < (memWord m (v + 16#64).toNat).toNat := by
  simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
    Nat.add_zero] at h
  rw [h3, BitVec.toNat_ofNat, Nat.zero_mod] at h
  have := (memWord m u.toNat).isLt
  have := (memWord m (u + 8#64).toNat).isLt
  have := (memWord m (u + 16#64).toNat).isLt
  have := (memWord m (u + 24#64).toNat).isLt
  have := (memWord m v.toNat).isLt
  have := (memWord m (v + 8#64).toNat).isLt
  omega

/-- The normalized words of u of 5 words shifted left by `S < 64`, without the low word, when the
top word has no bits above `64 - S`. -/
theorem norm5_words (u0 u1 u2 u3 ue S : Nat) (h0 : u0 < 2 ^ 64) (h1 : u1 < 2 ^ 64)
    (h2 : u2 < 2 ^ 64) (h3 : u3 < 2 ^ 64) (he : ue < 2 ^ (64 - S)) (hS : S < 64) :
    (u1 * 2 ^ S + u0 / 2 ^ (64 - S)) % 2 ^ 64 + 2 ^ 64 * ((u2 * 2 ^ S + u1 / 2 ^ (64 - S)) % 2 ^ 64 +
      2 ^ 64 * ((u3 * 2 ^ S + u2 / 2 ^ (64 - S)) % 2 ^ 64 +
        2 ^ 64 * ((ue * 2 ^ S + u3 / 2 ^ (64 - S)) % 2 ^ 64))) =
    (u1 + 2 ^ 64 * (u2 + 2 ^ 64 * (u3 + 2 ^ 64 * ue))) * 2 ^ S + u0 / 2 ^ (64 - S) := by
  have hPQ : 2 ^ (64 - S) * 2 ^ S = 2 ^ 64 := by rw [← pow_add]; congr 1; omega
  have he' : ue < 2 ^ 64 := lt_of_lt_of_le he (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h4 := norm4_words u1 u2 u3 ue S h1 h2 h3 he' hS
  have hz : ue / 2 ^ (64 - S) = 0 := Nat.div_eq_of_lt he
  rw [hz, Nat.mul_zero, Nat.add_zero] at h4
  have hut := top1_ut u0 u1 S hS h0
  have e : (u1 + 2 ^ 64 * (u2 + 2 ^ 64 * (u3 + 2 ^ 64 * ue))) * 2 ^ S + u0 / 2 ^ (64 - S) =
      (u1 * 2 ^ S + u0 / 2 ^ (64 - S)) + 2 ^ 64 * ((u2 + 2 ^ 64 * (u3 + 2 ^ 64 * ue)) * 2 ^ S) := by
    ring
  rw [e, ← hut, ← Nat.add_sub_cancel ((u2 + 2 ^ 64 * (u3 + 2 ^ 64 * ue)) * 2 ^ S)
    (u1 / 2 ^ (64 - S)), ← h4]
  omega

/-- The stores of s0 to s3 below sp are in the stack frame of `udivrem_top2<3>()` of `uint320`. -/
theorem unchangedExcept2_frame32_72 (m : Mem) (r sp a b c d : BitVec 64)
    (hs : (sp - 32#64).toNat + 32 ≤ 2 ^ 64) :
    UnchangedExcept2 m (memStore (memStore (memStore (memStore m
      (sp + 18446744073709551608#64).toNat a) (sp + 18446744073709551600#64).toNat b)
      (sp + 18446744073709551592#64).toNat c) (sp + 18446744073709551584#64).toNat d)
      r 72 (sp - 32#64) 32 := by
  simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
  exact unchangedExcept2_refl _ _ _ _ _

end IntxRV.Api
