import IntxRV.DivBy1
import IntxRV.Knuth3
import IntxRV.Gen.Api.udivrem_by1_5
/-!
# The digits of `internal::udivrem_by1<5>()`

The 5-word instance of `udivrem_by1()` divides its 5 words without a loop: after the top digit,
each digit has its own inlined `udivrem_2by1()` (`div2by1BVa` for the digit 3, `div2by1BVb` for the
others, with the register a2 that holds 0 in the high word of the estimate) and its own registers.
`By15St` is the state at the division of a digit, like `by1Head` of the loop of the dynamic
instance (`IntxRV/DivBy1.lean`), and `by15_d3` to `by15_d0` run the digits 3 to 0, each to the
next one, with the funnel shift of the next digit for the shifts 0 and above.
-/

namespace IntxRV

/-- `udivrem_2by1()` as the first digit after the top one in `udivrem_by1<5>()` computes it, with
the register `z` that holds 0 times `u1` in the high word of the estimate. -/
def div2by1BVa (u1 u0 d v z : BitVec 64) : BitVec 64 × BitVec 64 :=
  let p0 := v * u1
  let p1 := mulhu v u1
  let q0 := p0 + u0
  let q1 := u1 + z * u1 + p1 + (if q0 < p0 then 1#64 else 0#64)
  let r := u0 - (q1 + 1#64) * d
  let q2 := if q0 < r then q1 else q1 + 1#64
  let r2 := ((0#64 - if q0 < r then 1#64 else 0#64) &&& d) + r
  let k := if r2 < d then 1#64 else 0#64
  (q2 + (k ^^^ 1#64), r2 - ((k + 18446744073709551615#64) &&& d))

/-- `udivrem_2by1()` as the other digits of `udivrem_by1<5>()` compute it. -/
def div2by1BVb (u1 u0 d v z : BitVec 64) : BitVec 64 × BitVec 64 :=
  let p0 := v * u1
  let p1 := mulhu v u1
  let q0 := p0 + u0
  let q1 := u1 + (p1 + z * u1) + (if q0 < p0 then 1#64 else 0#64)
  let r := u0 - (q1 + 1#64) * d
  let q2 := if q0 < r then q1 else q1 + 1#64
  let r2 := ((0#64 - if q0 < r then 1#64 else 0#64) &&& d) + r
  let k := if r2 < d then 1#64 else 0#64
  (q2 + (k ^^^ 1#64), r2 - ((k + 18446744073709551615#64) &&& d))

theorem div2by1BVa_spec (u1 u0 d v z : BitVec 64) (hz : z = 0#64) (hd : 2 ^ 63 ≤ d.toNat)
    (hu : u1.toNat < d.toNat) (hv : v.toNat = (2 ^ 128 - 1) / d.toNat - 2 ^ 64) :
    (div2by1BVa u1 u0 d v z).1.toNat = (2 ^ 64 * u1.toNat + u0.toNat) / d.toNat ∧
      (div2by1BVa u1 u0 d v z).2.toNat = (2 ^ 64 * u1.toNat + u0.toNat) % d.toNat := by
  subst hz
  have h := div2by1BV_spec u1 u0 d v hd hu hv
  simp only [div2by1BV, BitVec.mul_comm u1 v, mulhu_comm u1 v] at h
  simp only [div2by1BVa, BitVec.zero_mul, BitVec.add_zero]
  exact h

theorem div2by1BVb_spec (u1 u0 d v z : BitVec 64) (hz : z = 0#64) (hd : 2 ^ 63 ≤ d.toNat)
    (hu : u1.toNat < d.toNat) (hv : v.toNat = (2 ^ 128 - 1) / d.toNat - 2 ^ 64) :
    (div2by1BVb u1 u0 d v z).1.toNat = (2 ^ 64 * u1.toNat + u0.toNat) / d.toNat ∧
      (div2by1BVb u1 u0 d v z).2.toNat = (2 ^ 64 * u1.toNat + u0.toNat) % d.toNat := by
  subst hz
  have h := div2by1BV_spec u1 u0 d v hd hu hv
  simp only [div2by1BV, BitVec.mul_comm u1 v, mulhu_comm u1 v] at h
  simp only [div2by1BVb, BitVec.zero_mul, BitVec.add_zero]
  exact h

end IntxRV

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
-- The guards that select the paths do not change the goals.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- The state of `udivrem_by1<5>()` from the entry `x`, `m` at the 2/1 division of the digit `i`:
the normalized divisor `D` in a4, its reciprocal in a5, the shift in a3, 0 in a2, the remainder
`rem` of the digits above `i` in the register `rr` and the digit `i` of the shifted numerator in
`dr`, with the quotient words above `i` stored. -/
def By15St (x : Regs) (m : Mem) (i : Nat) (rr dr : BitVec 5) (x' : Regs) (m' : Mem) : Prop :=
  let S := 63 - Nat.log2 (x.get 12#5).toNat
  let D := (x.get 12#5).toNat * 2 ^ S
  let U := words m (x.get 11#5) 5
  (x'.get 14#5).toNat = D ∧ (x'.get 15#5).toNat = (2 ^ 128 - 1) / D - 2 ^ 64 ∧
  x'.get 13#5 = BitVec.ofNat 64 S ∧ x'.get 12#5 = 0#64 ∧ x'.get 10#5 = x.get 10#5 ∧
  (x'.get rr).toNat < D ∧ (x'.get dr).toNat = U * 2 ^ S / 2 ^ (64 * i) % 2 ^ 64 ∧
  words m' (x.get 10#5 + BitVec.ofNat 64 (8 * (i + 1))) (4 - i) * D + (x'.get rr).toNat =
    U * 2 ^ S / 2 ^ (64 * (i + 1)) ∧
  UnchangedExcept m m' (x.get 10#5) 40 ∧
  x'.get 1#5 = x.get 1#5 ∧ (∀ r ∈ calleeSaved, x'.get r = x.get r)

/-- The digit 0 of `udivrem_by1<5>()` from 216: the quotient word q[0], the remainder shifted back
and the return. -/
theorem by15_d0 {hi : BitVec 20} {lo : BitVec 12} {D : List (BitVec 64)} (base : BitVec 64)
    (x : Regs) (m : Mem) (hpre : udivrem_by1_5.pre x m) (hr : x.get 1#5 &&& 3 = 0) (x' : Regs)
    (m' : Mem) (h : By15St x m 0 11#5 5#5 x' m') :
    Reach (bufWords (x.get 11#5) 5 ++ bufWords (x.get 10#5) 5 ++ D) (udivrem_by1_5_progAt hi lo)
      base (pcAt base 216) x' m' (x.get 1#5) (udivrem_by1_5.post x m) := by
  obtain ⟨h14, h15, h13, h12, h10, hrem, hdig, hq, hu, h1, hcs⟩ := h
  have hpre' := hpre
  simp only [udivrem_by1_5.pre, Buf, Disjoint] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hqa, hqn⟩, ⟨hua, hun⟩, hdis, -, -, hdpos⟩ := hpre'
  have hd0 : (x.get 12#5).toNat ≠ 0 := by omega
  have hL : Nat.log2 (x.get 12#5).toNat < 64 := (Nat.log2_lt hd0).mpr (x.get 12#5).isLt
  have hd63 : 2 ^ 63 ≤ (x'.get 14#5).toNat := by
    rw [h14]; have := Nat.log2_self_le hd0
    calc 2 ^ 63 = 2 ^ Nat.log2 (x.get 12#5).toNat * 2 ^ (63 - Nat.log2 (x.get 12#5).toNat) := by
          rw [← pow_add]; congr 1; omega
      _ ≤ _ := Nat.mul_le_mul_right _ this
  have hv : (x'.get 15#5).toNat = (2 ^ 128 - 1) / (x'.get 14#5).toNat - 2 ^ 64 := by
    rw [h15, h14]
  have hrem' : (x'.get 11#5).toNat < (x'.get 14#5).toNat := by rw [h14]; exact hrem
  have hS : (x'.get 13#5).toNat % 64 = 63 - Nat.log2 (x.get 12#5).toNat := by
    rw [h13, ofNat_S_toNat (by omega)]; omega
  rv_exec_cut 240
  all_goals
    have hs := div2by1BVb_spec (x'.get 11#5) (x'.get 5#5) (x'.get 14#5) (x'.get 15#5)
      (x'.get 12#5) h12 hd63 hrem' hv
    simp only [div2by1BVb] at hs
    rv_fold hs
    try simp only [zopz0zI_u_eq, decide_eq_true_eq, decide_eq_false_iff_not] at *
    try simp (disch := assumption) only [if_pos, if_neg] at hs
    try simp only [BitVec.add_assoc] at hs
    rv_fold hs
    -- The word q[0] and the return.
    refine Reach.step (by decide) rfl ?_
    simp only [StepGoal, Nat.reduceAdd]
    rv_val
    rw [h10]
    refine ⟨List.mem_append_left _ (List.mem_append_right _ (mem_bufWords_zero (by norm_num))), ?_⟩
    rv_exec_cut
    rv_val
    rw [h1, update_aligned hr]
    refine Reach.refl ?_
    have hres := defn_shr_toNat ‹Defn _ ((_ : BitVec 64) >>> ((x'.get 13#5).toNat % 64))›
    rw [hS] at hres
    simp only [udivrem_by1_5.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    simp (disch := decide) only [Regs.eq_get x]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    rw [h14] at hs
    simp only [Nat.mul_zero, pow_zero, Nat.div_one, Nat.zero_add, Nat.mul_one,
      show 4 - 0 = 4 from rfl] at hdig hq
    obtain ⟨hfq, hfr⟩ := by1_final hdpos hq hdig hs.1 hs.2
    rw [words_memStore_first _ _ _ _ (by norm_num) hqn]
    refine ⟨hfq, hres.trans hfr, (unchangedExcept_memStore _ _ ⟨le_refl _, by omega⟩).mpr hu, ?_⟩
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte, BitVec.ofNat_eq_ofNat]
    simp (disch := decide) only [Regs.eq_get x']
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hcs
    exact hcs

/-- The facts of the normalized divisor of `udivrem_by1<5>()` in a state of `By15St`. -/
theorem by15_dn {x : Regs} {m : Mem} (hpre : udivrem_by1_5.pre x m) {x' : Regs}
    (h14 : (x'.get 14#5).toNat = (x.get 12#5).toNat * 2 ^ (63 - Nat.log2 (x.get 12#5).toNat)) :
    2 ^ 63 ≤ (x'.get 14#5).toNat ∧ Nat.log2 (x.get 12#5).toNat < 64 ∧ 0 < (x.get 12#5).toNat := by
  simp only [udivrem_by1_5.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨-, -, -, -, -, hdpos⟩ := hpre
  have hd0 : (x.get 12#5).toNat ≠ 0 := by omega
  have hL : Nat.log2 (x.get 12#5).toNat < 64 := (Nat.log2_lt hd0).mpr (x.get 12#5).isLt
  refine ⟨?_, hL, hdpos⟩
  rw [h14]; have := Nat.log2_self_le hd0
  calc 2 ^ 63 = 2 ^ Nat.log2 (x.get 12#5).toNat * 2 ^ (63 - Nat.log2 (x.get 12#5).toNat) := by
        rw [← pow_add]; congr 1; omega
    _ ≤ _ := Nat.mul_le_mul_right _ this

/-- The digit 1 of `udivrem_by1<5>()` from 191: the quotient word q[1] and the digit 0 from u[0]. -/
theorem by15_d1 {hi : BitVec 20} {lo : BitVec 12} {D : List (BitVec 64)} (base : BitVec 64)
    (x : Regs) (m : Mem) (hpre : udivrem_by1_5.pre x m) (hr : x.get 1#5 &&& 3 = 0) (x' : Regs)
    (m' : Mem) (h : By15St x m 1 5#5 17#5 x' m')
    (h11 : x'.get 11#5 = memWord m (x.get 11#5).toNat) :
    Reach (bufWords (x.get 11#5) 5 ++ bufWords (x.get 10#5) 5 ++ D) (udivrem_by1_5_progAt hi lo)
      base (pcAt base 191) x' m' (x.get 1#5) (udivrem_by1_5.post x m) := by
  obtain ⟨h14, h15, h13, h12, h10, hrem, hdig, hq, hu, h1, hcs⟩ := h
  have hpre' := hpre
  simp only [udivrem_by1_5.pre, Buf, Disjoint] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hqa, hqn⟩, ⟨hua, hun⟩, hdis, -, -, hdpos⟩ := hpre'
  obtain ⟨hd63, hL, -⟩ := by15_dn hpre h14
  have hv : (x'.get 15#5).toNat = (2 ^ 128 - 1) / (x'.get 14#5).toNat - 2 ^ 64 := by
    rw [h15, h14]
  have hrem' : (x'.get 5#5).toNat < (x'.get 14#5).toNat := by rw [h14]; exact hrem
  have hS : (x'.get 13#5).toNat % 64 = 63 - Nat.log2 (x.get 12#5).toNat := by
    rw [h13, ofNat_S_toNat (by omega)]; omega
  rv_exec_cut 215
  all_goals
    have hs := div2by1BVb_spec (x'.get 5#5) (x'.get 17#5) (x'.get 14#5) (x'.get 15#5)
      (x'.get 12#5) h12 hd63 hrem' hv
    simp only [div2by1BVb] at hs
    rv_fold hs
    try simp only [zopz0zI_u_eq, decide_eq_true_eq, decide_eq_false_iff_not] at *
    try simp (disch := assumption) only [if_pos, if_neg] at hs
    try simp only [BitVec.add_assoc] at hs
    rv_fold hs
    -- The word q[1].
    refine Reach.step (by decide) rfl ?_
    simp only [StepGoal, Nat.reduceAdd]
    rv_val
    rw [h10]
    refine ⟨List.mem_append_left _ (List.mem_append_right _ (mem_bufWords (i := 1) (by norm_num))),
      ?_⟩
    have hd0 := defn_shl_toNat ‹Defn _ (x'.get 11#5 <<< ((x'.get 13#5).toNat % 64))›
    rw [hS, h11, ← words_mul_mod m (x.get 11#5) 5 _ (by norm_num)] at hd0
    rw [h14] at hs
    obtain ⟨hqi, hri⟩ := hs
    rw [hdig] at hqi hri
    have hstep := div_step 1 hq hqi hri
    refine by15_d0 base x m hpre hr _ _ ?_
    simp only [By15St]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    have hq8 : (x.get 10#5 + 8#64).toNat = (x.get 10#5).toNat + 8 := by
      rw [BitVec.toNat_add]; simp; omega
    have hD : 0 < (x.get 12#5).toNat * 2 ^ (63 - Nat.log2 (x.get 12#5).toNat) :=
      Nat.mul_pos hdpos (Nat.two_pow_pos _)
    refine ⟨h14, h15, h13, h12, h10, hri ▸ Nat.mod_lt _ hD, by simpa using hd0, ?_,
      (unchangedExcept_memStore _ _ ⟨by omega, by omega⟩).mpr hu, h1, ?_⟩
    · rw [show x.get 10#5 + BitVec.ofNat 64 (8 * (0 + 1)) = x.get 10#5 + 8#64 from rfl,
        words_memStore_first _ _ _ _ (by norm_num) (by omega)]
      simpa [BitVec.add_assoc] using hstep
    · intro r hr
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;>
      simp (config := { decide := true }) only [↓reduceIte] <;>
      exact hcs _ (by decide)

/-- The digit 2 of `udivrem_by1<5>()` from 161: the quotient word q[2] and the digit 1 from u[1]
and u[0]. -/
theorem by15_d2 {hi : BitVec 20} {lo : BitVec 12} {D : List (BitVec 64)} (base : BitVec 64)
    (x : Regs) (m : Mem) (hpre : udivrem_by1_5.pre x m) (hr : x.get 1#5 &&& 3 = 0) (x' : Regs)
    (m' : Mem) (h : By15St x m 2 6#5 5#5 x' m')
    (h11 : x'.get 11#5 = x.get 11#5)
    (h17 : x'.get 17#5 = memWord m (x.get 11#5 + 8#64).toNat)
    (h16 : x'.get 16#5 = BitVec.ofNat 64 (63 - Nat.log2 (x.get 12#5).toNat) ^^^
      18446744073709551615#64) :
    Reach (bufWords (x.get 11#5) 5 ++ bufWords (x.get 10#5) 5 ++ D) (udivrem_by1_5_progAt hi lo)
      base (pcAt base 161) x' m' (x.get 1#5) (udivrem_by1_5.post x m) := by
  obtain ⟨h14, h15, h13, h12, h10, hrem, hdig, hq, hu, h1, hcs⟩ := h
  have hpre' := hpre
  simp only [udivrem_by1_5.pre, Buf, Disjoint] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hqa, hqn⟩, ⟨hua, hun⟩, hdis, -, -, hdpos⟩ := hpre'
  obtain ⟨hd63, hL, -⟩ := by15_dn hpre h14
  have hv : (x'.get 15#5).toNat = (2 ^ 128 - 1) / (x'.get 14#5).toNat - 2 ^ 64 := by
    rw [h15, h14]
  have hrem' : (x'.get 6#5).toNat < (x'.get 14#5).toNat := by rw [h14]; exact hrem
  have hS64 : 63 - Nat.log2 (x.get 12#5).toNat < 64 := by omega
  have hu0 : memWord m' (x.get 11#5).toNat = memWord m (x.get 11#5).toNat :=
    memWord_of_unchangedExcept hu _ (by omega)
  rw [← regs_set_of_get' (by decide) h11, ← regs_set_of_get' (by decide) h13,
    ← regs_set_of_get' (by decide) h16]
  rv_exec_cut 181
  all_goals
    -- The word q[2].
    refine Reach.step (by decide) rfl ?_
    simp only [StepGoal, Nat.reduceAdd]
    rv_val
    try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    rw [h10]
    refine ⟨List.mem_append_left _ (List.mem_append_right _ (mem_bufWords (i := 2) (by norm_num))),
      ?_⟩
    rv_exec_cut 191
  all_goals
    have hs := div2by1BVb_spec (x'.get 6#5) (x'.get 5#5) (x'.get 14#5) (x'.get 15#5)
      (x'.get 12#5) h12 hd63 hrem' hv
    simp only [div2by1BVb] at hs
    rv_fold hs
    try simp only [zopz0zI_u_eq, decide_eq_true_eq, decide_eq_false_iff_not] at *
    try simp (disch := assumption) only [if_pos, if_neg] at hs
    try simp only [BitVec.add_assoc] at hs
    rv_fold hs
    rw [h14] at hs
    obtain ⟨hqi, hri⟩ := hs
    rw [hdig] at hqi hri
    have hstep := div_step 2 hq hqi hri
    have hD : 0 < (x.get 12#5).toNat * 2 ^ (63 - Nat.log2 (x.get 12#5).toNat) :=
      Nat.mul_pos hdpos (Nat.two_pow_pos _)
    have hq16 : (x.get 10#5 + 16#64).toNat = (x.get 10#5).toNat + 16 := by
      rw [BitVec.toNat_add]; simp; omega
    have hw0 := (‹Defn _ (memWord m' (x.get 11#5).toNat)›).eq
    rw [hu0] at hw0
    first
      | (rv_has ¬BitVec.ofNat 64 (63 - (x.get 12#5).toNat.log2) = 0#64
         have hf := toNat_fshl_code (x'.get 17#5) (memWord m (x.get 11#5).toNat)
           (BitVec.ofNat 64 (63 - Nat.log2 (x.get 12#5).toNat)) (by rw [ofNat_S_toNat hS64]; exact hS64)
         rw [← hw0] at hf
         rv_fold hf
         rw [hw0, h17, ofNat_S_toNat hS64] at hf
         have hd1 := norm_digit m (x.get 11#5) 5 _ 1 hS64 le_rfl (by norm_num)
         simp only [wordAt, show 1 - 1 = 0 from rfl, Nat.mul_zero, Nat.mul_one, BitVec.add_zero]
           at hd1
         rw [← hd1] at hf
         refine by15_d1 base x m hpre hr _ _ ?_ ?_
         · simp only [By15St]
           simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
           refine ⟨h14, h15, trivial, h12, h10, hri ▸ Nat.mod_lt _ hD, ?_, ?_,
             (unchangedExcept_memStore _ _ ⟨by omega, by omega⟩).mpr hu, h1, ?_⟩
           · simpa using hf
           · rw [show x.get 10#5 + BitVec.ofNat 64 (8 * (1 + 1)) = x.get 10#5 + 16#64 from rfl,
               words_memStore_first _ _ _ _ (by norm_num) (by omega)]
             simpa [BitVec.add_assoc] using hstep
           · intro r hr
             simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
             rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
               rfl | rfl | rfl <;>
             simp (config := { decide := true }) only [↓reduceIte] <;>
             exact hcs _ (by decide)
         · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
           exact hw0)
      | (rv_has BitVec.ofNat 64 (63 - (x.get 12#5).toNat.log2) = 0#64
         rv_get hz : BitVec.ofNat 64 (63 - (x.get 12#5).toNat.log2) = 0#64
         have hS0 := ofNat_S_eq hS64 hz
         have hd1 : (memWord m (x.get 11#5 + 8#64).toNat).toNat = words m (x.get 11#5) 5 *
             2 ^ (63 - Nat.log2 (x.get 12#5).toNat) / 2 ^ (64 * 1) % 2 ^ 64 := by
           rw [norm_digit m (x.get 11#5) 5 _ 1 hS64 le_rfl (by norm_num), hS0]
           simp only [pow_zero, Nat.mul_one, Nat.sub_zero, wordAt]
           rw [Nat.div_eq_of_lt (BitVec.isLt _), Nat.add_zero, Nat.mod_eq_of_lt (BitVec.isLt _)]
         refine by15_d1 base x m hpre hr _ _ ?_ ?_
         · simp only [By15St]
           simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
           refine ⟨h14, h15, trivial, h12, h10, hri ▸ Nat.mod_lt _ hD, ?_, ?_,
             (unchangedExcept_memStore _ _ ⟨by omega, by omega⟩).mpr hu, h1, ?_⟩
           · rw [h17]; exact hd1
           · rw [show x.get 10#5 + BitVec.ofNat 64 (8 * (1 + 1)) = x.get 10#5 + 16#64 from rfl,
               words_memStore_first _ _ _ _ (by norm_num) (by omega)]
             simpa [BitVec.add_assoc] using hstep
           · intro r hr
             simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
             rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
               rfl | rfl | rfl <;>
             simp (config := { decide := true }) only [↓reduceIte] <;>
             exact hcs _ (by decide)
         · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
           exact hw0)

/-- The digit 3 of `udivrem_by1<5>()` from 131: the quotient word q[3] and the digit 2 from u[2]
and u[1]. -/
theorem by15_d3 {hi : BitVec 20} {lo : BitVec 12} {D : List (BitVec 64)} (base : BitVec 64)
    (x : Regs) (m : Mem) (hpre : udivrem_by1_5.pre x m) (hr : x.get 1#5 &&& 3 = 0) (x' : Regs)
    (m' : Mem) (h : By15St x m 3 6#5 17#5 x' m')
    (h11 : x'.get 11#5 = x.get 11#5)
    (h5' : Defn (x'.get 5#5) (memWord m (x.get 11#5 + 16#64).toNat))
    (h16 : x'.get 16#5 = BitVec.ofNat 64 (63 - Nat.log2 (x.get 12#5).toNat) ^^^
      18446744073709551615#64) :
    Reach (bufWords (x.get 11#5) 5 ++ bufWords (x.get 10#5) 5 ++ D) (udivrem_by1_5_progAt hi lo)
      base (pcAt base 131) x' m' (x.get 1#5) (udivrem_by1_5.post x m) := by
  have h5 := h5'.eq
  clear h5'
  obtain ⟨h14, h15, h13, h12, h10, hrem, hdig, hq, hu, h1, hcs⟩ := h
  have hpre' := hpre
  simp only [udivrem_by1_5.pre, Buf, Disjoint] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hqa, hqn⟩, ⟨hua, hun⟩, hdis, -, -, hdpos⟩ := hpre'
  obtain ⟨hd63, hL, -⟩ := by15_dn hpre h14
  have hv : (x'.get 15#5).toNat = (2 ^ 128 - 1) / (x'.get 14#5).toNat - 2 ^ 64 := by
    rw [h15, h14]
  have hrem' : (x'.get 6#5).toNat < (x'.get 14#5).toNat := by rw [h14]; exact hrem
  have hS64 : 63 - Nat.log2 (x.get 12#5).toNat < 64 := by omega
  have hu1 : memWord m' (x.get 11#5 + 8#64).toNat = memWord m (x.get 11#5 + 8#64).toNat :=
    memWord_of_unchangedExcept hu _ (by bv_omega)
  rw [← regs_set_of_get' (by decide) h11, ← regs_set_of_get' (by decide) h13,
    ← regs_set_of_get' (by decide) h16]
  rv_exec_cut 151
  all_goals
    -- The word q[3].
    refine Reach.step (by decide) rfl ?_
    simp only [StepGoal, Nat.reduceAdd]
    rv_val
    try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    rw [h10]
    refine ⟨List.mem_append_left _ (List.mem_append_right _ (mem_bufWords (i := 3) (by norm_num))),
      ?_⟩
    rv_exec_cut 161
  all_goals
    have hs := div2by1BVa_spec (x'.get 6#5) (x'.get 17#5) (x'.get 14#5) (x'.get 15#5)
      (x'.get 12#5) h12 hd63 hrem' hv
    simp only [div2by1BVa] at hs
    rv_fold hs
    try simp only [zopz0zI_u_eq, decide_eq_true_eq, decide_eq_false_iff_not] at *
    try simp (disch := assumption) only [if_pos, if_neg] at hs
    try simp only [BitVec.add_assoc] at hs
    rv_fold hs
    rw [h14] at hs
    obtain ⟨hqi, hri⟩ := hs
    rw [hdig] at hqi hri
    have hstep := div_step 3 hq hqi hri
    have hD : 0 < (x.get 12#5).toNat * 2 ^ (63 - Nat.log2 (x.get 12#5).toNat) :=
      Nat.mul_pos hdpos (Nat.two_pow_pos _)
    have hq24 : (x.get 10#5 + 24#64).toNat = (x.get 10#5).toNat + 24 := by
      rw [BitVec.toNat_add]; simp; omega
    have hw1 := (‹Defn _ (memWord m' (x.get 11#5 + 8#64).toNat)›).eq
    rw [hu1] at hw1
    first
      | (rv_has ¬BitVec.ofNat 64 (63 - (x.get 12#5).toNat.log2) = 0#64
         have hf := toNat_fshl_code (x'.get 5#5) (memWord m (x.get 11#5 + 8#64).toNat)
           (BitVec.ofNat 64 (63 - Nat.log2 (x.get 12#5).toNat)) (by rw [ofNat_S_toNat hS64]; exact hS64)
         rw [← hw1] at hf
         rv_fold hf
         rw [hw1, h5, ofNat_S_toNat hS64] at hf
         have hd2 := norm_digit m (x.get 11#5) 5 _ 2 hS64 (by norm_num) (by norm_num)
         simp only [wordAt, show 2 - 1 = 1 from rfl, Nat.mul_one] at hd2
         rw [← hd2] at hf
         refine by15_d2 base x m hpre hr _ _ ?_ ?_ ?_ ?_
         · simp only [By15St]
           simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
           refine ⟨h14, h15, trivial, h12, h10, hri ▸ Nat.mod_lt _ hD, ?_, ?_,
             (unchangedExcept_memStore _ _ ⟨by omega, by omega⟩).mpr hu, h1, ?_⟩
           · simpa using hf
           · rw [show x.get 10#5 + BitVec.ofNat 64 (8 * (2 + 1)) = x.get 10#5 + 24#64 from rfl,
               words_memStore_first _ _ _ _ (by norm_num) (by omega)]
             simpa [BitVec.add_assoc] using hstep
           · intro r hr
             simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
             rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
               rfl | rfl | rfl <;>
             simp (config := { decide := true }) only [↓reduceIte] <;>
             exact hcs _ (by decide)
         all_goals simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
         exact hw1)
      | (rv_has BitVec.ofNat 64 (63 - (x.get 12#5).toNat.log2) = 0#64
         rv_get hz : BitVec.ofNat 64 (63 - (x.get 12#5).toNat.log2) = 0#64
         have hS0 := ofNat_S_eq hS64 hz
         have hd2 : (memWord m (x.get 11#5 + 16#64).toNat).toNat = words m (x.get 11#5) 5 *
             2 ^ (63 - Nat.log2 (x.get 12#5).toNat) / 2 ^ (64 * 2) % 2 ^ 64 := by
           rw [norm_digit m (x.get 11#5) 5 _ 2 hS64 (by norm_num) (by norm_num), hS0]
           simp only [pow_zero, Nat.mul_one, Nat.sub_zero, wordAt]
           rw [Nat.div_eq_of_lt (BitVec.isLt _), Nat.add_zero, Nat.mod_eq_of_lt (BitVec.isLt _)]
         refine by15_d2 base x m hpre hr _ _ ?_ ?_ ?_ ?_
         · simp only [By15St]
           simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
           refine ⟨h14, h15, trivial, h12, h10, hri ▸ Nat.mod_lt _ hD, ?_, ?_,
             (unchangedExcept_memStore _ _ ⟨by omega, by omega⟩).mpr hu, h1, ?_⟩
           · rw [h5]; exact hd2
           · rw [show x.get 10#5 + BitVec.ofNat 64 (8 * (2 + 1)) = x.get 10#5 + 24#64 from rfl,
               words_memStore_first _ _ _ _ (by norm_num) (by omega)]
             simpa [BitVec.add_assoc] using hstep
           · intro r hr
             simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
             rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
               rfl | rfl | rfl <;>
             simp (config := { decide := true }) only [↓reduceIte] <;>
             exact hcs _ (by decide)
         all_goals simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
         exact hw1)

end IntxRV.Api
