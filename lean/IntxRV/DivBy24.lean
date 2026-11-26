import IntxRV.DivBy2
import IntxRV.Knuth3
import IntxRV.Gen.Api.udivrem_by2_4
/-!
# The digits of `internal::udivrem_by2<4>()`

The instance of `udivrem_by2()` for a quotient of 4 words divides the 5 words of u without a loop:
after the top digits, the code inlines `udivrem_3by2()` for each of the digits 2, 1 and 0, with the
products in other orders than `udivrem_3by2()` itself and registers that hold 0 in some of the
products (`div3by2BVc`, `div3by2BVd` and `div3by2BVe`). `by24_b1` to `by24_b3` run the copies of the
top digits and of the digits 2 and 1 to their ends (`by24_div3_paths`, as `by2_div3_paths` of
`IntxRV/DivBy2.lean`), and `by24_sub_top` the subtraction when u[4] is at most the top word of d.
`By24St` is the state at the division of a digit, and `by24_d2` to `by24_d0` run the digits 2 to 0,
each to the next one.
-/

namespace IntxRV

/-- `udivrem_3by2()` as the digit 2 of `udivrem_by2<4>()` computes it, with the register `z` that
holds 0 times `u2` in the high word of the estimate. -/
def div3by2BVc (u2 u1 u0 d0 d1 v z : BitVec 64) : BitVec 64 × BitVec 64 × BitVec 64 :=
  let p0 := v * u2
  let p1 := mulhu v u2
  let q0 := p0 + u1
  let q1 := u2 + z * u2 + p1 + (if q0 < p0 then 1#64 else 0#64)
  let rd0 := u0 - q1 * d0
  let rd1 := u1 - (d1 * q1 + mulhu q1 d0) - (if u0 < rd0 then 1#64 else 0#64)
  let r0 := rd0 - d0
  let r1 := rd1 - d1 - (if rd0 < r0 then 1#64 else 0#64)
  let s0 := if r1 < q0 then r0 else rd0
  let s1 := if r1 < q0 then r1 else rd1
  let q := q1 + (if r1 < q0 then 1#64 else 0#64)
  if (if s1 = d1 then s0 < d0 else s1 < d1) then (q, s0, s1)
  else (q + 1, s0 - d0, s1 - d1 - (if s0 < s0 - d0 then 1#64 else 0#64))

/-- `udivrem_3by2()` as the digit 1 of `udivrem_by2<4>()` computes it. -/
def div3by2BVd (u2 u1 u0 d0 d1 v z : BitVec 64) : BitVec 64 × BitVec 64 × BitVec 64 :=
  let p0 := v * u2
  let p1 := mulhu v u2
  let q0 := p0 + u1
  let q1 := u2 + (p1 + z * u2) + (if q0 < p0 then 1#64 else 0#64)
  let rd0 := u0 - q1 * d0
  let rd1 := u1 - (d1 * q1 + mulhu q1 d0) - (if u0 < rd0 then 1#64 else 0#64)
  let r0 := rd0 - d0
  let r1 := rd1 - d1 - (if rd0 < r0 then 1#64 else 0#64)
  let s0 := if r1 < q0 then r0 else rd0
  let s1 := if r1 < q0 then r1 else rd1
  let q := q1 + (if r1 < q0 then 1#64 else 0#64)
  if (if s1 = d1 then s0 < d0 else s1 < d1) then (q, s0, s1)
  else (q + 1, s0 - d0, s1 - d1 - (if s0 < s0 - d0 then 1#64 else 0#64))

/-- `udivrem_3by2()` as the digit 0 of `udivrem_by2<4>()` computes it, with the registers `y` and
`z` that hold 0 in the products `y * v` and `u2 * z` of the estimate. -/
def div3by2BVe (u2 u1 u0 d0 d1 v y z : BitVec 64) : BitVec 64 × BitVec 64 × BitVec 64 :=
  let p0 := u2 * v
  let p1 := mulhu u2 v
  let q0 := p0 + u1
  let q1 := u2 + y * v + (p1 + u2 * z) + (if q0 < p0 then 1#64 else 0#64)
  let rd0 := u0 - q1 * d0
  let rd1 := u1 - (q1 * d1 + mulhu q1 d0) - (if u0 < rd0 then 1#64 else 0#64)
  let r0 := rd0 - d0
  let r1 := rd1 - d1 - (if rd0 < r0 then 1#64 else 0#64)
  let s0 := if r1 < q0 then r0 else rd0
  let s1 := if r1 < q0 then r1 else rd1
  let q := q1 + (if r1 < q0 then 1#64 else 0#64)
  if (if s1 = d1 then s0 < d0 else s1 < d1) then (q, s0, s1)
  else (q + 1, s0 - d0, s1 - d1 - (if s0 < s0 - d0 then 1#64 else 0#64))

theorem div3by2BVc_eq (u2 u1 u0 d0 d1 v z : BitVec 64) (hz : z = 0#64) :
    div3by2BVc u2 u1 u0 d0 d1 v z = div3by2BV u2 u1 u0 d0 d1 v := by
  subst hz
  simp only [div3by2BVc, div3by2BV, BitVec.zero_mul, BitVec.add_zero, BitVec.mul_comm d1]

theorem div3by2BVd_eq (u2 u1 u0 d0 d1 v z : BitVec 64) (hz : z = 0#64) :
    div3by2BVd u2 u1 u0 d0 d1 v z = div3by2BV u2 u1 u0 d0 d1 v := by
  subst hz
  simp only [div3by2BVd, div3by2BV, BitVec.zero_mul, BitVec.add_zero, BitVec.mul_comm d1]

theorem div3by2BVe_eq (u2 u1 u0 d0 d1 v y z : BitVec 64) (hy : y = 0#64) (hz : z = 0#64) :
    div3by2BVe u2 u1 u0 d0 d1 v y z = div3by2BV u2 u1 u0 d0 d1 v := by
  subst hy hz
  simp only [div3by2BVe, div3by2BV, BitVec.zero_mul, BitVec.mul_zero, BitVec.add_zero,
    BitVec.mul_comm u2 v, mulhu_comm u2 v]

/-- The quotient and the remainder of the inlined `udivrem_3by2()` of a digit of
`udivrem_by2<4>()`: `div3by2BV_spec`. -/
theorem div3by2BVc_spec (u2 u1 u0 d0 d1 v z : BitVec 64) (hz : z = 0#64)
    (hD1 : 2 ^ 127 ≤ d0.toNat + 2 ^ 64 * d1.toNat)
    (hX : u2.toNat * 2 ^ 64 + u1.toNat < d0.toNat + 2 ^ 64 * d1.toNat)
    (hv : v.toNat = (2 ^ 192 - 1) / (d0.toNat + 2 ^ 64 * d1.toNat) - 2 ^ 64) :
    (div3by2BVc u2 u1 u0 d0 d1 v z).1.toNat =
        (u2.toNat * 2 ^ 128 + u1.toNat * 2 ^ 64 + u0.toNat) / (d0.toNat + 2 ^ 64 * d1.toNat) ∧
      (div3by2BVc u2 u1 u0 d0 d1 v z).2.1.toNat + 2 ^ 64 * (div3by2BVc u2 u1 u0 d0 d1 v z).2.2.toNat =
        (u2.toNat * 2 ^ 128 + u1.toNat * 2 ^ 64 + u0.toNat) % (d0.toNat + 2 ^ 64 * d1.toNat) := by
  rw [div3by2BVc_eq _ _ _ _ _ _ _ hz]
  exact div3by2BV_spec u2 u1 u0 d0 d1 v hD1 hX hv

theorem div3by2BVd_spec (u2 u1 u0 d0 d1 v z : BitVec 64) (hz : z = 0#64)
    (hD1 : 2 ^ 127 ≤ d0.toNat + 2 ^ 64 * d1.toNat)
    (hX : u2.toNat * 2 ^ 64 + u1.toNat < d0.toNat + 2 ^ 64 * d1.toNat)
    (hv : v.toNat = (2 ^ 192 - 1) / (d0.toNat + 2 ^ 64 * d1.toNat) - 2 ^ 64) :
    (div3by2BVd u2 u1 u0 d0 d1 v z).1.toNat =
        (u2.toNat * 2 ^ 128 + u1.toNat * 2 ^ 64 + u0.toNat) / (d0.toNat + 2 ^ 64 * d1.toNat) ∧
      (div3by2BVd u2 u1 u0 d0 d1 v z).2.1.toNat + 2 ^ 64 * (div3by2BVd u2 u1 u0 d0 d1 v z).2.2.toNat =
        (u2.toNat * 2 ^ 128 + u1.toNat * 2 ^ 64 + u0.toNat) % (d0.toNat + 2 ^ 64 * d1.toNat) := by
  rw [div3by2BVd_eq _ _ _ _ _ _ _ hz]
  exact div3by2BV_spec u2 u1 u0 d0 d1 v hD1 hX hv

theorem div3by2BVe_spec (u2 u1 u0 d0 d1 v y z : BitVec 64) (hy : y = 0#64) (hz : z = 0#64)
    (hD1 : 2 ^ 127 ≤ d0.toNat + 2 ^ 64 * d1.toNat)
    (hX : u2.toNat * 2 ^ 64 + u1.toNat < d0.toNat + 2 ^ 64 * d1.toNat)
    (hv : v.toNat = (2 ^ 192 - 1) / (d0.toNat + 2 ^ 64 * d1.toNat) - 2 ^ 64) :
    (div3by2BVe u2 u1 u0 d0 d1 v y z).1.toNat =
        (u2.toNat * 2 ^ 128 + u1.toNat * 2 ^ 64 + u0.toNat) / (d0.toNat + 2 ^ 64 * d1.toNat) ∧
      (div3by2BVe u2 u1 u0 d0 d1 v y z).2.1.toNat +
          2 ^ 64 * (div3by2BVe u2 u1 u0 d0 d1 v y z).2.2.toNat =
        (u2.toNat * 2 ^ 128 + u1.toNat * 2 ^ 64 + u0.toNat) % (d0.toNat + 2 ^ 64 * d1.toNat) := by
  rw [div3by2BVe_eq _ _ _ _ _ _ _ _ hy hz]
  exact div3by2BV_spec u2 u1 u0 d0 d1 v hD1 hX hv

end IntxRV

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- The paths of an inlined `udivrem_3by2()` of `udivrem_by2<4>()` to its end, as
`by2_div3_paths`, for posts with more facts after `Div3Out`. -/
macro "by24_div3_paths" hs:term : tactic => `(tactic| (
  rv_exec
  all_goals
    beta_reduce
    simp only [Div3Out]
    rv_cse
    have hs := $hs
    simp only [div3by2BVo, div3by2BV, div3by2BVc, div3by2BVd, div3by2BVe, Bool.false_eq_true,
      ↓reduceIte] at hs
    rv_fold hs
    rv_fold hs
    simp only [zopz0zI_u_eq, decide_eq_true_eq, decide_eq_false_iff_not, beq_eq_false_iff_ne,
      ne_eq] at *
    rv_conds
    simp (disch := assumption) only [if_pos, if_neg] at hs
    rv_fold hs
    rv_fold hs
    refine ⟨by first | rfl | trivial, ?_⟩
    repeat' apply And.intro
    all_goals first
      | (intro r hr
         simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
         simp (config := { decide := true }) only [Regs.set_apply, hr, ↓reduceIte, if_false])
      | (simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]; done)
      | (simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
         first | done | exact hs.1 | exact hs.2)))

/-- The inlined `udivrem_3by2()` of the top digits of `udivrem_by2<4>()`, from 154 to 183:
`a2:t3:t1` by `a7:a6` with the reciprocal in t0, to the quotient in a2 and the remainder in
`t2:t1`. -/
theorem by24_b1 {A : List (BitVec 64)} {hi : BitVec 20} {lo : BitVec 12} (base : BitVec 64)
    (x : Regs) (m : Mem)
    (hd : 2 ^ 127 ≤ (x.get 16#5).toNat + 2 ^ 64 * (x.get 17#5).toNat)
    (hu : (x.get 12#5).toNat * 2 ^ 64 + (x.get 28#5).toNat <
      (x.get 16#5).toNat + 2 ^ 64 * (x.get 17#5).toNat)
    (hv : (x.get 5#5).toNat =
      (2 ^ 192 - 1) / ((x.get 16#5).toNat + 2 ^ 64 * (x.get 17#5).toNat) - 2 ^ 64) :
    Reach A (udivrem_by2_4_progAt hi lo) base (pcAt base 154) x m (pcAt base 183) (fun x' m' =>
      m' = m ∧ Div3Out x x' ((x.get 12#5).toNat * 2 ^ 128 + (x.get 28#5).toNat * 2 ^ 64 +
        (x.get 6#5).toNat) ((x.get 16#5).toNat + 2 ^ 64 * (x.get 17#5).toNat) 12#5 6#5 7#5
        [6#5, 7#5, 12#5, 13#5, 28#5, 29#5, 30#5]) := by
  by24_div3_paths div3by2BVo_spec false (x.get 12#5) (x.get 28#5) (x.get 6#5) (x.get 16#5)
    (x.get 17#5) (x.get 5#5) hd hu hv

/-- The inlined `udivrem_3by2()` of the digit 2 of `udivrem_by2<4>()`, from 197 to 228:
`t2:t1:a3` by `a7:a6`, to the quotient in t2 and the remainder in `t1:a3`. -/
theorem by24_b2 {A : List (BitVec 64)} {hi : BitVec 20} {lo : BitVec 12} (base : BitVec 64)
    (x : Regs) (m : Mem) (hz : x.get 12#5 = 0#64)
    (hd : 2 ^ 127 ≤ (x.get 16#5).toNat + 2 ^ 64 * (x.get 17#5).toNat)
    (hu : (x.get 7#5).toNat * 2 ^ 64 + (x.get 6#5).toNat <
      (x.get 16#5).toNat + 2 ^ 64 * (x.get 17#5).toNat)
    (hv : (x.get 5#5).toNat =
      (2 ^ 192 - 1) / ((x.get 16#5).toNat + 2 ^ 64 * (x.get 17#5).toNat) - 2 ^ 64) :
    Reach A (udivrem_by2_4_progAt hi lo) base (pcAt base 197) x m (pcAt base 228) (fun x' m' =>
      m' = m ∧ Div3Out x x' ((x.get 7#5).toNat * 2 ^ 128 + (x.get 6#5).toNat * 2 ^ 64 +
        (x.get 13#5).toNat) ((x.get 16#5).toNat + 2 ^ 64 * (x.get 17#5).toNat) 7#5 13#5 6#5
        [6#5, 7#5, 13#5, 28#5, 29#5, 30#5, 31#5]) := by
  by24_div3_paths div3by2BVc_spec (x.get 7#5) (x.get 6#5) (x.get 13#5) (x.get 16#5) (x.get 17#5)
    (x.get 5#5) (x.get 12#5) hz hd hu hv

/-- The inlined `udivrem_3by2()` of the digit 1 of `udivrem_by2<4>()`, from 236 to 268:
`t1:a3:t4` by `a7:a6`, to the quotient in t2 and the remainder in `t1:a3`, with t3 = 0. -/
theorem by24_b3 {A : List (BitVec 64)} {hi : BitVec 20} {lo : BitVec 12} (base : BitVec 64)
    (x : Regs) (m : Mem) (hz : x.get 12#5 = 0#64)
    (hd : 2 ^ 127 ≤ (x.get 16#5).toNat + 2 ^ 64 * (x.get 17#5).toNat)
    (hu : (x.get 6#5).toNat * 2 ^ 64 + (x.get 13#5).toNat <
      (x.get 16#5).toNat + 2 ^ 64 * (x.get 17#5).toNat)
    (hv : (x.get 5#5).toNat =
      (2 ^ 192 - 1) / ((x.get 16#5).toNat + 2 ^ 64 * (x.get 17#5).toNat) - 2 ^ 64) :
    Reach A (udivrem_by2_4_progAt hi lo) base (pcAt base 236) x m (pcAt base 268) (fun x' m' =>
      m' = m ∧ Div3Out x x' ((x.get 6#5).toNat * 2 ^ 128 + (x.get 13#5).toNat * 2 ^ 64 +
        (x.get 29#5).toNat) ((x.get 16#5).toNat + 2 ^ 64 * (x.get 17#5).toNat) 7#5 13#5 6#5
        [6#5, 7#5, 13#5, 28#5, 29#5, 30#5, 31#5] ∧ x'.get 28#5 = 0#64) := by
  by24_div3_paths div3by2BVd_spec (x.get 6#5) (x.get 13#5) (x.get 29#5) (x.get 16#5) (x.get 17#5)
    (x.get 5#5) (x.get 12#5) hz hd hu hv

/-- The subtraction of the top words of `udivrem_by2<4>()` when u[4] is at most d1, from 122 to
138: `t3:t4` minus `a3:a2` if it is not below, the quotient word 0 or 1 in a2 and the remainder in
`t2:t1`. -/
theorem by24_sub_top {A : List (BitVec 64)} {hi : BitVec 20} {lo : BitVec 12} (base : BitVec 64)
    (x : Regs) (m : Mem) (hd : 0 < (x.get 13#5).toNat)
    (hu : (x.get 28#5).toNat ≤ (x.get 13#5).toNat) :
    Reach A (udivrem_by2_4_progAt hi lo) base (pcAt base 122) x m (pcAt base 138) (fun x' m' =>
      m' = m ∧ Div3Out x x' ((x.get 29#5).toNat + 2 ^ 64 * (x.get 28#5).toNat)
        ((x.get 12#5).toNat + 2 ^ 64 * (x.get 13#5).toNat) 12#5 6#5 7#5
        [6#5, 7#5, 12#5, 30#5]) := by
  have hT : (x.get 29#5).toNat + 2 ^ 64 * (x.get 28#5).toNat <
      2 * ((x.get 12#5).toNat + 2 ^ 64 * (x.get 13#5).toNat) := by
    have := (x.get 29#5).isLt; omega
  obtain ⟨hq, hr⟩ := div_lt_two hT
  rv_exec
  all_goals
    simp only [Div3Out]
    try simp only [beq_eq_false_iff_ne, bne_eq_false_iff_eq, ne_eq] at *
  -- The two tests of t3 = a3 agree.
  all_goals first
    | (rv_get he : x.get 28#5 = x.get 13#5
       rv_get hne : ¬x.get 28#5 = x.get 13#5
       exact absurd he hne)
    | skip
  all_goals
    refine ⟨by first | rfl | trivial, ?_, ?_, ?_, ?_⟩
    rotate_left 2
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp (config := { decide := true }) only [Regs.set_apply, hr, ↓reduceIte]
    all_goals
      simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      first | rw [hq] | rw [hr]
      simp only [Defn] at *
      subst_vars
      split_ifs at * <;> (try simp only [BitVec.reduceXOr] at *) <;> first | bv_omega | simp_all

/-- The state of `udivrem_by2<4>()` from the entry `x`, `m` at the 3/2 division of the digit `i`:
the normalized divisor `D` in `a7:a6`, its reciprocal in t0, the shift in a4 and its complement in
a5, 0 in a2 and the remainder `rem` of the digits above `i` in `rh:rl`, with the quotient words
above `i` stored. -/
def By24St (x : Regs) (m : Mem) (i : Nat) (rh rl : BitVec 5) (x' : Regs) (m' : Mem) : Prop :=
  let S := 63 - Nat.log2 (x.get 13#5).toNat
  let D := ((x.get 12#5).toNat + 2 ^ 64 * (x.get 13#5).toNat) * 2 ^ S
  let U := words m (x.get 11#5) 5
  (x'.get 16#5).toNat + 2 ^ 64 * (x'.get 17#5).toNat = D ∧
  (x'.get 5#5).toNat = (2 ^ 192 - 1) / D - 2 ^ 64 ∧
  x'.get 14#5 = BitVec.ofNat 64 S ∧ x'.get 15#5 = BitVec.ofNat 64 S ^^^ 18446744073709551615#64 ∧
  x'.get 12#5 = 0#64 ∧ x'.get 10#5 = x.get 10#5 ∧ x'.get 11#5 = x.get 11#5 ∧
  (x'.get rl).toNat + 2 ^ 64 * (x'.get rh).toNat < D ∧
  words m' (x.get 10#5 + BitVec.ofNat 64 (8 * (i + 1))) (3 - i) * D +
      ((x'.get rl).toNat + 2 ^ 64 * (x'.get rh).toNat) = U * 2 ^ S / 2 ^ (64 * (i + 1)) ∧
  UnchangedExcept m m' (x.get 10#5) 32 ∧
  x'.get 1#5 = x.get 1#5 ∧ (∀ r ∈ calleeSaved, x'.get r = x.get r)

/-- The facts of the divisor of `udivrem_by2<4>()` from its precondition. -/
theorem by24_dn {x : Regs} {m : Mem} (hpre : udivrem_by2_4.pre x m) :
    (x.get 13#5).toNat ≠ 0 ∧ Nat.log2 (x.get 13#5).toNat < 64 ∧
      2 ^ 127 ≤ ((x.get 12#5).toNat + 2 ^ 64 * (x.get 13#5).toNat) *
        2 ^ (63 - Nat.log2 (x.get 13#5).toNat) := by
  simp only [udivrem_by2_4.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨-, -, -, -, -, hd⟩ := hpre
  have hd1 : (x.get 13#5).toNat ≠ 0 := by have := (x.get 12#5).isLt; omega
  exact ⟨hd1, (Nat.log2_lt hd1).mpr (x.get 13#5).isLt, by2_D127 _ _ hd1⟩

/-- The remainder shifted back by `0 < S < 64` from the definitions of the run: the funnel shift
`(b << 1) << ~t | a >> t` and `b >> t`. -/
theorem fshr_defs {S : Nat} {w1 w2 w3 w4 w a b t : BitVec 64} (ht : t.toNat = S) (hS : S < 64)
    (hS0 : 0 < S) (h4 : Defn w4 (a >>> (t.toNat % 64))) (h3 : Defn w3 (b <<< 1))
    (h2 : Defn w2 (w3 <<< ((t ^^^ 18446744073709551615#64).toNat % 64)))
    (h1 : Defn w1 (w2 ||| w4)) (h : Defn w (b >>> (t.toNat % 64))) :
    w1.toNat + 2 ^ 64 * w.toNat = (a.toNat + 2 ^ 64 * b.toNat) / 2 ^ S := by
  have e1 : w1.toNat = b.toNat * 2 ^ (64 - S) % 2 ^ 64 + a.toNat / 2 ^ S := by
    rw [h1.eq, h2.eq, h3.eq, h4.eq, toNat_fshr_code a b t (by omega) (by omega), ht]
  have e2 : w.toNat = b.toNat / 2 ^ S := by rw [defn_shr_toNat h, ht, Nat.mod_eq_of_lt hS]
  rw [e1, e2]
  exact fshr_words _ _ _ hS

/-- The digit 0 of `udivrem_by2<4>()` from 269: the inlined `udivrem_3by2()` with the word u[0]
shifted, the quotient word q[0], the remainder shifted back and the return. -/
theorem by24_d0 {hi : BitVec 20} {lo : BitVec 12} {D : List (BitVec 64)} (base : BitVec 64)
    (x : Regs) (m : Mem) (hpre : udivrem_by2_4.pre x m) (hr : x.get 1#5 &&& 3 = 0) (x' : Regs)
    (m' : Mem) (h : By24St x m 0 6#5 13#5 x' m') (h28 : x'.get 28#5 = 0#64) :
    Reach (bufWords (x.get 11#5) 5 ++ bufWords (x.get 10#5) 4 ++ D) (udivrem_by2_4_progAt hi lo)
      base (pcAt base 269) x' m' (x.get 1#5) (udivrem_by2_4.post x m) := by
  obtain ⟨hdn, hv, h14, h15, h12, h10, h11, hrem, hq, hu, h1, hcs⟩ := h
  have hpre' := hpre
  simp only [udivrem_by2_4.pre, Buf, Disjoint] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hqa, hqn⟩, ⟨hua, hun⟩, hdis, -, -, hd⟩ := hpre'
  obtain ⟨hd1, hL, hD⟩ := by24_dn hpre
  have hS64 : 63 - Nat.log2 (x.get 13#5).toNat < 64 := by omega
  have hdpos : 0 < (x.get 12#5).toNat + 2 ^ 64 * (x.get 13#5).toNat := by omega
  have hu0 : memWord m' (x.get 11#5).toNat = memWord m (x.get 11#5).toNat :=
    memWord_of_unchangedExcept hu _ (by omega)
  rw [← regs_set_of_get' (by decide) h14, ← regs_set_of_get' (by decide) h15]
  rv_exec_cut 273
  -- The word u[0].
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  rw [h11]
  refine ⟨List.mem_append_left _ (List.mem_append_left _ (mem_bufWords_zero (by norm_num))),
    fun w0 hw0 => ?_⟩
  rw [hu0] at hw0
  rv_exec_cut 304 333
  all_goals
    rv_cse
    have hdig : (w0 <<< ((BitVec.ofNat 64 (63 - Nat.log2 (x.get 13#5).toNat)).toNat % 64)).toNat =
        words m (x.get 11#5) 5 * 2 ^ (63 - Nat.log2 (x.get 13#5).toNat) % 2 ^ 64 := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, ofNat_S_toNat hS64, Nat.mod_eq_of_lt hS64,
        hw0.eq, ← words_mul_mod m (x.get 11#5) 5 _ (by norm_num)]
    have hs := div3by2BVe_spec (x'.get 6#5) (x'.get 13#5)
      (w0 <<< ((BitVec.ofNat 64 (63 - Nat.log2 (x.get 13#5).toNat)).toNat % 64)) (x'.get 16#5)
      (x'.get 17#5) (x'.get 5#5) (x'.get 28#5) (x'.get 12#5) h28 h12 (by rw [hdn]; exact hD)
      (by rw [hdn]; omega) (by rw [hv, hdn])
    simp only [div3by2BVe] at hs
    rv_fold hs
    rv_fold hs
    rv_fold hdig
    simp only [zopz0zI_u_eq, decide_eq_true_eq, decide_eq_false_iff_not,
      ne_eq] at *
    rv_conds
    simp (disch := assumption) only [if_pos, if_neg] at hs
    rv_fold hs
    rv_fold hs
    -- The word q[0] and the return.
    refine Reach.step (by decide) (by rv_fetch) ?_
    simp only [StepGoal, Nat.reduceAdd]
    rv_val
    try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    rw [h10]
    refine ⟨List.mem_append_left _ (List.mem_append_right _ (mem_bufWords_zero (by norm_num))), ?_⟩
    rv_exec_cut
    all_goals
      rv_val
      try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      rw [h1, update_aligned hr]
      refine Reach.refl ?_
      simp only [udivrem_by2_4.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq]
      simp (disch := decide) only [Regs.eq_get x]
      simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      -- The quotient and the remainder of the numerator normalized by S.
      rw [hdn, show ∀ a b c : Nat, a * 2 ^ 128 + b * 2 ^ 64 + c = 2 ^ 64 * (b + 2 ^ 64 * a) + c
        from fun a b c => by ring, hdig] at hs
      have hq' : words m' (x.get 10#5 + 8#64) 3 *
          (((x.get 12#5).toNat + 2 ^ 64 * (x.get 13#5).toNat) * 2 ^ (63 - (x.get 13#5).toNat.log2)) +
          ((x'.get 13#5).toNat + 2 ^ 64 * (x'.get 6#5).toNat) =
          words m (x.get 11#5) 5 * 2 ^ (63 - (x.get 13#5).toNat.log2) / 2 ^ 64 := by
        simpa using hq
      obtain ⟨hfq, hfr⟩ := by1_final hdpos hq' rfl hs.1 hs.2
      refine ⟨?_, ?_, (unchangedExcept_memStore _ _ ⟨le_refl _, by omega⟩).mpr hu, ?_⟩
      · rw [words_memStore_first _ _ _ _ (by norm_num) hqn]
        exact hfq
      · rw [← hfr]
        first
          | (rv_get hz : BitVec.ofNat 64 (63 - (x.get 13#5).toNat.log2) = 0#64
             have hS0 := ofNat_S_eq hS64 hz
             have hres := defn_shr_toNat ‹Defn _ ((_ : BitVec 64) >>>
               ((BitVec.ofNat 64 (63 - (x.get 13#5).toNat.log2)).toNat % 64))›
             rw [hres, hz, hS0]
             simp)
          | (rv_get hnz : ¬BitVec.ofNat 64 (63 - (x.get 13#5).toNat.log2) = 0#64
             apply fshr_defs (ofNat_S_toNat hS64) hS64 (ofNat_S_ne hS64 hnz)
             all_goals assumption)
      · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte,
          BitVec.ofNat_eq_ofNat]
        simp (disch := decide) only [Regs.eq_get x']
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
          forall_eq] at hcs
        exact hcs

/-- The digit 1 of `udivrem_by2<4>()` from 236: the inlined `udivrem_3by2()` and the quotient word
q[1]. -/
theorem by24_d1 {hi : BitVec 20} {lo : BitVec 12} {D : List (BitVec 64)} (base : BitVec 64)
    (x : Regs) (m : Mem) (hpre : udivrem_by2_4.pre x m) (hr : x.get 1#5 &&& 3 = 0) (x' : Regs)
    (m' : Mem) (h : By24St x m 1 6#5 13#5 x' m')
    (hdig : (x'.get 29#5).toNat = words m (x.get 11#5) 5 *
      2 ^ (63 - Nat.log2 (x.get 13#5).toNat) / 2 ^ (64 * 1) % 2 ^ 64) :
    Reach (bufWords (x.get 11#5) 5 ++ bufWords (x.get 10#5) 4 ++ D) (udivrem_by2_4_progAt hi lo)
      base (pcAt base 236) x' m' (x.get 1#5) (udivrem_by2_4.post x m) := by
  obtain ⟨hdn, hv, h14, h15, h12, h10, h11, hrem, hq, hu, h1, hcs⟩ := h
  have hpre' := hpre
  simp only [udivrem_by2_4.pre, Buf, Disjoint] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hqa, hqn⟩, ⟨hua, hun⟩, hdis, -, -, hd⟩ := hpre'
  obtain ⟨hd1, hL, hD⟩ := by24_dn hpre
  refine Reach.trans (by24_b3 base _ _ h12 (by rw [hdn]; exact hD) (by rw [hdn]; omega)
    (by rw [hv, hdn])) ?_
  intro x'' m'' ⟨hm, ⟨hq0, hr0, h00, hfr⟩, h28⟩
  subst hm
  rw [hdn, hdig, show ∀ a b c : Nat, a * 2 ^ 128 + b * 2 ^ 64 + c = 2 ^ 64 * (b + 2 ^ 64 * a) + c
    from fun a b c => by ring] at hq0 hr0
  have hstep := div_step 1 hq hq0 hr0
  rw [regs_eq_sets _ x'' _ h00 hfr]
  simp only [setRegs]
  -- The word q[1].
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  rw [h10]
  refine ⟨List.mem_append_left _ (List.mem_append_right _ (mem_bufWords (i := 1) (by norm_num))),
    ?_⟩
  have hq8 : (x.get 10#5 + 8#64).toNat = (x.get 10#5).toNat + 8 := by
    rw [BitVec.toNat_add]; simp; omega
  have hDp : 0 < ((x.get 12#5).toNat + 2 ^ 64 * (x.get 13#5).toNat) *
      2 ^ (63 - Nat.log2 (x.get 13#5).toNat) := by omega
  refine by24_d0 base x m hpre hr _ _ ?_ ?_
  · simp only [By24St]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    rw [Regs.eq_get x'' (show (13#5 : BitVec 5) ≠ 0 by decide),
      Regs.eq_get x'' (show (6#5 : BitVec 5) ≠ 0 by decide)]
    refine ⟨hdn, hv, h14, h15, h12, h10, h11, hr0 ▸ Nat.mod_lt _ hDp, ?_,
      (unchangedExcept_memStore _ _ ⟨by omega, by omega⟩).mpr hu, h1, ?_⟩
    · rw [show x.get 10#5 + BitVec.ofNat 64 (8 * (0 + 1)) = x.get 10#5 + 8#64 from rfl,
        words_memStore_first _ _ _ _ (by norm_num) (by omega),
        Regs.eq_get x'' (show (7#5 : BitVec 5) ≠ 0 by decide)]
      simpa [BitVec.add_assoc] using hstep
    · intro r hr
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;>
      simp (config := { decide := true }) only [↓reduceIte] <;>
      exact hcs _ (by decide)
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    rw [Regs.eq_get x'' (show (28#5 : BitVec 5) ≠ 0 by decide)]
    exact h28

/-- The digit 2 of `udivrem_by2<4>()` from 197: the inlined `udivrem_3by2()`, the quotient word q[2]
and the digit 1 from u[1] and u[0]. -/
theorem by24_d2 {hi : BitVec 20} {lo : BitVec 12} {D : List (BitVec 64)} (base : BitVec 64)
    (x : Regs) (m : Mem) (hpre : udivrem_by2_4.pre x m) (hr : x.get 1#5 &&& 3 = 0) (x' : Regs)
    (m' : Mem) (h : By24St x m 2 7#5 6#5 x' m')
    (hdig : (x'.get 13#5).toNat = words m (x.get 11#5) 5 *
      2 ^ (63 - Nat.log2 (x.get 13#5).toNat) / 2 ^ (64 * 2) % 2 ^ 64) :
    Reach (bufWords (x.get 11#5) 5 ++ bufWords (x.get 10#5) 4 ++ D) (udivrem_by2_4_progAt hi lo)
      base (pcAt base 197) x' m' (x.get 1#5) (udivrem_by2_4.post x m) := by
  obtain ⟨hdn, hv, h14, h15, h12, h10, h11, hrem, hq, hu, h1, hcs⟩ := h
  have hpre' := hpre
  simp only [udivrem_by2_4.pre, Buf, Disjoint] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hqa, hqn⟩, ⟨hua, hun⟩, hdis, -, -, hd⟩ := hpre'
  obtain ⟨hd1, hL, hD⟩ := by24_dn hpre
  have hS64 : 63 - Nat.log2 (x.get 13#5).toNat < 64 := by omega
  have hu0 : memWord m' (x.get 11#5).toNat = memWord m (x.get 11#5).toNat :=
    memWord_of_unchangedExcept hu _ (by omega)
  have hu1 : memWord m' (x.get 11#5 + 8#64).toNat = memWord m (x.get 11#5 + 8#64).toNat :=
    memWord_of_unchangedExcept hu _ (by bv_omega)
  refine Reach.trans (by24_b2 base _ _ h12 (by rw [hdn]; exact hD) (by rw [hdn]; omega)
    (by rw [hv, hdn])) ?_
  intro x'' m'' ⟨hm, hq0, hr0, h00, hfr⟩
  subst hm
  rw [hdn, hdig, show ∀ a b c : Nat, a * 2 ^ 128 + b * 2 ^ 64 + c = 2 ^ 64 * (b + 2 ^ 64 * a) + c
    from fun a b c => by ring] at hq0 hr0
  have hstep := div_step 2 hq hq0 hr0
  rw [regs_eq_sets _ x'' _ h00 hfr]
  simp only [setRegs]
  rw [← regs_set_of_get' (by decide) h10, ← regs_set_of_get' (by decide) h11,
    ← regs_set_of_get' (by decide) h14, ← regs_set_of_get' (by decide) h15]
  -- The word q[2].
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  refine ⟨List.mem_append_left _ (List.mem_append_right _ (mem_bufWords (i := 2) (by norm_num))),
    ?_⟩
  -- The word u[1].
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  refine ⟨List.mem_append_left _ (List.mem_append_left _ (mem_bufWords (i := 1) (by norm_num))),
    fun w1 hw1 => ?_⟩
  try rw [memWord_memStore_of_ne _ _ _ _ (by bv_omega)] at hw1
  rw [hu1] at hw1
  rv_exec_cut 231 236
  -- s ≠ 0: the word u[0] for the funnel shift of the digit 1.
  all_goals first
    | (rv_not_at 231; skip)
    | (refine Reach.step (by decide) (by rv_fetch) ?_
       simp only [StepGoal, Nat.reduceAdd]
       rv_val
       try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
       try simp only [BitVec.add_zero]
       refine ⟨List.mem_append_left _ (List.mem_append_left _ (mem_bufWords_zero (by norm_num))),
         fun w0 hw0 => ?_⟩
       try rw [memWord_memStore_of_ne _ _ _ _ (by bv_omega)] at hw0
       rw [hu0] at hw0
       rv_exec_cut 236)
  all_goals
    have hDp : 0 < ((x.get 12#5).toNat + 2 ^ 64 * (x.get 13#5).toNat) *
        2 ^ (63 - Nat.log2 (x.get 13#5).toNat) := by omega
    have hq16 : (x.get 10#5 + 16#64).toNat = (x.get 10#5).toNat + 16 := by
      rw [BitVec.toNat_add]; simp; omega
    refine by24_d1 base x m hpre hr _ _ ?_ ?_
    · simp only [By24St]
      simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      rw [Regs.eq_get x'' (show (13#5 : BitVec 5) ≠ 0 by decide),
        Regs.eq_get x'' (show (6#5 : BitVec 5) ≠ 0 by decide)]
      refine ⟨hdn, hv, trivial, trivial, h12, trivial, trivial, hr0 ▸ Nat.mod_lt _ hDp, ?_,
        (unchangedExcept_memStore _ _ ⟨by omega, by omega⟩).mpr hu, h1, ?_⟩
      · rw [show x.get 10#5 + BitVec.ofNat 64 (8 * (1 + 1)) = x.get 10#5 + 16#64 from rfl,
          words_memStore_first _ _ _ _ (by norm_num) (by omega),
          Regs.eq_get x'' (show (7#5 : BitVec 5) ≠ 0 by decide)]
        simpa [BitVec.add_assoc] using hstep
      · intro r hr
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl <;>
        simp (config := { decide := true }) only [↓reduceIte] <;>
        exact hcs _ (by decide)
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      first
        | (rv_get hnz : ¬BitVec.ofNat 64 (63 - (x.get 13#5).toNat.log2) = 0#64
           have hf := toNat_fshl_code w1 w0 (BitVec.ofNat 64 (63 - Nat.log2 (x.get 13#5).toNat))
             (by rw [ofNat_S_toNat hS64]; exact hS64)
           rv_fold hf
           rv_fold hf
           rw [hw1.eq, hw0.eq, ofNat_S_toNat hS64] at hf
           have hd1 := norm_digit m (x.get 11#5) 5 _ 1 hS64 le_rfl (by norm_num)
           simp only [wordAt, show 1 - 1 = 0 from rfl, Nat.mul_zero, Nat.mul_one, BitVec.add_zero]
             at hd1
           rw [← hd1] at hf
           simpa using hf)
        | (rv_get hz : BitVec.ofNat 64 (63 - (x.get 13#5).toNat.log2) = 0#64
           have hS0 := ofNat_S_eq hS64 hz
           rw [hw1.eq, norm_digit m (x.get 11#5) 5 _ 1 hS64 le_rfl (by norm_num), hS0]
           simp only [pow_zero, Nat.mul_one, Nat.sub_zero, wordAt]
           rw [Nat.div_eq_of_lt (BitVec.isLt _), Nat.add_zero, Nat.mod_eq_of_lt (BitVec.isLt _)])

end IntxRV.Api
