import IntxRV.Arith
import IntxRV.Div3by2
import IntxRV.Shift
import IntxRV.Recip3
/-!
# The lemmas that the proofs of the division functions share

The copies of `udivrem_3by2()` that the division functions inline (`div3by2BVo`, `Div3Out`) and
the tactic that runs the paths of a copy to its end (`by2_div3_paths`); the words of the divisors
and of the numerators normalized by the count of the leading zeros, and the shifts of the code
that normalizes them. The proofs import this module rather than the lemmas of `udivrem_by1()` and
`udivrem_by2()` (`DivBy1.lean`, `DivBy2.lean`), which import the code of these functions: a
change of the code of a function rebuilds the proofs of its callers only.
-/

namespace IntxRV.Api
open IntxRV

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
-- The guards that select the paths do not change the goals.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `div3by2BV` with the products in the order of the copies inlined in `udivrem_by2()`: `u2 * v`
and `mulhu u2 v`, and `d1 * q1` if `dq`. -/
def div3by2BVo (dq : Bool) (u2 u1 u0 d0 d1 v : BitVec 64) : BitVec 64 × BitVec 64 × BitVec 64 :=
  let p0 := u2 * v
  let p1 := mulhu u2 v
  let q0 := p0 + u1
  let q1 := u2 + p1 + (if q0 < p0 then 1#64 else 0#64)
  let rd0 := u0 - q1 * d0
  let rd1 := u1 - ((if dq then d1 * q1 else q1 * d1) + mulhu q1 d0) -
    (if u0 < rd0 then 1#64 else 0#64)
  let r0 := rd0 - d0
  let r1 := rd1 - d1 - (if rd0 < r0 then 1#64 else 0#64)
  let s0 := if r1 < q0 then r0 else rd0
  let s1 := if r1 < q0 then r1 else rd1
  let q := q1 + (if r1 < q0 then 1#64 else 0#64)
  if (if s1 = d1 then s0 < d0 else s1 < d1) then (q, s0, s1)
  else (q + 1, s0 - d0, s1 - d1 - (if s0 < s0 - d0 then 1#64 else 0#64))

theorem div3by2BVo_eq (dq : Bool) (u2 u1 u0 d0 d1 v : BitVec 64) :
    div3by2BVo dq u2 u1 u0 d0 d1 v = div3by2BV u2 u1 u0 d0 d1 v := by
  cases dq <;> simp only [div3by2BVo, div3by2BV, Bool.false_eq_true, ↓reduceIte,
    BitVec.mul_comm u2 v, mulhu_comm u2 v, BitVec.mul_comm d1]

/-- The quotient and the remainder of an inlined `udivrem_3by2()` of `udivrem_by2()`. -/
theorem div3by2BVo_spec (dq : Bool) (u2 u1 u0 d0 d1 v : BitVec 64)
    (hD1 : 2 ^ 127 ≤ d0.toNat + 2 ^ 64 * d1.toNat)
    (hX : u2.toNat * 2 ^ 64 + u1.toNat < d0.toNat + 2 ^ 64 * d1.toNat)
    (hv : v.toNat = (2 ^ 192 - 1) / (d0.toNat + 2 ^ 64 * d1.toNat) - 2 ^ 64) :
    (div3by2BVo dq u2 u1 u0 d0 d1 v).1.toNat =
        (u2.toNat * 2 ^ 128 + u1.toNat * 2 ^ 64 + u0.toNat) / (d0.toNat + 2 ^ 64 * d1.toNat) ∧
      (div3by2BVo dq u2 u1 u0 d0 d1 v).2.1.toNat +
          2 ^ 64 * (div3by2BVo dq u2 u1 u0 d0 d1 v).2.2.toNat =
        (u2.toNat * 2 ^ 128 + u1.toNat * 2 ^ 64 + u0.toNat) % (d0.toNat + 2 ^ 64 * d1.toNat) := by
  rw [div3by2BVo_eq]
  exact div3by2BV_spec u2 u1 u0 d0 d1 v hD1 hX hv

/-- The registers `x'` after an inlined `udivrem_3by2()` of `udivrem_by2()` from `x`: the quotient
of `U` by `D` in `rq`, the remainder in `rh:rl`, and the registers outside `cl` unchanged, as
functions (`regs_eq_sets`). -/
def Div3Out (x x' : Regs) (U D : Nat) (rq rl rh : BitVec 5) (cl : List (BitVec 5)) : Prop :=
  (x'.get rq).toNat = U / D ∧ (x'.get rl).toNat + 2 ^ 64 * (x'.get rh).toNat = U % D ∧
    x' 0 = x 0 ∧ ∀ r, r ∉ cl → x' r = x r

/-- The registers `x` with the registers `cl` set to their values in `y`. -/
def setRegs (x y : Regs) : List (BitVec 5) → Regs
  | [] => x
  | r :: cl => (setRegs x y cl).set r (y r)

theorem setRegs_apply (x y : Regs) (j : BitVec 5) : ∀ cl : List (BitVec 5),
    setRegs x y cl j = if j ≠ 0 ∧ j ∈ cl then y j else x j
  | [] => by simp [setRegs]
  | r :: cl => by
    rw [setRegs, Regs.set_apply, setRegs_apply x y j cl]
    by_cases hr : r = 0 <;> by_cases hj : j = r <;> simp_all

/-- The registers that differ from `x` only in `cl` are `x` with these registers set: a run
continues from the registers after a step that `Reach.trans` takes as a whole. -/
theorem regs_eq_sets (x y : Regs) (cl : List (BitVec 5)) (h0 : y 0 = x 0)
    (h : ∀ r, r ∉ cl → y r = x r) : y = setRegs x y cl := by
  funext j
  rw [setRegs_apply]
  split_ifs with hc
  · rfl
  · by_cases hj : j = 0
    · subst hj; exact h0
    · exact h j (fun hm => hc ⟨hj, hm⟩)

/-- The paths of an inlined `udivrem_3by2()` to its end, with `hs` its quotient and remainder by
`div3by2BV_spec`: on each path `rv_fold` writes them with the names of the run, and the branch
conditions (`rv_conds`) select the words in the registers. -/
macro "by2_div3_paths" hs:term : tactic => `(tactic| (
  rv_exec
  all_goals
    beta_reduce
    simp only [Div3Out]
    -- The correction recomputes rd0 - d0 and rd1 - d1: one name for each value.
    rv_cse
    have hs := $hs
    simp only [div3by2BVo, div3by2BV, Bool.false_eq_true, ↓reduceIte] at hs
    -- rv_cse moves definitions to the end: the second pass folds the ones before them.
    rv_fold hs
    rv_fold hs
    simp only [zopz0zI_u_eq, decide_eq_true_eq, decide_eq_false_iff_not, beq_eq_false_iff_ne,
      ne_eq] at *
    rv_conds
    simp (disch := assumption) only [if_pos, if_neg] at hs
    rv_fold hs
    rv_fold hs
    refine ⟨by first | rfl | trivial, ?_, ?_, ?_, ?_⟩
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      exact hs.1
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      exact hs.2
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp (config := { decide := true }) only [Regs.set_apply, hr, ↓reduceIte, if_false]))

/-- The two words of a divisor `d1:d0` shifted left by `S` bits: `d0 << S` and the funnel shift of
`d1` and `d0`, without the bits shifted out of the top, which `d1 * 2^S < 2^64` excludes. -/
theorem norm2_words {d0 d1 S : Nat} (hS : S < 64) (h0 : d0 < 2 ^ 64) (h1 : d1 * 2 ^ S < 2 ^ 64) :
    d0 * 2 ^ S % 2 ^ 64 + 2 ^ 64 * ((d1 * 2 ^ S + d0 / 2 ^ (64 - S)) % 2 ^ 64) =
      (d0 + 2 ^ 64 * d1) * 2 ^ S := by
  have hPQ : 2 ^ S * 2 ^ (64 - S) = 2 ^ 64 := by rw [← pow_add]; congr 1; omega
  have hQ : 0 < 2 ^ (64 - S) := by positivity
  have hdq : d0 / 2 ^ (64 - S) < 2 ^ S := by
    rw [Nat.div_lt_iff_lt_mul hQ, hPQ]; exact h0
  -- d1 * 2^S is a multiple of 2^S below 2^64: the low bits of d0 fit below it.
  have hlt : d1 * 2 ^ S + d0 / 2 ^ (64 - S) < 2 ^ 64 := by
    have : d1 * 2 ^ S + 2 ^ S ≤ 2 ^ 64 := by
      rw [← hPQ, ← Nat.succ_mul, Nat.mul_comm (2 ^ S)]
      apply Nat.mul_le_mul_right
      have : d1 * 2 ^ S < 2 ^ (64 - S) * 2 ^ S := by rw [Nat.mul_comm (2 ^ (64 - S)), hPQ]; exact h1
      exact Nat.lt_of_mul_lt_mul_right this
    omega
  rw [Nat.mod_eq_of_lt hlt]
  have hmod : d0 * 2 ^ S % 2 ^ 64 = d0 % 2 ^ (64 - S) * 2 ^ S := by
    rw [← hPQ, Nat.mul_comm (2 ^ S), Nat.mul_mod_mul_right, Nat.mul_comm]
  have hd := Nat.div_add_mod d0 (2 ^ (64 - S))
  rw [hmod, ← hPQ]
  calc d0 % 2 ^ (64 - S) * 2 ^ S + 2 ^ S * 2 ^ (64 - S) * (d1 * 2 ^ S + d0 / 2 ^ (64 - S))
      = (2 ^ (64 - S) * (d0 / 2 ^ (64 - S)) + d0 % 2 ^ (64 - S)) * 2 ^ S +
          2 ^ S * 2 ^ (64 - S) * d1 * 2 ^ S := by ring
    _ = (d0 + 2 ^ S * 2 ^ (64 - S) * d1) * 2 ^ S := by rw [hd]; ring

/-- The funnel shift right of `b:a` by `t`, `0 < t < 64`, as `udivrem_by2()` computes it:
`(b << 1) << ~t` and `a >> t`. -/
theorem toNat_fshr_code (a b t : BitVec 64) (ht : t.toNat < 64) (ht0 : 0 < t.toNat) :
    (((b <<< 1) <<< ((t ^^^ 18446744073709551615#64).toNat % 64)) ||| (a >>> (t.toNat % 64))).toNat =
      b.toNat * 2 ^ (64 - t.toNat) % 2 ^ 64 + a.toNat / 2 ^ t.toNat := by
  rw [toNat_xor_allOnes_mod_64, Nat.mod_eq_of_lt ht, ← BitVec.shiftLeft_add,
    show 1 + (63 - t.toNat) = 64 - t.toNat by omega]
  exact toNat_shl_or_shr' a b t.toNat ht

/-- Two words shifted right by `S < 64`: the funnel shift and the shifted top word. -/
theorem fshr_words (r0 r1 S : Nat) (hS : S < 64) :
    (r1 * 2 ^ (64 - S) % 2 ^ 64 + r0 / 2 ^ S) + 2 ^ 64 * (r1 / 2 ^ S) =
      (r0 + 2 ^ 64 * r1) / 2 ^ S := by
  have hPQ : 2 ^ (64 - S) * 2 ^ S = 2 ^ 64 := by rw [← pow_add]; congr 1; omega
  have hm : r1 * 2 ^ (64 - S) % 2 ^ 64 = r1 % 2 ^ S * 2 ^ (64 - S) := by
    rw [← hPQ, Nat.mul_comm (2 ^ (64 - S)), Nat.mul_mod_mul_right]
  have hd : (r0 + 2 ^ 64 * r1) / 2 ^ S = r0 / 2 ^ S + r1 * 2 ^ (64 - S) := by
    rw [← hPQ, show r0 + 2 ^ (64 - S) * 2 ^ S * r1 = r0 + r1 * 2 ^ (64 - S) * 2 ^ S by ring,
      Nat.add_mul_div_right _ _ (Nat.two_pow_pos S)]
  rw [hm, hd]
  have := Nat.div_add_mod r1 (2 ^ S)
  rw [← hPQ]
  calc r1 % 2 ^ S * 2 ^ (64 - S) + r0 / 2 ^ S + 2 ^ (64 - S) * 2 ^ S * (r1 / 2 ^ S)
      = r0 / 2 ^ S + (2 ^ S * (r1 / 2 ^ S) + r1 % 2 ^ S) * 2 ^ (64 - S) := by ring
    _ = r0 / 2 ^ S + r1 * 2 ^ (64 - S) := by rw [this]

/-- Three words shifted left by `S` with the top bits of the word below. -/
theorem norm3_words (a0 a1 a2 S : Nat) (h0 : a0 < 2 ^ 64) (h1 : a1 < 2 ^ 64) (h2 : a2 < 2 ^ 64)
    (hS : S < 64) :
    (a1 + 2 ^ 64 * a2) * 2 ^ S + a0 / 2 ^ (64 - S) = a2 / 2 ^ (64 - S) * 2 ^ 128 +
      (a2 * 2 ^ S + a1 / 2 ^ (64 - S)) % 2 ^ 64 * 2 ^ 64 +
      (a1 * 2 ^ S + a0 / 2 ^ (64 - S)) % 2 ^ 64 := by
  have hPQ : 2 ^ S * 2 ^ (64 - S) = 2 ^ 64 := by rw [← pow_add]; congr 1; omega
  have hQ : 0 < 2 ^ (64 - S) := by positivity
  -- a * 2^S = 2^64 * (a / 2^(64 - S)) + (a % 2^(64 - S)) * 2^S, and the low bits fit below.
  have sp : ∀ a, a * 2 ^ S = 2 ^ 64 * (a / 2 ^ (64 - S)) + a % 2 ^ (64 - S) * 2 ^ S := by
    intro a
    have := Nat.div_add_mod a (2 ^ (64 - S))
    rw [← hPQ]
    calc a * 2 ^ S = (2 ^ (64 - S) * (a / 2 ^ (64 - S)) + a % 2 ^ (64 - S)) * 2 ^ S := by
          rw [this]
      _ = _ := by ring
  have lo : ∀ a b, a < 2 ^ 64 → b < 2 ^ 64 →
      (a * 2 ^ S + b / 2 ^ (64 - S)) % 2 ^ 64 = a % 2 ^ (64 - S) * 2 ^ S + b / 2 ^ (64 - S) := by
    intro a b ha hb
    have hb' : b / 2 ^ (64 - S) < 2 ^ S := by
      rw [Nat.div_lt_iff_lt_mul hQ, hPQ]; exact hb
    have ha' : a % 2 ^ (64 - S) < 2 ^ (64 - S) := Nat.mod_lt _ hQ
    have : a % 2 ^ (64 - S) * 2 ^ S + b / 2 ^ (64 - S) < 2 ^ 64 := by
      have : (a % 2 ^ (64 - S) + 1) * 2 ^ S ≤ 2 ^ (64 - S) * 2 ^ S :=
        Nat.mul_le_mul_right _ (by omega)
      rw [Nat.mul_comm (2 ^ (64 - S)), hPQ] at this
      nlinarith
    rw [sp a, Nat.add_assoc, Nat.mul_add_mod, Nat.mod_eq_of_lt this]
  have ha2 : a2 / 2 ^ (64 - S) < 2 ^ S := by
    rw [Nat.div_lt_iff_lt_mul hQ, hPQ]; exact h2
  rw [lo a2 a1 h2 h1, lo a1 a0 h1 h0]
  have e2 := sp a2
  have e1 := sp a1
  calc (a1 + 2 ^ 64 * a2) * 2 ^ S + a0 / 2 ^ (64 - S)
      = a1 * 2 ^ S + 2 ^ 64 * (a2 * 2 ^ S) + a0 / 2 ^ (64 - S) := by ring
    _ = _ := by rw [e1, e2]; ring

/-- The value of two words: below `2^128`. -/
theorem lt_2_128_of_words {a b : BitVec 64} {D : Nat} (h : a.toNat + 2 ^ 64 * b.toNat = D) :
    D < 2 ^ 128 := by
  have := a.isLt; have := b.isLt; omega

/-- The funnel shift of `a:b` left by `0 < t < 64` as the code computes it, with `srl` by `~t`. -/
theorem toNat_fshl_code (a b t : BitVec 64) (ht : t.toNat < 64) :
    ((a <<< (t.toNat % 64)) ||| ((b >>> 1) >>> ((t ^^^ 18446744073709551615#64).toNat % 64))).toNat =
      (a.toNat * 2 ^ t.toNat + b.toNat / 2 ^ (64 - t.toNat)) % 2 ^ 64 := by
  rw [toNat_xor_allOnes_mod_64, Nat.mod_eq_of_lt ht, ushiftRight_one_ushiftRight _ _ ht,
    toNat_shl_or_shr _ _ _ ht]
  have e64 : (2 : Nat) ^ 64 = 2 ^ t.toNat * 2 ^ (64 - t.toNat) := by rw [← pow_add]; congr 1; omega
  have hb : b.toNat / 2 ^ (64 - t.toNat) < 2 ^ t.toNat := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← e64]; exact b.isLt
  have hc64 : b.toNat / 2 ^ (64 - t.toNat) < 2 ^ 64 :=
    lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hm : a.toNat * 2 ^ t.toNat % 2 ^ 64 + 2 ^ t.toNat ≤ 2 ^ 64 := by
    rw [e64, Nat.mul_comm a.toNat, Nat.mul_mod_mul_left]
    have := Nat.mod_lt a.toNat (show 0 < 2 ^ (64 - t.toNat) by positivity)
    have := Nat.mul_le_mul_left (2 ^ t.toNat) (show a.toNat % 2 ^ (64 - t.toNat) + 1 ≤
      2 ^ (64 - t.toNat) by omega)
    rw [Nat.mul_add, Nat.mul_one] at this
    omega
  have hlt : a.toNat * 2 ^ t.toNat % 2 ^ 64 + b.toNat / 2 ^ (64 - t.toNat) < 2 ^ 64 := by omega
  rw [Nat.add_mod, Nat.mod_eq_of_lt hc64, Nat.mod_eq_of_lt hlt]

theorem ofNat_S_toNat {S : Nat} (h : S < 64) : (BitVec.ofNat 64 S).toNat = S := by
  rw [BitVec.toNat_ofNat]; omega

theorem ofNat_S_ne {S : Nat} (h : S < 64) (hne : ¬BitVec.ofNat 64 S = 0#64) : 0 < S := by
  rcases Nat.eq_zero_or_pos S with rfl | h0
  · exact absurd rfl hne
  · exact h0

/-- The shift amount of `srl` by `negw s`: `64 - s` for `0 < s < 64`. -/
theorem negw_shift : ∀ k < 64, 0 < k →
    (BitVec.signExtend 64 (BitVec.setWidth 32 0#64 - BitVec.setWidth 32 (BitVec.ofNat 64 k))).toNat
      % 64 = 64 - k := by
  decide

/-- The top word of a divisor normalized by `S`: at least `2^63`. -/
theorem norm2_hi {d0 d1 S : Nat} (hS : S < 64) (h0 : d0 < 2 ^ 64) (h1 : d1 * 2 ^ S < 2 ^ 64)
    (h63 : 2 ^ 63 ≤ d1 * 2 ^ S) : 2 ^ 63 ≤ (d1 * 2 ^ S + d0 / 2 ^ (64 - S)) % 2 ^ 64 := by
  have := norm2_words hS h0 h1
  have hm := Nat.mod_lt (d0 * 2 ^ S) (Nat.two_pow_pos 64)
  have : (d0 + 2 ^ 64 * d1) * 2 ^ S = d0 * 2 ^ S + 2 ^ 64 * (d1 * 2 ^ S) := by ring
  have : d0 * 2 ^ S < 2 ^ 64 * 2 ^ S := Nat.mul_lt_mul_of_pos_right h0 (Nat.two_pow_pos _)
  nlinarith

/-- Two words below `2^128` shifted left by `S` with the top bits of the word below. -/
theorem norm2_low (t0 t1 c S : Nat) (h0 : t0 < 2 ^ 64) (hc : c < 2 ^ 64) (hS : S < 64)
    (h : (t0 + 2 ^ 64 * t1) * 2 ^ S < 2 ^ 128) :
    (t0 * 2 ^ S + c / 2 ^ (64 - S)) % 2 ^ 64 + 2 ^ 64 * ((t1 * 2 ^ S + t0 / 2 ^ (64 - S)) % 2 ^ 64) =
      (t0 + 2 ^ 64 * t1) * 2 ^ S + c / 2 ^ (64 - S) := by
  have h1 : t1 < 2 ^ 64 := by
    by_contra hn
    have : 2 ^ 128 ≤ (t0 + 2 ^ 64 * t1) * 2 ^ S := by
      have : 2 ^ 128 ≤ 2 ^ 64 * t1 := by
        calc (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 := by norm_num
          _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
      nlinarith [Nat.one_le_two_pow (n := S)]
    omega
  have := norm3_words c t0 t1 S hc h0 h1 hS
  have hPQ : 2 ^ (64 - S) * 2 ^ S = 2 ^ 64 := by rw [← pow_add]; congr 1; omega
  have hzero : t1 / 2 ^ (64 - S) = 0 := by
    apply Nat.div_eq_of_lt
    by_contra hc
    have h3 : 2 ^ 64 ≤ t1 * 2 ^ S := by
      rw [← hPQ]; exact Nat.mul_le_mul_right _ (Nat.le_of_not_lt hc)
    have : 2 ^ 128 ≤ (t0 + 2 ^ 64 * t1) * 2 ^ S :=
      calc (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 := by norm_num
        _ ≤ 2 ^ 64 * (t1 * 2 ^ S) := Nat.mul_le_mul_left _ h3
        _ ≤ (t0 + 2 ^ 64 * t1) * 2 ^ S := by rw [Nat.add_mul, ← Nat.mul_assoc]; omega
    omega
  rw [hzero] at this
  omega

theorem ofNat_S_eq {S : Nat} (h : S < 64) (he : BitVec.ofNat 64 S = 0#64) : S = 0 := by
  have := congrArg BitVec.toNat he
  rwa [ofNat_S_toNat h] at this

/-- `recip3BV_spec` with the low word `t0` of the divisor from a fact about it: the run names it. -/
theorem recip3BV_spec_of {t0 : BitVec 64} {n : Nat} (_h0 : t0.toNat = n) (d1 L H : BitVec 64)
    (hd : 2 ^ 63 ≤ d1.toNat)
    (hL : L.toNat = 523520 / (d1.toNat / 2 ^ 55) * (523520 / (d1.toNat / 2 ^ 55)))
    (hH : H.toNat = 2 ^ 11 * (523520 / (d1.toNat / 2 ^ 55)) - 1) :
    (recip3BV t0 d1 L H).toNat = (2 ^ 192 - 1) / (t0.toNat + 2 ^ 64 * d1.toNat) - 2 ^ 64 :=
  recip3BV_spec t0 d1 L H hd hL hH

/-- The high word of the top digits of the numerator for `0 < S < 64`: below the normalized divisor. -/
theorem top_hi_lt {wB dn : BitVec 64} {S : Nat} (h63 : 2 ^ 63 ≤ dn.toNat) (hS : S < 64)
    (hS0 : 0 < S) :
    (wB >>> ((BitVec.signExtend 64 (BitVec.setWidth 32 0#64 - BitVec.setWidth 32
      (BitVec.ofNat 64 S))).toNat % 64)).toNat < dn.toNat := by
  rw [negw_shift S hS hS0, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := wB.isLt
  have : wB.toNat / 2 ^ (64 - S) < 2 ^ S := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show S + (64 - S) = 64 by omega]
    exact wB.isLt
  have : 2 ^ S ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- The counter of the loop of `udivrem_by2()`, n - 3. -/
theorem cnt_sub3 (n : BitVec 64) (h : 3 ≤ n.toNat) :
    n + 18446744073709551613#64 = BitVec.ofNat 64 (n.toNat - 3) := by
  bv_omega

end IntxRV.Api
