import IntxRV.DivTop1
import IntxRV.Gen.Api.udivrem_top2_3

/-!
# The division by the top two words of the divisor: `udivrem_top2<3>()`

`udivrem_top2<3>()` divides u by v of 3 words when the quotient fits in two words. It divides the
top digits of u, normalized by the count `s` of the leading zeros of v[2], by the top 128 bits
`vt` of the normalized v with two inlined copies of `udivrem_3by2()` (`top2_div_top`,
`top2_div_low`), so `q` and the remainder `r0` of `u / Q` by `v / Q` for `Q = 2^(64 - s)`. The
quotient is the quotient of the top digits, not less than `u / v` (`top2_est`), and
`r0 * Q + u mod Q - q * (v mod Q)` is `u - q * v` up to a borrow (`top2_nat`): the code multiplies
`q` only by the low word of v (`top2_submul_words`). The correction loop adds v while there is no
carry out of the 3 words (`top2_loop`).

The block lemmas run the code from the second division to the return: `top2_shift` from the
denormalization of the remainder by `fshr`, `top2_sub` from the `submul()` of the quotient words,
`top2_loop` and `top2_exit`.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- The remainder of `udivrem_top2()` from the remainder `r0` of the top digits of u by the top
digits `V / Q` of v: `rw = r0 * Q + u mod Q` less `q * (v mod Q)` is `u - q * v`, up to the borrow. -/
theorem top2_nat {U V q r0 R vl rw b Q : Nat} (hT : U / Q = q * (V / Q) + r0) (hvl : vl = V % Q)
    (hrw : rw = r0 * Q + U % Q) (hsm : R + q * vl = rw + 2 ^ 192 * b) :
    R + q * V = U + 2 ^ 192 * b := by
  calc R + q * V = R + q * (Q * (V / Q) + V % Q) := by rw [Nat.div_add_mod]
    _ = (R + q * vl) + Q * (q * (V / Q)) := by rw [hvl]; ring
    _ = rw + 2 ^ 192 * b + Q * (q * (V / Q)) := by rw [hsm]
    _ = Q * (q * (V / Q) + r0) + U % Q + 2 ^ 192 * b := by rw [hrw]; ring
    _ = Q * (U / Q) + U % Q + 2 ^ 192 * b := by rw [hT]
    _ = U + 2 ^ 192 * b := by rw [Nat.div_add_mod]

/-- The quotient of the top digits of u by the top digits of v is not less than `u / v`. -/
theorem top2_est {U V q r0 Q : Nat} (hD : 0 < V / Q) (hT : U / Q = q * (V / Q) + r0)
    (hr : r0 < V / Q) : U / V ≤ q := by
  have hQ : 0 < Q := by
    rcases Nat.eq_zero_or_pos Q with h | h
    · rw [h, Nat.div_zero] at hD; omega
    · exact h
  have hq : U / Q / (V / Q) = q := by
    rw [hT, Nat.mul_comm, Nat.mul_add_div hD, Nat.div_eq_of_lt hr, Nat.add_zero]
  have hle : V / Q * Q ≤ V := Nat.div_mul_le_self V Q
  calc U / V ≤ U / (V / Q * Q) := Nat.div_le_div_left hle (Nat.mul_pos hD hQ)
    _ = U / Q / (V / Q) := by rw [Nat.mul_comm, Nat.div_div_eq_div_mul]
    _ = q := hq

/-- Three words shifted right by `S < 64`: the funnel shifts and the shifted top word. -/
theorem fshr3_words (w0 w1 w2 S : Nat) (hS : S < 64) :
    (w1 * 2 ^ (64 - S) % 2 ^ 64 + w0 / 2 ^ S) + 2 ^ 64 * ((w2 * 2 ^ (64 - S) % 2 ^ 64 + w1 / 2 ^ S) +
      2 ^ 64 * (w2 / 2 ^ S)) = (w0 + 2 ^ 64 * (w1 + 2 ^ 64 * w2)) / 2 ^ S := by
  have h1 := fshr_words w0 w1 S hS
  have h2 := fshr_words (w0 + 2 ^ 64 * w1) w2 S hS
  have hPQ : 2 ^ (64 - S) * 2 ^ S = 2 ^ 64 := by rw [← pow_add]; congr 1; omega
  have hP : 0 < 2 ^ S := by positivity
  have hm : w2 * 2 ^ (64 - S) % 2 ^ 64 = w2 % 2 ^ S * 2 ^ (64 - S) := by
    rw [← hPQ, Nat.mul_comm (2 ^ (64 - S)), Nat.mul_mod_mul_right]
  -- (w0 + 2^64 w1 + 2^128 w2) / 2^S = (w0 + 2^64 w1) / 2^S + 2^(128 - S) w2.
  have hd : (w0 + 2 ^ 64 * (w1 + 2 ^ 64 * w2)) / 2 ^ S =
      (w0 + 2 ^ 64 * w1) / 2 ^ S + 2 ^ 64 * (w2 * 2 ^ (64 - S)) := by
    rw [show w0 + 2 ^ 64 * (w1 + 2 ^ 64 * w2) = w0 + 2 ^ 64 * w1 +
      2 ^ 64 * (w2 * 2 ^ (64 - S)) * 2 ^ S by rw [← hPQ]; ring, Nat.add_mul_div_right _ _ hP]
  rw [hd, ← h1]
  have hw2 := Nat.div_add_mod w2 (2 ^ S)
  have : w2 * 2 ^ (64 - S) = 2 ^ 64 * (w2 / 2 ^ S) + w2 % 2 ^ S * 2 ^ (64 - S) := by
    conv_lhs => rw [← hw2]
    rw [← hPQ]; ring
  rw [hm, this]
  ring

/-- The 3-word remainder of `udivrem_top2()`: `r0 * 2^(64 - S) + u0 mod 2^(64 - S)`, from the shift
of `u0 << S` and the words of `r0` right by `S`. -/
theorem top2_rw (u0 r0 S : Nat) (hS : S < 64) :
    (u0 * 2 ^ S % 2 ^ 64 + 2 ^ 64 * r0) / 2 ^ S = r0 * 2 ^ (64 - S) + u0 % 2 ^ (64 - S) := by
  have hPQ : 2 ^ S * 2 ^ (64 - S) = 2 ^ 64 := by rw [← pow_add]; congr 1; omega
  have hP : 0 < 2 ^ S := by positivity
  have hm : u0 * 2 ^ S % 2 ^ 64 = u0 % 2 ^ (64 - S) * 2 ^ S := by
    rw [← hPQ, Nat.mul_comm (2 ^ S) (2 ^ (64 - S)), Nat.mul_mod_mul_right]
  rw [hm, show u0 % 2 ^ (64 - S) * 2 ^ S + 2 ^ 64 * r0 =
    (r0 * 2 ^ (64 - S) + u0 % 2 ^ (64 - S)) * 2 ^ S by rw [← hPQ]; ring,
    Nat.mul_div_cancel _ hP]

/-- `u - s - bin` with its borrow `u < u - s` or `u - s < u - s - bin` as a condition, for a borrow
in of 0 or 1. -/
theorem defn_sub_borrow_cond {d r u s bin : BitVec 64} (hd : Defn d (u - s)) (hr : Defn r (d - bin))
    (hbin : bin.toNat ≤ 1) :
    r.toNat + s.toNat + bin.toNat = u.toNat + 2 ^ 64 * (if u < d ∨ d < r then 1 else 0) := by
  rw [hr.eq, hd.eq]
  have hu := u.isLt; have hs := s.isLt
  have h1 : (u - s).toNat = (u.toNat + (2 ^ 64 - s.toNat)) % 2 ^ 64 := by
    rw [BitVec.toNat_sub]; omega
  have h2 : (u - s - bin).toNat = ((u - s).toNat + (2 ^ 64 - bin.toNat)) % 2 ^ 64 := by
    rw [BitVec.toNat_sub]; omega
  by_cases c1 : u < u - s <;> by_cases c2 : u - s < u - s - bin <;>
    simp only [c1, c2, true_or, or_true, or_self, ↓reduceIte] <;>
    simp only [BitVec.lt_def] at c1 c2 <;> omega

/-- The 1-word `submul()` of each word of the quotient and their borrows in the RV64 code of
`udivrem_top2<3>()`: the words `R` of `rw - q * vl` and the borrow out of them, from the definitions
of the values (in the order in which `apply` and `assumption` find them from the names of the
results). -/
theorem top2_submul_words {rw0 rw1 rw2 vl q0 q1 p0 h0 p1 h1 R0 y1 c0 c1 b0 b1 R1 c2 z2 R2 : BitVec 64}
    (hR2 : Defn R2 (z2 - c2)) (hz2 : Defn z2 (rw2 - b1)) (hc2 : Defn c2 (if y1 < R1 then 1#64 else 0#64))
    (hR1 : Defn R1 (y1 - b0)) (hb1 : Defn b1 (h1 + c1)) (hb0 : Defn b0 (h0 + c0))
    (hc1 : Defn c1 (if rw1 < y1 then 1#64 else 0#64)) (hc0 : Defn c0 (if rw0 < R0 then 1#64 else 0#64))
    (hy1 : Defn y1 (rw1 - p1)) (hR0 : Defn R0 (rw0 - p0)) (hh1 : Defn h1 (mulhu vl q1))
    (hp1 : Defn p1 (vl * q1)) (hh0 : Defn h0 (mulhu vl q0)) (hp0 : Defn p0 (vl * q0)) :
    R0.toNat + 2 ^ 64 * (R1.toNat + 2 ^ 64 * R2.toNat) +
        (q0.toNat + 2 ^ 64 * q1.toNat) * vl.toNat =
      rw0.toNat + 2 ^ 64 * (rw1.toNat + 2 ^ 64 * rw2.toNat) +
        2 ^ 192 * (if rw2 < z2 ∨ z2 < R2 then 1 else 0) := by
  have m0 := defn_mul_mulhu hp0 hh0
  have m1 := defn_mul_mulhu hp1 hh1
  have k0 := defn_mulhu_le hh0
  have k1 := defn_mulhu_le hh1
  have l0 := defn_bit_le hc0
  have l1 := defn_bit_le hc1
  have l2 := defn_bit_le hc2
  have n0 := defn_sub_borrow0 hR0 hc0
  have n1 := defn_sub_borrow0 hy1 hc1
  have n2 := defn_sub_borrow0 hR1 hc2
  have e0 := defn_add_exact hb0 (by omega)
  have e1 := defn_add_exact hb1 (by omega)
  have n3 := defn_sub_borrow_cond hz2 hR2 l2
  have hd : (q0.toNat + 2 ^ 64 * q1.toNat) * vl.toNat =
      vl.toNat * q0.toNat + 2 ^ 64 * (vl.toNat * q1.toNat) := by ring
  rw [hd]
  generalize (if rw2 < z2 ∨ z2 < R2 then 1 else 0) = c at *
  omega

/-- A 2-word quotient less 1: `q0 - 1` and `q1` less the borrow `q0 < q0 - 1`. -/
theorem dec2_toNat {q0 q1 bq q1' : BitVec 64}
    (hbq : Defn bq (if q0 < q0 + 18446744073709551615#64 then 1#64 else 0#64))
    (hq1 : Defn q1' (q1 - bq)) (hq : 0 < q0.toNat + 2 ^ 64 * q1.toNat) :
    (q0 + 18446744073709551615#64).toNat + 2 ^ 64 * q1'.toNat + 1 =
      q0.toNat + 2 ^ 64 * q1.toNat := by
  rw [hq1.eq, hbq.eq]
  have := q0.isLt; have := q1.isLt
  by_cases h0 : q0.toNat = 0
  · have hc : q0 < q0 + 18446744073709551615#64 := by
      rw [BitVec.lt_def, BitVec.toNat_add, h0]; simp
    rw [if_pos hc, BitVec.toNat_sub, BitVec.toNat_add, h0]
    simp
    omega
  · have hc : ¬q0 < q0 + 18446744073709551615#64 := by
      rw [BitVec.lt_def, BitVec.toNat_add]; simp; omega
    rw [if_neg hc, BitVec.toNat_sub, BitVec.toNat_add]
    simp
    omega

/-- The addition of 3 words in the correction loop of `udivrem_top2<3>()`: the words `n` of `r + v`
and the carry out of them as a condition. -/
theorem add3c_words {r0 r1 r2 v0 v1 v2 n0 a1 c0 e1 n1 f1 c1 a2 n2 : BitVec 64}
    (hn0 : Defn n0 (r0 + v0)) (hn1 : Defn n1 (a1 + c0)) (ha1 : Defn a1 (r1 + v1))
    (hc0 : Defn c0 (if n0 < r0 then 1#64 else 0#64))
    (he1 : Defn e1 (if a1 < r1 then 1#64 else 0#64))
    (hf1 : Defn f1 (if n1 < a1 then 1#64 else 0#64)) (hn2 : Defn n2 (a2 + c1))
    (ha2 : Defn a2 (r2 + v2)) (hc1 : Defn c1 (e1 ||| f1)) :
    n0.toNat + 2 ^ 64 * (n1.toNat + 2 ^ 64 * n2.toNat) +
        2 ^ 192 * (if a2 < r2 ∨ n2 < a2 then 1 else 0) =
      r0.toNat + 2 ^ 64 * (r1.toNat + 2 ^ 64 * r2.toNat) +
        (v0.toNat + 2 ^ 64 * (v1.toNat + 2 ^ 64 * v2.toNat)) := by
  have e0 := defn_carry_left hn0 hc0
  have l0 := defn_bit_le hc0
  obtain ⟨e1', l1⟩ := defn_add_carry ha1 he1 hn1 hf1 hc1 l0
  rw [hn2.eq, ha2.eq]
  have := r2.isLt; have := v2.isLt
  have h1 : (r2 + v2).toNat = (r2.toNat + v2.toNat) % 2 ^ 64 := BitVec.toNat_add _ _
  have h2 : (r2 + v2 + c1).toNat = ((r2 + v2).toNat + c1.toNat) % 2 ^ 64 := BitVec.toNat_add _ _
  by_cases d1 : r2 + v2 < r2 <;> by_cases d2 : r2 + v2 + c1 < r2 + v2 <;>
    simp only [d1, d2, true_or, or_true, or_self, ↓reduceIte] <;>
    simp only [BitVec.lt_def] at d1 d2 <;> omega

/-- The result of a division by 3 words stored as the quotient `q1:q0` and the remainder `a`. -/
theorem words_ret8q2 (m : Mem) (r q0 q1 a0 a1 a2 z : BitVec 64) (hz : z = 0#64)
    (hr : r.toNat + 64 ≤ 2 ^ 64)
    (m' : Mem) (hm : m' = memStore (memStore (memStore (memStore (memStore (memStore (memStore
      (memStore m r.toNat q0) (r + 8#64).toNat q1) (r + 16#64).toNat z)
      (r + 24#64).toNat z) (r + 32#64).toNat a0) (r + 40#64).toNat a1) (r + 48#64).toNat a2)
      (r + 56#64).toNat z) :
    words m' r 4 = q0.toNat + 2 ^ 64 * q1.toNat ∧
      words m' (r + 32#64) 4 = a0.toNat + 2 ^ 64 * (a1.toNat + 2 ^ 64 * a2.toNat) ∧
      UnchangedExcept m m' r 64 := by
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

/-- The end of `udivrem_top2<3>()` from 0x3bc: the stores of the quotient in `a1:t2` and the
remainder in `a4:a3:a2`, and the return. -/
theorem top2_exit {hi : BitVec 20} {lo : BitVec 12} (base T : BitVec 64) (x : Regs) (m : Mem)
    (hpre : udivrem_top2_3.pre x m) (hr : x.get 1#5 &&& 3 = 0) (x' : Regs) (m' : Mem)
    (h10 : x'.get 10#5 = x.get 10#5) (h1 : x'.get 1#5 = x.get 1#5)
    (hcs : ∀ i ∈ calleeSaved, x' i = x i)
    (hm : UnchangedExcept2 m m' (x.get 10#5) 64 (x.get 2#5 - 32#64) 32)
    (hqr : (x'.get 7#5).toNat + 2 ^ 64 * (x'.get 11#5).toNat =
        words m (x.get 11#5) 4 / words m (x.get 12#5) 4 ∧
      (x'.get 12#5).toNat + 2 ^ 64 * ((x'.get 13#5).toNat + 2 ^ 64 * (x'.get 14#5).toNat) =
        words m (x.get 11#5) 4 % words m (x.get 12#5) 4) :
    Reach (bufWords (x.get 11#5) 4 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 8 ++
        bufWords (x.get 2#5 - 32#64) 4 ++ bufWords T 256) (udivrem_top2_3_progAt hi lo) base
      (pcAt base 239) x' m' (x.get 1#5) (udivrem_top2_3.post x m) := by
  have hpre' := hpre
  simp only [udivrem_top2_3.pre, Buf] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hra, hrn⟩, -⟩ := hpre'
  rw [← h10]
  have hrn' : (x'.get 10#5).toNat + 64 ≤ 2 ^ 64 := h10 ▸ hrn
  rv_exec
  rv_val
  rw [h1, update_aligned hr]
  refine Reach.refl ?_
  have hz : x'.get 0#5 = 0#64 := by rw [show (0#5 : BitVec 5) = 0 from rfl, Regs.get_zero]; rfl
  have hw := words_ret8q2 m' (x'.get 10#5) (x'.get 7#5) (x'.get 11#5) (x'.get 12#5) (x'.get 13#5)
    (x'.get 14#5) _ hz hrn' _ rfl
  simp only [udivrem_top2_3.post]
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

/-- The quotient of `udivrem_top2()` in the loop is larger than `u / v`: the borrow is 1. -/
theorem top2_q_gt {R q U V : Nat} (hR : R < 2 ^ 192) (h : R + q * V = U + 2 ^ 192) :
    U / V < q := top1_q_gt (b := 1) hR (by rw [h]; ring) (by norm_num)

theorem add3c_carry {r0 r1 r2 v0 v1 v2 n0 a1 c0 e1 n1 f1 c1 a2 n2 : BitVec 64}
    (hn0 : Defn n0 (r0 + v0)) (hn1 : Defn n1 (a1 + c0)) (ha1 : Defn a1 (r1 + v1))
    (hc0 : Defn c0 (if n0 < r0 then 1#64 else 0#64))
    (he1 : Defn e1 (if a1 < r1 then 1#64 else 0#64))
    (hf1 : Defn f1 (if n1 < a1 then 1#64 else 0#64)) (hn2 : Defn n2 (a2 + c1))
    (ha2 : Defn a2 (r2 + v2)) (hc1 : Defn c1 (e1 ||| f1)) (hc : a2 < r2 ∨ n2 < a2) :
    n0.toNat + 2 ^ 64 * (n1.toNat + 2 ^ 64 * n2.toNat) + 2 ^ 192 =
      r0.toNat + 2 ^ 64 * (r1.toNat + 2 ^ 64 * r2.toNat) +
        (v0.toNat + 2 ^ 64 * (v1.toNat + 2 ^ 64 * v2.toNat)) := by
  have h := add3c_words hn0 hn1 ha1 hc0 he1 hf1 hn2 ha2 hc1
  rwa [if_pos hc, Nat.mul_one] at h

theorem add3c_nocarry {r0 r1 r2 v0 v1 v2 n0 a1 c0 e1 n1 f1 c1 a2 n2 : BitVec 64}
    (hn0 : Defn n0 (r0 + v0)) (hn1 : Defn n1 (a1 + c0)) (ha1 : Defn a1 (r1 + v1))
    (hc0 : Defn c0 (if n0 < r0 then 1#64 else 0#64))
    (he1 : Defn e1 (if a1 < r1 then 1#64 else 0#64))
    (hf1 : Defn f1 (if n1 < a1 then 1#64 else 0#64)) (hn2 : Defn n2 (a2 + c1))
    (ha2 : Defn a2 (r2 + v2)) (hc1 : Defn c1 (e1 ||| f1)) (h1 : ¬a2 < r2) (h2 : ¬n2 < a2) :
    n0.toNat + 2 ^ 64 * (n1.toNat + 2 ^ 64 * n2.toNat) =
      r0.toNat + 2 ^ 64 * (r1.toNat + 2 ^ 64 * r2.toNat) +
        (v0.toNat + 2 ^ 64 * (v1.toNat + 2 ^ 64 * v2.toNat)) := by
  have h := add3c_words hn0 hn1 ha1 hc0 he1 hf1 hn2 ha2 hc1
  rwa [if_neg (by first | rv_taut | tauto), Nat.mul_zero, Nat.add_zero] at h

/-- The quotient and the remainder after the last correction of `udivrem_top2()`. -/
theorem top2_exit_nat {R' q' R q U V : Nat} (h : R' + 2 ^ 192 = R + V) (hd : q' + 1 = q)
    (hsm : R + q * V = U + 2 ^ 192) (hR : R < 2 ^ 192) : q' = U / V ∧ R' = U % V := by
  have : q * V = q' * V + V := by rw [← hd]; ring
  exact div_mod_of_lt (by omega) (by omega)

/-- The invariant of the loop of `udivrem_top2()` after a correction without a carry. -/
theorem top2_cont_nat {R' q' R q U V : Nat} (h : R' = R + V) (hd : q' + 1 = q)
    (hsm : R + q * V = U + 2 ^ 192) : R' + q' * V = U + 2 ^ 192 := by
  have : q * V = q' * V + V := by rw [← hd]; ring
  omega

/-- The registers and the memory at the head of the correction loop of `udivrem_top2<3>()`, at
0x3ec: `a5:a3:a4 + q * v = u + 2^192`, with the quotient `q` in `a1:t1` and the words of v in
`a6:a7:t0`; `n` the excess of `q`. -/
def top2Loop (x : Regs) (m : Mem) (n : Nat) (x' : Regs) (m' : Mem) : Prop :=
  x'.get 10#5 = x.get 10#5 ∧ x'.get 1#5 = x.get 1#5 ∧ (∀ i ∈ calleeSaved, x' i = x i) ∧
    UnchangedExcept2 m m' (x.get 10#5) 64 (x.get 2#5 - 32#64) 32 ∧
    (x'.get 16#5).toNat + 2 ^ 64 * ((x'.get 17#5).toNat + 2 ^ 64 * (x'.get 5#5).toNat) =
      words m (x.get 12#5) 4 ∧
    (x'.get 15#5).toNat + 2 ^ 64 * ((x'.get 13#5).toNat + 2 ^ 64 * (x'.get 14#5).toNat) +
      ((x'.get 6#5).toNat + 2 ^ 64 * (x'.get 11#5).toNat) * words m (x.get 12#5) 4 =
      words m (x.get 11#5) 4 + 2 ^ 192 ∧
    n = (x'.get 6#5).toNat + 2 ^ 64 * (x'.get 11#5).toNat -
      words m (x.get 11#5) 4 / words m (x.get 12#5) 4

/-- The correction loop of `udivrem_top2<3>()` from 0x3ec. -/
theorem top2_loop {hi : BitVec 20} {lo : BitVec 12} (base T : BitVec 64) (x : Regs) (m : Mem)
    (hpre : udivrem_top2_3.pre x m) (hr : x.get 1#5 &&& 3 = 0) :
    ∀ n x' m', top2Loop x m n x' m' →
    Reach (bufWords (x.get 11#5) 4 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 8 ++
        bufWords (x.get 2#5 - 32#64) 4 ++ bufWords T 256) (udivrem_top2_3_progAt hi lo) base
      (pcAt base 251) x' m' (x.get 1#5) (udivrem_top2_3.post x m) := by
  apply Reach.loop (top2Loop x m)
  intro n x' m' h ih
  obtain ⟨h10, h1, hcs, hm, hv, hsm, hn⟩ := h
  have hR := words3_lt (x'.get 15#5) (x'.get 13#5) (x'.get 14#5)
  have hlt := top2_q_gt hR hsm
  rv_step
  rv_exec_cut 239 251
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
    | (rv_not_at 239; skip)
    | (have ha := add3c_carry (r0 := x'.get 15#5) (r1 := x'.get 13#5) (r2 := x'.get 14#5)
         (v0 := x'.get 16#5) (v1 := x'.get 17#5) (v2 := x'.get 5#5) rfl rfl rfl rfl rfl rfl rfl rfl rfl
         (by first | rv_taut | tauto)
       rw [hv] at ha
       refine top2_exit base T x m hpre hr _ _ ?_ ?_ ?_ hm ?_
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

theorem top2_submul_b {rw0 rw1 rw2 vl q0 q1 p0 h0 p1 h1 R0 y1 c0 c1 b0 b1 R1 c2 z2 R2 : BitVec 64}
    (hR2 : Defn R2 (z2 - c2)) (hz2 : Defn z2 (rw2 - b1)) (hc2 : Defn c2 (if y1 < R1 then 1#64 else 0#64))
    (hR1 : Defn R1 (y1 - b0)) (hb1 : Defn b1 (h1 + c1)) (hb0 : Defn b0 (h0 + c0))
    (hc1 : Defn c1 (if rw1 < y1 then 1#64 else 0#64)) (hc0 : Defn c0 (if rw0 < R0 then 1#64 else 0#64))
    (hy1 : Defn y1 (rw1 - p1)) (hR0 : Defn R0 (rw0 - p0)) (hh1 : Defn h1 (mulhu vl q1))
    (hp1 : Defn p1 (vl * q1)) (hh0 : Defn h0 (mulhu vl q0)) (hp0 : Defn p0 (vl * q0)) (hc : rw2 < z2 ∨ z2 < R2) :
    R0.toNat + 2 ^ 64 * (R1.toNat + 2 ^ 64 * R2.toNat) +
        (q0.toNat + 2 ^ 64 * q1.toNat) * vl.toNat =
      rw0.toNat + 2 ^ 64 * (rw1.toNat + 2 ^ 64 * rw2.toNat) + 2 ^ 192 := by
  have h := top2_submul_words hR2 hz2 hc2 hR1 hb1 hb0 hc1 hc0 hy1 hR0 hh1 hp1 hh0 hp0
  rwa [if_pos hc, Nat.mul_one] at h

theorem top2_submul_nb {rw0 rw1 rw2 vl q0 q1 p0 h0 p1 h1 R0 y1 c0 c1 b0 b1 R1 c2 z2 R2 : BitVec 64}
    (hR2 : Defn R2 (z2 - c2)) (hz2 : Defn z2 (rw2 - b1)) (hc2 : Defn c2 (if y1 < R1 then 1#64 else 0#64))
    (hR1 : Defn R1 (y1 - b0)) (hb1 : Defn b1 (h1 + c1)) (hb0 : Defn b0 (h0 + c0))
    (hc1 : Defn c1 (if rw1 < y1 then 1#64 else 0#64)) (hc0 : Defn c0 (if rw0 < R0 then 1#64 else 0#64))
    (hy1 : Defn y1 (rw1 - p1)) (hR0 : Defn R0 (rw0 - p0)) (hh1 : Defn h1 (mulhu vl q1))
    (hp1 : Defn p1 (vl * q1)) (hh0 : Defn h0 (mulhu vl q0)) (hp0 : Defn p0 (vl * q0)) (h1 : ¬rw2 < z2) (h2 : ¬z2 < R2) :
    R0.toNat + 2 ^ 64 * (R1.toNat + 2 ^ 64 * R2.toNat) +
        (q0.toNat + 2 ^ 64 * q1.toNat) * vl.toNat =
      rw0.toNat + 2 ^ 64 * (rw1.toNat + 2 ^ 64 * rw2.toNat) := by
  have h := top2_submul_words hR2 hz2 hc2 hR1 hb1 hb0 hc1 hc0 hy1 hR0 hh1 hp1 hh0 hp0
  rwa [if_neg (by first | rv_taut | tauto), Nat.mul_zero, Nat.add_zero] at h

/-- The quotient and the remainder of `udivrem_top2()` when the remainder has no borrow. -/
theorem top2_sub_exit_nat {U V q r0 R vl rw Q : Nat} (hV : 0 < V) (hD : 0 < V / Q)
    (hT : U / Q = q * (V / Q) + r0) (hr : r0 < V / Q) (hvl : vl = V % Q)
    (hrw : rw = r0 * Q + U % Q) (hs : R + q * vl = rw) : q = U / V ∧ R = U % V := by
  have h := top2_nat (b := 0) hT hvl hrw (by rw [hs]; ring)
  have hq := top2_est hD hT hr
  have := Nat.mul_le_mul_right V hq
  have := Nat.div_add_mod' U V
  have := Nat.mod_lt U hV
  exact div_mod_of_lt (by omega) (by omega)

/-- The words of v of 3 words, with the top word 0. -/
theorem words_v3 (m : Mem) (a : BitVec 64) (h : memWord m (a + 24#64).toNat = 0#64) :
    (memWord m a.toNat).toNat + 2 ^ 64 * ((memWord m (a + 8#64).toNat).toNat +
      2 ^ 64 * (memWord m (a + 16#64).toNat).toNat) = words m a 4 := by
  simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
    Nat.add_zero]
  rw [h]
  simp

/-- The end of `udivrem_top2<3>()` from the `submul()` of the quotient words at 0x370: the
remainder `rw = r0 * Q + u mod Q` in `a7:t2:a6`, `v mod Q` in a3 and the quotient in `a1:t1`, for
the quotient `q` and the remainder `r0` of `u / Q` by `v / Q`. -/
theorem top2_sub {hi : BitVec 20} {lo : BitVec 12} (base T : BitVec 64) (x : Regs) (m : Mem)
    (hpre : udivrem_top2_3.pre x m) (hr : x.get 1#5 &&& 3 = 0) (x' : Regs) (m' : Mem)
    (h10 : x'.get 10#5 = x.get 10#5) (h1 : x'.get 1#5 = x.get 1#5)
    (h12 : x'.get 12#5 = x.get 12#5) (hcs : ∀ i ∈ calleeSaved, x' i = x i)
    (hm : UnchangedExcept2 m m' (x.get 10#5) 64 (x.get 2#5 - 32#64) 32) (r0 Q : Nat)
    (hD : 0 < words m (x.get 12#5) 4 / Q)
    (hT : words m (x.get 11#5) 4 / Q =
      ((x'.get 6#5).toNat + 2 ^ 64 * (x'.get 11#5).toNat) * (words m (x.get 12#5) 4 / Q) + r0)
    (hr0 : r0 < words m (x.get 12#5) 4 / Q)
    (hvl : (x'.get 13#5).toNat = words m (x.get 12#5) 4 % Q)
    (hrw : (x'.get 16#5).toNat + 2 ^ 64 * ((x'.get 7#5).toNat + 2 ^ 64 * (x'.get 17#5).toNat) =
      r0 * Q + words m (x.get 11#5) 4 % Q) :
    Reach (bufWords (x.get 11#5) 4 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 8 ++
        bufWords (x.get 2#5 - 32#64) 4 ++ bufWords T 256) (udivrem_top2_3_progAt hi lo) base
      (pcAt base 220) x' m' (x.get 1#5) (udivrem_top2_3.post x m) := by
  have hpre' := hpre
  simp only [udivrem_top2_3.pre, Buf] at hpre'
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
  rv_exec_cut 239 251
  all_goals try simp only [zopz0zI_u_eq, decide_eq_true_eq, decide_eq_false_iff_not] at *
  all_goals try rv_conds
  all_goals
    simp only [Defn] at *
    subst_vars
    rw [h12]
  -- No borrow: the end.
  all_goals first
    | (rv_not_at 239; skip)
    | (have hs := top2_submul_nb (rw0 := x'.get 16#5) (rw1 := x'.get 7#5) (rw2 := x'.get 17#5)
         (vl := x'.get 13#5) (q0 := x'.get 6#5) (q1 := x'.get 11#5) rfl rfl rfl rfl rfl rfl rfl rfl
         rfl rfl rfl rfl rfl rfl (by assumption) (by assumption)
       refine top2_exit base T x m hpre hr _ _ ?_ ?_ ?_ hm ?_
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
      rfl rfl rfl rfl rfl rfl (by first | rv_taut | tauto)
    refine top2_loop base T x m hpre hr _ _ _ ⟨?_, ?_, ?_, hm, ?_, ?_, rfl⟩
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

/-- The low `64 - t` bits of a word by the mask `2^64 - 1 >> t`. -/
theorem toNat_and_mask (v t : BitVec 64) (ht : t.toNat < 64) :
    (v &&& (18446744073709551615#64 >>> (t.toNat % 64))).toNat = v.toNat % 2 ^ (64 - t.toNat) := by
  rw [Nat.mod_eq_of_lt ht, BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat, show 18446744073709551615 % 2 ^ 64 = 2 ^ 64 - 1 from rfl]
  have hPQ : 2 ^ (64 - t.toNat) * 2 ^ t.toNat = 2 ^ 64 := by rw [← pow_add]; congr 1; omega
  have hP : 1 ≤ 2 ^ t.toNat := Nat.one_le_two_pow
  have hQ : 1 ≤ 2 ^ (64 - t.toNat) := Nat.one_le_two_pow
  have h : (2 ^ 64 - 1) / 2 ^ t.toNat = 2 ^ (64 - t.toNat) - 1 := by
    apply Nat.div_eq_of_lt_le
    · rw [Nat.sub_mul, Nat.one_mul]; omega
    · rw [Nat.sub_add_cancel hQ]; omega
  rw [h, Nat.and_two_pow_sub_one_eq_mod]

/-- A number modulo a power of 2 that divides 2^64 by its low word. -/
theorem mod_low (a0 r S : Nat) (hS : S ≤ 64) :
    (a0 + 2 ^ 64 * r) % 2 ^ (64 - S) = a0 % 2 ^ (64 - S) := by
  have : 2 ^ 64 = 2 ^ (64 - S) * 2 ^ S := by rw [← pow_add]; congr 1; omega
  rw [this, Nat.mul_assoc, Nat.add_mul_mod_self_left]

/-- The end of `udivrem_top2<3>()` after the division of the top digits, from 0x338: the quotient
`q` in `a1:t1` and the remainder `r0` in `t3:t2` of `u / Q` by `v / Q` for `Q = 2^(64 - s)`, the
shift `s` in a4 and `~s` in a5, and the words u[0] in t0 and v[0] in a3. -/
theorem top2_shift {hi : BitVec 20} {lo : BitVec 12} (base T : BitVec 64) (x : Regs) (m : Mem)
    (hpre : udivrem_top2_3.pre x m) (hr : x.get 1#5 &&& 3 = 0) (x' : Regs) (m' : Mem)
    (h10 : x'.get 10#5 = x.get 10#5) (h1 : x'.get 1#5 = x.get 1#5)
    (h12 : x'.get 12#5 = x.get 12#5) (hcs : ∀ i ∈ calleeSaved, x' i = x i)
    (hm : UnchangedExcept2 m m' (x.get 10#5) 64 (x.get 2#5 - 32#64) 32)
    (hS : (x'.get 14#5).toNat < 64) (h15 : x'.get 15#5 = x'.get 14#5 ^^^ 18446744073709551615#64)
    (hv0 : x'.get 13#5 = memWord m (x.get 12#5).toNat)
    (hu0 : x'.get 5#5 = memWord m (x.get 11#5).toNat)
    (hD : 0 < words m (x.get 12#5) 4 / 2 ^ (64 - (x'.get 14#5).toNat))
    (hT : words m (x.get 11#5) 4 / 2 ^ (64 - (x'.get 14#5).toNat) =
      ((x'.get 6#5).toNat + 2 ^ 64 * (x'.get 11#5).toNat) *
        (words m (x.get 12#5) 4 / 2 ^ (64 - (x'.get 14#5).toNat)) +
      ((x'.get 7#5).toNat + 2 ^ 64 * (x'.get 28#5).toNat))
    (hr0 : (x'.get 7#5).toNat + 2 ^ 64 * (x'.get 28#5).toNat <
      words m (x.get 12#5) 4 / 2 ^ (64 - (x'.get 14#5).toNat)) :
    Reach (bufWords (x.get 11#5) 4 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 8 ++
        bufWords (x.get 2#5 - 32#64) 4 ++ bufWords T 256) (udivrem_top2_3_progAt hi lo) base
      (pcAt base 206) x' m' (x.get 1#5) (udivrem_top2_3.post x m) := by
  -- The words v mod Q and u mod Q by the low words.
  have hvq : words m (x.get 12#5) 4 % 2 ^ (64 - (x'.get 14#5).toNat) =
      (memWord m (x.get 12#5).toNat).toNat % 2 ^ (64 - (x'.get 14#5).toNat) := by
    simp only [words]; exact mod_low _ _ _ (by omega)
  have huq : words m (x.get 11#5) 4 % 2 ^ (64 - (x'.get 14#5).toNat) =
      (memWord m (x.get 11#5).toNat).toNat % 2 ^ (64 - (x'.get 14#5).toNat) := by
    simp only [words]; exact mod_low _ _ _ (by omega)
  have hz0 : x'.get 0#5 = 0#64 := by rw [show (0#5 : BitVec 5) = 0 from rfl, Regs.get_zero]; rfl
  have hPQ : 2 ^ (x'.get 14#5).toNat * 2 ^ (64 - (x'.get 14#5).toNat) = 2 ^ 64 := by
    rw [← pow_add]; congr 1; omega
  rv_exec_cut 220
  all_goals
    simp only [Defn] at *
    subst_vars
    simp only [hz0, BitVec.zero_add] at *
  all_goals
    refine top2_sub base T x m hpre hr _ _ ?_ ?_ ?_ ?_ hm
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

/-- `div3by2BV` with the products in the order of the second copy inlined in `udivrem_top2<3>()`,
`u2 * v` and `mulhu u2 v`, and its product by the high word 0. -/
def div3by2BVz (u2 u1 u0 d0 d1 v : BitVec 64) : BitVec 64 × BitVec 64 × BitVec 64 :=
  let p0 := u2 * v
  let p1 := mulhu u2 v
  let q0 := p0 + u1
  let q1 := u2 + 0#64 * v + p1 + (if q0 < p0 then 1#64 else 0#64)
  let rd0 := u0 - q1 * d0
  let rd1 := u1 - (q1 * d1 + mulhu q1 d0) - (if u0 < rd0 then 1#64 else 0#64)
  let r0 := rd0 - d0
  let r1 := rd1 - d1 - (if rd0 < r0 then 1#64 else 0#64)
  let s0 := if r1 < q0 then r0 else rd0
  let s1 := if r1 < q0 then r1 else rd1
  let q := q1 + (if r1 < q0 then 1#64 else 0#64)
  if (if s1 = d1 then s0 < d0 else s1 < d1) then (q, s0, s1)
  else (q + 1#64, s0 - d0, s1 - d1 - (if s0 < s0 - d0 then 1#64 else 0#64))

theorem div3by2BVz_spec (u2 u1 u0 d0 d1 v : BitVec 64)
    (hD1 : 2 ^ 127 ≤ d0.toNat + 2 ^ 64 * d1.toNat)
    (hX : u2.toNat * 2 ^ 64 + u1.toNat < d0.toNat + 2 ^ 64 * d1.toNat)
    (hv : v.toNat = (2 ^ 192 - 1) / (d0.toNat + 2 ^ 64 * d1.toNat) - 2 ^ 64) :
    (div3by2BVz u2 u1 u0 d0 d1 v).1.toNat =
        (u2.toNat * 2 ^ 128 + u1.toNat * 2 ^ 64 + u0.toNat) / (d0.toNat + 2 ^ 64 * d1.toNat) ∧
      (div3by2BVz u2 u1 u0 d0 d1 v).2.1.toNat +
          2 ^ 64 * (div3by2BVz u2 u1 u0 d0 d1 v).2.2.toNat =
        (u2.toNat * 2 ^ 128 + u1.toNat * 2 ^ 64 + u0.toNat) % (d0.toNat + 2 ^ 64 * d1.toNat) := by
  have h := div3by2BV_spec u2 u1 u0 d0 d1 v hD1 hX hv
  simp only [div3by2BV, BitVec.mul_comm v u2, mulhu_comm v u2] at h
  simp only [div3by2BVz, BitVec.zero_mul, BitVec.add_zero]
  exact h

/-- The first inlined `udivrem_3by2()` of `udivrem_top2<3>()`, from 0x230 to 0x2a8: `t3:a1:t2` by
`a6:a7` with the reciprocal in t4, to the quotient in a1 and the remainder in `t3:t2`, with t5 0. -/
theorem top2_div_top {A : List (BitVec 64)} {hi : BitVec 20} {lo : BitVec 12} (base : BitVec 64)
    (x : Regs) (m : Mem)
    (hd : 2 ^ 127 ≤ (x.get 17#5).toNat + 2 ^ 64 * (x.get 16#5).toNat)
    (hu : (x.get 28#5).toNat * 2 ^ 64 + (x.get 11#5).toNat <
      (x.get 17#5).toNat + 2 ^ 64 * (x.get 16#5).toNat)
    (hv : (x.get 29#5).toNat =
      (2 ^ 192 - 1) / ((x.get 17#5).toNat + 2 ^ 64 * (x.get 16#5).toNat) - 2 ^ 64) :
    Reach A (udivrem_top2_3_progAt hi lo) base (pcAt base 140) x m (pcAt base 170) (fun x' m' =>
      m' = m ∧ x'.get 30#5 = 0#64 ∧ Div3Out x x' ((x.get 28#5).toNat * 2 ^ 128 +
        (x.get 11#5).toNat * 2 ^ 64 + (x.get 7#5).toNat)
        ((x.get 17#5).toNat + 2 ^ 64 * (x.get 16#5).toNat) 11#5 7#5 28#5
        [7#5, 8#5, 9#5, 11#5, 28#5, 30#5, 31#5]) := by
  rv_exec
  all_goals
    beta_reduce
    simp only [Div3Out]
    rv_cse
    have hs := div3by2BV_spec (x.get 28#5) (x.get 11#5) (x.get 7#5) (x.get 17#5) (x.get 16#5)
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

/-- The second inlined `udivrem_3by2()` of `udivrem_top2<3>()`, from 0x2a8 to 0x338, with the
restore of s0 to s3 from the frame and of sp: `t3:t2:t1` by `a6:a7` with the reciprocal in t4 and
t5 0, to the quotient in t1 and the remainder in `t3:t2`. -/
theorem top2_div_low {A : List (BitVec 64)} {hi : BitVec 20} {lo : BitVec 12} (base : BitVec 64)
    (x : Regs) (m : Mem)
    (hd : 2 ^ 127 ≤ (x.get 17#5).toNat + 2 ^ 64 * (x.get 16#5).toNat)
    (hu : (x.get 28#5).toNat * 2 ^ 64 + (x.get 7#5).toNat <
      (x.get 17#5).toNat + 2 ^ 64 * (x.get 16#5).toNat)
    (hv : (x.get 29#5).toNat =
      (2 ^ 192 - 1) / ((x.get 17#5).toNat + 2 ^ 64 * (x.get 16#5).toNat) - 2 ^ 64)
    (h30 : x.get 30#5 = 0#64)
    (hsp : ∀ k ∈ [0, 8, 16, 24], (x.get 2#5 + BitVec.ofNat 64 k) ∈ A) :
    Reach A (udivrem_top2_3_progAt hi lo) base (pcAt base 170) x m (pcAt base 206) (fun x' m' =>
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
    refine Reach.step (by decide) (by rv_fetch) ?_
    simp only [StepGoal, Nat.reduceAdd]
    rv_val
    refine ⟨hsp 24 (by simp), fun ws0 hws0 => ?_⟩
    refine Reach.step (by decide) (by rv_fetch) ?_
    simp only [StepGoal, Nat.reduceAdd]
    rv_val
    refine ⟨hsp 16 (by simp), fun ws1 hws1 => ?_⟩
    refine Reach.step (by decide) (by rv_fetch) ?_
    simp only [StepGoal, Nat.reduceAdd]
    rv_val
    refine ⟨hsp 8 (by simp), fun ws2 hws2 => ?_⟩
    refine Reach.step (by decide) (by rv_fetch) ?_
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

/-- The quotient and the remainder of the top digits of `udivrem_top2()` by the two divisions of
3 by 2 words. -/
theorem top2_digits {T0 T1 T2 T3 D q1 r1lo r1hi q0 r0 T : Nat}
    (hT : T0 + 2 ^ 64 * (T1 + 2 ^ 64 * (T2 + 2 ^ 64 * T3)) = T)
    (hq1 : q1 = (T3 * 2 ^ 128 + T2 * 2 ^ 64 + T1) / D)
    (hr1 : r1lo + 2 ^ 64 * r1hi = (T3 * 2 ^ 128 + T2 * 2 ^ 64 + T1) % D)
    (hq0 : q0 = (r1hi * 2 ^ 128 + r1lo * 2 ^ 64 + T0) / D)
    (hr0 : r0 = (r1hi * 2 ^ 128 + r1lo * 2 ^ 64 + T0) % D) :
    T = (q0 + 2 ^ 64 * q1) * D + r0 := by
  have e1 := Nat.div_add_mod (T3 * 2 ^ 128 + T2 * 2 ^ 64 + T1) D
  have e2 := Nat.div_add_mod (r1hi * 2 ^ 128 + r1lo * 2 ^ 64 + T0) D
  rw [← hq1, ← hr1] at e1
  rw [← hq0, ← hr0] at e2
  have : (q0 + 2 ^ 64 * q1) * D = D * q0 + 2 ^ 64 * (D * q1) := by ring
  rw [this]
  omega

/-- The stores of s0 to s3 below sp are in the stack frame of `udivrem_top2<3>()`. -/
theorem unchangedExcept2_frame32 (m : Mem) (r sp a b c d : BitVec 64)
    (hs : (sp - 32#64).toNat + 32 ≤ 2 ^ 64) :
    UnchangedExcept2 m (memStore (memStore (memStore (memStore m
      (sp + 18446744073709551608#64).toNat a) (sp + 18446744073709551600#64).toNat b)
      (sp + 18446744073709551592#64).toNat c) (sp + 18446744073709551584#64).toNat d)
      r 64 (sp - 32#64) 32 := by
  simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
  exact unchangedExcept2_refl _ _ _ _ _

/-- The words of the frame of 32 bytes below sp. -/
theorem frame32_mem (sp : BitVec 64) : ∀ k ∈ [0, 8, 16, 24],
    sp + 18446744073709551584#64 + BitVec.ofNat 64 k ∈ bufWords (sp - 32#64) 4 := by
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · have := mem_bufWords (a := sp - 32#64) (n := 4) (i := 0) (by norm_num)
    rwa [show sp - 32#64 + BitVec.ofNat 64 (8 * 0) = sp + 18446744073709551584#64 +
      BitVec.ofNat 64 0 by bv_omega] at this
  · have := mem_bufWords (a := sp - 32#64) (n := 4) (i := 1) (by norm_num)
    rwa [show sp - 32#64 + BitVec.ofNat 64 (8 * 1) = sp + 18446744073709551584#64 +
      BitVec.ofNat 64 8 by bv_omega] at this
  · have := mem_bufWords (a := sp - 32#64) (n := 4) (i := 2) (by norm_num)
    rwa [show sp - 32#64 + BitVec.ofNat 64 (8 * 2) = sp + 18446744073709551584#64 +
      BitVec.ofNat 64 16 by bv_omega] at this
  · have := mem_bufWords (a := sp - 32#64) (n := 4) (i := 3) (by norm_num)
    rwa [show sp - 32#64 + BitVec.ofNat 64 (8 * 3) = sp + 18446744073709551584#64 +
      BitVec.ofNat 64 24 by bv_omega] at this

/-- The words that `udivrem_top2<3>()` saves in its frame. -/
theorem frame32_reads (m : Mem) (sp a b c d : BitVec 64) :
    let M := memStore (memStore (memStore (memStore m (sp + 18446744073709551608#64).toNat a)
      (sp + 18446744073709551600#64).toNat b) (sp + 18446744073709551592#64).toNat c)
      (sp + 18446744073709551584#64).toNat d
    memWord M (sp + 18446744073709551584#64 + 24#64).toNat = a ∧
      memWord M (sp + 18446744073709551584#64 + 16#64).toNat = b ∧
      memWord M (sp + 18446744073709551584#64 + 8#64).toNat = c ∧
      memWord M (sp + 18446744073709551584#64).toNat = d := by
  intro M
  simp only [M, BitVec.add_assoc, BitVec.reduceAdd]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | bv_omega | fail) only [memWord_memStore_self, memWord_memStore_of_ne]

/-- A number with the low word `a0` divided by `2^(64 - S)`. -/
theorem div_low_word (a0 X S : Nat) (hS : S ≤ 64) :
    (a0 + 2 ^ 64 * X) / 2 ^ (64 - S) = X * 2 ^ S + a0 / 2 ^ (64 - S) := by
  have hPQ : 2 ^ 64 = 2 ^ S * 2 ^ (64 - S) := by rw [← pow_add]; congr 1; omega
  rw [hPQ, show a0 + 2 ^ S * 2 ^ (64 - S) * X = a0 + X * 2 ^ S * 2 ^ (64 - S) by ring,
    Nat.add_mul_div_right _ _ (by positivity)]
  ring

/-- The normalized words of u of 4 words shifted left by `S < 64`, without the low word. -/
theorem norm4_words (u0 u1 u2 u3 S : Nat) (h0 : u0 < 2 ^ 64) (h1 : u1 < 2 ^ 64)
    (h2 : u2 < 2 ^ 64) (h3 : u3 < 2 ^ 64) (hS : S < 64) :
    (u1 * 2 ^ S + u0 / 2 ^ (64 - S)) % 2 ^ 64 + 2 ^ 64 * ((u2 * 2 ^ S + u1 / 2 ^ (64 - S)) % 2 ^ 64 +
      2 ^ 64 * ((u3 * 2 ^ S + u2 / 2 ^ (64 - S)) % 2 ^ 64 + 2 ^ 64 * (u3 / 2 ^ (64 - S)))) =
    (u1 + 2 ^ 64 * (u2 + 2 ^ 64 * u3)) * 2 ^ S + u0 / 2 ^ (64 - S) := by
  have h3w := norm3_words u1 u2 u3 S h1 h2 h3 hS
  have hut := top1_ut u0 u1 S hS h0
  have e : (u1 + 2 ^ 64 * (u2 + 2 ^ 64 * u3)) * 2 ^ S + u0 / 2 ^ (64 - S) =
      (u1 * 2 ^ S + u0 / 2 ^ (64 - S)) + 2 ^ 64 * ((u2 + 2 ^ 64 * u3) * 2 ^ S) := by ring
  rw [e, ← hut]
  have e2 : (u2 + 2 ^ 64 * u3) * 2 ^ S = (u2 + 2 ^ 64 * u3) * 2 ^ S + u1 / 2 ^ (64 - S) -
      u1 / 2 ^ (64 - S) := by omega
  rw [e2, h3w]
  omega

/-- The frame of 32 bytes below sp of `udivrem_top2<3>()` is outside the code and the data of the
image: its words are outside them. -/
theorem frame32_outside (sp base : BitVec 64) (o1 o2 : Nat)
    (h0 : (sp - 32#64).toNat + 8 ≤ base.toNat ∨ base.toNat + o1 + o2 ≤ (sp - 32#64).toNat)
    (h3 : (sp - 32#64 + BitVec.ofNat 64 (8 * 3)).toNat + 8 ≤ base.toNat ∨
      base.toNat + o1 + o2 ≤ (sp - 32#64 + BitVec.ofNat 64 (8 * 3)).toNat)
    (hs : (sp - 32#64).toNat + 32 ≤ 2 ^ 64) (hoff : 32 ≤ o1 + o2) :
    (sp - 32#64).toNat + 32 ≤ base.toNat ∨ base.toNat + o1 + o2 ≤ (sp - 32#64).toNat := by
  have : (sp - 32#64 + BitVec.ofNat 64 (8 * 3)).toNat = (sp - 32#64).toNat + 24 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  omega

end IntxRV.Api
