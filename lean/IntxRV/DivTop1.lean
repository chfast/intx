import IntxRV.DivBy2
import IntxRV.Umul256

/-!
# The division by the top word of the divisor: `udivrem_top1<3>()`

`udivrem_top1<TOP>()` estimates the quotient digit from the top 64 bits of the normalized divisor
and the matching two words of the numerator with `udivrem_2by1()`, computes the remainder
`u - q * v` on the original operands with `submul()`, and adds `v` back while the borrow is not 0.
The estimate is not less than the quotient (`top1_est`, Knuth's Theorem B), so the loop ends.

The block lemmas of the RV64 code of `udivrem_top1<3>()`: `submul4_words` for the 4-word
`submul()` (by its definitions, for `apply` and `assumption`), `top1_3_exit` for the stores of the
result, `top1_3_loop` for the correction loop (with `Reach.loop` and the excess of the quotient as
the measure), and `top1_3_tail` from the test of the borrow.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- A 4-word number with a lower top word is smaller. -/
theorem words_lt_of_top4 (m : Mem) (a b : BitVec 64)
    (h : (memWord m (a + 24#64).toNat).toNat < (memWord m (b + 24#64).toNat).toNat) :
    words m a 4 < words m b 4 := by
  simp only [words, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero, Nat.add_zero] at h ⊢
  have := (memWord m a.toNat).isLt
  have := (memWord m (a + 8#64).toNat).isLt
  have := (memWord m (a + 16#64).toNat).isLt
  have := (memWord m b.toNat).isLt
  omega

/-- The memory that changes only at `a` changes only at `a` and `b`. -/
theorem unchangedExcept2_of {m m' : Mem} {a : BitVec 64} {la : Nat} (b : BitVec 64) (lb : Nat)
    (h : UnchangedExcept m m' a la) : UnchangedExcept2 m m' a la b lb :=
  fun k ha _ => h k ha

/-- The top word of a 4-word number of at least 2^192 is not 0. -/
theorem top4_ne_zero (m : Mem) (a : BitVec 64) (h : 2 ^ (64 * 3) ≤ words m a 4) :
    memWord m (a + 24#64).toNat ≠ 0 := by
  intro h0
  simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
    Nat.add_zero] at h
  rw [h0] at h
  have := (memWord m a.toNat).isLt
  have := (memWord m (a + 8).toNat).isLt
  have := (memWord m (a + 16).toNat).isLt
  simp at h
  omega

/-- `u - p` and its borrow `u < u - p`. -/
theorem defn_sub_borrow0 {r b u p : BitVec 64} (hr : Defn r (u - p))
    (hb : Defn b (if u < r then 1#64 else 0#64)) :
    r.toNat + p.toNat = u.toNat + 2 ^ 64 * b.toNat := by
  rw [hb.eq, hr.eq]
  have hu := u.isLt; have hp := p.isLt
  rw [BitVec.toNat_sub]
  split <;> rename_i h <;> simp only [BitVec.lt_def, BitVec.toNat_sub] at h <;> simp <;> omega

/-- `u - s - bin` and its borrow `u < u - s` or `u - s < u - s - bin`, for a borrow in of 0 or 1. -/
theorem defn_sub_borrow {d e r f b u s bin : BitVec 64} (hd : Defn d (u - s))
    (he : Defn e (if u < d then 1#64 else 0#64)) (hr : Defn r (d - bin))
    (hf : Defn f (if d < r then 1#64 else 0#64)) (hb : Defn b (e ||| f)) (hbin : bin.toNat ≤ 1) :
    r.toNat + s.toNat + bin.toNat = u.toNat + 2 ^ 64 * b.toNat ∧ b.toNat ≤ 1 := by
  rw [hb.eq, he.eq, hf.eq, hr.eq, hd.eq]
  have hu := u.isLt; have hs := s.isLt
  have h1 : (u - s).toNat = (u.toNat + (2 ^ 64 - s.toNat)) % 2 ^ 64 := by
    rw [BitVec.toNat_sub]; omega
  have h2 : (u - s - bin).toNat = ((u - s).toNat + (2 ^ 64 - bin.toNat)) % 2 ^ 64 := by
    rw [BitVec.toNat_sub]; omega
  by_cases c1 : u < u - s <;> by_cases c2 : u - s < u - s - bin <;>
    simp only [c1, c2, ↓reduceIte] <;> simp only [BitVec.lt_def] at c1 c2 <;> simp <;> omega

/-- `a + b + c` and its carry `a + b < a` or `a + b + c < a + b`, for a carry in of 0 or 1. -/
theorem defn_add_carry {s e n f co a b c : BitVec 64} (hs : Defn s (a + b))
    (he : Defn e (if s < a then 1#64 else 0#64)) (hn : Defn n (s + c))
    (hf : Defn f (if n < s then 1#64 else 0#64)) (hco : Defn co (e ||| f)) (hc : c.toNat ≤ 1) :
    n.toNat + 2 ^ 64 * co.toNat = a.toNat + b.toNat + c.toNat ∧ co.toNat ≤ 1 := by
  rw [hco.eq, he.eq, hf.eq, hn.eq, hs.eq]
  have ha := a.isLt; have hb := b.isLt
  have h1 : (a + b).toNat = (a.toNat + b.toNat) % 2 ^ 64 := BitVec.toNat_add _ _
  have h2 : (a + b + c).toNat = ((a + b).toNat + c.toNat) % 2 ^ 64 := BitVec.toNat_add _ _
  by_cases c1 : a + b < a <;> by_cases c2 : a + b + c < a + b <;>
    simp only [c1, c2, ↓reduceIte] <;> simp only [BitVec.lt_def] at c1 c2 <;> simp <;> omega

theorem defn_bit_le {c s t : BitVec 64} (hc : Defn c (if s < t then 1#64 else 0#64)) :
    c.toNat ≤ 1 := by
  rw [hc.eq]; split <;> simp

/-- The sum of the words of `submul()` of 4 words, by the sums of the products, their carries and
the borrows of the subtractions. -/
theorem submul4_nat {u0 u1 u2 u3 X0 X1 X2 X3 p0 h0 p1 h1 p2 h2 p3 h3 s1 c1 s2 c2 s3 c3 g3 r0 b0 r1 b1
    r2 b2 r3 b3 : Nat}
    (m0 : p0 + 2 ^ 64 * h0 = X0) (m1 : p1 + 2 ^ 64 * h1 = X1) (m2 : p2 + 2 ^ 64 * h2 = X2)
    (m3 : p3 + 2 ^ 64 * h3 = X3) (e1 : s1 + 2 ^ 64 * c1 = p1 + h0)
    (e2 : s2 + 2 ^ 64 * c2 = p2 + (h1 + c1)) (e3 : s3 + 2 ^ 64 * c3 = p3 + (h2 + c2))
    (eg : g3 = c3 + h3) (n0 : r0 + p0 = u0 + 2 ^ 64 * b0) (n1 : r1 + s1 + b0 = u1 + 2 ^ 64 * b1)
    (n2 : r2 + s2 + b1 = u2 + 2 ^ 64 * b2) (n3 : r3 + s3 + b2 = u3 + 2 ^ 64 * b3) :
    r0 + 2 ^ 64 * (r1 + 2 ^ 64 * (r2 + 2 ^ 64 * r3)) +
        (X0 + 2 ^ 64 * (X1 + 2 ^ 64 * (X2 + 2 ^ 64 * X3))) =
      u0 + 2 ^ 64 * (u1 + 2 ^ 64 * (u2 + 2 ^ 64 * u3)) + 2 ^ 256 * (g3 + b3) := by
  subst m0 m1 m2 m3 eg
  omega

set_option maxHeartbeats 4000000 in
/-- `submul()` of 4 words in the RV64 code of `udivrem_top1<3>()`: the words `r` of `u - q * v`
and the borrow `w`, from the definitions of the values (in the reverse order of the run, so that
`apply` and `assumption` find them by the names of the results). -/
theorem submul4_words {u0 u1 u2 u3 v0 v1 v2 v3 q p0 h0 p1 h1 p2 s1 a2 c1 s2 h2 r0 b0 d1 e1 r1 f1 b1
    p3 a3 c2 s3 h3 d2 e2 r2 c3 d3 f2 g3 b2 e3 r3 f3 b3 w : BitVec 64}
    (hw : Defn w (g3 + b3)) (hg3 : Defn g3 (c3 + h3)) (hb3 : Defn b3 (e3 ||| f3))
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
    (hp0 : Defn p0 (v0 * q)) :
    r0.toNat + 2 ^ 64 * (r1.toNat + 2 ^ 64 * (r2.toNat + 2 ^ 64 * r3.toNat)) +
        q.toNat * (v0.toNat + 2 ^ 64 * (v1.toNat + 2 ^ 64 * (v2.toNat + 2 ^ 64 * v3.toNat))) =
      u0.toNat + 2 ^ 64 * (u1.toNat + 2 ^ 64 * (u2.toNat + 2 ^ 64 * u3.toNat)) +
        2 ^ 256 * w.toNat := by
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
  have hS := submul4_nat (defn_mul_mulhu hp0 hh0) (defn_mul_mulhu hp1 hh1) (defn_mul_mulhu hp2 hh2)
    (defn_mul_mulhu hp3 hh3) (defn_carry_left hs1 hc1) (defn_carry3 ha2 hs2 hc2 (by omega))
    (defn_carry3 ha3 hs3 hc3 (by omega)) (defn_add_exact hg3 (by omega))
    (defn_sub_borrow0 hr0 hb0) n1 n2 n3
  have hd : q.toNat * (v0.toNat + 2 ^ 64 * (v1.toNat + 2 ^ 64 * (v2.toNat + 2 ^ 64 * v3.toNat))) =
      v0.toNat * q.toNat + 2 ^ 64 * (v1.toNat * q.toNat + 2 ^ 64 * (v2.toNat * q.toNat +
        2 ^ 64 * (v3.toNat * q.toNat))) := by ring
  rw [hd]
  -- The borrow does not overflow: q * v < 2^64 * 2^256 - 2^256.
  have hqv : q.toNat * (v0.toNat + 2 ^ 64 * (v1.toNat + 2 ^ 64 * (v2.toNat + 2 ^ 64 * v3.toNat))) ≤
      (2 ^ 64 - 1) * (2 ^ 256 - 1) := by
    have := v0.isLt; have := v1.isLt; have := v2.isLt; have := v3.isLt
    exact Nat.mul_le_mul (by have := q.isLt; omega) (by omega)
  rw [hd] at hqv
  have hR : r0.toNat + 2 ^ 64 * (r1.toNat + 2 ^ 64 * (r2.toNat + 2 ^ 64 * r3.toNat)) < 2 ^ 256 := by
    have := r0.isLt; have := r1.isLt; have := r2.isLt; have := r3.isLt; omega
  have ew := defn_add hw
  generalize r0.toNat + 2 ^ 64 * (r1.toNat + 2 ^ 64 * (r2.toNat + 2 ^ 64 * r3.toNat)) = R at *
  generalize v0.toNat * q.toNat + 2 ^ 64 * (v1.toNat * q.toNat + 2 ^ 64 * (v2.toNat * q.toNat +
    2 ^ 64 * (v3.toNat * q.toNat))) = P at *
  generalize u0.toNat + 2 ^ 64 * (u1.toNat + 2 ^ 64 * (u2.toNat + 2 ^ 64 * u3.toNat)) = U at *
  have : g3.toNat + b3.toNat < 2 ^ 64 := by omega
  rw [ew, Nat.mod_eq_of_lt this]
  exact hS

/-- The addition of 4 words in the correction loop of `udivrem_top1<3>()`: the words `n` of
`r + v` and the carry `c3`. -/
theorem add4_words {r0 r1 r2 r3 v0 v1 v2 v3 a0 a1 c0 e1 n1 f1 c1 a2 e2 n2 f2 c2 a3 e3 n3 f3
    c3 : BitVec 64}
    (hc3 : Defn c3 (e3 ||| f3)) (hf3 : Defn f3 (if n3 < a3 then 1#64 else 0#64))
    (hn3 : Defn n3 (a3 + c2)) (he3 : Defn e3 (if a3 < r3 then 1#64 else 0#64))
    (ha3 : Defn a3 (r3 + v3)) (hc2 : Defn c2 (e2 ||| f2))
    (hf2 : Defn f2 (if n2 < a2 then 1#64 else 0#64)) (hn2 : Defn n2 (a2 + c1))
    (he2 : Defn e2 (if a2 < r2 then 1#64 else 0#64)) (ha2 : Defn a2 (r2 + v2))
    (hc1 : Defn c1 (e1 ||| f1)) (hf1 : Defn f1 (if n1 < a1 then 1#64 else 0#64))
    (hn1 : Defn n1 (a1 + c0)) (he1 : Defn e1 (if a1 < r1 then 1#64 else 0#64))
    (hc0 : Defn c0 (if a0 < r0 then 1#64 else 0#64)) (ha1 : Defn a1 (r1 + v1))
    (ha0 : Defn a0 (r0 + v0)) :
    a0.toNat + 2 ^ 64 * (n1.toNat + 2 ^ 64 * (n2.toNat + 2 ^ 64 * n3.toNat)) + 2 ^ 256 * c3.toNat =
      r0.toNat + 2 ^ 64 * (r1.toNat + 2 ^ 64 * (r2.toNat + 2 ^ 64 * r3.toNat)) +
        (v0.toNat + 2 ^ 64 * (v1.toNat + 2 ^ 64 * (v2.toNat + 2 ^ 64 * v3.toNat))) ∧
      c3.toNat ≤ 1 := by
  have e0 := defn_carry_left ha0 hc0
  have l0 := defn_bit_le hc0
  obtain ⟨e1', l1⟩ := defn_add_carry ha1 he1 hn1 hf1 hc1 l0
  obtain ⟨e2', l2⟩ := defn_add_carry ha2 he2 hn2 hf2 hc2 l1
  obtain ⟨e3', l3⟩ := defn_add_carry ha3 he3 hn3 hf3 hc3 l2
  exact ⟨by omega, l3⟩

/-- The quotient estimate of `udivrem_top1<3>()` from the top words of the normalized operands is
not less than the quotient (Knuth, TAOCP Vol. 2, 4.3.1, Theorem B). -/
theorem top1_est {U V u2 u3 v2 v3 S q : Nat} (hS : S < 64)
    (hU : U < (u2 + 2 ^ 64 * u3 + 1) * 2 ^ 128) (hV : (v2 + 2 ^ 64 * v3) * 2 ^ 128 ≤ V)
    (hD : 0 < v3 * 2 ^ S + v2 / 2 ^ (64 - S))
    (hq : q = (u3 * 2 ^ S + u2 / 2 ^ (64 - S)) / (v3 * 2 ^ S + v2 / 2 ^ (64 - S))) :
    U / V ≤ q := by
  have hPQ : 2 ^ S * 2 ^ (64 - S) = 2 ^ 64 := by rw [← pow_add]; congr 1; omega
  have hQ : 0 < 2 ^ (64 - S) := by positivity
  have hP : 0 < 2 ^ S := by positivity
  -- (u2 + 2^64 u3 + 1) 2^S ≤ (N + 1) 2^64 for the top N of the normalized numerator.
  have hN : (u2 + 2 ^ 64 * u3 + 1) * 2 ^ S ≤
      (u3 * 2 ^ S + u2 / 2 ^ (64 - S) + 1) * 2 ^ 64 := by
    have h1 : u2 + 1 ≤ (u2 / 2 ^ (64 - S) + 1) * 2 ^ (64 - S) := by
      have := Nat.lt_mul_div_succ u2 hQ
      rw [Nat.mul_comm] at this; omega
    rw [← hPQ]
    have := Nat.mul_le_mul_left (2 ^ S) h1
    nlinarith
  -- D 2^64 ≤ (v2 + 2^64 v3) 2^S for the top D of the normalized divisor.
  have hDv : (v3 * 2 ^ S + v2 / 2 ^ (64 - S)) * 2 ^ 64 ≤ (v2 + 2 ^ 64 * v3) * 2 ^ S := by
    have h1 : v2 / 2 ^ (64 - S) * 2 ^ (64 - S) ≤ v2 := Nat.div_mul_le_self _ _
    rw [← hPQ]
    have := Nat.mul_le_mul_left (2 ^ S) h1
    nlinarith
  have hq1 : u3 * 2 ^ S + u2 / 2 ^ (64 - S) + 1 ≤ (q + 1) * (v3 * 2 ^ S + v2 / 2 ^ (64 - S)) := by
    have := Nat.lt_mul_div_succ (u3 * 2 ^ S + u2 / 2 ^ (64 - S)) hD
    rw [← hq] at this; nlinarith
  have hlt : U * 2 ^ S < (q + 1) * V * 2 ^ S := by
    calc U * 2 ^ S < (u2 + 2 ^ 64 * u3 + 1) * 2 ^ 128 * 2 ^ S :=
          Nat.mul_lt_mul_of_pos_right hU hP
      _ = (u2 + 2 ^ 64 * u3 + 1) * 2 ^ S * 2 ^ 128 := by ring
      _ ≤ (u3 * 2 ^ S + u2 / 2 ^ (64 - S) + 1) * 2 ^ 64 * 2 ^ 128 := Nat.mul_le_mul_right _ hN
      _ ≤ (q + 1) * (v3 * 2 ^ S + v2 / 2 ^ (64 - S)) * 2 ^ 64 * 2 ^ 128 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hq1)
      _ = (q + 1) * ((v3 * 2 ^ S + v2 / 2 ^ (64 - S)) * 2 ^ 64) * 2 ^ 128 := by ring
      _ ≤ (q + 1) * ((v2 + 2 ^ 64 * v3) * 2 ^ S) * 2 ^ 128 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hDv)
      _ = (q + 1) * ((v2 + 2 ^ 64 * v3) * 2 ^ 128) * 2 ^ S := by ring
      _ ≤ (q + 1) * V * 2 ^ S := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hV)
  have : U < (q + 1) * V := Nat.lt_of_mul_lt_mul_right hlt
  have hV0 : 0 < V := by
    rcases Nat.eq_zero_or_pos V with h | h
    · rw [h] at this; omega
    · exact h
  have := (Nat.div_lt_iff_lt_mul hV0).mpr this
  omega

/-- The top two words of the normalized numerator of `udivrem_top1<3>()`: `ut_hi` and `ut_lo`. -/
theorem top1_ut (u2 u3 S : Nat) (hS : S < 64) (hu2 : u2 < 2 ^ 64) :
    2 ^ 64 * (u3 / 2 ^ (64 - S)) + (u3 * 2 ^ S + u2 / 2 ^ (64 - S)) % 2 ^ 64 =
      u3 * 2 ^ S + u2 / 2 ^ (64 - S) := by
  have hPQ : 2 ^ S * 2 ^ (64 - S) = 2 ^ 64 := by rw [← pow_add]; congr 1; omega
  have hQ : 0 < 2 ^ (64 - S) := by positivity
  have hu := Nat.div_add_mod u3 (2 ^ (64 - S))
  have hm := Nat.mod_lt u3 hQ
  have hlo : u2 / 2 ^ (64 - S) < 2 ^ S := by
    rw [Nat.div_lt_iff_lt_mul hQ, hPQ]; exact hu2
  -- u3 * 2^S = 2^64 * (u3 / 2^(64 - S)) + (u3 % 2^(64 - S)) * 2^S, and the low bits fit below.
  have he : u3 * 2 ^ S + u2 / 2 ^ (64 - S) =
      2 ^ 64 * (u3 / 2 ^ (64 - S)) + (u3 % 2 ^ (64 - S) * 2 ^ S + u2 / 2 ^ (64 - S)) := by
    rw [← hPQ]
    conv_lhs => rw [← hu]
    ring
  have hfit : u3 % 2 ^ (64 - S) * 2 ^ S + u2 / 2 ^ (64 - S) < 2 ^ 64 := by
    have : (u3 % 2 ^ (64 - S) + 1) * 2 ^ S ≤ 2 ^ (64 - S) * 2 ^ S := Nat.mul_le_mul_right _ hm
    rw [Nat.mul_comm (2 ^ (64 - S)), hPQ] at this
    nlinarith
  rw [he, Nat.mul_add_mod, Nat.mod_eq_of_lt hfit]


/-- The result of a division by 4 words stored as the quotient `q` and the remainder `a`. -/
theorem words_ret8 (m : Mem) (r q a0 a1 a2 a3 z : BitVec 64) (hz : z = 0#64)
    (hr : r.toNat + 64 ≤ 2 ^ 64)
    (m' : Mem) (hm : m' = memStore (memStore (memStore (memStore (memStore (memStore (memStore
      (memStore m r.toNat q) (r + 8#64).toNat z) (r + 16#64).toNat z)
      (r + 24#64).toNat z) (r + 32#64).toNat a0) (r + 40#64).toNat a1) (r + 48#64).toNat a2)
      (r + 56#64).toNat a3) :
    words m' r 4 = q.toNat ∧
      words m' (r + 32#64) 4 = a0.toNat + 2 ^ 64 * (a1.toNat + 2 ^ 64 * (a2.toNat +
        2 ^ 64 * a3.toNat)) ∧
      UnchangedExcept m m' r 64 := by
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

/-- The end of `udivrem_top1<3>()` from 0x2c8: the stores of the quotient in a2 and the remainder in
`a3:a5:a4:t2`, and the return. -/
theorem top1_3_exit {hi : BitVec 20} {lo : BitVec 12} (base T : BitVec 64) (x : Regs) (m : Mem)
    (hpre : udivrem_top1_3.pre x m) (hr : x.get 1#5 &&& 3 = 0) (x' : Regs) (m' : Mem)
    (h10 : x'.get 10#5 = x.get 10#5) (h1 : x'.get 1#5 = x.get 1#5)
    (hcs : ∀ i ∈ calleeSaved, x' i = x i)
    (hm : UnchangedExcept2 m m' (x.get 10#5) 64 (x.get 2#5 - 16#64) 16)
    (hqr : (x'.get 12#5).toNat = words m (x.get 11#5) 4 / words m (x.get 12#5) 4 ∧
      (x'.get 7#5).toNat + 2 ^ 64 * ((x'.get 14#5).toNat + 2 ^ 64 * ((x'.get 15#5).toNat +
        2 ^ 64 * (x'.get 13#5).toNat)) = words m (x.get 11#5) 4 % words m (x.get 12#5) 4) :
    Reach (bufWords (x.get 11#5) 4 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 8 ++
        bufWords (x.get 2#5 - 16#64) 2 ++ bufWords T 256) (udivrem_top1_3_progAt hi lo) base
      (pcAt base 178) x' m' (x.get 1#5) (udivrem_top1_3.post x m) := by
  have hpre' := hpre
  simp only [udivrem_top1_3.pre, Buf] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hra, hrn⟩, -⟩ := hpre'
  rw [← h10]
  have hrn' : (x'.get 10#5).toNat + 64 ≤ 2 ^ 64 := h10 ▸ hrn
  rv_exec
  rv_val
  rw [h1, update_aligned hr]
  refine Reach.refl ?_
  have hz : x'.get 0#5 = 0#64 := by rw [show (0#5 : BitVec 5) = 0 from rfl, Regs.get_zero]; rfl
  have hw := words_ret8 m' (x'.get 10#5) (x'.get 12#5) (x'.get 7#5) (x'.get 14#5) (x'.get 15#5)
    (x'.get 13#5) _ hz hrn' _ rfl
  simp only [udivrem_top1_3.post]
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

/-- The quotient and the remainder from `r + q * V = U` with `r < V`. -/
theorem div_mod_of_lt {r q U V : Nat} (h : r + q * V = U) (hr : r < V) : q = U / V ∧ r = U % V := by
  have hV : 0 < V := by omega
  subst h
  rw [Nat.add_mul_div_right _ _ hV, Nat.div_eq_of_lt hr, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt hr]
  simp

/-- The quotient is larger than `U / V` while the borrow is not 0. -/
theorem top1_q_gt {R q U V b : Nat} (hR : R < 2 ^ 256) (h : R + q * V = U + 2 ^ 256 * b)
    (hb : b ≠ 0) : U / V < q := by
  have hqv : U < q * V := by
    have : 2 ^ 256 ≤ 2 ^ 256 * b := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hb)
    omega
  by_contra hn
  have : q * V ≤ U / V * V := Nat.mul_le_mul_right _ (by omega)
  have := Nat.div_mul_le_self U V
  omega

theorem words4_lt (a0 a1 a2 a3 : BitVec 64) :
    a0.toNat + 2 ^ 64 * (a1.toNat + 2 ^ 64 * (a2.toNat + 2 ^ 64 * a3.toNat)) < 2 ^ 256 := by
  have := a0.isLt; have := a1.isLt; have := a2.isLt; have := a3.isLt; omega

/-- One correction of the quotient in the loop of `udivrem_top1<3>()`: `q - 1` and `r + v`, with
the borrow less the carry (the definitions in the order in which `apply` and `assumption` find them
from the words of the sum). -/
theorem top1_body_sm {r0 r1 r2 r3 v0 v1 v2 v3 q b b' a0 a1 c0 e1 n1 f1 c1 a2 e2 n2 f2 c2 a3 e3
    n3 f3 c3 : BitVec 64} {U V : Nat}
    (ha0 : Defn a0 (r0 + v0)) (hn1 : Defn n1 (a1 + c0)) (ha1 : Defn a1 (r1 + v1))
    (hc0 : Defn c0 (if a0 < r0 then 1#64 else 0#64))
    (he1 : Defn e1 (if a1 < r1 then 1#64 else 0#64))
    (hf1 : Defn f1 (if n1 < a1 then 1#64 else 0#64)) (hn2 : Defn n2 (a2 + c1))
    (ha2 : Defn a2 (r2 + v2)) (hc1 : Defn c1 (e1 ||| f1))
    (he2 : Defn e2 (if a2 < r2 then 1#64 else 0#64))
    (hf2 : Defn f2 (if n2 < a2 then 1#64 else 0#64)) (hn3 : Defn n3 (a3 + c2))
    (ha3 : Defn a3 (r3 + v3)) (hc2 : Defn c2 (e2 ||| f2))
    (he3 : Defn e3 (if a3 < r3 then 1#64 else 0#64))
    (hf3 : Defn f3 (if n3 < a3 then 1#64 else 0#64)) (hc3 : Defn c3 (e3 ||| f3))
    (hb' : Defn b' (b - c3))
    (hv : v0.toNat + 2 ^ 64 * (v1.toNat + 2 ^ 64 * (v2.toNat + 2 ^ 64 * v3.toNat)) = V)
    (hsm : r0.toNat + 2 ^ 64 * (r1.toNat + 2 ^ 64 * (r2.toNat + 2 ^ 64 * r3.toNat)) +
      q.toNat * V = U + 2 ^ 256 * b.toNat) (hb : b ≠ 0#64) :
    a0.toNat + 2 ^ 64 * (n1.toNat + 2 ^ 64 * (n2.toNat + 2 ^ 64 * n3.toNat)) +
      (q + 18446744073709551615#64).toNat * V = U + 2 ^ 256 * b'.toNat := by
  obtain ⟨ha, hc⟩ := add4_words hc3 hf3 hn3 he3 ha3 hc2 hf2 hn2 he2 ha2 hc1 hf1 hn1 he1 hc0 ha1 ha0
  have hb1 : 1 ≤ b.toNat := by
    have : b.toNat ≠ 0 := fun h => hb (BitVec.eq_of_toNat_eq (by simpa using h))
    omega
  have hR := words4_lt r0 r1 r2 r3
  have hgt := top1_q_gt hR hsm (by omega)
  have hq0 := Nat.lt_of_le_of_lt (Nat.zero_le _) hgt
  have hq1 : (q + 18446744073709551615#64).toNat + 1 = q.toNat := by
    rw [BitVec.toNat_add]; have := q.isLt; simp; omega
  have hbt : b'.toNat = b.toNat - c3.toNat := by
    rw [hb'.eq, BitVec.toNat_sub]; have := b.isLt; omega
  have hqV : q.toNat * V = (q + 18446744073709551615#64).toNat * V + V := by rw [← hq1]; ring
  rw [hv] at ha
  rw [hbt]
  have : 2 ^ 256 * (b.toNat - c3.toNat) = 2 ^ 256 * b.toNat - 2 ^ 256 * c3.toNat :=
    Nat.mul_sub _ _ _
  have : 2 ^ 256 * c3.toNat ≤ 2 ^ 256 * b.toNat := Nat.mul_le_mul_left _ (by omega)
  omega

/-- The last correction of the loop of `udivrem_top1<3>()`, to the borrow 0: the quotient and the
remainder. -/
theorem top1_body_exit {r0 r1 r2 r3 v0 v1 v2 v3 q b b' a0 a1 c0 e1 n1 f1 c1 a2 e2 n2 f2 c2 a3 e3
    n3 f3 c3 : BitVec 64} {U V : Nat}
    (ha0 : Defn a0 (r0 + v0)) (hn1 : Defn n1 (a1 + c0)) (ha1 : Defn a1 (r1 + v1))
    (hc0 : Defn c0 (if a0 < r0 then 1#64 else 0#64))
    (he1 : Defn e1 (if a1 < r1 then 1#64 else 0#64))
    (hf1 : Defn f1 (if n1 < a1 then 1#64 else 0#64)) (hn2 : Defn n2 (a2 + c1))
    (ha2 : Defn a2 (r2 + v2)) (hc1 : Defn c1 (e1 ||| f1))
    (he2 : Defn e2 (if a2 < r2 then 1#64 else 0#64))
    (hf2 : Defn f2 (if n2 < a2 then 1#64 else 0#64)) (hn3 : Defn n3 (a3 + c2))
    (ha3 : Defn a3 (r3 + v3)) (hc2 : Defn c2 (e2 ||| f2))
    (he3 : Defn e3 (if a3 < r3 then 1#64 else 0#64))
    (hf3 : Defn f3 (if n3 < a3 then 1#64 else 0#64)) (hc3 : Defn c3 (e3 ||| f3))
    (hb' : Defn b' (b - c3)) (hz : b' = 0#64)
    (hv : v0.toNat + 2 ^ 64 * (v1.toNat + 2 ^ 64 * (v2.toNat + 2 ^ 64 * v3.toNat)) = V)
    (hsm : r0.toNat + 2 ^ 64 * (r1.toNat + 2 ^ 64 * (r2.toNat + 2 ^ 64 * r3.toNat)) +
      q.toNat * V = U + 2 ^ 256 * b.toNat) (hb : b ≠ 0#64) :
    (q + 18446744073709551615#64).toNat = U / V ∧
      a0.toNat + 2 ^ 64 * (n1.toNat + 2 ^ 64 * (n2.toNat + 2 ^ 64 * n3.toNat)) = U % V := by
  have h := top1_body_sm ha0 hn1 ha1 hc0 he1 hf1 hn2 ha2 hc1 he2 hf2 hn3 ha3 hc2 he3 hf3 hc3 hb' hv
    hsm hb
  obtain ⟨ha, hc⟩ := add4_words hc3 hf3 hn3 he3 ha3 hc2 hf2 hn2 he2 ha2 hc1 hf1 hn1 he1 hc0 ha1 ha0
  -- The borrow b less the carry is 0: the carry is 1 and the sum r + v wraps.
  have hbc : b = c3 := by rw [hz, Defn] at hb'; bv_omega
  have hb1 : 1 ≤ b.toNat := by
    have : b.toNat ≠ 0 := fun h => hb (BitVec.eq_of_toNat_eq (by simpa using h))
    omega
  rw [← hbc] at hc ha
  have hR := words4_lt r0 r1 r2 r3
  rw [hz] at h
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.mul_zero, Nat.add_zero] at h
  exact div_mod_of_lt h (by omega)

/-- The measure of the loop of `udivrem_top1<3>()`, the excess of the quotient, decreases. -/
theorem top1_body_k {q : BitVec 64} {U V n : Nat} (hlt : U / V < q.toNat)
    (hn : n = q.toNat - U / V) : (q + 18446744073709551615#64).toNat - U / V < n := by
  have hq0 := Nat.lt_of_le_of_lt (Nat.zero_le _) hlt
  have hq1 : (q + 18446744073709551615#64).toNat + 1 = q.toNat := by
    rw [BitVec.toNat_add]; have := q.isLt; simp; omega
  omega

/-- The registers and the memory at the head of the correction loop of `udivrem_top1<3>()`, at
0x2ec: `t1:a4:a5:a3 + q * v = u + 2^256 * borrow`, with the remainder words `r`, the quotient `q`
in a2, the borrow in t3, not 0, and the words of v in `a1:a6:a7:t0`; `n` the excess of `q`. -/
def top1Loop (x : Regs) (m : Mem) (n : Nat) (x' : Regs) (m' : Mem) : Prop :=
  x'.get 10#5 = x.get 10#5 ∧ x'.get 1#5 = x.get 1#5 ∧ (∀ i ∈ calleeSaved, x' i = x i) ∧
    UnchangedExcept2 m m' (x.get 10#5) 64 (x.get 2#5 - 16#64) 16 ∧
    (x'.get 11#5).toNat + 2 ^ 64 * ((x'.get 16#5).toNat + 2 ^ 64 * ((x'.get 17#5).toNat +
      2 ^ 64 * (x'.get 5#5).toNat)) = words m (x.get 12#5) 4 ∧
    (x'.get 6#5).toNat + 2 ^ 64 * ((x'.get 14#5).toNat + 2 ^ 64 * ((x'.get 15#5).toNat +
      2 ^ 64 * (x'.get 13#5).toNat)) + (x'.get 12#5).toNat * words m (x.get 12#5) 4 =
      words m (x.get 11#5) 4 + 2 ^ 256 * (x'.get 28#5).toNat ∧
    x'.get 28#5 ≠ 0#64 ∧ n = (x'.get 12#5).toNat - words m (x.get 11#5) 4 / words m (x.get 12#5) 4

/-- The registers outside the ones a run sets keep the callee-saved registers. -/
theorem calleeSaved_of {x x' : Regs} (h : ∀ i ∈ calleeSaved, x' i = x i) (y : Regs)
    (hy : ∀ i ∈ calleeSaved, y i = x' i) : ∀ i ∈ calleeSaved, y i = x i :=
  fun i hi => (hy i hi).trans (h i hi)

/-- The correction loop of `udivrem_top1<3>()` from 0x2ec. -/
theorem top1_3_loop {hi : BitVec 20} {lo : BitVec 12} (base T : BitVec 64) (x : Regs) (m : Mem)
    (hpre : udivrem_top1_3.pre x m) (hr : x.get 1#5 &&& 3 = 0) :
    ∀ n x' m', top1Loop x m n x' m' →
    Reach (bufWords (x.get 11#5) 4 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 8 ++
        bufWords (x.get 2#5 - 16#64) 2 ++ bufWords T 256) (udivrem_top1_3_progAt hi lo) base
      (pcAt base 187) x' m' (x.get 1#5) (udivrem_top1_3.post x m) := by
  apply Reach.loop (top1Loop x m)
  intro n x' m' h ih
  obtain ⟨h10, h1, hcs, hm, hv, hsm, hb, hn⟩ := h
  have hlt := top1_q_gt (words4_lt _ _ _ _) hsm
    (fun h0 => hb (BitVec.eq_of_toNat_eq (by simpa using h0)))
  rv_step
  rv_exec_cut 178 187
  -- The borrow is 0: the end.
  all_goals first
    | (rv_not_at 178; skip)
    | (refine top1_3_exit base T x m hpre hr _ _ ?_ ?_ ?_ hm ?_
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

/-- The quotient and the remainder without a correction: the borrow is 0 and the estimate is not
less than the quotient. -/
theorem top1_tail_exit {R q U V : Nat} {b : BitVec 64} (hV : 0 < V)
    (hsm : R + q * V = U + 2 ^ 256 * b.toNat) (hz : b = 0#64) (hq : U / V ≤ q) :
    q = U / V ∧ R = U % V := by
  subst hz
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.mul_zero, Nat.add_zero] at hsm
  have := Nat.mul_le_mul_right V hq
  have := Nat.div_add_mod' U V
  have := Nat.mod_lt U hV
  exact div_mod_of_lt hsm (by omega)

/-- The end of `udivrem_top1<3>()` from the test of the borrow at 0x2c0: `t1:a4:a5:a3 + q * v =
u + 2^256 * borrow` with the quotient estimate `q` in a2 not less than `u / v`. -/
theorem top1_3_tail {hi : BitVec 20} {lo : BitVec 12} (base T : BitVec 64) (x : Regs) (m : Mem)
    (hpre : udivrem_top1_3.pre x m) (hr : x.get 1#5 &&& 3 = 0) (x' : Regs) (m' : Mem)
    (h10 : x'.get 10#5 = x.get 10#5) (h1 : x'.get 1#5 = x.get 1#5)
    (hcs : ∀ i ∈ calleeSaved, x' i = x i)
    (hm : UnchangedExcept2 m m' (x.get 10#5) 64 (x.get 2#5 - 16#64) 16)
    (hv : (x'.get 11#5).toNat + 2 ^ 64 * ((x'.get 16#5).toNat + 2 ^ 64 * ((x'.get 17#5).toNat +
      2 ^ 64 * (x'.get 5#5).toNat)) = words m (x.get 12#5) 4)
    (hsm : (x'.get 6#5).toNat + 2 ^ 64 * ((x'.get 14#5).toNat + 2 ^ 64 * ((x'.get 15#5).toNat +
      2 ^ 64 * (x'.get 13#5).toNat)) + (x'.get 12#5).toNat * words m (x.get 12#5) 4 =
      words m (x.get 11#5) 4 + 2 ^ 256 * (x'.get 28#5).toNat)
    (hq : words m (x.get 11#5) 4 / words m (x.get 12#5) 4 ≤ (x'.get 12#5).toNat) :
    Reach (bufWords (x.get 11#5) 4 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 8 ++
        bufWords (x.get 2#5 - 16#64) 2 ++ bufWords T 256) (udivrem_top1_3_progAt hi lo) base
      (pcAt base 176) x' m' (x.get 1#5) (udivrem_top1_3.post x m) := by
  have hpre' := hpre
  simp only [udivrem_top1_3.pre] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  have hV : 0 < words m (x.get 12#5) 4 := by
    have := hpre'.2.2.2.2.2.2.2.2.2.1; have : 0 < 2 ^ (64 * 3) := by positivity
    omega
  have hz0 : x'.get 0#5 = 0#64 := by rw [show (0#5 : BitVec 5) = 0 from rfl, Regs.get_zero]; rfl
  rv_step
  rv_exec_cut 178 187
  all_goals simp only [hz0, bne_eq_false_iff_eq] at *
  -- The borrow is 0: no correction.
  all_goals first
    | (rv_not_at 178; skip)
    | (refine top1_3_exit base T x m hpre hr _ _ ?_ ?_ ?_ hm ?_
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
    exact top1_3_loop base T x m hpre hr _ _ _ ⟨h10, h1, hcs, hm, hv, hsm, by assumption, rfl⟩

/-- `div2by1BV` with the products in the order of the copy inlined in `udivrem_top1<3>()`: `v * u1`
and `mulhu v u1`. -/
def div2by1BVc (u1 u0 d v : BitVec 64) : BitVec 64 × BitVec 64 :=
  let p0 := v * u1
  let p1 := mulhu v u1
  let q0 := p0 + u0
  let q1 := u1 + p1 + (if q0 < p0 then 1#64 else 0#64)
  let r := u0 - (q1 + 1#64) * d
  let q2 := if q0 < r then q1 else q1 + 1#64
  let r2 := ((0#64 - if q0 < r then 1#64 else 0#64) &&& d) + r
  let k := if r2 < d then 1#64 else 0#64
  (q2 + (k ^^^ 1#64), r2 - ((k + 18446744073709551615#64) &&& d))

theorem div2by1BVc_spec (u1 u0 d v : BitVec 64) (hd : 2 ^ 63 ≤ d.toNat)
    (hu : u1.toNat < d.toNat) (hv : v.toNat = (2 ^ 128 - 1) / d.toNat - 2 ^ 64) :
    (div2by1BVc u1 u0 d v).1.toNat = (2 ^ 64 * u1.toNat + u0.toNat) / d.toNat := by
  have h := (div2by1BV_spec u1 u0 d v hd hu hv).1
  simp only [div2by1BV, BitVec.mul_comm u1 v, mulhu_comm u1 v] at h
  exact h

/-- The funnel shift of the top word `d1` and the word `d0` below it by `S` does not wrap when
`d1 * 2^S` fits in a word. -/
theorem fshl_lt {d0 d1 S : Nat} (hS : S < 64) (h0 : d0 < 2 ^ 64) (h1 : d1 * 2 ^ S < 2 ^ 64) :
    d1 * 2 ^ S + d0 / 2 ^ (64 - S) < 2 ^ 64 := by
  have := norm2_words hS h0 h1
  have hm := Nat.mod_lt (d0 * 2 ^ S) (Nat.two_pow_pos 64)
  have : (d0 + 2 ^ 64 * d1) * 2 ^ S = d0 * 2 ^ S + 2 ^ 64 * (d1 * 2 ^ S) := by ring
  have : d0 * 2 ^ S < 2 ^ 64 * 2 ^ S := Nat.mul_lt_mul_of_pos_right h0 (Nat.two_pow_pos _)
  have hlt := Nat.mod_lt (d1 * 2 ^ S + d0 / 2 ^ (64 - S)) (Nat.two_pow_pos 64)
  -- The low word of the shift is the low bits of d0: the high word is the whole sum.
  by_contra hn
  have hge : 2 ^ 64 ≤ d1 * 2 ^ S + d0 / 2 ^ (64 - S) := by omega
  have hQ : 0 < 2 ^ (64 - S) := by positivity
  have hPQ : 2 ^ S * 2 ^ (64 - S) = 2 ^ 64 := by rw [← pow_add]; congr 1; omega
  have hlo : d0 / 2 ^ (64 - S) < 2 ^ S := by rw [Nat.div_lt_iff_lt_mul hQ, hPQ]; exact h0
  -- d1 * 2^S is a multiple of 2^S below 2^64, so at most 2^64 - 2^S.
  have hk : d1 * 2 ^ S + 2 ^ S ≤ 2 ^ 64 := by
    have : d1 < 2 ^ (64 - S) := by
      by_contra h
      have : 2 ^ (64 - S) * 2 ^ S ≤ d1 * 2 ^ S := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.mul_comm, hPQ] at this; omega
    have : (d1 + 1) * 2 ^ S ≤ 2 ^ (64 - S) * 2 ^ S := Nat.mul_le_mul_right _ this
    rw [Nat.mul_comm (2 ^ (64 - S)), hPQ] at this; nlinarith
  omega

/-- A 4-word number is less than its top two words and one, times 2^128. -/
theorem words4_lt_top2 (m : Mem) (a : BitVec 64) :
    words m a 4 < ((memWord m (a + 16#64).toNat).toNat +
      2 ^ 64 * (memWord m (a + 24#64).toNat).toNat + 1) * 2 ^ 128 := by
  simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
    Nat.add_zero]
  have := (memWord m a.toNat).isLt
  have := (memWord m (a + 8#64).toNat).isLt
  omega

/-- A 4-word number is at least its top two words times 2^128. -/
theorem words4_ge_top2 (m : Mem) (a : BitVec 64) :
    ((memWord m (a + 16#64).toNat).toNat + 2 ^ 64 * (memWord m (a + 24#64).toNat).toNat) *
      2 ^ 128 ≤ words m a 4 := by
  simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
    Nat.add_zero]
  omega


/-- The store of s0 below sp is in the stack frame of `udivrem_top1<3>()`. -/
theorem unchangedExcept2_s0 (m : Mem) (r sp v : BitVec 64) (hs : (sp - 16#64).toNat + 16 ≤ 2 ^ 64) :
    UnchangedExcept2 m (memStore m (sp + 18446744073709551608#64).toNat v) r 64 (sp - 16#64) 16 := by
  rw [unchangedExcept2_memStore _ _ (Or.inr ⟨by bv_omega, by bv_omega⟩)]
  exact unchangedExcept2_refl _ _ _ _ _

/-- The word of the stored words at `b`. -/
theorem memWord_storeWords_getD {b : Nat} : ∀ {m : Mem} {a : Nat} (ws : List (BitVec 64)),
    a ≤ b → (b - a) % 8 = 0 → b < a + 8 * ws.length →
    memWord (storeWords m a ws) b = ws.getD ((b - a) / 8) 0
  | _, _, [], h1, _, h => by simp at h; omega
  | m, a, w :: ws, h1, h2, h3 => by
    simp only [List.length_cons] at h3
    rw [storeWords]
    by_cases hb : b = a
    · subst hb
      rw [memWord_storeWords_of_le ws (by omega), memWord_memStore_self]
      simp
    · rw [memWord_storeWords_getD ws (by omega) (by omega) (by omega)]
      have : (b - a) / 8 = (b - (a + 8)) / 8 + 1 := by omega
      rw [this, List.getD_cons_succ]

/-- The stores of words above the data leave it. -/
theorem holdsData_storeWords_of_ge {c : Nat} (ws : List (BitVec 64)) :
    ∀ {m : Mem} {a : BitVec 64} (ds : List (BitVec 64)), a.toNat + 8 * ds.length ≤ c →
    a.toNat + 8 * ds.length ≤ 2 ^ 64 → HoldsData m a ds → HoldsData (storeWords m c ws) a ds
  | _, _, [], _, _, _ => trivial
  | m, a, d :: ds, h1, h2, ⟨hd, hds⟩ => by
    simp only [List.length_cons] at h1 h2
    refine ⟨by rw [memWord_storeWords_of_le ws (by omega)]; exact hd, ?_⟩
    cases ds with
    | nil => trivial
    | cons d' ds' =>
      simp only [List.length_cons] at h1 h2
      have h8 : (a + 8).toNat = a.toNat + 8 := by bv_omega
      exact holdsData_storeWords_of_ge ws (d' :: ds') (by simp; omega) (by simp; omega) hds

/-- `nonVacuousI_of` with the words `ws` of the arguments stored at `a`, above the data in the RAM
of `envM_exists`: `pre` must hold for the memory with them. -/
theorem nonVacuousI_of_args {code : Code} {data : List (BitVec 64)} {off : Nat}
    {bufs : Regs → List (BitVec 64)} {pre : Regs → Mem → Prop} (x : Regs) (a : Nat)
    (ws : List (BitVec 64))
    (hc : 4 * code.length ≤ off) (ho : off % 8 = 0) (hoff : off ≤ 0x80000400)
    (hd : 8 * data.length ≤ 0x800)
    (hb : ∀ a ∈ bufs x, 0x80000000 ≤ a.toNat ∧ a.toNat + 8 ≤ 0x80001000 ∧
      a.toNat % 8 = 0 ∧ (a.toNat + 8 ≤ 0x80000400 - off ∨ 0x80000400 + 8 * data.length ≤ a.toNat))
    (ha : 0x80000400 + 8 * data.length ≤ a) (hpre : ∀ m, pre x (storeWords m a ws)) :
    NonVacuousI code data off bufs pre := by
  obtain ⟨S, val, e, hm, hw⟩ := envM_exists
  have hbase : (BitVec.ofNat 64 (0x80000400 - off)).toNat = 0x80000400 - off := by
    rw [BitVec.toNat_ofNat]; omega
  have hdat : BitVec.ofNat 64 (0x80000400 - off) + BitVec.ofNat 64 off = 0x80000400#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hbase, BitVec.toNat_ofNat]
    simp; omega
  refine ⟨{ S with mem := storeWords (storeWords S.mem 0x80000400 data) a ws }, val, x,
    BitVec.ofNat 64 (0x80000400 - off), e.with_mem _, ?_, hc, ?_,
    fun a ha => ?_, fun a ha => ?_, ?_, hpre _⟩
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, hbase, show BitVec.toNat (7 : BitVec 64) = 2 ^ 3 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, show BitVec.toNat (0 : BitVec 64) = 0 from rfl]
    omega
  · rw [hbase]; omega
  · obtain ⟨h1, h2, h3, h4⟩ := hb a ha
    exact ⟨(hw a h1 h2 h3).1, present_storeWords _ (present_storeWords _ (hw a h1 h2 h3).2),
      by rw [hbase]; omega⟩
  · rw [dataWords, hdat] at ha
    obtain ⟨i, hi, rfl⟩ := exists_of_mem_bufWords ha
    have hn : (0x80000400#64 + BitVec.ofNat 64 (8 * i)).toNat = 0x80000400 + 8 * i := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; simp; omega
    exact ⟨(hw _ (by omega) (by omega) (by omega)).1,
      present_storeWords _ (present_storeWords _ (hw _ (by omega) (by omega) (by omega)).2)⟩
  · rw [hdat]
    exact holdsData_storeWords_of_ge ws data (by simp; omega) (by simp; omega)
      (holdsData_storeWords (a := 0x80000400#64) data (by simp; omega))

end IntxRV.Api
