import IntxRV.Api.udivrem_top2_3_320
import IntxRV.Div256
import IntxRV.Gen.Api.udivrem_top2_3_equal_320

/-!
# The blocks of `udivrem_top2<3, true>()` of `uint320` by `uint256`

With EQUAL the top word of u may equal v[2] and the quotient has up to 129 bits. The code
subtracts `v 2^128` from u when u is not less, selected by the borrow of the top 3 words of the
normalized u minus the normalized v (`topE_sel`); the quotient bit 128 is then 1. When the top 2
words of the normalized u then equal the top 2 words of the normalized v the estimate is clamped
to `2^128 - 1` (`topE_clamp_run`): the remainder of the clamped estimate, the low 2 words of the
normalized u plus vt, has a bit 128 that the correction of the estimate takes into account
(`topE_r0h`). The other blocks are those of `IntxRV/DivTop2_320.lean` in other registers: the two
divisions of 3 by 2 words, the subtraction of q times the low bits of v, the correction loop
(`topE_loop`) and the stores of the quotient of 3 words (`topE_exit`).
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- With the top word of u at most the top word of v, u is less than `2 v 2^128`. -/
theorem topE_bound {U V : Nat} (hV : 2 ^ 128 ≤ V) (hpre : U / 2 ^ 256 < V / 2 ^ 128 + 1) :
    U < 2 * (V * 2 ^ 128) := by
  have h1 : U < (V / 2 ^ 128 + 1) * 2 ^ 256 := by
    have := Nat.lt_mul_of_div_lt hpre (Nat.two_pow_pos 256)
    rwa [Nat.mul_comm] at this ⊢
  have h2 : V / 2 ^ 128 * 2 ^ 128 ≤ V := Nat.div_mul_le_self V _
  have h3 : (V / 2 ^ 128 + 1) * 2 ^ 256 = V / 2 ^ 128 * 2 ^ 128 * 2 ^ 128 + 2 ^ 128 * 2 ^ 128 := by
    rw [show (2 : Nat) ^ 256 = 2 ^ 128 * 2 ^ 128 by rw [← pow_add]]; ring
  nlinarith

/-- The quotient bit 128: `u = qe 2^128 v + u'` with `u' < v 2^128`. -/
theorem topE_split {U V U' qe : Nat} (hV : 0 < V) (hU : U = qe * 2 ^ 128 * V + U')
    (hU' : U' < V * 2 ^ 128) :
    U / V = qe * 2 ^ 128 + U' / V ∧ U % V = U' % V ∧ U' / V < 2 ^ 128 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hU, Nat.add_comm, Nat.add_mul_div_right _ _ hV, Nat.add_comm]
  · rw [hU, Nat.add_comm, Nat.add_mul_mod_self_right]
  · exact Nat.div_lt_of_lt_mul hU'

/-- The clamped estimate: the top 2 digits of the normalized u' are the top digits of v. -/
theorem topE_clamp {T D : Nat} (h : T / 2 ^ 128 = D) :
    T = (2 ^ 128 - 1) * D + (T % 2 ^ 128 + D) := by
  have := Nat.div_add_mod T (2 ^ 128)
  rw [h] at this
  have e : (2 ^ 128 - 1) * D + D = 2 ^ 128 * D := by
    rw [Nat.sub_mul, Nat.one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ (by norm_num))]
  omega

/-- With the bit 128 of the remainder of the clamped estimate set, the estimate is the quotient
and the remainder is `r0 Q + u' mod Q - q (v mod Q)`, whatever the borrow out of 3 words. -/
theorem topE_r0h {U V q r0 R vl rw b Q D X : Nat} (hQ : 0 < Q) (hQ64 : Q ≤ 2 ^ 64)
    (hT : U / Q = q * D + r0) (hD : D = V / Q) (hvl : vl = V % Q) (hX : X = r0 * Q + U % Q)
    (hrw : rw = X % 2 ^ 192) (hsm : R + q * vl = rw + 2 ^ 192 * b) (hR : R < 2 ^ 192)
    (hq : q = 2 ^ 128 - 1) (hr0 : 2 ^ 128 ≤ r0) (hr0l : r0 < 2 ^ 129) (hUV : U < V * 2 ^ 128)
    (hV : V < 2 ^ 192) :
    U / V = q ∧ U % V = R := by
  -- u - q v = X - q vl, not negative.
  have hUq : U = q * V + (X - q * vl) ∧ q * vl ≤ X := by
    have hV' : V = Q * D + vl := by rw [hD, hvl, Nat.div_add_mod]
    have hU' : U = Q * (U / Q) + U % Q := (Nat.div_add_mod U Q).symm
    have hqvl : q * vl < 2 ^ 128 * Q := by
      have : vl < Q := by rw [hvl]; exact Nat.mod_lt _ hQ
      calc q * vl ≤ q * Q := Nat.mul_le_mul_left _ this.le
        _ < 2 ^ 128 * Q := by rw [hq]; exact Nat.mul_lt_mul_of_pos_right (by norm_num) hQ
    have hXl : 2 ^ 128 * Q ≤ X := by
      have := Nat.mul_le_mul_right Q hr0; rw [hX]; omega
    refine ⟨?_, by omega⟩
    rw [hU', hT, hX, hV']
    have : q * vl ≤ r0 * Q + U % Q := by rw [← hX]; omega
    zify [this]
    ring
  obtain ⟨hU, hle⟩ := hUq
  -- u - q v < v: u < v 2^128 = (q + 1) v.
  have hlt : X - q * vl < V := by
    have : U < (q + 1) * V := by rw [hq, Nat.sub_add_cancel (by norm_num), Nat.mul_comm]; exact hUV
    nlinarith
  have hdiv : U / V = q ∧ U % V = X - q * vl := by
    have hV0 : 0 < V := by omega
    rw [hU, Nat.add_comm, Nat.mul_comm q V, Nat.add_mul_div_left _ _ hV0, Nat.div_eq_of_lt hlt,
      Nat.zero_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
    exact ⟨rfl, rfl⟩
  refine ⟨hdiv.1, ?_⟩
  rw [hdiv.2]
  -- The 3 words: X mod 2^192 and the borrow b.
  have hXlt : X - q * vl < 2 ^ 192 := by omega
  have hmod := Nat.div_add_mod X (2 ^ 192)
  rw [← hrw] at hmod
  have hX2 : X / 2 ^ 192 ≤ 1 := by
    have : X < 2 * 2 ^ 192 := by
      rw [hX]
      have : U % Q < Q := Nat.mod_lt _ hQ
      have h1 : r0 * Q + Q ≤ 2 ^ 129 * Q := by nlinarith
      have h2 : 2 ^ 129 * Q ≤ 2 ^ 129 * 2 ^ 64 := Nat.mul_le_mul_left _ hQ64
      norm_num at h2 ⊢
      omega
    omega
  omega

/-- The top word of u, u[4], is at most v[2] by the precondition with EQUAL. -/
theorem topE_ue (m : Mem) (u v : BitVec 64)
    (h : words m u 5 / 2 ^ (64 * (3 + 1)) < words m v 4 / 2 ^ (64 * (3 - 1)) + 1)
    (h3 : memWord m (v + 24#64).toNat = 0#64) :
    (memWord m (u + 32#64).toNat).toNat ≤ (memWord m (v + 16#64).toNat).toNat := by
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

/-- The first inlined `udivrem_3by2()` of `udivrem_top2<3, true>()` of `uint320`, from 162 to
192: `t2:t4:t3` by `a5:a6` with the reciprocal in t5, to the quotient in t2 and the remainder in
`t3:t4`, with t6 0. -/
theorem topE_div_top {A : List (BitVec 64)} {hi : BitVec 20} {lo : BitVec 12} (base : BitVec 64)
    (x : Regs) (m : Mem)
    (hd : 2 ^ 127 ≤ (x.get 5#5).toNat + 2 ^ 64 * (x.get 16#5).toNat)
    (hu : (x.get 7#5).toNat * 2 ^ 64 + (x.get 29#5).toNat <
      (x.get 5#5).toNat + 2 ^ 64 * (x.get 16#5).toNat)
    (hv : (x.get 30#5).toNat =
      (2 ^ 192 - 1) / ((x.get 5#5).toNat + 2 ^ 64 * (x.get 16#5).toNat) - 2 ^ 64) :
    Reach A (udivrem_top2_3_equal_320_progAt hi lo) base (pcAt base 162) x m (pcAt base 192)
      (fun x' m' => m' = m ∧ x'.get 31#5 = 0#64 ∧ Div3Out x x' ((x.get 7#5).toNat * 2 ^ 128 +
        (x.get 29#5).toNat * 2 ^ 64 + (x.get 28#5).toNat)
        ((x.get 5#5).toNat + 2 ^ 64 * (x.get 16#5).toNat) 7#5 28#5 29#5
        [7#5, 8#5, 9#5, 18#5, 28#5, 29#5, 31#5]) := by
  rv_exec
  all_goals
    beta_reduce
    simp only [Div3Out]
    rv_cse
    have hs := div3by2BV_spec (x.get 7#5) (x.get 29#5) (x.get 28#5) (x.get 5#5) (x.get 16#5)
      (x.get 30#5) hd hu hv
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

/-- The second inlined `udivrem_3by2()` of `udivrem_top2<3, true>()` of `uint320`, from 192 to
224 (with the add-back out of line): `t4:t3:a6` by `a5:a6` with the reciprocal in t5 and t6 0, to
the quotient in t4 and the remainder in `a6:t5` (a6 high), with t3 0 (the bit 128 of the remainder). -/
theorem topE_div_low {A : List (BitVec 64)} {hi : BitVec 20} {lo : BitVec 12} (base : BitVec 64)
    (x : Regs) (m : Mem)
    (hd : 2 ^ 127 ≤ (x.get 5#5).toNat + 2 ^ 64 * (x.get 16#5).toNat)
    (hu : (x.get 29#5).toNat * 2 ^ 64 + (x.get 28#5).toNat <
      (x.get 5#5).toNat + 2 ^ 64 * (x.get 16#5).toNat)
    (hv : (x.get 30#5).toNat =
      (2 ^ 192 - 1) / ((x.get 5#5).toNat + 2 ^ 64 * (x.get 16#5).toNat) - 2 ^ 64)
    (h31 : x.get 31#5 = 0#64) :
    Reach A (udivrem_top2_3_equal_320_progAt hi lo) base (pcAt base 192) x m (pcAt base 224)
      (fun x' m' => m' = m ∧ x'.get 28#5 = 0#64 ∧ Div3Out x x' ((x.get 29#5).toNat * 2 ^ 128 +
        (x.get 28#5).toNat * 2 ^ 64 + (x.get 6#5).toNat)
        ((x.get 5#5).toNat + 2 ^ 64 * (x.get 16#5).toNat) 29#5 30#5 6#5
        [5#5, 6#5, 8#5, 9#5, 16#5, 28#5, 29#5, 30#5, 31#5]) := by
  rv_exec
  all_goals
    beta_reduce
    simp only [Div3Out]
    rv_cse
    rw [h31] at *
    have hs := div3by2BVz_spec (x.get 29#5) (x.get 28#5) (x.get 6#5) (x.get 5#5) (x.get 16#5)
      (x.get 30#5) hd hu hv
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

/-- The bit or of 2 borrows, not both 1, is their sum. -/
theorem or_bits_toNat {a b : BitVec 64} (ha : a.toNat ≤ 1) (hb : b.toNat ≤ 1)
    (hab : a.toNat + b.toNat ≤ 1) : (a ||| b).toNat = a.toNat + b.toNat := by
  have ea : a = 0#64 ∨ a = 1#64 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ha with h | h
    · exact Or.inl (BitVec.eq_of_toNat_eq (by simpa using h))
    · exact Or.inr (BitVec.eq_of_toNat_eq (by simpa using h))
  have eb : b = 0#64 ∨ b = 1#64 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with h | h
    · exact Or.inl (BitVec.eq_of_toNat_eq (by simpa using h))
    · exact Or.inr (BitVec.eq_of_toNat_eq (by simpa using h))
  rcases ea with rfl | rfl <;> rcases eb with rfl | rfl
  all_goals first | decide | (simp at hab)

/-- The clamped estimate of `udivrem_top2<3, true>()` of `uint320`, from 301 to 224: the quotient
`2^128 - 1` in `a7:t4` and the remainder `t1:t0 + vt` of the top digits in `a6:t5` with its bit
128 in t3, from `a6`, `t3` (t0, t1) and `a5:a6` (vt). -/
theorem topE_clamp_run {A : List (BitVec 64)} {hi : BitVec 20} {lo : BitVec 12} (base : BitVec 64)
    (x : Regs) (m : Mem) :
    Reach A (udivrem_top2_3_equal_320_progAt hi lo) base (pcAt base 301) x m (pcAt base 224)
      (fun x' m' => m' = m ∧ x'.get 7#5 = 18446744073709551615#64 ∧
        x'.get 29#5 = 18446744073709551615#64 ∧ (x'.get 28#5).toNat ≤ 1 ∧
        (x'.get 30#5).toNat + 2 ^ 64 * (x'.get 6#5).toNat + 2 ^ 128 * (x'.get 28#5).toNat =
          (x.get 6#5).toNat + 2 ^ 64 * (x.get 28#5).toNat +
            ((x.get 5#5).toNat + 2 ^ 64 * (x.get 16#5).toNat) ∧
        x' 0 = x 0 ∧ ∀ r, r ∉ [5#5, 6#5, 7#5, 16#5, 28#5, 29#5, 30#5] → x' r = x r) := by
  rv_exec
  rename_i s0 hs0 s1 hs1 c0 hc0 c1 hc1 s2 hs2 c2 hc2 c hc
  have h0 := defn_carry_left hs0 hc0
  have h1 := defn_carry_left hs1 hc1
  have h2 := defn_carry_left hs2 hc2
  have hc0b : c0.toNat ≤ 1 := by rw [hc0.eq]; split <;> simp
  have hc1b : c1.toNat ≤ 1 := by rw [hc1.eq]; split <;> simp
  have hc2b : c2.toNat ≤ 1 := by rw [hc2.eq]; split <;> simp
  have h12 : c1.toNat + c2.toNat ≤ 1 := by
    have := s1.isLt; have := s2.isLt; have := (x.get 28#5).isLt; have := (x.get 16#5).isLt
    omega
  have hcv : c.toNat = c1.toNat + c2.toNat ∧ c.toNat ≤ 1 := by
    rw [hc.eq, or_bits_toNat hc1b hc2b h12]; exact ⟨rfl, h12⟩
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · exact hcv.2
  · rw [hcv.1]
    linarith
  · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp (config := { decide := true }) only [Regs.set_apply, hr, ↓reduceIte]

/-- The result of `udivrem_top2<3, true>()` of `uint320` stored as the quotient `q` of three words
and the remainder `a` of 3 words, in the order of its stores. -/
theorem words_ret9q3 (m : Mem) (r q0 q1 q2 a0 a1 a2 z : BitVec 64) (hz : z = 0#64)
    (hr : r.toNat + 72 ≤ 2 ^ 64)
    (m' : Mem) (hm : m' = memStore (memStore (memStore (memStore (memStore (memStore (memStore
      (memStore (memStore m (r + 64#64).toNat z) r.toNat q0) (r + 8#64).toNat q1) (r + 16#64).toNat q2)
      (r + 24#64).toNat z) (r + 32#64).toNat z) (r + 40#64).toNat a0)
      (r + 48#64).toNat a1) (r + 56#64).toNat a2) :
    words m' r 5 = q0.toNat + 2 ^ 64 * (q1.toNat + 2 ^ 64 * q2.toNat) ∧
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

/-- The end of `udivrem_top2<3, true>()` of `uint320` from 268: the quotient bit 128 from the
borrow of the subtraction of `v 2^128` in a1, the stores of the quotient in `a7:t0:a1` and the
remainder in `a4:a3:a2`, and the return. -/
theorem topE_exit {hi : BitVec 20} {lo : BitVec 12} (base T : BitVec 64) (x : Regs) (m : Mem)
    (hpre : udivrem_top2_3_equal_320.pre x m) (hr : x.get 1#5 &&& 3 = 0) (x' : Regs) (m' : Mem)
    (h10 : x'.get 10#5 = x.get 10#5) (h1 : x'.get 1#5 = x.get 1#5)
    (hcs : ∀ i ∈ calleeSaved, x' i = x i)
    (hm : UnchangedExcept2 m m' (x.get 10#5) 72 (x.get 2#5 - 48#64) 48)
    (hqr : (x'.get 5#5).toNat + 2 ^ 64 * ((x'.get 7#5).toNat +
        2 ^ 64 * (x'.get 11#5 ^^^ 1#64).toNat) =
        words m (x.get 11#5) 5 / words m (x.get 12#5) 4 ∧
      (x'.get 12#5).toNat + 2 ^ 64 * ((x'.get 13#5).toNat + 2 ^ 64 * (x'.get 14#5).toNat) =
        words m (x.get 11#5) 5 % words m (x.get 12#5) 4) :
    Reach (bufWords (x.get 11#5) 5 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 9 ++
        bufWords (x.get 2#5 - 48#64) 6 ++ bufWords T 256) (udivrem_top2_3_equal_320_progAt hi lo)
      base (pcAt base 268) x' m' (x.get 1#5) (udivrem_top2_3_equal_320.post x m) := by
  have hpre' := hpre
  simp only [udivrem_top2_3_equal_320.pre, Buf] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hra, hrn⟩, -⟩ := hpre'
  rw [← h10]
  have hrn' : (x'.get 10#5).toNat + 72 ≤ 2 ^ 64 := h10 ▸ hrn
  rv_exec
  rv_val
  rw [h1, update_aligned hr]
  refine Reach.refl ?_
  have hw := words_ret9q3 m' (x'.get 10#5) (x'.get 5#5) (x'.get 7#5) (x'.get 11#5 ^^^ 1#64)
    (x'.get 12#5) (x'.get 13#5) (x'.get 14#5) (0 : BitVec 64) rfl hrn' _ rfl
  simp only [udivrem_top2_3_equal_320.post]
  simp (disch := decide) only [Regs.eq_get x]
  rw [← h10] at hm ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hw.1, hqr.1]
  · rw [hw.2.1, hqr.2]
  · simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
    exact hm
  · intro i hi
    have hne : i ≠ 11#5 := fun h => by subst h; exact absurd hi (by decide)
    rw [Regs.set_apply, if_pos (by decide), Regs.set_apply, if_neg (by decide), if_neg hne]
    exact hcs i hi

/-- The quotient and the remainder after the last correction of `udivrem_top2<3, true>()`, with
the quotient bit 128. -/
theorem topE_exit_nat {R' q0 q1 R q U' U V qe : Nat} (h : R' + 2 ^ 192 = R + V) (hd : q0 + 2 ^ 64 * q1 + 1 = q)
    (hsm : R + q * V = U' + 2 ^ 192) (hR : R < 2 ^ 192) (hqe : qe * 2 ^ 128 * V + U' = U)
    (hU' : U' < V * 2 ^ 128) :
    q0 + 2 ^ 64 * (q1 + 2 ^ 64 * qe) = U / V ∧ R' = U % V := by
  obtain ⟨h1, h2⟩ := top2_exit_nat h hd hsm hR
  have hV : 0 < V := by
    rcases Nat.eq_zero_or_pos V with hv | hv
    · subst hv; simp at hU'
    · exact hv
  obtain ⟨s1, s2, -⟩ := topE_split (U := U) hV hqe.symm hU'
  refine ⟨?_, by rw [s2, h2]⟩
  rw [s1, ← h1]; ring

/-- The registers and the memory at the head of the correction loop of `udivrem_top2<3>()` of
`uint320`, at 254: `a5:a3:a4 + q * v = u + 2^192`, with the quotient `q` in `a1:t1` and the words of
v in `a6:a7:t0`; `n` the excess of `q`. -/
def topELoop (x : Regs) (m : Mem) (U' : Nat) (n : Nat) (x' : Regs) (m' : Mem) : Prop :=
  x'.get 10#5 = x.get 10#5 ∧ x'.get 1#5 = x.get 1#5 ∧ (∀ i ∈ calleeSaved, x' i = x i) ∧
    UnchangedExcept2 m m' (x.get 10#5) 72 (x.get 2#5 - 48#64) 48 ∧
    (x'.get 16#5).toNat + 2 ^ 64 * ((x'.get 17#5).toNat + 2 ^ 64 * (x'.get 6#5).toNat) =
      words m (x.get 12#5) 4 ∧
    (x'.get 15#5).toNat + 2 ^ 64 * ((x'.get 13#5).toNat + 2 ^ 64 * (x'.get 14#5).toNat) +
      ((x'.get 29#5).toNat + 2 ^ 64 * (x'.get 7#5).toNat) * words m (x.get 12#5) 4 =
      U' + 2 ^ 192 ∧
    (x'.get 11#5 ^^^ 1#64).toNat * 2 ^ 128 * words m (x.get 12#5) 4 + U' = words m (x.get 11#5) 5 ∧
    U' < words m (x.get 12#5) 4 * 2 ^ 128 ∧
    n = (x'.get 29#5).toNat + 2 ^ 64 * (x'.get 7#5).toNat - U' / words m (x.get 12#5) 4

/-- The correction loop of `udivrem_top2<3>()` of `uint320` from 254. -/
theorem topE_loop {hi : BitVec 20} {lo : BitVec 12} (base T : BitVec 64) (x : Regs) (m : Mem)
    (hpre : udivrem_top2_3_equal_320.pre x m) (hr : x.get 1#5 &&& 3 = 0) (U' : Nat) :
    ∀ n x' m', topELoop x m U' n x' m' →
    Reach (bufWords (x.get 11#5) 5 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 9 ++
        bufWords (x.get 2#5 - 48#64) 6 ++ bufWords T 256) (udivrem_top2_3_equal_320_progAt hi lo) base
      (pcAt base 282) x' m' (x.get 1#5) (udivrem_top2_3_equal_320.post x m) := by
  apply Reach.loop (topELoop x m U')
  intro n x' m' h ih
  obtain ⟨h10, h1, hcs, hm, hv, hsm, hqe, hU', hn⟩ := h
  have hR := words3_lt (x'.get 15#5) (x'.get 13#5) (x'.get 14#5)
  have hlt := top2_q_gt hR hsm
  rv_step
  rv_exec_cut 268 282
  all_goals try simp only [zopz0zI_u_eq, decide_eq_true_eq, decide_eq_false_iff_not] at *
  all_goals try rv_conds
  -- The sum r + v and the quotient less 1, from the values of the run.
  all_goals
    simp only [Defn] at *
    subst_vars
    have hd := dec2_toNat (q0 := x'.get 29#5) (q1 := x'.get 7#5) rfl rfl
      (Nat.lt_of_le_of_lt (Nat.zero_le _) hlt)
  -- A carry out of r + v: the end.
  all_goals first
    | (rv_not_at 268; skip)
    | (have ha := add3c_carry (r0 := x'.get 15#5) (r1 := x'.get 13#5) (r2 := x'.get 14#5)
         (v0 := x'.get 16#5) (v1 := x'.get 17#5) (v2 := x'.get 6#5) rfl rfl rfl rfl rfl rfl rfl rfl rfl
         (by tauto)
       rw [hv] at ha
       refine topE_exit base T x m hpre hr _ _ ?_ ?_ ?_ hm ?_
       · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h10
       · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h1
       · refine calleeSaved_of hcs _ ?_
         intro i hi
         simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
         rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
           rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
       · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
         exact topE_exit_nat ha hd hsm hR hqe hU')
  -- No carry: the next correction.
  all_goals
    have ha := add3c_nocarry (r0 := x'.get 15#5) (r1 := x'.get 13#5) (r2 := x'.get 14#5)
      (v0 := x'.get 16#5) (v1 := x'.get 17#5) (v2 := x'.get 6#5) rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (by assumption) (by assumption)
    rw [hv] at ha
    refine ih _ ?_ _ _ ⟨?_, ?_, ?_, hm, ?_, ?_, ?_, hU', rfl⟩
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
    · exact hqe

/-- The borrow of `udivrem_top2<3, true>()` as the or of the two borrows of the top word. -/
theorem topE_bor_zero {bor c3 c4 : BitVec 64} {a b : Prop} [Decidable a] [Decidable b]
    (h : Defn bor (c3 ||| c4)) (h3 : Defn c3 (if a then 1#64 else 0#64))
    (h4 : Defn c4 (if b then 1#64 else 0#64)) : bor = 0#64 ↔ ¬a ∧ ¬b := by
  rw [h.eq, h3.eq, h4.eq]
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb]

/-- No borrow out of `r0 Q + u mod Q - q (v mod Q)` with `q` not less than the quotient: `q` is
the quotient and the words the remainder. -/
theorem topE_nb_nat {U V q r0 R vl rw Q : Nat} (hT : U / Q = q * (V / Q) + r0)
    (hvl : vl = V % Q) (hrw : rw = r0 * Q + U % Q) (hsm : R + q * vl = rw)
    (hq : U / V ≤ q) (hV : 0 < V) : U / V = q ∧ U % V = R := by
  have h := top2_nat hT hvl hrw (b := 0) (by rw [hsm]; ring)
  rw [Nat.mul_zero, Nat.add_zero] at h
  have hR : R < V := by
    by_contra hc
    have : (q + 1) * V ≤ U := by nlinarith
    have : q + 1 ≤ U / V := (Nat.le_div_iff_mul_le hV).2 this
    omega
  have := div_mod_of_lt (q := q) (r := R) (by omega : R + q * V = U) hR
  exact ⟨this.1.symm, this.2.symm⟩

/-- The quotient and the remainder at the end of `udivrem_top2<3, true>()` without the correction
loop: no borrow, or the bit 128 of the remainder of the clamped estimate set. -/
theorem topE_sub_exit_nat {U U' V q q0 q1 qe r0 R vl rw Q c : Nat} (hQ : 0 < Q) (hQ64 : Q ≤ 2 ^ 64)
    (hq01 : q = q0 + 2 ^ 64 * q1)
    (hT : U' / Q = q * (V / Q) + r0) (hvl : vl = V % Q) (hrw : rw = (r0 * Q + U' % Q) % 2 ^ 192)
    (hsm : R + q * vl = rw + 2 ^ 192 * c) (hR : R < 2 ^ 192) (hr0l : r0 < 2 ^ 129)
    (hq : U' / V ≤ q) (hclamp : 2 ^ 128 ≤ r0 → q = 2 ^ 128 - 1)
    (hqe : qe * 2 ^ 128 * V + U' = U) (hU' : U' < V * 2 ^ 128) (hV : 0 < V) (hVl : V < 2 ^ 192)
    (hc : c = 0 ∨ 2 ^ 128 ≤ r0) :
    q0 + 2 ^ 64 * (q1 + 2 ^ 64 * qe) = U / V ∧ R = U % V := by
  have hU'res : U' / V = q ∧ U' % V = R := by
    rcases Nat.lt_or_ge r0 (2 ^ 128) with h | h
    · have hc0 : c = 0 := by rcases hc with hc | hc <;> omega
      subst hc0
      have hX : r0 * Q + U' % Q < 2 ^ 192 := by
        have : U' % Q < Q := Nat.mod_lt _ hQ
        have h1 : r0 * Q + Q ≤ 2 ^ 128 * Q := by nlinarith
        have h2 : 2 ^ 128 * Q ≤ 2 ^ 128 * 2 ^ 64 := Nat.mul_le_mul_left _ hQ64
        norm_num at h2 ⊢; omega
      rw [Nat.mod_eq_of_lt hX] at hrw
      exact topE_nb_nat hT hvl hrw (by rw [hsm]; ring) hq hV
    · exact topE_r0h hQ hQ64 hT rfl hvl rfl hrw hsm hR (hclamp h) h hr0l hU' hVl
  obtain ⟨s1, s2, -⟩ := topE_split (U := U) hV hqe.symm hU'
  refine ⟨?_, by rw [s2, hU'res.2]⟩
  rw [s1, hU'res.1, hq01]; ring

/-- The invariant of the correction loop of `udivrem_top2<3, true>()` at its start: a borrow with
the bit 128 of the remainder of the top digits clear. -/
theorem topE_loop_nat {U' V q r0 R vl rw Q : Nat} (hQ : 0 < Q) (hQ64 : Q ≤ 2 ^ 64)
    (hT : U' / Q = q * (V / Q) + r0) (hvl : vl = V % Q) (hrw : rw = (r0 * Q + U' % Q) % 2 ^ 192)
    (hsm : R + q * vl = rw + 2 ^ 192 * 1) (hr0 : r0 < 2 ^ 128) :
    R + q * V = U' + 2 ^ 192 := by
  have hX : r0 * Q + U' % Q < 2 ^ 192 := by
    have : U' % Q < Q := Nat.mod_lt _ hQ
    have h1 : r0 * Q + Q ≤ 2 ^ 128 * Q := by nlinarith
    have h2 : 2 ^ 128 * Q ≤ 2 ^ 128 * 2 ^ 64 := Nat.mul_le_mul_left _ hQ64
    norm_num at h2 ⊢; omega
  rw [Nat.mod_eq_of_lt hX] at hrw
  have := top2_nat hT hvl hrw hsm
  simpa using this

/-- The end of `udivrem_top2<3, true>()` of `uint320` from the `submul()` of the quotient words at
247: the remainder `rw = (r0 * Q + u' mod Q) mod 2^192` in `t1:t5:a6`, `v mod Q` in a3, the quotient
in `t4:t2` and the bit 128 of `r0` in t3, for the quotient `q` and the remainder `r0` of `u' / Q`
by `v / Q`, `u' = u - qe v 2^128` with the quotient bit `qe` from a1. -/
theorem topE_sub {hi : BitVec 20} {lo : BitVec 12} (base T : BitVec 64) (x : Regs) (m : Mem)
    (hpre : udivrem_top2_3_equal_320.pre x m) (hr : x.get 1#5 &&& 3 = 0) (x' : Regs) (m' : Mem)
    (h10 : x'.get 10#5 = x.get 10#5) (h1 : x'.get 1#5 = x.get 1#5)
    (h12 : x'.get 12#5 = x.get 12#5) (hcs : ∀ i ∈ calleeSaved, x' i = x i)
    (hm : UnchangedExcept2 m m' (x.get 10#5) 72 (x.get 2#5 - 48#64) 48) (U' r0 Q : Nat)
    (hQ : 0 < Q) (hQ64 : Q ≤ 2 ^ 64)
    (hT : U' / Q =
      ((x'.get 29#5).toNat + 2 ^ 64 * (x'.get 7#5).toNat) * (words m (x.get 12#5) 4 / Q) + r0)
    (hvl : (x'.get 13#5).toNat = words m (x.get 12#5) 4 % Q)
    (hrw : (x'.get 16#5).toNat + 2 ^ 64 * ((x'.get 30#5).toNat + 2 ^ 64 * (x'.get 6#5).toNat) =
      (r0 * Q + U' % Q) % 2 ^ 192)
    (hr0h : (x'.get 28#5).toNat = r0 / 2 ^ 128) (hr0l : r0 < 2 ^ 129)
    (hq : U' / words m (x.get 12#5) 4 ≤ (x'.get 29#5).toNat + 2 ^ 64 * (x'.get 7#5).toNat)
    (hclamp : 2 ^ 128 ≤ r0 → (x'.get 29#5).toNat + 2 ^ 64 * (x'.get 7#5).toNat = 2 ^ 128 - 1)
    (hqe : (x'.get 11#5 ^^^ 1#64).toNat * 2 ^ 128 * words m (x.get 12#5) 4 + U' =
      words m (x.get 11#5) 5)
    (hU' : U' < words m (x.get 12#5) 4 * 2 ^ 128) :
    Reach (bufWords (x.get 11#5) 5 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 9 ++
        bufWords (x.get 2#5 - 48#64) 6 ++ bufWords T 256) (udivrem_top2_3_equal_320_progAt hi lo)
      base (pcAt base 247) x' m' (x.get 1#5) (udivrem_top2_3_equal_320.post x m) := by
  have hpre' := hpre
  simp only [udivrem_top2_3_equal_320.pre, Buf] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr, hv1, hv2,
    hu3⟩ := hpre'
  simp only [Disjoint] at hdrv hdsv
  have hV : 0 < words m (x.get 12#5) 4 := by
    have : 0 < 2 ^ (64 * 2) := by positivity
    omega
  have hVl : words m (x.get 12#5) 4 < 2 ^ 192 := by simpa using hv2
  have hv3 := top4_zero m (x.get 12#5) hv2
  have hw0 : memWord m' (x.get 12#5).toNat = memWord m (x.get 12#5).toNat :=
    memWord_of_unchangedExcept2 hm _ (by bv_omega) (by bv_omega)
  have hw1 : memWord m' (x.get 12#5 + 8#64).toNat = memWord m (x.get 12#5 + 8#64).toNat :=
    memWord_of_unchangedExcept2 hm _ (by bv_omega) (by bv_omega)
  have hw2 : memWord m' (x.get 12#5 + 16#64).toNat = memWord m (x.get 12#5 + 16#64).toNat :=
    memWord_of_unchangedExcept2 hm _ (by bv_omega) (by bv_omega)
  have hr0h' : r0 < 2 ^ 128 ↔ x'.get 28#5 = 0#64 := by
    constructor
    · intro h; apply BitVec.eq_of_toNat_eq; rw [hr0h, Nat.div_eq_of_lt h]; rfl
    · intro h; have := congrArg BitVec.toNat h; rw [hr0h] at this
      simp at this; exact this
  rw [← h12]
  rv_exec_cut 264
  rename_i p0 hp0 h0 hh0 p1 hp1 h1' hh1 R0 hR0 y1 hy1 c0 hc0 c1 hc1 b0 hb0 b1 hb1 R1 hR1 z2 hz2 c2 hc2
    c3 hc3 R2 hR2 c4 hc4 bor hbor
  have hs := top2_submul_words hR2 hz2 hc2 hR1 hb1 hb0 hc1 hc0 hy1 hR0 hh1 hp1 hh0 hp0
  have hbz := topE_bor_zero hbor hc3 hc4
  have hR := words3_lt R0 R1 R2
  have hcs' : ∀ y : Regs, (∀ i ∈ calleeSaved, y i = x' i) → ∀ i ∈ calleeSaved, y i = x i :=
    fun y hy => calleeSaved_of hcs y hy
  rv_exec_cut 266 282
  · -- No borrow: the end.
    rename_i hb0'
    have hc0' := hbz.1 hb0'
    rw [h12]
    rv_exec_cut 268
    refine topE_exit base T x m hpre hr _ _ ?_ ?_ ?_ hm ?_
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h10
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h1
    · refine hcs' _ ?_
      intro i hi
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      exact topE_sub_exit_nat hQ hQ64 rfl hT hvl hrw hs hR hr0l hq hclamp hqe hU' hV hVl
        (Or.inl (by rw [if_neg (by tauto)]))
  · -- A borrow and the bit 128 of r0 clear: the correction loop.
    rename_i hb1' hb2' wv0 hwv0 wv1 hwv1 wv2 hwv2
    rw [h12]
    have hr0 : r0 < 2 ^ 128 := hr0h'.2 hb2'
    have hc1' : (x'.get 6#5 < z2 ∨ z2 < R2) := by
      by_contra hc; exact hb1' (hbz.2 (by tauto))
    rw [if_pos hc1'] at hs
    refine topE_loop base T x m hpre hr U' _ _ _ ⟨?_, ?_, ?_, hm, ?_, ?_, ?_, hU', rfl⟩
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · exact h10
    · exact h1
    · refine hcs' _ ?_
      intro i hi
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    · rw [hwv0.eq, hwv1.eq, hwv2.eq, h12, hw0, hw1, hw2]
      exact words_v3 m _ hv3
    · exact topE_loop_nat hQ hQ64 hT hvl hrw hs hr0
    · exact hqe
  · -- A borrow and the bit 128 of r0 set: the end.
    rename_i hb1' hb2'
    have hr0 : 2 ^ 128 ≤ r0 := by
      by_contra hc; exact hb2' (hr0h'.1 (by omega))
    rw [h12]
    rv_exec_cut 268
    refine topE_exit base T x m hpre hr _ _ ?_ ?_ ?_ hm ?_
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h10
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact h1
    · refine hcs' _ ?_
      intro i hi
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      exact topE_sub_exit_nat hQ hQ64 rfl hT hvl hrw hs hR hr0l hq hclamp hqe hU' hV hVl
        (Or.inr hr0)

/-- Four words shifted right by `S < 64`: the funnel shifts and the shifted top word. -/
theorem fshr4_words (w0 w1 w2 w3 S : Nat) (hS : S < 64) :
    (w1 * 2 ^ (64 - S) % 2 ^ 64 + w0 / 2 ^ S) + 2 ^ 64 * ((w2 * 2 ^ (64 - S) % 2 ^ 64 + w1 / 2 ^ S) +
      2 ^ 64 * ((w3 * 2 ^ (64 - S) % 2 ^ 64 + w2 / 2 ^ S) + 2 ^ 64 * (w3 / 2 ^ S))) =
    (w0 + 2 ^ 64 * (w1 + 2 ^ 64 * (w2 + 2 ^ 64 * w3))) / 2 ^ S := by
  rw [← fshr3_words w0 w1 (w2 + 2 ^ 64 * w3) S hS]
  have hPQ : 2 ^ (64 - S) * 2 ^ S = 2 ^ 64 := by rw [← pow_add]; congr 1; omega
  have hP : 0 < 2 ^ S := by positivity
  have e1 : (w2 + 2 ^ 64 * w3) * 2 ^ (64 - S) % 2 ^ 64 = w2 * 2 ^ (64 - S) % 2 ^ 64 := by
    rw [show (w2 + 2 ^ 64 * w3) * 2 ^ (64 - S) = w2 * 2 ^ (64 - S) + 2 ^ 64 * (w3 * 2 ^ (64 - S))
      by ring, Nat.add_mul_mod_self_left]
  have e2 : (w2 + 2 ^ 64 * w3) / 2 ^ S = w2 / 2 ^ S + w3 * 2 ^ (64 - S) := by
    rw [show w2 + 2 ^ 64 * w3 = w2 + w3 * 2 ^ (64 - S) * 2 ^ S by rw [← hPQ]; ring,
      Nat.add_mul_div_right _ _ hP]
  have e3 : w3 * 2 ^ (64 - S) = w3 * 2 ^ (64 - S) % 2 ^ 64 + 2 ^ 64 * (w3 / 2 ^ S) := by
    have := Nat.div_add_mod (w3 * 2 ^ (64 - S)) (2 ^ 64)
    have h4 : w3 * 2 ^ (64 - S) / 2 ^ 64 = w3 / 2 ^ S := by
      rw [← hPQ, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ (by positivity)]
    omega
  rw [e1, e2]
  generalize w3 * 2 ^ (64 - S) % 2 ^ 64 = A at e3 ⊢
  generalize w3 / 2 ^ S = B at e3 ⊢
  generalize w3 * 2 ^ (64 - S) = C at e3 ⊢
  subst e3
  ring

/-- Setting sp to its own value keeps the registers. -/
theorem regs_set_of_get2 {x : Regs} {v : BitVec 64} (h : x.get 2#5 = v) : x.set 2#5 v = x := by
  funext j
  simp only [Regs.set_apply, show ((2#5 : BitVec 5) = 0) = False by decide, if_false]
  split_ifs with hj
  · subst hj; rw [← h, Regs.eq_get x (by decide)]
  · rfl

/-- The end of `udivrem_top2<3, true>()` of `uint320` after the division of the top digits, from
224: the quotient `q` in `t4:t2` and the remainder `r0` in `t3:a6:t5` of `u' / Q` by `v / Q` for
`Q = 2^(64 - s)`, the shift `s` in a5 and `~s` in a4, u[0] in a7 and v[0] in a3, and s0 to s4 in
the frame of 48 bytes. -/
theorem topE_shift {hi : BitVec 20} {lo : BitVec 12} (base T : BitVec 64) (x : Regs) (m : Mem)
    (hpre : udivrem_top2_3_equal_320.pre x m) (hr : x.get 1#5 &&& 3 = 0) (x' : Regs) (m' : Mem)
    (h10 : x'.get 10#5 = x.get 10#5) (h1 : x'.get 1#5 = x.get 1#5)
    (h12 : x'.get 12#5 = x.get 12#5) (h2 : x'.get 2#5 = x.get 2#5 + 18446744073709551568#64)
    (hcs : ∀ i ∈ calleeSaved, i ∉ [2#5, 8#5, 9#5, 18#5, 19#5, 20#5] → x' i = x i)
    (hf : memWord m' (x.get 2#5 + 18446744073709551608#64).toNat = x.get 8#5 ∧
      memWord m' (x.get 2#5 + 18446744073709551600#64).toNat = x.get 9#5 ∧
      memWord m' (x.get 2#5 + 18446744073709551592#64).toNat = x.get 18#5 ∧
      memWord m' (x.get 2#5 + 18446744073709551584#64).toNat = x.get 19#5 ∧
      memWord m' (x.get 2#5 + 18446744073709551576#64).toNat = x.get 20#5)
    (hm : UnchangedExcept2 m m' (x.get 10#5) 72 (x.get 2#5 - 48#64) 48)
    (hS : (x'.get 15#5).toNat < 64) (h14 : x'.get 14#5 = x'.get 15#5 ^^^ 18446744073709551615#64)
    (hv0 : x'.get 13#5 = memWord m (x.get 12#5).toNat)
    (hu0 : x'.get 17#5 = memWord m (x.get 11#5).toNat) (U' : Nat)
    (hUQ : U' % 2 ^ (64 - (x'.get 15#5).toNat) =
      words m (x.get 11#5) 5 % 2 ^ (64 - (x'.get 15#5).toNat))
    (hT : U' / 2 ^ (64 - (x'.get 15#5).toNat) =
      ((x'.get 29#5).toNat + 2 ^ 64 * (x'.get 7#5).toNat) *
        (words m (x.get 12#5) 4 / 2 ^ (64 - (x'.get 15#5).toNat)) +
      ((x'.get 30#5).toNat + 2 ^ 64 * (x'.get 6#5).toNat + 2 ^ 128 * (x'.get 28#5).toNat))
    (hr0h : (x'.get 28#5).toNat ≤ 1)
    (hq : U' / words m (x.get 12#5) 4 ≤ (x'.get 29#5).toNat + 2 ^ 64 * (x'.get 7#5).toNat)
    (hclamp : (x'.get 28#5).toNat = 1 →
      (x'.get 29#5).toNat + 2 ^ 64 * (x'.get 7#5).toNat = 2 ^ 128 - 1)
    (hqe : (x'.get 11#5 ^^^ 1#64).toNat * 2 ^ 128 * words m (x.get 12#5) 4 + U' =
      words m (x.get 11#5) 5)
    (hU' : U' < words m (x.get 12#5) 4 * 2 ^ 128) :
    Reach (bufWords (x.get 11#5) 5 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 9 ++
        bufWords (x.get 2#5 - 48#64) 6 ++ bufWords T 256) (udivrem_top2_3_equal_320_progAt hi lo)
      base (pcAt base 224) x' m' (x.get 1#5) (udivrem_top2_3_equal_320.post x m) := by
  have hpre' := hpre
  simp only [udivrem_top2_3_equal_320.pre, Buf] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr, hv1, hv2,
    hu3⟩ := hpre'
  have hPQ : 2 ^ (x'.get 15#5).toNat * 2 ^ (64 - (x'.get 15#5).toNat) = 2 ^ 64 := by
    rw [← pow_add]; congr 1; omega
  have hQ : 0 < 2 ^ (64 - (x'.get 15#5).toNat) := by positivity
  have hQ64 : 2 ^ (64 - (x'.get 15#5).toNat) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)
  -- The low words of u and v modulo Q.
  have hvq : words m (x.get 12#5) 4 % 2 ^ (64 - (x'.get 15#5).toNat) =
      (memWord m (x.get 12#5).toNat).toNat % 2 ^ (64 - (x'.get 15#5).toNat) := by
    simp only [words]; exact mod_low _ _ _ (by omega)
  have huq : U' % 2 ^ (64 - (x'.get 15#5).toNat) =
      (memWord m (x.get 11#5).toNat).toNat % 2 ^ (64 - (x'.get 15#5).toNat) := by
    rw [hUQ]; simp only [words]; exact mod_low _ _ _ (by omega)
  have hr0lo := (x'.get 30#5).isLt
  have hr0hi := (x'.get 6#5).isLt
  have hr0div : ((x'.get 30#5).toNat + 2 ^ 64 * (x'.get 6#5).toNat + 2 ^ 128 * (x'.get 28#5).toNat) /
      2 ^ 128 = (x'.get 28#5).toNat := by omega
  obtain ⟨f8, f9, f18, f19, f20⟩ := hf
  rw [← regs_set_of_get2 h2]
  rv_exec_cut 234
  rename_i wm hwm wvl hwvl wu hwu ws0 hws0 ws1 hws1 ws2 hws2 ws3 hws3 ws4 hws4
  rw [f8] at hws0
  rw [f9] at hws1
  rw [f18] at hws2
  rw [f19] at hws3
  rw [f20] at hws4
  have hvl : wvl.toNat = words m (x.get 12#5) 4 % 2 ^ (64 - (x'.get 15#5).toNat) := by
    rw [hwvl.eq, hwm.eq, toNat_and_mask _ _ hS, hv0, hvq]
  have hcsx : ∀ y : Regs, y 2#5 = x 2#5 → y 8#5 = x 8#5 → y 9#5 = x 9#5 → y 18#5 = x 18#5 →
      y 19#5 = x 19#5 → y 20#5 = x 20#5 →
      (∀ i ∈ calleeSaved, i ∉ [2#5, 8#5, 9#5, 18#5, 19#5, 20#5] → y i = x' i) →
      ∀ i ∈ calleeSaved, y i = x i := by
    intro y y2 y8 y9 y18 y19 y20 hy i hi
    by_cases hx : i ∈ [2#5, 8#5, 9#5, 18#5, 19#5, 20#5]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    · rw [hy i hi hx]; exact hcs i hi hx
  have hr0l : (x'.get 30#5).toNat + 2 ^ 64 * (x'.get 6#5).toNat + 2 ^ 128 * (x'.get 28#5).toNat <
      2 ^ 129 := by omega
  rv_exec_cut 247
  · -- s = 0: the words of u[0] and r0 not shifted.
    rename_i hbs
    have h0 : (x'.get 15#5).toNat = 0 := by rw [hbs]; rfl
    refine topE_sub base T x m hpre hr _ _ ?_ ?_ ?_ ?_ hm U'
      ((x'.get 30#5).toNat + 2 ^ 64 * (x'.get 6#5).toNat + 2 ^ 128 * (x'.get 28#5).toNat)
      (2 ^ (64 - (x'.get 15#5).toNat)) hQ hQ64 ?_ ?_ ?_ ?_ hr0l ?_ ?_ ?_ hU'
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · exact h10
    · exact h1
    · exact h12
    · refine hcsx _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals try simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
      all_goals try (rw [Regs.eq_get x (by decide)]; first | exact hws0.eq | exact hws1.eq | exact hws2.eq | exact hws3.eq | exact hws4.eq)
      · rw [Regs.eq_get x (by decide)]; try bv_omega
      · intro i hi hx
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl <;> simp (config := { decide := true }) only [↓reduceIte] at hx ⊢
    · exact hT
    · exact hvl
    · rw [hwu.eq, huq, h0, hu0]
      simp only [Nat.zero_mod, BitVec.shiftLeft_zero, Nat.sub_zero]
      rw [Nat.mod_eq_of_lt (memWord m (x.get 11#5).toNat).isLt,
        show ((x'.get 30#5).toNat + 2 ^ 64 * (x'.get 6#5).toNat + 2 ^ 128 * (x'.get 28#5).toNat) *
          2 ^ 64 + (memWord m (x.get 11#5).toNat).toNat =
          ((memWord m (x.get 11#5).toNat).toNat + 2 ^ 64 * ((x'.get 30#5).toNat +
            2 ^ 64 * (x'.get 6#5).toNat)) + 2 ^ 192 * (x'.get 28#5).toNat by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (words3_lt _ _ _)]
    · exact hr0div.symm
    · exact hq
    · intro h; exact hclamp (by omega)
    · exact hqe
  · -- s ≠ 0: the words of u[0] << s and r0 shifted right by s.
    rename_i hbs a hA b hB c hC d hD e hE f hF g hG h hH i' hI rw0 hrw0 rw1 hrw1 rw2 hrw2
    have hs0 : 0 < (x'.get 15#5).toNat := by
      rcases Nat.eq_zero_or_pos (x'.get 15#5).toNat with h0 | h0
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) hbs
      · exact h0
    have hwu' : wu.toNat = (memWord m (x.get 11#5).toNat).toNat * 2 ^ (x'.get 15#5).toNat % 2 ^ 64 := by
      rw [hwu.eq, hu0, BitVec.toNat_shiftLeft, Nat.mod_eq_of_lt hS, Nat.shiftLeft_eq]
    have hv0' : rw0.toNat = (x'.get 30#5).toNat * 2 ^ (64 - (x'.get 15#5).toNat) % 2 ^ 64 +
        wu.toNat / 2 ^ (x'.get 15#5).toNat := by
      rw [hrw0.eq, hG.eq, hA.eq, hB.eq, h14]; exact toNat_fshr_code _ _ _ hS hs0
    have hv1' : rw1.toNat = (x'.get 6#5).toNat * 2 ^ (64 - (x'.get 15#5).toNat) % 2 ^ 64 +
        (x'.get 30#5).toNat / 2 ^ (x'.get 15#5).toNat := by
      rw [hrw1.eq, hH.eq, hC.eq, hD.eq, h14]; exact toNat_fshr_code _ _ _ hS hs0
    have hv2' : rw2.toNat = (x'.get 28#5).toNat * 2 ^ (64 - (x'.get 15#5).toNat) % 2 ^ 64 +
        (x'.get 6#5).toNat / 2 ^ (x'.get 15#5).toNat := by
      rw [hrw2.eq, hI.eq, hE.eq, hF.eq, h14]; exact toNat_fshr_code _ _ _ hS hs0
    have h4 := fshr4_words wu.toNat (x'.get 30#5).toNat (x'.get 6#5).toNat (x'.get 28#5).toNat
      (x'.get 15#5).toNat hS
    have hz : (x'.get 28#5).toNat / 2 ^ (x'.get 15#5).toNat = 0 := by
      apply Nat.div_eq_of_lt
      calc (x'.get 28#5).toNat ≤ 1 := hr0h
        _ < 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (x'.get 15#5).toNat := Nat.pow_le_pow_right (by norm_num) hs0
    rw [hz, Nat.mul_zero, Nat.add_zero, ← hv0', ← hv1', ← hv2', hwu',
      show (memWord m (x.get 11#5).toNat).toNat * 2 ^ (x'.get 15#5).toNat % 2 ^ 64 +
        2 ^ 64 * ((x'.get 30#5).toNat + 2 ^ 64 * ((x'.get 6#5).toNat + 2 ^ 64 * (x'.get 28#5).toNat)) =
        (memWord m (x.get 11#5).toNat).toNat * 2 ^ (x'.get 15#5).toNat % 2 ^ 64 +
        2 ^ 64 * ((x'.get 30#5).toNat + 2 ^ 64 * (x'.get 6#5).toNat + 2 ^ 128 * (x'.get 28#5).toNat)
        by ring, top2_rw _ _ _ hS] at h4
    have hX : ((x'.get 30#5).toNat + 2 ^ 64 * (x'.get 6#5).toNat + 2 ^ 128 * (x'.get 28#5).toNat) *
        2 ^ (64 - (x'.get 15#5).toNat) + U' % 2 ^ (64 - (x'.get 15#5).toNat) < 2 ^ 192 := by
      have hQ63 : 2 ^ (64 - (x'.get 15#5).toNat) ≤ 2 ^ 63 :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have := Nat.mod_lt U' hQ
      have h1 : ((x'.get 30#5).toNat + 2 ^ 64 * (x'.get 6#5).toNat + 2 ^ 128 * (x'.get 28#5).toNat) *
          2 ^ (64 - (x'.get 15#5).toNat) + 2 ^ (64 - (x'.get 15#5).toNat) ≤
          2 ^ 129 * 2 ^ (64 - (x'.get 15#5).toNat) := by nlinarith
      have h2 : 2 ^ 129 * 2 ^ (64 - (x'.get 15#5).toNat) ≤ 2 ^ 129 * 2 ^ 63 :=
        Nat.mul_le_mul_left _ hQ63
      omega
    rw [huq] at hX
    refine topE_sub base T x m hpre hr _ _ ?_ ?_ ?_ ?_ hm U'
      ((x'.get 30#5).toNat + 2 ^ 64 * (x'.get 6#5).toNat + 2 ^ 128 * (x'.get 28#5).toNat)
      (2 ^ (64 - (x'.get 15#5).toNat)) hQ hQ64 ?_ ?_ ?_ ?_ hr0l ?_ ?_ ?_ hU'
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · exact h10
    · exact h1
    · exact h12
    · refine hcsx _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      all_goals try simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
      all_goals try (rw [Regs.eq_get x (by decide)]; first | exact hws0.eq | exact hws1.eq | exact hws2.eq | exact hws3.eq | exact hws4.eq)
      · rw [Regs.eq_get x (by decide)]; try bv_omega
      · intro i hi hx
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl <;> simp (config := { decide := true }) only [↓reduceIte] at hx ⊢
    · exact hT
    · exact hvl
    · rw [h4, huq, Nat.mod_eq_of_lt hX]
    · exact hr0div.symm
    · exact hq
    · intro h; exact hclamp (by omega)
    · exact hqe

/-- The run of `udivrem_top2<3, true>()` of `uint320` from 104, after the selection of
`u' = u - qe v 2^128`: the top words of `u' / Q` in `t2:t4:t3:a6`, the quotient bit as `1 - a1`,
and s0 to s4 in the frame of 48 bytes. -/
theorem topE_mid (hi : BitVec 20) (lo : BitVec 12) (base T : BitVec 64) (x : Regs) (m : Mem)
    (hT : pcAt base 107 + ((hi ++ 0x000#12).signExtend 64 + lo.signExtend 64) = T)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64) (hr : x.get 1#5 &&& 3 = 0)
    (hpre : udivrem_top2_3_equal_320.pre x m) (x' : Regs) (m' : Mem)
    (hhold : HoldsData m' T reciprocal_2by1_image_data)
    (h10 : x'.get 10#5 = x.get 10#5) (h1 : x'.get 1#5 = x.get 1#5)
    (h12 : x'.get 12#5 = x.get 12#5) (h2 : x'.get 2#5 = x.get 2#5 + 18446744073709551568#64)
    (hcs : ∀ i ∈ calleeSaved, i ∉ [2#5, 8#5, 9#5, 18#5, 19#5, 20#5] → x' i = x i)
    (hf : memWord m' (x.get 2#5 + 18446744073709551608#64).toNat = x.get 8#5 ∧
      memWord m' (x.get 2#5 + 18446744073709551600#64).toNat = x.get 9#5 ∧
      memWord m' (x.get 2#5 + 18446744073709551592#64).toNat = x.get 18#5 ∧
      memWord m' (x.get 2#5 + 18446744073709551584#64).toNat = x.get 19#5 ∧
      memWord m' (x.get 2#5 + 18446744073709551576#64).toNat = x.get 20#5)
    (hm : UnchangedExcept2 m m' (x.get 10#5) 72 (x.get 2#5 - 48#64) 48)
    (hS : (x'.get 15#5).toNat < 64) (h14 : x'.get 14#5 = x'.get 15#5 ^^^ 18446744073709551615#64)
    (hv0 : x'.get 13#5 = memWord m (x.get 12#5).toNat)
    (hu0 : x'.get 17#5 = memWord m (x.get 11#5).toNat)
    (hDw : (x'.get 5#5).toNat + 2 ^ 64 * (x'.get 16#5).toNat =
      words m (x.get 12#5) 4 / 2 ^ (64 - (x'.get 15#5).toNat))
    (hd63 : 2 ^ 63 ≤ (x'.get 16#5).toNat) (U' : Nat)
    (hUQ : U' % 2 ^ (64 - (x'.get 15#5).toNat) =
      words m (x.get 11#5) 5 % 2 ^ (64 - (x'.get 15#5).toNat))
    (hTw : (x'.get 6#5).toNat + 2 ^ 64 * ((x'.get 28#5).toNat + 2 ^ 64 * ((x'.get 29#5).toNat +
      2 ^ 64 * (x'.get 7#5).toNat)) = U' / 2 ^ (64 - (x'.get 15#5).toNat))
    (hqe : (x'.get 11#5 ^^^ 1#64).toNat * 2 ^ 128 * words m (x.get 12#5) 4 + U' =
      words m (x.get 11#5) 5)
    (hU' : U' < words m (x.get 12#5) 4 * 2 ^ 128) :
    Reach (bufWords (x.get 11#5) 5 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 9 ++
        bufWords (x.get 2#5 - 48#64) 6 ++ bufWords T 256) (udivrem_top2_3_equal_320_progAt hi lo)
      base (pcAt base 104) x' m' (x.get 1#5) (udivrem_top2_3_equal_320.post x m) := by
  have hpre' := hpre
  simp only [udivrem_top2_3_equal_320.pre, Buf] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr, hv1, hv2,
    hu3⟩ := hpre'
  have hQ : 0 < 2 ^ (64 - (x'.get 15#5).toNat) := by positivity
  -- The top 2 digits of u' / Q are at most the top digits of v.
  have hD := hDw.symm
  have hTD : U' / 2 ^ (64 - (x'.get 15#5).toNat) / 2 ^ 128 ≤
      (x'.get 5#5).toNat + 2 ^ 64 * (x'.get 16#5).toNat := by
    rw [hDw, Nat.div_div_eq_div_mul]
    calc U' / (2 ^ (64 - (x'.get 15#5).toNat) * 2 ^ 128)
        ≤ words m (x.get 12#5) 4 * 2 ^ 128 / (2 ^ (64 - (x'.get 15#5).toNat) * 2 ^ 128) :=
          Nat.div_le_div_right hU'.le
      _ = words m (x.get 12#5) 4 / 2 ^ (64 - (x'.get 15#5).toNat) :=
          Nat.mul_div_mul_right _ _ (by positivity)
  have hT2 : U' / 2 ^ (64 - (x'.get 15#5).toNat) / 2 ^ 128 =
      (x'.get 29#5).toNat + 2 ^ 64 * (x'.get 7#5).toNat := by
    rw [← hTw]
    have := (x'.get 6#5).isLt; have := (x'.get 28#5).isLt
    omega
  have hTlo : U' / 2 ^ (64 - (x'.get 15#5).toNat) % 2 ^ 128 =
      (x'.get 6#5).toNat + 2 ^ 64 * (x'.get 28#5).toNat := by
    rw [← hTw]
    have := (x'.get 6#5).isLt; have := (x'.get 28#5).isLt
    omega
  have hVpos : 0 < words m (x.get 12#5) 4 := by
    have : 0 < 2 ^ (64 * 2) := by positivity
    omega
  have hqU : U' / words m (x.get 12#5) 4 < 2 ^ 128 := Nat.div_lt_of_lt_mul hU'
  rv_exec_cut 106 301
  rotate_left
  · -- The top 2 digits are the top digits of v: the clamped estimate.
    rename_i hb2 hb3
    have hc : U' / 2 ^ (64 - (x'.get 15#5).toNat) / 2 ^ 128 =
        words m (x.get 12#5) 4 / 2 ^ (64 - (x'.get 15#5).toNat) := by
      rw [hT2, ← hDw, hb2, hb3]
    have hcl := topE_clamp hc
    refine Reach.trans (topE_clamp_run base x' m') ?_
    intro x3 m3 ⟨hm3, h37, h329, h328, hr03, h03, hfr3⟩
    subst hm3
    have g : ∀ r, r ∉ [5#5, 6#5, 7#5, 16#5, 28#5, 29#5, 30#5] → r ≠ 0 → x3.get r = x'.get r := by
      intro r hr hr0
      rw [← Regs.eq_get x3 hr0, ← Regs.eq_get x' hr0]; exact hfr3 r hr
    have e1 := g 1#5 (by decide) (by decide)
    have e2 := g 2#5 (by decide) (by decide)
    have e10 := g 10#5 (by decide) (by decide)
    have e11 := g 11#5 (by decide) (by decide)
    have e12 := g 12#5 (by decide) (by decide)
    have e13 := g 13#5 (by decide) (by decide)
    have e14 := g 14#5 (by decide) (by decide)
    have e15 := g 15#5 (by decide) (by decide)
    have e17 := g 17#5 (by decide) (by decide)
    have hq3 : (x3.get 29#5).toNat + 2 ^ 64 * (x3.get 7#5).toNat = 2 ^ 128 - 1 := by
      rw [h37, h329]; rfl
    refine topE_shift base T x m hpre hr x3 _ (by rw [e10]; exact h10) (by rw [e1]; exact h1)
      (by rw [e12]; exact h12) (by rw [e2]; exact h2) ?_ hf hm (by rw [e15]; exact hS)
      (by rw [e14, e15]; exact h14) (by rw [e13]; exact hv0) (by rw [e17]; exact hu0) U'
      (by rw [e15]; exact hUQ) ?_ h328 (by rw [hq3]; omega) (fun _ => hq3) (by rw [e11]; exact hqe) hU'
    · intro i hi hx
      rw [hfr3 i (by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl <;> decide)]
      exact hcs i hi hx
    · rw [e15, hq3, hr03, ← hTlo, hDw]
      exact hcl
  -- The top 2 digits are less than the top digits of v: the reciprocal and the two divisions.
  all_goals
    have hlt : (x'.get 7#5).toNat * 2 ^ 64 + (x'.get 29#5).toNat <
        (x'.get 5#5).toNat + 2 ^ 64 * (x'.get 16#5).toNat := by
      have hne : (x'.get 29#5).toNat + 2 ^ 64 * (x'.get 7#5).toNat ≠
          (x'.get 5#5).toNat + 2 ^ 64 * (x'.get 16#5).toNat := by
        intro h
        have := (x'.get 29#5).isLt; have := (x'.get 5#5).isLt
        have e29 : x'.get 29#5 = x'.get 5#5 := BitVec.eq_of_toNat_eq (by omega)
        have e7 : x'.get 7#5 = x'.get 16#5 := BitVec.eq_of_toNat_eq (by omega)
        first | exact ‹¬x'.get 29#5 = x'.get 5#5› e29 | exact ‹¬x'.get 7#5 = x'.get 16#5› e7
      rw [hT2] at hTD
      omega
    rv_exec_cut 162
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
    rw [memHalf_lo, holdsData_get hhold
        (by rw [show reciprocal_2by1_image_data.length = 256 from rfl]; exact hix),
      ← List.getD_eq_getElem _ 0, image_data_get _ hix] at hwL
    rv_exec_cut 162
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
    rw [table_entry_add4 T hd63 hw, memHalf_hi, holdsData_get hhold
        (by rw [show reciprocal_2by1_image_data.length = 256 from rfl]; exact hix),
      ← List.getD_eq_getElem _ 0, image_data_get _ hix] at hwH
    rv_exec_cut 162
    -- The reciprocal of vt.
    rv_cse
    obtain ⟨hL, hH⟩ := table_LH hd63 hwL hwH
    have hv := recip3BV_spec (x'.get 5#5) (x'.get 16#5) wL wH hd63 hL hH
    simp only [recip3BV] at hv
    rw [show (0 : BitVec 64) = 0#64 from rfl] at hv
    rv_fold hv
    rv_fold hv
    -- The first division of the top digits t3:t2:t1.
    refine Reach.trans (topE_div_top base _ _ ?_ ?_ ?_) ?_
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      omega
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      exact hlt
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      exact hv
    intro x2 m2 ⟨hm2, h31, hq1, hr1, h02, hfr2⟩
    subst hm2
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte] at hq1 hr1
    have h31' : x2 31#5 = 0#64 := by rw [Regs.eq_get x2 (by decide)]; exact h31
    rw [regs_eq_sets _ x2 _ h02 hfr2]
    simp only [setRegs]
    rw [← Regs.eq_get x2 (by decide : (7#5 : BitVec 5) ≠ 0)] at hq1
    rw [← Regs.eq_get x2 (by decide : (28#5 : BitVec 5) ≠ 0),
      ← Regs.eq_get x2 (by decide : (29#5 : BitVec 5) ≠ 0)] at hr1
    have hD1 : 2 ^ 127 ≤ (x'.get 5#5).toNat + 2 ^ 64 * (x'.get 16#5).toNat := by omega
    have hX : (x2 29#5).toNat * 2 ^ 64 + (x2 28#5).toNat <
        (x'.get 5#5).toNat + 2 ^ 64 * (x'.get 16#5).toNat := by
      have := Nat.mod_lt ((x'.get 7#5).toNat * 2 ^ 128 + (x'.get 29#5).toNat * 2 ^ 64 +
        (x'.get 28#5).toNat) (Nat.lt_of_lt_of_le (Nat.two_pow_pos 127) hD1)
      calc (x2 29#5).toNat * 2 ^ 64 + (x2 28#5).toNat = (x2 28#5).toNat + 2 ^ 64 * (x2 29#5).toNat := by
            ring
        _ = _ := hr1
        _ < _ := this
    -- The second division of r1:t0 by vt.
    refine Reach.trans (topE_div_low base _ _ ?_ ?_ ?_ ?_) ?_
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · exact hD1
    · exact hX
    · exact hv
    · exact h31'
    intro x3 m3 ⟨hm3, h28, hq0, hr0, h03, hfr3⟩
    subst hm3
    try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte] at hq0 hr0
    rw [← Regs.eq_get x3 (by decide : (29#5 : BitVec 5) ≠ 0)] at hq0
    rw [← Regs.eq_get x3 (by decide : (30#5 : BitVec 5) ≠ 0),
      ← Regs.eq_get x3 (by decide : (6#5 : BitVec 5) ≠ 0)] at hr0
    have h28' : x3 28#5 = 0#64 := by rw [Regs.eq_get x3 (by decide)]; exact h28
    rw [regs_eq_sets _ x3 _ h03 hfr3]
    simp only [setRegs]
    have hdig := top2_digits hTw hq1 hr1 hq0 hr0
    rw [hDw] at hdig
    have hr0D : (x3 30#5).toNat + 2 ^ 64 * (x3 6#5).toNat <
        words m (x.get 12#5) 4 / 2 ^ (64 - (x'.get 15#5).toNat) := by
      rw [hr0, ← hDw]; exact Nat.mod_lt _ (Nat.lt_of_lt_of_le (Nat.two_pow_pos 127) hD1)
    refine topE_shift base T x m hpre hr _ _ ?_ ?_ ?_ ?_ ?_ hf hm ?_ ?_ ?_ ?_ U' ?_ ?_ ?_ ?_ ?_ ?_ hU'
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · exact h10
    · exact h1
    · exact h12
    · exact h2
    · intro i hi hx
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl
      all_goals simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at hx ⊢
      all_goals first
        | (rw [Regs.eq_get x' (by decide)]
           exact (Regs.eq_get x' (by decide)).symm.trans (hcs _ (by decide) (by decide)))
        | exact hcs _ (by decide) (by decide)
    · exact hS
    · exact h14
    · exact hv0
    · exact hu0
    · exact hUQ
    · rw [h28', BitVec.toNat_ofNat, Nat.zero_mod, Nat.mul_zero, Nat.add_zero]
      exact hdig
    · rw [h28']; decide
    · refine top2_est (Nat.lt_of_lt_of_le (Nat.two_pow_pos 127) (by rw [← hDw]; exact hD1)) ?_ hr0D
      exact hdig
    · rw [h28']; intro h; exact absurd h (by decide)
    · exact hqe

/-- The normalized v of 3 words: the low word `v[0] << s` and the top words `v / 2^(64 - s)`. -/
theorem topE_vs (V s : Nat) (hs : s < 64) :
    V * 2 ^ s % 2 ^ 64 + 2 ^ 64 * (V / 2 ^ (64 - s)) = V * 2 ^ s := by
  have hPQ : 2 ^ (64 - s) * 2 ^ s = 2 ^ 64 := by rw [← pow_add]; congr 1; omega
  have : V / 2 ^ (64 - s) = V * 2 ^ s / 2 ^ 64 := by
    rw [← hPQ, Nat.mul_div_mul_right _ _ (by positivity)]
  rw [this, Nat.mod_add_div]

/-- The selection of `u' = u - qe v 2^128` from the borrow `b` of the top 3 words of the
normalized u minus the normalized v. -/
theorem topE_sel_nat {u V s t0 Tt D Vs b : Nat} (hs : s < 64)
    (hT : t0 + 2 ^ 64 * Tt = u / 2 ^ (64 - s)) (ht0 : t0 < 2 ^ 64) (hVs : Vs = V * 2 ^ s)
    (hsub : D + Vs = Tt + 2 ^ 192 * b) (hD : D < 2 ^ 192) (hb : b ≤ 1)
    (hU2 : u < 2 * (V * 2 ^ 128)) :
    (b = 1 → u < V * 2 ^ 128) ∧
    (b = 0 → V * 2 ^ 128 ≤ u ∧ (u - V * 2 ^ 128) / 2 ^ (64 - s) = t0 + 2 ^ 64 * D ∧
      (u - V * 2 ^ 128) % 2 ^ (64 - s) = u % 2 ^ (64 - s) ∧ u - V * 2 ^ 128 < V * 2 ^ 128) := by
  have hPQ : 2 ^ s * 2 ^ (64 - s) = 2 ^ 64 := by rw [← pow_add]; congr 1; omega
  have hQ : 0 < 2 ^ (64 - s) := by positivity
  have hV128 : V * 2 ^ 128 = 2 ^ (64 - s) * (2 ^ 64 * Vs) := by
    rw [hVs, show (2 : Nat) ^ 128 = 2 ^ 64 * (2 ^ s * 2 ^ (64 - s)) by rw [hPQ]; norm_num]; ring
  have hdm := Nat.div_add_mod u (2 ^ (64 - s))
  rw [← hT] at hdm
  have hmQ := Nat.mod_lt u hQ
  constructor
  · intro hb1
    subst hb1
    have h1 : t0 + 2 ^ 64 * Tt + 1 ≤ 2 ^ 64 * Vs := by omega
    have h2 := Nat.mul_le_mul_left (2 ^ (64 - s)) h1
    rw [hV128]
    rw [Nat.mul_add, Nat.mul_one] at h2
    omega
  · intro hb0
    subst hb0
    have hTt : Tt = D + Vs := by omega
    have e : 2 ^ (64 - s) * (t0 + 2 ^ 64 * Tt) =
        2 ^ (64 - s) * (t0 + 2 ^ 64 * D) + 2 ^ (64 - s) * (2 ^ 64 * Vs) := by
      rw [hTt]; ring
    have hle : 2 ^ (64 - s) * (2 ^ 64 * Vs) ≤ u := by omega
    have hsplit : u - V * 2 ^ 128 = 2 ^ (64 - s) * (t0 + 2 ^ 64 * D) + u % 2 ^ (64 - s) := by
      rw [hV128]; omega
    refine ⟨by rw [hV128]; exact hle, ?_, ?_, ?_⟩
    · rw [hsplit, Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_right _ _ hQ, Nat.div_eq_of_lt hmQ,
        Nat.zero_add]
    · rw [hsplit, Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_right, Nat.mod_mod]
    · rw [← hV128] at hle; omega

/-- The run of `udivrem_top2<3, true>()` of `uint320` from 87, after the frame stores: the
selection of `u' = u - qe v 2^128` by the borrow of the top 3 words of the normalized u minus the
normalized v. -/
theorem topE_sel (hi : BitVec 20) (lo : BitVec 12) (base T : BitVec 64) (x : Regs) (m : Mem)
    (hT : pcAt base 107 + ((hi ++ 0x000#12).signExtend 64 + lo.signExtend 64) = T)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64) (hr : x.get 1#5 &&& 3 = 0)
    (hpre : udivrem_top2_3_equal_320.pre x m) (x' : Regs) (m' : Mem)
    (hhold : HoldsData m' T reciprocal_2by1_image_data)
    (h10 : x'.get 10#5 = x.get 10#5) (h1 : x'.get 1#5 = x.get 1#5)
    (h12 : x'.get 12#5 = x.get 12#5) (h2 : x'.get 2#5 = x.get 2#5 + 18446744073709551568#64)
    (hcs : ∀ i ∈ calleeSaved, i ∉ [2#5, 8#5, 9#5, 18#5, 19#5, 20#5] → x' i = x i)
    (hf : memWord m' (x.get 2#5 + 18446744073709551608#64).toNat = x.get 8#5 ∧
      memWord m' (x.get 2#5 + 18446744073709551600#64).toNat = x.get 9#5 ∧
      memWord m' (x.get 2#5 + 18446744073709551592#64).toNat = x.get 18#5 ∧
      memWord m' (x.get 2#5 + 18446744073709551584#64).toNat = x.get 19#5 ∧
      memWord m' (x.get 2#5 + 18446744073709551576#64).toNat = x.get 20#5)
    (hm : UnchangedExcept2 m m' (x.get 10#5) 72 (x.get 2#5 - 48#64) 48)
    (hS : (x'.get 15#5).toNat < 64) (h14 : x'.get 14#5 = x'.get 15#5 ^^^ 18446744073709551615#64)
    (hv0 : x'.get 13#5 = memWord m (x.get 12#5).toNat)
    (hu0 : x'.get 17#5 = memWord m (x.get 11#5).toNat)
    (hDw : (x'.get 5#5).toNat + 2 ^ 64 * (x'.get 16#5).toNat =
      words m (x.get 12#5) 4 / 2 ^ (64 - (x'.get 15#5).toNat))
    (hd63 : 2 ^ 63 ≤ (x'.get 16#5).toNat)
    (hTw : (x'.get 6#5).toNat + 2 ^ 64 * ((x'.get 28#5).toNat + 2 ^ 64 * ((x'.get 29#5).toNat +
      2 ^ 64 * (x'.get 7#5).toNat)) = words m (x.get 11#5) 5 / 2 ^ (64 - (x'.get 15#5).toNat)) :
    Reach (bufWords (x.get 11#5) 5 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 9 ++
        bufWords (x.get 2#5 - 48#64) 6 ++ bufWords T 256) (udivrem_top2_3_equal_320_progAt hi lo)
      base (pcAt base 87) x' m' (x.get 1#5) (udivrem_top2_3_equal_320.post x m) := by
  have hpre' := hpre
  simp only [udivrem_top2_3_equal_320.pre, Buf] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨-, -, -, -, -, -, -, -, -, hv1, hv2, hu3⟩ := hpre'
  have hU2 := topE_bound (by simpa using hv1) (by simpa using hu3)
  rv_exec_cut 104
  all_goals
    rename_i c12 hc12 c11 hc11 c10 hc10 c9 hc9 c8 hc8 c7 hc7 c6 hc6 c5 hc5 c4 hc4 c3 hc3 c2 hc2
      c1 hc1 c0 hc0 hb
    have hS' : (x'.get 15#5).toNat % 64 = (x'.get 15#5).toNat := Nat.mod_eq_of_lt hS
    have hvl : c12.toNat = words m (x.get 12#5) 4 * 2 ^ (x'.get 15#5).toNat % 2 ^ 64 := by
      rw [hc12.eq, BitVec.toNat_shiftLeft, hS', Nat.shiftLeft_eq, hv0,
        words_mul_mod _ _ _ _ (by norm_num)]
    have hVs := topE_vs (words m (x.get 12#5) 4) _ hS
    rw [← hDw, ← hvl] at hVs
    have e0 := defn_sub_borrow0 hc9 hc7
    obtain ⟨e1, l1⟩ := defn_sub_borrow hc11 hc8 hc6 hc5 hc4 (defn_bit_le hc7)
    obtain ⟨e2, l2⟩ := defn_sub_borrow hc10 hc3 hc2 hc1 hc0 l1
    have hsub : c9.toNat + 2 ^ 64 * (c6.toNat + 2 ^ 64 * c2.toNat) +
        (c12.toNat + 2 ^ 64 * ((x'.get 5#5).toNat + 2 ^ 64 * (x'.get 16#5).toNat)) =
        (x'.get 28#5).toNat + 2 ^ 64 * ((x'.get 29#5).toNat + 2 ^ 64 * (x'.get 7#5).toNat) +
        2 ^ 192 * c0.toNat := by
      clear hTw hDw hVs hU2 hvl hS'
      omega
    have hsel := topE_sel_nat (u := words m (x.get 11#5) 5) (V := words m (x.get 12#5) 4)
      hS hTw (x'.get 6#5).isLt hVs hsub
      (by have := c9.isLt; have := c6.isLt; have := c2.isLt; omega) l2 hU2
    have hcs' := hcs
  · -- u < v 2^128: u' = u, qe = 0.
    have hc01 : c0.toNat = 1 := by
      have : c0.toNat ≠ 0 := fun h => hb (BitVec.eq_of_toNat_eq (by simpa using h))
      omega
    have hc0' : c0 = 1#64 := BitVec.eq_of_toNat_eq (by simpa using hc01)
    refine topE_mid hi lo base T x m hT hw hr hpre _ m' hhold ?_ ?_ ?_ ?_ ?_ hf hm ?_ ?_ ?_ ?_ ?_ ?_
      (words m (x.get 11#5) 5) rfl ?_ ?_ (hsel.1 hc01)
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · exact h10
    · exact h1
    · exact h12
    · exact h2
    · intro i hi hx
      have := hcs i hi hx
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at hx this ⊢ <;>
        exact this
    · exact hS
    · exact h14
    · exact hv0
    · exact hu0
    · exact hDw
    · exact hd63
    · exact hTw
    · rw [hc0']; simp
  · -- u ≥ v 2^128: u' = u - v 2^128, qe = 1.
    have hc00 : c0.toNat = 0 := by rw [hb]; rfl
    obtain ⟨hle, hdiv, hmod, hlt⟩ := hsel.2 hc00
    refine topE_mid hi lo base T x m hT hw hr hpre _ m' hhold ?_ ?_ ?_ ?_ ?_ hf hm ?_ ?_ ?_ ?_ ?_ ?_
      (words m (x.get 11#5) 5 - words m (x.get 12#5) 4 * 2 ^ 128) hmod ?_ ?_ hlt
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · exact h10
    · exact h1
    · exact h12
    · exact h2
    · intro i hi hx
      have := hcs i hi hx
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at hx this ⊢ <;>
        exact this
    · exact hS
    · exact h14
    · exact hv0
    · exact hu0
    · exact hDw
    · exact hd63
    · rw [hdiv]
    · rw [hb]; simp only [BitVec.zero_xor, BitVec.toNat_ofNat]; norm_num; omega

/-- The stores to the frame of 48 bytes below sp keep the table of the reciprocal. -/
theorem holdsData_frame48 (m : Mem) (sp T a b c d e : BitVec 64)
    (hs : (sp - 48#64).toNat + 48 ≤ 2 ^ 64) (hT : T.toNat + 8 * 256 ≤ 2 ^ 64)
    (hstk : (sp - 48#64).toNat + 48 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (sp - 48#64).toNat)
    (h : HoldsData m T reciprocal_2by1_image_data) :
    HoldsData (memStore (memStore (memStore (memStore (memStore m
      (sp + 18446744073709551608#64).toNat a) (sp + 18446744073709551600#64).toNat b)
      (sp + 18446744073709551592#64).toNat c) (sp + 18446744073709551584#64).toNat d)
      (sp + 18446744073709551576#64).toNat e) T reciprocal_2by1_image_data := by
  have hl : reciprocal_2by1_image_data.length = 256 := rfl
  simp (disch := first | (rw [hl]; exact hT) | (rw [hl]; bv_omega)) only [holdsData_memStore_iff]
  exact h

/-- The 5 words that `udivrem_top2<3, true>()` saves in its frame of 48 bytes below sp, and the
memory after the stores changed only in the frame. -/
theorem frame48 (m : Mem) (sp a b c d e : BitVec 64) (hs : (sp - 48#64).toNat + 48 ≤ 2 ^ 64) :
    let M := memStore (memStore (memStore (memStore (memStore m (sp + 18446744073709551608#64).toNat a)
      (sp + 18446744073709551600#64).toNat b) (sp + 18446744073709551592#64).toNat c)
      (sp + 18446744073709551584#64).toNat d) (sp + 18446744073709551576#64).toNat e
    (memWord M (sp + 18446744073709551608#64).toNat = a ∧
      memWord M (sp + 18446744073709551600#64).toNat = b ∧
      memWord M (sp + 18446744073709551592#64).toNat = c ∧
      memWord M (sp + 18446744073709551584#64).toNat = d ∧
      memWord M (sp + 18446744073709551576#64).toNat = e) ∧
    ∀ r lr, UnchangedExcept2 m M r lr (sp - 48#64) 48 := by
  intro M
  refine ⟨?_, fun r lr => ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp (disch := first | bv_omega | fail) only [M, memWord_memStore_self, memWord_memStore_of_ne]
  · simp only [M]
    simp (disch := first | (right; constructor <;> bv_omega) | fail) only [unchangedExcept2_memStore]
    exact unchangedExcept2_refl _ _ _ _ _

/-- The run of `udivrem_top2<3, true>()` of `uint320` from 81, where the paths of the
normalization meet: the normalized top words of v in `a6:a5` (vt), of u in `t2:t4:t3:a6`
(t3:t2:t1:t0), v[0] in a3, u[0] in a7, the shift in a5 and its complement in a4. -/
theorem topE_main (hi : BitVec 20) (lo : BitVec 12) (base T : BitVec 64) (x : Regs)
    (m : Mem) (hT : pcAt base 107 + ((hi ++ 0x000#12).signExtend 64 + lo.signExtend 64) = T)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64) (hr : x.get 1#5 &&& 3 = 0)
    (hstk : (x.get 2#5 - 48#64).toNat + 48 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 2#5 - 48#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hpre : udivrem_top2_3_equal_320.pre x m)
    (x' : Regs) (h0 : x' 0#5 = x 0#5)
    (hfr : ∀ r, r ∉ [5#5, 6#5, 7#5, 11#5, 13#5, 14#5, 15#5, 16#5, 17#5, 28#5, 29#5, 30#5, 31#5] →
      x' r = x r)
    (hS : (x' 15#5).toNat < 64) (h14 : x' 14#5 = x' 15#5 ^^^ 18446744073709551615#64)
    (hv0 : x' 13#5 = memWord m (x.get 12#5).toNat) (hu0 : x' 17#5 = memWord m (x.get 11#5).toNat)
    (hDw : (x' 5#5).toNat + 2 ^ 64 * (x' 16#5).toNat =
      words m (x.get 12#5) 4 / 2 ^ (64 - (x' 15#5).toNat))
    (hd63 : 2 ^ 63 ≤ (x' 16#5).toNat)
    (hTw : (x' 6#5).toNat + 2 ^ 64 * ((x' 28#5).toNat + 2 ^ 64 * ((x' 29#5).toNat +
      2 ^ 64 * (x' 7#5).toNat)) = words m (x.get 11#5) 5 / 2 ^ (64 - (x' 15#5).toNat)) :
    Reach (bufWords (x.get 11#5) 5 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 9 ++
        bufWords (x.get 2#5 - 48#64) 6 ++ bufWords T 256) (udivrem_top2_3_equal_320_progAt hi lo)
      base (pcAt base 81) x' m (x.get 1#5) (udivrem_top2_3_equal_320.post x m) := by
  rw [regs_eq_sets x x' _ h0 hfr]
  simp only [setRegs]
  have hpre0 := hpre
  simp only [udivrem_top2_3_equal_320.pre, Buf] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr, hv1, hv2,
    hu3⟩ := hpre
  rv_exec_cut 87
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.reduceSignExtend,
    BitVec.add_assoc, BitVec.reduceAdd]
  obtain ⟨hf, hm⟩ := frame48 m (x.get 2#5) (x.get 8#5) (x.get 9#5) (x.get 18#5) (x.get 19#5)
    (x.get 20#5) hsn
  refine topE_sel hi lo base T x m hT hw hr hpre0 _ _
    (holdsData_frame48 m _ T _ _ _ _ _ hsn hw hstk hhold)
    ?_ ?_ ?_ ?_ ?_ hf (hm _ _) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  all_goals try simp (disch := decide) only [Regs.eq_get x'] at hS h14 hv0 hu0 hDw hd63 hTw ⊢
  · intro i hi hx
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at hx ⊢
  · exact hS
  · exact h14
  · exact hv0
  · exact hu0
  · exact hDw
  · exact hd63
  · exact hTw

/-- The frame of 48 bytes below sp of `udivrem_top2<3, true>()` is outside the code and the data of
the image: its words are outside them. -/
theorem frame48_outside (sp base : BitVec 64) (o1 o2 : Nat)
    (h0 : (sp - 48#64).toNat + 8 ≤ base.toNat ∨ base.toNat + o1 + o2 ≤ (sp - 48#64).toNat)
    (h5 : (sp - 48#64 + BitVec.ofNat 64 (8 * 5)).toNat + 8 ≤ base.toNat ∨
      base.toNat + o1 + o2 ≤ (sp - 48#64 + BitVec.ofNat 64 (8 * 5)).toNat)
    (hs : (sp - 48#64).toNat + 48 ≤ 2 ^ 64) (hoff : 48 ≤ o1 + o2) :
    (sp - 48#64).toNat + 48 ≤ base.toNat ∨ base.toNat + o1 + o2 ≤ (sp - 48#64).toNat := by
  have : (sp - 48#64 + BitVec.ofNat 64 (8 * 5)).toNat = (sp - 48#64).toNat + 40 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  omega

end IntxRV.Api
