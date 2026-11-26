import IntxRV.AddMod

/-!
# The fast path and the dispatch of `addmod()`

For a modulus of at least 2^192 and the top words of x and y at most its top word, x and y are less
than twice the modulus: `addmod()` subtracts the modulus from x (`am_x`, from 68) and from y
(`am_y`, from 89) unless it borrows, adds the two remainders and subtracts the modulus from the sum
unless the sum does not carry and the subtraction borrows (`am_sum`, from 113). The dispatch from 6
(`am_main`) takes this path or the path of `udivrem<320, 256>()` (`am_slow`,
`IntxRV/AddMod.lean`). See `IntxRV/Api/addmod_256.lean`.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option hygiene false in
-- The image of `addmod()` with its segments nested to the right: the fetch of an instruction of
-- `addmod()` reduces only the first segments.
local notation "PA" => addmod_256_image_prog_0 ++ (addmod_256_image_prog_1 ++ (addmod_256_image_prog_2 ++
  (addmod_256_image_prog_3 ++ (addmod_256_image_prog_4 ++ (addmod_256_image_prog_5 ++
  (addmod_256_image_prog_6 ++ (addmod_256_image_prog_7 ++ (addmod_256_image_prog_8 ++
  (addmod_256_image_prog_9 ++ (addmod_256_image_prog_10 ++ (addmod_256_image_prog_11 ++
  (addmod_256_image_prog_12 ++ (addmod_256_image_prog_13 ++ (addmod_256_image_prog_14 ++
  (addmod_256_image_prog_15 ++ (addmod_256_image_prog_16 ++ (addmod_256_image_prog_17 ++
  (addmod_256_image_prog_18 ++ (addmod_256_image_prog_19 ++ (addmod_256_image_prog_20 ++
  (addmod_256_image_prog_21 ++ (addmod_256_image_prog_22 ++ (addmod_256_image_prog_23 ++
  (addmod_256_image_prog_24 ++ (addmod_256_image_prog_25 ++ (addmod_256_image_prog_26 ++
  (addmod_256_image_prog_27 ++ (addmod_256_image_prog_28 ++ (addmod_256_image_prog_29 ++
  (addmod_256_image_prog_30 ++ (addmod_256_image_prog_31 ++ (addmod_256_image_prog_32 ++
  (addmod_256_image_prog_33 ++ (addmod_256_image_prog_34 ++ (addmod_256_image_prog_35 ++
  (addmod_256_image_prog_36 ++ (addmod_256_image_prog_37 ++ (addmod_256_image_prog_38 ++
  (addmod_256_image_prog_39 ++ (addmod_256_image_prog_40 ++ (addmod_256_image_prog_41 ++
  (addmod_256_image_prog_42 ++ (addmod_256_image_prog_43 ++ (addmod_256_image_prog_44 ++
  (addmod_256_image_prog_45 ++ (addmod_256_image_prog_46 ++ (addmod_256_image_prog_47 ++
  (addmod_256_image_prog_48 ++
  (addmod_256_image_prog_49)))))))))))))))))))))))))))))))))))))))))))))))))

set_option hygiene false in
/-- The callee-saved registers that the frame keeps, through the sets of the other registers. -/
local macro "am_cs" : tactic => `(tactic| (
  intro r hr' hn
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte] at hn ⊢))

/-- The subtraction of 4 words in `addmod()`: the words `b` of `n - m` and the borrow out of them
as a condition. -/
theorem am_sub4c_words {n0 n1 n2 n3 m0 m1 m2 m3 b0 bb0 c1 bb1a b1 bb1b bb1 c2 bb2a b2 bb2b bb2 c3
      b3 : BitVec 64}
    (hb0 : Defn b0 (n0 - m0)) (hbb0 : Defn bb0 (if n0 < b0 then 1#64 else 0#64))
    (hc1 : Defn c1 (n1 - m1)) (hbb1a : Defn bb1a (if n1 < c1 then 1#64 else 0#64))
    (hb1 : Defn b1 (c1 - bb0)) (hbb1b : Defn bb1b (if c1 < b1 then 1#64 else 0#64))
    (hbb1 : Defn bb1 (bb1a ||| bb1b))
    (hc2 : Defn c2 (n2 - m2)) (hbb2a : Defn bb2a (if n2 < c2 then 1#64 else 0#64))
    (hb2 : Defn b2 (c2 - bb1)) (hbb2b : Defn bb2b (if c2 < b2 then 1#64 else 0#64))
    (hbb2 : Defn bb2 (bb2a ||| bb2b)) (hc3 : Defn c3 (n3 - m3)) (hb3 : Defn b3 (c3 - bb2)) :
    b0.toNat + 2 ^ 64 * (b1.toNat + 2 ^ 64 * (b2.toNat + 2 ^ 64 * b3.toNat)) +
        (m0.toNat + 2 ^ 64 * (m1.toNat + 2 ^ 64 * (m2.toNat + 2 ^ 64 * m3.toNat))) =
      n0.toNat + 2 ^ 64 * (n1.toNat + 2 ^ 64 * (n2.toNat + 2 ^ 64 * n3.toNat)) +
        2 ^ 256 * (if n3 < c3 ∨ c3 < b3 then 1 else 0) := by
  have e0 := defn_sub_borrow0 hb0 hbb0
  obtain ⟨e1, l1⟩ := defn_sub_borrow hc1 hbb1a hb1 hbb1b hbb1 (defn_bit_le hbb0)
  obtain ⟨e2, l2⟩ := defn_sub_borrow hc2 hbb2a hb2 hbb2b hbb2 l1
  have e3 := defn_sub_borrow_cond hc3 hb3 l2
  generalize (if n3 < c3 ∨ c3 < b3 then 1 else 0) = br at *
  omega

/-- The sum of two remainders less the modulus when it carries out or does not borrow. -/
theorem am_res_b {xn yn M a b c br : Nat} (hxn : xn < M) (hyn : yn < M) (hM : M < 2 ^ 256)
    (ha : a + 2 ^ 256 * c = xn + yn) (hb : b + M = a + 2 ^ 256 * br) (hc : c ≤ 1)
    (hbr : br ≤ 1) (ha256 : a < 2 ^ 256) (hb256 : b < 2 ^ 256) (hcb : c = 1 ∨ br = 0) :
    b = (xn + yn) % M := by
  have h := am_sum_nat hxn hyn hM ha hb hc hbr ha256 hb256
  rwa [if_pos hcb] at h

/-- The sum of two remainders when it does not carry out and borrows. -/
theorem am_res_a {xn yn M a b c br : Nat} (hxn : xn < M) (hyn : yn < M) (hM : M < 2 ^ 256)
    (ha : a + 2 ^ 256 * c = xn + yn) (hb : b + M = a + 2 ^ 256 * br) (hc : c ≤ 1)
    (hbr : br ≤ 1) (ha256 : a < 2 ^ 256) (hb256 : b < 2 ^ 256) (hc0 : c = 0) (hbr1 : br = 1) :
    a = (xn + yn) % M := by
  have h := am_sum_nat hxn hyn hM ha hb hc hbr ha256 hb256
  rwa [if_neg (by omega)] at h

theorem am_ite_le {p : Prop} [Decidable p] : (if p then 1 else 0) ≤ 1 := by
  split <;> omega

theorem am_nat4_lt (a0 a1 a2 a3 : BitVec 64) :
    a0.toNat + 2 ^ 64 * (a1.toNat + 2 ^ 64 * (a2.toNat + 2 ^ 64 * a3.toNat)) < 2 ^ 256 := by
  have := a0.isLt; have := a1.isLt; have := a2.isLt; have := a3.isLt; omega

theorem am_bit_ne {p : Prop} [Decidable p] (h : ¬(if p then 1#64 else 0#64) = 0#64) : p := by
  by_contra hp; rw [if_neg hp] at h; exact h rfl

theorem am_bit_eq {p : Prop} [Decidable p] (h : (if p then 1#64 else 0#64) = 0#64) : ¬p := by
  intro hp; rw [if_pos hp] at h; exact absurd h (by decide)

theorem am_or_eq {p q : Prop} [Decidable p] [Decidable q]
    (h : ((if p then 1#64 else 0#64) ||| (if q then 1#64 else 0#64)) = 0#64) : ¬(p ∨ q) := by
  rintro (hp | hq)
  · rw [if_pos hp] at h; split at h <;> exact absurd h (by decide)
  · rw [if_pos hq] at h; split at h <;> exact absurd h (by decide)

theorem am_or_ne {p q : Prop} [Decidable p] [Decidable q]
    (h : ¬((if p then 1#64 else 0#64) ||| (if q then 1#64 else 0#64)) = 0#64) : p ∨ q := by
  by_contra hpq; rw [not_or] at hpq; rw [if_neg hpq.1, if_neg hpq.2] at h; exact h rfl

theorem am_bit_eq' {p : Prop} [Decidable p] (h : 0#64 = if p then 1#64 else 0#64) : ¬p :=
  am_bit_eq h.symm

theorem am_or_eq' {p q : Prop} [Decidable p] [Decidable q]
    (h : 0#64 = ((if p then 1#64 else 0#64) ||| (if q then 1#64 else 0#64))) : ¬(p ∨ q) :=
  am_or_eq h.symm

/-- The end of the path of `addmod()` for a modulus of at least 2^192 from 113: the sum of the two
remainders and its one subtraction of the modulus, and the store of the result. -/
theorem am_sum {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hr : x.get 1#5 &&& 3 = 0) (hpre : addmod_256.pre x m) (x' : Regs) (m' : Mem)
    (hF : AMFrame x m x' m') (h8 : x'.get 8#5 = x.get 10#5)
    (hm0 : x'.get 5#5 = memWord m (x.get 13#5).toNat)
    (hm1 : x'.get 17#5 = memWord m (x.get 13#5 + 8#64).toNat)
    (hm2 : x'.get 10#5 = memWord m (x.get 13#5 + 16#64).toNat)
    (hm3 : x'.get 15#5 = memWord m (x.get 13#5 + 24#64).toNat) (xn yn : Nat)
    (hxn : (x'.get 6#5).toNat + 2 ^ 64 * ((x'.get 7#5).toNat + 2 ^ 64 * ((x'.get 11#5).toNat +
      2 ^ 64 * (x'.get 14#5).toNat)) = xn)
    (hyn : (x'.get 13#5).toNat + 2 ^ 64 * ((x'.get 28#5).toNat + 2 ^ 64 * ((x'.get 12#5).toNat +
      2 ^ 64 * (x'.get 16#5).toNat)) = yn)
    (hxM : xn < words m (x.get 13#5) 4) (hyM : yn < words m (x.get 13#5) 4)
    (hM0 : words m (x.get 13#5) 4 ≠ 0)
    (hxy : (xn + yn) % words m (x.get 13#5) 4 =
      (words m (x.get 11#5) 4 + words m (x.get 12#5) 4) % words m (x.get 13#5) 4) :
    Reach (amBufs x D) PA base (pcAt base 113) x' m' (x.get 1#5) (addmod_256.post x m) := by
  have hpre0 := hpre
  simp only [addmod_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hxa, hxn'⟩, ⟨hya, hyn'⟩, ⟨hma, hmn⟩, hdrx, hdry, hdrm, ⟨hsa, hsn⟩, hdsx,
    hdsy, hdsm, hdsr⟩ := hpre
  have hM : words m (x.get 13#5) 4 < 2 ^ 256 := by simpa using words_lt m 4 (x.get 13#5)
  rw [← regs_set_of_get' (by decide) h8]
  rv_exec_cut 55
  all_goals try simp only [zopz0zI_u_eq, decide_eq_true_eq, decide_eq_false_iff_not] at *
  all_goals try rv_conds
  all_goals
    have ha := add4c_words (r0 := x'.get 6#5) (r1 := x'.get 7#5) (r2 := x'.get 11#5)
      (r3 := x'.get 14#5) (v0 := x'.get 13#5) (v1 := x'.get 28#5) (v2 := x'.get 12#5)
      (v3 := x'.get 16#5) (by assumption) (by assumption) (by assumption) (by assumption)
      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
    have hb := am_sub4c_words (m0 := x'.get 5#5) (m1 := x'.get 17#5) (m2 := x'.get 10#5)
      (m3 := x'.get 15#5) (by assumption) (by assumption) (by assumption) (by assumption)
      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
    rw [hxn, hyn] at ha
    rw [hm0, hm1, hm2, hm3, ← words4_unfold] at hb
    refine am_epi base x m hr _ _ (AMFrame.regs (AMFrame.mem hF hpre0 ?_) ?_ ?_) ?_
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte,
        BitVec.reduceSignExtend]
      simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
      exact unchangedExcept2_refl _ _ _ _ _
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · am_cs
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte,
        BitVec.reduceSignExtend]
      rw [if_neg hM0, ← hxy]
      first
        | rw [← am_res_b hxM hyM hM ha hb am_ite_le am_ite_le (am_nat4_lt _ _ _ _)
            (am_nat4_lt _ _ _ _) (by
              simp only [Defn] at *
              subst_vars
              first
                | exact Or.inl (if_pos (Or.inl (by assumption)))
                | exact Or.inl (if_pos (Or.inr (am_bit_ne (by assumption))))
                | exact Or.inr (if_neg (am_or_eq (by assumption)))
                | exact Or.inr (if_neg (am_or_eq' (by assumption))))]
        | rw [← am_res_a hxM hyM hM ha hb am_ite_le am_ite_le (am_nat4_lt _ _ _ _)
            (am_nat4_lt _ _ _ _) (by
              simp only [Defn] at *
              subst_vars
              first
                | exact if_neg (not_or.2 ⟨by assumption, am_bit_eq (by assumption)⟩)
                | exact if_neg (not_or.2 ⟨by assumption, am_bit_eq' (by assumption)⟩))
            (by
              simp only [Defn] at *
              subst_vars
              exact if_pos (am_or_ne (by assumption)))]
      simp (disch := first | bv_omega | fail) only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
        BitVec.reduceAdd, BitVec.add_zero, memWord_memStore_self, memWord_memStore_of_ne,
        Nat.mul_zero, Nat.add_zero]

/-- A number of 4 words is less than its top word plus 1 times 2^192. -/
theorem am_words_lt_top (m : Mem) (a : BitVec 64) :
    words m a 4 < ((memWord m (a + 24#64).toNat).toNat + 1) * 2 ^ 192 := by
  rw [words4_unfold]
  have := (memWord m a.toNat).isLt; have := (memWord m (a + 8#64).toNat).isLt
  have := (memWord m (a + 16#64).toNat).isLt
  omega

/-- A number of 4 words is at least its top word times 2^192. -/
theorem am_words_ge_top (m : Mem) (a : BitVec 64) :
    (memWord m (a + 24#64).toNat).toNat * 2 ^ 192 ≤ words m a 4 := by
  rw [words4_unfold]
  omega

theorem am_lt_of_lt_sub {a b : BitVec 64} (h : a < a - b) : a.toNat < b.toNat := by
  bv_omega

/-- A number with its top word less than the top word of the modulus is less than the modulus. -/
theorem am_lt_of_top {V M v3 m3 : Nat} (hV : V < (v3 + 1) * 2 ^ 192) (hM : m3 * 2 ^ 192 ≤ M)
    (h : v3 < m3) : V < M := by
  have : (v3 + 1) * 2 ^ 192 ≤ m3 * 2 ^ 192 := Nat.mul_le_mul_right _ h
  omega

/-- The normalization that keeps a number that borrows when the modulus is subtracted from it. -/
theorem am_norm_b {B N M : Nat} {p q : Prop} [Decidable p] [Decidable q]
    (hsub : B + M = N + 2 ^ 256 * (if p ∨ q then 1 else 0)) (hq : q) (hB : B < 2 ^ 256) :
    N = N % M := by
  rw [if_pos (Or.inr hq)] at hsub
  exact (Nat.mod_eq_of_lt (by omega)).symm

/-- The normalization that subtracts the modulus from a number that does not borrow. -/
theorem am_norm_c {B N M : Nat} {p q : Prop} [Decidable p] [Decidable q]
    (hsub : B + M = N + 2 ^ 256 * (if p ∨ q then 1 else 0)) (hp : ¬p) (hq : ¬q)
    (h2 : N < 2 * M) : B = N % M := by
  rw [if_neg (not_or.2 ⟨hp, hq⟩)] at hsub
  rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- The normalization of y in `addmod()` from 89: y or y - mod, the remainder of y. -/
theorem am_y {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hr : x.get 1#5 &&& 3 = 0) (hpre : addmod_256.pre x m) (x' : Regs) (m' : Mem)
    (hF : AMFrame x m x' m') (h8 : x'.get 8#5 = x.get 10#5) (h12 : x'.get 12#5 = x.get 12#5)
    (hm0 : x'.get 5#5 = memWord m (x.get 13#5).toNat)
    (hm1 : x'.get 17#5 = memWord m (x.get 13#5 + 8#64).toNat)
    (hm2 : x'.get 10#5 = memWord m (x.get 13#5 + 16#64).toNat)
    (hm3 : x'.get 15#5 = memWord m (x.get 13#5 + 24#64).toNat)
    (h16 : x'.get 16#5 = memWord m (x.get 12#5 + 24#64).toNat)
    (hxv : (x'.get 6#5).toNat + 2 ^ 64 * ((x'.get 7#5).toNat + 2 ^ 64 * ((x'.get 11#5).toNat +
      2 ^ 64 * (x'.get 14#5).toNat)) = words m (x.get 11#5) 4 % words m (x.get 13#5) 4)
    (hM0 : words m (x.get 13#5) 4 ≠ 0) (hY2 : words m (x.get 12#5) 4 < 2 * words m (x.get 13#5) 4) :
    Reach (amBufs x D) PA base (pcAt base 89) x' m' (x.get 1#5) (addmod_256.post x m) := by
  have hY := hF.words_arg hpre 12#5 (by decide)
  have hy3 := hF.memWord_arg hpre 12#5 (by decide) 24#64 (by decide)
  have hYeq := (words4_unfold m' (x.get 12#5)).symm.trans hY
  have hMeq : (x'.get 5#5).toNat + 2 ^ 64 * ((x'.get 17#5).toNat + 2 ^ 64 * ((x'.get 10#5).toNat +
      2 ^ 64 * (x'.get 15#5).toNat)) = words m (x.get 13#5) 4 := by
    rw [hm0, hm1, hm2, hm3, words4_unfold]
  rw [← hy3] at h16
  rw [← regs_set_of_get' (by decide) h12, ← regs_set_of_get' (by decide) h16]
  rv_exec_cut 113
  all_goals try simp only [zopz0zI_u_eq, decide_eq_true_eq, decide_eq_false_iff_not] at *
  all_goals try rv_conds
  all_goals
    try have hsub := am_sub4c_words (m0 := x'.get 5#5) (m1 := x'.get 17#5)
          (m2 := x'.get 10#5) (m3 := x'.get 15#5) (by assumption) (by assumption) (by assumption)
          (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
          (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
          (by assumption)
    refine am_sum base x m hr hpre _ m' (AMFrame.regs hF ?_ ?_) ?_ ?_ ?_ ?_ ?_
      (words m (x.get 11#5) 4 % words m (x.get 13#5) 4)
      (words m (x.get 12#5) 4 % words m (x.get 13#5) 4) ?_ ?_
      (Nat.mod_lt _ (Nat.pos_of_ne_zero hM0)) (Nat.mod_lt _ (Nat.pos_of_ne_zero hM0)) hM0
      (Nat.add_mod _ _ _).symm
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    all_goals first | am_cs | assumption | skip
  all_goals
    simp only [Defn] at *
    subst_vars
    first
      | rw [hYeq]
        exact (Nat.mod_eq_of_lt (am_lt_of_top (am_words_lt_top m _) (am_words_ge_top m _)
          (by rw [← hy3, ← hm3]; exact am_lt_of_lt_sub (by assumption)))).symm
      | rw [hYeq]
        have h := am_norm_b hsub (am_bit_ne (by assumption)) (am_nat4_lt _ _ _ _)
        rw [hYeq, hMeq] at h
        exact h
      | have h := am_norm_c hsub (by assumption)
          (by first | exact am_bit_eq (by assumption) | exact am_bit_eq' (by assumption))
          (by rw [hYeq, hMeq]; exact hY2)
        rw [hYeq, hMeq] at h
        exact h

/-- The normalization of x in `addmod()` from 68 with the words of x and the modulus in the
registers: x or x - mod, the remainder of x. -/
theorem am_x {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hr : x.get 1#5 &&& 3 = 0) (hpre : addmod_256.pre x m) (x' : Regs) (m' : Mem)
    (hF : AMFrame x m x' m') (h8 : x'.get 8#5 = x.get 10#5) (h12 : x'.get 12#5 = x.get 12#5)
    (hm0 : x'.get 5#5 = memWord m (x.get 13#5).toNat)
    (hm1 : x'.get 17#5 = memWord m (x.get 13#5 + 8#64).toNat)
    (hm2 : x'.get 10#5 = memWord m (x.get 13#5 + 16#64).toNat)
    (hm3 : x'.get 15#5 = memWord m (x.get 13#5 + 24#64).toNat)
    (h16 : x'.get 16#5 = memWord m (x.get 12#5 + 24#64).toNat)
    (hx0 : x'.get 6#5 = memWord m (x.get 11#5).toNat)
    (hx1 : x'.get 7#5 = memWord m (x.get 11#5 + 8#64).toNat)
    (hx2 : x'.get 11#5 = memWord m (x.get 11#5 + 16#64).toNat)
    (hx3 : x'.get 14#5 = memWord m (x.get 11#5 + 24#64).toNat)
    (hM0 : words m (x.get 13#5) 4 ≠ 0) (hX2 : words m (x.get 11#5) 4 < 2 * words m (x.get 13#5) 4)
    (hY2 : words m (x.get 12#5) 4 < 2 * words m (x.get 13#5) 4) :
    Reach (amBufs x D) PA base (pcAt base 68) x' m' (x.get 1#5) (addmod_256.post x m) := by
  have hMeq : (x'.get 5#5).toNat + 2 ^ 64 * ((x'.get 17#5).toNat + 2 ^ 64 * ((x'.get 10#5).toNat +
      2 ^ 64 * (x'.get 15#5).toNat)) = words m (x.get 13#5) 4 := by
    rw [hm0, hm1, hm2, hm3, words4_unfold]
  have hXeq : (x'.get 6#5).toNat + 2 ^ 64 * ((x'.get 7#5).toNat + 2 ^ 64 * ((x'.get 11#5).toNat +
      2 ^ 64 * (x'.get 14#5).toNat)) = words m (x.get 11#5) 4 := by
    rw [hx0, hx1, hx2, hx3, words4_unfold]
  rv_exec_cut 89
  all_goals try simp only [zopz0zI_u_eq, decide_eq_true_eq, decide_eq_false_iff_not] at *
  all_goals try rv_conds
  all_goals
    try have hsub := am_sub4c_words (m0 := x'.get 5#5) (m1 := x'.get 17#5)
          (m2 := x'.get 10#5) (m3 := x'.get 15#5) (by assumption) (by assumption) (by assumption)
          (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
          (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
          (by assumption)
    refine am_y base x m hr hpre _ m' (AMFrame.regs hF ?_ ?_) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hM0 hY2
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    all_goals first | am_cs | assumption | skip
  all_goals
    simp only [Defn] at *
    subst_vars
    first
      | rw [hXeq]
        exact (Nat.mod_eq_of_lt (am_lt_of_top (am_words_lt_top m _) (am_words_ge_top m _)
          (by rw [← hx3, ← hm3]; exact am_lt_of_lt_sub (by assumption)))).symm
      | rw [hXeq]
        have h := am_norm_b hsub (am_bit_ne (by assumption)) (am_nat4_lt _ _ _ _)
        rw [hXeq, hMeq] at h
        exact h
      | have h := am_norm_c hsub (by assumption)
          (by first | exact am_bit_eq (by assumption) | exact am_bit_eq' (by assumption))
          (by rw [hXeq, hMeq]; exact hX2)
        rw [hXeq, hMeq] at h
        exact h

theorem am_toNat_ne_zero {a : BitVec 64} (h : ¬a = 0#64) : a.toNat ≠ 0 := by
  intro h0; exact h (BitVec.eq_of_toNat_eq (by simp [h0]))

/-- The dispatch of `addmod()` from 6, after the prologue: the path of a sum of 5 words divided
by `udivrem<320, 256>()` for a modulus below 2^192 or a top word of x or y above the top word of
the modulus, and the path of the normalizations of x and y otherwise. -/
theorem am_main {D : List (BitVec 64)} (base T : BitVec 64) (x : Regs) (m : Mem)
    (hb3 : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0) (hpre : addmod_256.pre x m)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64)
    (hTr : (x.get 10#5).toNat + 32 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hTs : (x.get 2#5 - 496#64).toNat + 496 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 496#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hD : ∀ a ∈ bufWords T 256, a ∈ D)
    (hT0 : pcAt (pcAt (pcAt base 158) 182) 5 + ((0x3#20 ++ 0x000#12).signExtend 64 +
      (0xc04#12).signExtend 64) = T)
    (hT1 : pcAt (pcAt (pcAt base 158) 375) 5 + ((0x3#20 ++ 0x000#12).signExtend 64 +
      (0x900#12).signExtend 64) = T)
    (hT2 : pcAt (pcAt (pcAt base 158) 618) 54 + ((0x2#20 ++ 0x000#12).signExtend 64 +
      (0x470#12).signExtend 64) = T)
    (hT3 : pcAt (pcAt (pcAt base 158) 932) 50 + ((0x2#20 ++ 0x000#12).signExtend 64 +
      (0xf98#12).signExtend 64) = T)
    (hT4 : pcAt (pcAt (pcAt base 158) 1275) 65 + ((0x2#20 ++ 0x000#12).signExtend 64 +
      (0xa00#12).signExtend 64) = T)
    (hT5 : pcAt (pcAt (pcAt base 158) 1457) 64 + ((0x1#20 ++ 0x000#12).signExtend 64 +
      (0x72c#12).signExtend 64) = T)
    (hT6 : pcAt (pcAt (pcAt base 158) 1661) 87 + ((0x1#20 ++ 0x000#12).signExtend 64 +
      (0x3a0#12).signExtend 64) = T)
    (hT7 : pcAt (pcAt (pcAt base 158) 1948) 107 + ((0x1#20 ++ 0x000#12).signExtend 64 +
      (0xed4#12).signExtend 64) = T)
    (hT8 : pcAt (pcAt (pcAt base 158) 2273) 84 + ((0x1#20 ++ 0x000#12).signExtend 64 +
      (0xa1c#12).signExtend 64) = T)
    (hT9 : pcAt (pcAt (pcAt base 158) 2585) 184 + ((0x0#20 ++ 0x000#12).signExtend 64 +
      (0x3ac#12).signExtend 64) = T)
    (x' : Regs) (m' : Mem) (hF : AMFrame x m x' m') (h10 : x'.get 10#5 = x.get 10#5)
    (h11 : x'.get 11#5 = x.get 11#5) (h12 : x'.get 12#5 = x.get 12#5)
    (h13 : x'.get 13#5 = x.get 13#5) :
    Reach (amBufs x D) PA base (pcAt base 6) x' m' (x.get 1#5) (addmod_256.post x m) := by
  replace hT0 := PLift.up hT0
  replace hT1 := PLift.up hT1
  replace hT2 := PLift.up hT2
  replace hT3 := PLift.up hT3
  replace hT4 := PLift.up hT4
  replace hT5 := PLift.up hT5
  replace hT6 := PLift.up hT6
  replace hT7 := PLift.up hT7
  replace hT8 := PLift.up hT8
  replace hT9 := PLift.up hT9
  have hpre0 := hpre
  have hxw := hF.memWord_arg hpre0 11#5 (by decide)
  have hyw := hF.memWord_arg hpre0 12#5 (by decide)
  have hmw := hF.memWord_arg hpre0 13#5 (by decide)
  have hx0 := hxw 0#64 (by decide)
  have hm0 := hmw 0#64 (by decide)
  rw [BitVec.add_zero] at hx0 hm0
  have hxl := am_words_lt_top m (x.get 11#5)
  have hyl := am_words_lt_top m (x.get 12#5)
  have hmg := am_words_ge_top m (x.get 13#5)
  rw [← regs_set_of_get' (by decide) h10, ← regs_set_of_get' (by decide) h11,
    ← regs_set_of_get' (by decide) h12, ← regs_set_of_get' (by decide) h13]
  rv_exec_cut 13 68
  all_goals rv_subst
  all_goals simp only [hxw 8#64 (by decide), hxw 16#64 (by decide), hxw 24#64 (by decide),
    hyw 24#64 (by decide), hmw 8#64 (by decide), hmw 16#64 (by decide), hmw 24#64 (by decide),
    hx0, hm0] at *
  all_goals try simp only [zopz0zKzJ_u_eq, zopz0zI_u_eq, decide_eq_true_eq,
    decide_eq_false_iff_not, BitVec.le_def, BitVec.lt_def] at *
  -- The modulus below 2^192 or the top word of x or y above the top word of the modulus.
  all_goals first
    | (rv_not_at 13; skip)
    | (refine am_slow base T x m hb3 hr hpre0 hw hTr hTs hhold hD hT0.down hT1.down hT2.down
         hT3.down hT4.down hT5.down hT6.down hT7.down hT8.down hT9.down _ m'
         (AMFrame.regs hF ?_ ?_) ?_ ?_ ?_ ?_ ?_
       all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
       all_goals first | am_cs | skip)
  -- The normalizations of x and y.
  all_goals first
    | (rv_not_at 68; skip)
    | (have hm3 := am_toNat_ne_zero (a := memWord m (x.get 13#5 + 24#64).toNat) (by assumption)
       refine am_x base x m hr hpre0 _ m' (AMFrame.regs hF ?_ ?_) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
         ?_ (by omega) (am_lt2 hxl hmg (by omega) (by omega)) (am_lt2 hyl hmg (by omega) (by omega))
       all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
       all_goals first | am_cs | skip)

end IntxRV.Api
