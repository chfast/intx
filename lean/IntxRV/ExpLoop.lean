import IntxRV.Exp
import IntxRV.Api.shl_256


/-!
# The loop of `exp()`

The square and multiply over the bits of the exponent from its bit width: the head of the loop at
125 (`EXHead`, the result is the power of the base by the bits above `i`), a step from 126 by the
square (`ex_sq`), the bit `k` (`ex_after`) and the product with the base (`ex_mb`, `ex_cp`), and
the loop by induction on the bits left (`ex_loop`). Before the loop, the bit width of the exponent
by the SWAR count of the leading zeros (`ex_bw`), and the base 2 by the call of `operator<<`
(`ex_main`). See `IntxRV/Api/exp_256.lean`.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
-- The paths share the tactics, which some paths do not use.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

/-- One step of the square and multiply: `B ^ (E >> k)` from `B ^ (E >> (k + 1))` and the bit
`k` of `E`. -/
theorem ex_step_nat (B E k M : Nat) :
    (if E.testBit k then B * (B ^ (E >>> (k + 1)) % M * (B ^ (E >>> (k + 1)) % M) % M) % M
      else B ^ (E >>> (k + 1)) % M * (B ^ (E >>> (k + 1)) % M) % M) = B ^ (E >>> k) % M := by
  have hE : E >>> k = 2 * (E >>> (k + 1)) + (if E.testBit k then 1 else 0) := by
    rw [Nat.shiftRight_succ, Nat.testBit_eq_decide_div_mod_eq, ← Nat.shiftRight_eq_div_pow]
    generalize E >>> k = q
    split <;> rename_i h <;> simp at h <;> omega
  rw [hE, pow_add, pow_mul', ← Nat.mul_mod, ← pow_two]
  split
  · rw [pow_one, Nat.mul_comm ((B ^ (E >>> (k + 1))) ^ 2) B, Nat.mul_mod B, Nat.mod_mod,
      ← Nat.mul_mod]
  · rw [pow_zero, Nat.mul_one]

/-- The bit `s` of a word as `srl` and `andi 1` show it. -/
theorem ex_bit_zero (w : BitVec 64) (s : Nat) :
    (w >>> s &&& 1#64) = 0#64 ↔ w.getLsbD s = false := by
  rcases and_one_cases (w >>> s) with h | h
  · rw [h]
    have : ¬((w >>> s &&& 1#64) = 1#64) := by rw [h]; decide
    rw [shr_and_one_eq_one] at this
    simpa using this
  · rw [h]
    have := (shr_and_one_eq_one w s).1 h
    simp [this]

/-- The state of `exp()` at the head 125 of the loop over the bits of the exponent, with `i` bits
left: the result at sp + 8 is the power of the base by the bits above them. -/
def EXHead (x : Regs) (m : Mem) (i : Nat) (x' : Regs) (m' : Mem) : Prop :=
  EXFrame x m x' m' ∧ x'.get 10#5 = x.get 10#5 ∧ x'.get 11#5 = x.get 11#5 ∧
  x'.get 12#5 = x.get 12#5 ∧ x'.get 13#5 = BitVec.ofNat 64 i ∧
  x'.get 14#5 = x.get 2#5 + 18446744073709551512#64 ∧ x'.get 15#5 = 3#64 ∧ x'.get 16#5 = 4#64 ∧
  i ≤ 256 ∧ words m' (x.get 2#5 + 18446744073709551512#64) 4 =
    words m (x.get 11#5) 4 ^ (words m (x.get 12#5) 4 >>> i) % 2 ^ 256

set_option hygiene false in
/-- The words of the memory after the stores of a run. -/
local macro "ex_words" : tactic => `(tactic| (
  try simp only [BitVec.reduceSignExtend, BitVec.add_assoc, BitVec.reduceAdd]
  simp (disch := first | bv_omega | fail) only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
    BitVec.reduceAdd, BitVec.add_zero, memWord_memStore_self, memWord_memStore_of_ne,
    Nat.mul_zero, Nat.add_zero]))

set_option hygiene false in
/-- The callee-saved registers that the frame keeps, through the sets of the other registers. -/
local macro "ex_cs" : tactic => `(tactic| (
  intro r hr' hn
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte] at hn ⊢))

set_option hygiene false in
/-- The destructured precondition of `exp()`. -/
local macro "ex_pre" : tactic => `(tactic| (
  have hpre0 := hpre
  simp only [exp_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hba, hbn⟩, ⟨hea, hen⟩, hdrb, hdre, ⟨hsa, hsn⟩, hdsb, hdse, hdsr⟩ := hpre))

/-- The copy of the temporary at sp + 40 to the result at sp + 8 from 117, to the head 125. -/
theorem ex_cp {D : List (BitVec 64)} (base ret : BitVec 64) (x : Regs) (m : Mem)
    (hpre : exp_256.pre x m) (x' : Regs) (m' : Mem) (Q : Regs → Mem → Prop)
    (hF : EXFrame x m x' m') (h10 : x'.get 10#5 = x.get 10#5) (h11 : x'.get 11#5 = x.get 11#5)
    (h12 : x'.get 12#5 = x.get 12#5) (k : Nat) (h13 : x'.get 13#5 = BitVec.ofNat 64 k)
    (h14 : x'.get 14#5 = x.get 2#5 + 18446744073709551512#64) (h15 : x'.get 15#5 = 3#64)
    (h16 : x'.get 16#5 = 4#64) (hk : k ≤ 256)
    (hT : words m' (x.get 2#5 + 18446744073709551544#64) 4 =
      words m (x.get 11#5) 4 ^ (words m (x.get 12#5) 4 >>> k) % 2 ^ 256)
    (hloop : ∀ x'' m'', EXHead x m k x'' m'' →
      Reach (exBufs x D) exp_256_image_prog base (pcAt base 125) x'' m'' ret Q) :
    Reach (exBufs x D) exp_256_image_prog base (pcAt base 117) x' m' ret Q := by
  ex_pre
  have hsp := hF.1
  rw [← regs_set_of_get' (by decide) h10, ← regs_set_of_get' (by decide) h11,
    ← regs_set_of_get' (by decide) h12, ← regs_set_of_get' (by decide) hsp,
    ← regs_set_of_get' (by decide) h13, ← regs_set_of_get' (by decide) h14,
    ← regs_set_of_get' (by decide) h15, ← regs_set_of_get' (by decide) h16]
  rv_exec_cut 125
  refine hloop _ _ ⟨EXFrame.regs (EXFrame.mem hF hpre0 ?_) ?_ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hk,
    ?_⟩
  · try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte,
      BitVec.reduceSignExtend]
    simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
    exact unchangedExcept2_refl _ _ _ _ _
  all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  all_goals try ex_cs
  all_goals try exact hsp.symm
  rw [← hT]
  ex_words
  rv_loads
  rfl

theorem ex_ofNat_pred (k : Nat) :
    BitVec.ofNat 64 (k + 1) + 18446744073709551615#64 = BitVec.ofNat 64 k := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]
  rw [show (1#64 + 18446744073709551615#64) = 0#64 from rfl, BitVec.add_zero]

theorem ex_toNat_ofNat (k : Nat) (hk : k < 256) : (BitVec.ofNat 64 k).toNat = k := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem ex_word_lt (k : Nat) (hk : k < 256) : k / 64 < 4 := by omega

theorem ex_bit_lt (k : Nat) (hk : k < 256) : k < 64 * 4 := by omega

theorem ex_word_off (k : Nat) (hk : k < 256) : (BitVec.ofNat 64 (8 * (k / 64))).toNat + 8 ≤ 32 := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega

/-- The rest of a step of the loop from 176, after the square: the bit `k` of the exponent, the
copy of the square to the result and, for the bit 1, the product with the base, to the head 125
with `k` bits left. -/
theorem ex_after {D : List (BitVec 64)} (base ret : BitVec 64) (x : Regs) (m : Mem)
    (hpre : exp_256.pre x m) (x' : Regs) (m' : Mem) (Q : Regs → Mem → Prop)
    (hF : EXFrame x m x' m') (h10 : x'.get 10#5 = x.get 10#5) (h11 : x'.get 11#5 = x.get 11#5)
    (h12 : x'.get 12#5 = x.get 12#5) (k : Nat) (h13 : x'.get 13#5 = BitVec.ofNat 64 (k + 1))
    (h14 : x'.get 14#5 = x.get 2#5 + 18446744073709551512#64) (h15 : x'.get 15#5 = 3#64)
    (h16 : x'.get 16#5 = 4#64) (hk : k < 256)
    (hT : words m' (x.get 2#5 + 18446744073709551544#64) 4 =
      words m (x.get 11#5) 4 ^ (words m (x.get 12#5) 4 >>> (k + 1)) % 2 ^ 256 *
        (words m (x.get 11#5) 4 ^ (words m (x.get 12#5) 4 >>> (k + 1)) % 2 ^ 256) % 2 ^ 256)
    (hloop : ∀ x'' m'', EXHead x m k x'' m'' →
      Reach (exBufs x D) exp_256_image_prog base (pcAt base 125) x'' m'' ret Q) :
    Reach (exBufs x D) exp_256_image_prog base (pcAt base 176) x' m' ret Q := by
  ex_pre
  have hsp := hF.1
  have hew := hF.memWord_arg hpre0 12#5 (by decide)
  rw [← regs_set_of_get' (by decide) h10, ← regs_set_of_get' (by decide) h11,
    ← regs_set_of_get' (by decide) h12, ← regs_set_of_get' (by decide) hsp,
    ← regs_set_of_get' (by decide) h13, ← regs_set_of_get' (by decide) h14,
    ← regs_set_of_get' (by decide) h15, ← regs_set_of_get' (by decide) h16]
  rv_exec
  have hk1 := ex_ofNat_pred k
  have hkn := ex_toNat_ofNat k hk
  have hi := ex_word_lt k hk
  simp only [hk1] at *
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  simp only [Defn] at *
  subst_vars
  rw [shr3_and, hkn]
  refine ⟨List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (mem_bufWords hi)))), fun w hw => ?_⟩
  rw [hew _ (ex_word_off k hk)] at hw
  have hbit := testBit_words m 4 (x.get 12#5) k (ex_bit_lt k hk)
  rw [← hw] at hbit
  rv_exec_cut 125 192
  all_goals try simp only [hkn] at *
  all_goals rename_i wb hb hwb
  all_goals rw [hwb.eq] at hb
  · -- The bit 0: the square is the result.
    have hb0 : (words m (x.get 12#5) 4).testBit k = false := by
      rw [hbit]; exact (ex_bit_zero w _).1 hb
    refine hloop _ _ ⟨EXFrame.regs (EXFrame.mem hF hpre0 ?_) ?_ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      by omega, ?_⟩
    · try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte,
        BitVec.reduceSignExtend]
      simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
      exact unchangedExcept2_refl _ _ _ _ _
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    all_goals try ex_cs
    all_goals try exact hsp.symm
    rw [← ex_step_nat (words m (x.get 11#5) 4) (words m (x.get 12#5) 4) k (2 ^ 256),
      if_neg (by simp [hb0]), ← hT]
    try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    ex_words
    rv_loads
    rfl
  · -- The bit 1: the product of the base and the square.
    have hb1 : (words m (x.get 12#5) 4).testBit k = true := by
      rw [hbit]; simpa using mt (ex_bit_zero w _).2 hb
    generalize hM : memStore (memStore (memStore (memStore m' _ _) _ _) _ _) _ _ = M192
    have hcopy : words M192 (x.get 2#5 + 18446744073709551512#64) 4 =
        words m (x.get 11#5) 4 ^ (words m (x.get 12#5) 4 >>> (k + 1)) % 2 ^ 256 *
          (words m (x.get 11#5) 4 ^ (words m (x.get 12#5) 4 >>> (k + 1)) % 2 ^ 256) % 2 ^ 256 := by
      rw [← hM, ← hT]
      simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      ex_words
      rv_loads
      rfl
    refine ex_mb base ret x m hpre0 _ M192 Q (EXFrame.regs (EXFrame.mem hF hpre0 ?_) ?_ ?_) ?_ ?_
      ?_ ?_ ?_ ?_ (fun x3 m3 hF3 h103 h113 h123 h133 h143 h153 h163 hP _ => ?_)
    · rw [← hM]
      try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte,
        BitVec.reduceSignExtend]
      simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
      exact unchangedExcept2_refl _ _ _ _ _
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    all_goals try ex_cs
    all_goals try exact hsp.symm
    refine ex_cp base ret x m hpre0 x3 m3 Q hF3 h103 h113 h123 k ?_ h143 h153 h163 (by omega) ?_
      hloop
    · rw [h133]; simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · rw [hP, hcopy,
        ← ex_step_nat (words m (x.get 11#5) 4) (words m (x.get 12#5) 4) k (2 ^ 256), if_pos hb1]

theorem ex_ofNat_ne_zero (k : Nat) (hk : k + 1 ≤ 256) : ¬BitVec.ofNat 64 (k + 1) = 0#64 := by
  intro h
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
  simp at this

/-- A step of the loop from 126 with `k + 1` bits left: the square, the bit `k` and the product,
to the head with `k` bits left. -/
theorem ex_head126 {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hpre : exp_256.pre x m) (k : Nat) (x' : Regs) (m' : Mem) (hH : EXHead x m (k + 1) x' m')
    (hloop : ∀ x'' m'', EXHead x m k x'' m'' →
      Reach (exBufs x D) exp_256_image_prog base (pcAt base 125) x'' m'' (x.get 1#5)
        (exp_256.post x m)) :
    Reach (exBufs x D) exp_256_image_prog base (pcAt base 126) x' m' (x.get 1#5)
      (exp_256.post x m) := by
  obtain ⟨hF, h10, h11, h12, h13, h14, h15, h16, hi, hR⟩ := hH
  refine ex_sq base _ x m hpre x' m' _ hF h10 h11 h12 h14 h15 h16
    (fun x'' m'' hF'' h10'' h11'' h12'' h13'' h14'' h15'' h16'' hT _ => ?_)
  refine ex_after base _ x m hpre x'' m'' _ hF'' h10'' h11'' h12'' k (h13''.trans h13) h14'' h15''
    h16'' (by omega) ?_ hloop
  rw [hT, hR]

/-- The loop of `exp()` from its head 125 with `i` bits of the exponent left. -/
theorem ex_loop {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hr : x.get 1#5 &&& 3 = 0) (hpre : exp_256.pre x m) :
    ∀ (i : Nat) (x' : Regs) (m' : Mem), EXHead x m i x' m' →
      Reach (exBufs x D) exp_256_image_prog base (pcAt base 125) x' m' (x.get 1#5)
        (exp_256.post x m)
  | 0, x', m', hH => by
    obtain ⟨hF, h10, h11, h12, h13, h14, h15, h16, hi, hR⟩ := hH
    rv_exec_cut 97 126
    · refine ex_ret base x m hr hpre x' m' hF h10 ?_
      rw [hR, Nat.shiftRight_zero]
    · exfalso
      rename_i hb
      rw [h13] at hb
      exact hb (Regs.get_zero x').symm
  | k + 1, x', m', hH => by
    have hH0 := hH
    obtain ⟨hF, h10, h11, h12, h13, h14, h15, h16, hi, hR⟩ := hH
    rv_exec_cut 97 126
    · exact absurd (h13 ▸ (by assumption)) (ex_ofNat_ne_zero k hi)
    · exact ex_head126 base x m hpre k x' m' hH0 (ex_loop base x m hr hpre k)

/-- The bit width of the exponent from the word count `c / 64` and the leading zeros `63 - L` of
the top word. -/
theorem ex_bw_reg (c L K : Nat) (hc : c ≤ 256) (hc64 : 64 ≤ c) (hL : L ≤ 63)
    (hK : K + 1 = L + 1 + (c - 64)) :
    BitVec.ofNat 64 c - BitVec.ofNat 64 (63 - L) = BitVec.ofNat 64 (K + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := c) (by omega), Nat.mod_eq_of_lt (a := 63 - L) (by omega),
    Nat.mod_eq_of_lt (a := K + 1) (by omega)]
  omega

/-- The leading zeros of a nonzero word are not 64 times the count of the words. -/
theorem ex_bw_ne (c : Nat) (t : BitVec 64) (ht : ¬t = 0#64) (hc : c ≤ 256) (hc64 : 64 ≤ c) :
    ¬BitVec.ofNat 64 c = BitVec.ofNat 64 (if t = 0#64 then 64 else 63 - t.toNat.log2) := by
  rw [if_neg ht]
  intro h
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := c) (by omega),
    Nat.mod_eq_of_lt (by omega)] at this
  omega

theorem ex_ne_zero_of {w : BitVec 64} (h : ¬w = 0#64) : w.toNat ≠ 0 := by
  intro h0; exact h (BitVec.eq_of_toNat_eq (by simpa using h0))

/-- The bit width of the exponent with the top word `w3`. -/
theorem ex_bw4 (w0 w1 w2 w3 : BitVec 64) (h3 : ¬w3 = 0#64) :
    256#64 - BitVec.ofNat 64 (if w3 = 0#64 then 64 else 63 - w3.toNat.log2) =
      BitVec.ofNat 64 (Nat.log2 (w0.toNat + 2 ^ 64 * (w1.toNat + 2 ^ 64 * (w2.toNat + 2 ^ 64 * w3.toNat))) + 1) := by
  have h := bit_width_words4 w0 w1 w2 w3
  have := ex_ne_zero_of h3
  have hL := log2_lt_64 h3
  rw [if_neg h3]
  rw [if_neg (by omega), if_pos (show w3 ≠ 0 from h3)] at h
  exact ex_bw_reg 256 _ _ (by omega) (by omega) (by omega) (by omega)

/-- The bit width of the exponent with the top word `w2`. -/
theorem ex_bw3 (w0 w1 w2 w3 : BitVec 64) (h3 : w3 = 0#64) (h2 : ¬w2 = 0#64) :
    192#64 - BitVec.ofNat 64 (if w2 = 0#64 then 64 else 63 - w2.toNat.log2) =
      BitVec.ofNat 64 (Nat.log2 (w0.toNat + 2 ^ 64 * (w1.toNat + 2 ^ 64 * (w2.toNat + 2 ^ 64 * w3.toNat))) + 1) := by
  have h := bit_width_words4 w0 w1 w2 w3
  have := ex_ne_zero_of h2
  have hL := log2_lt_64 h2
  rw [if_neg h2]
  rw [if_neg (by subst h3; simp only [BitVec.toNat_ofNat, Nat.zero_mod]; omega),
    if_neg (show ¬(w3 ≠ 0) by simpa using h3), if_pos (show w2 ≠ 0 from h2)] at h
  exact ex_bw_reg 192 _ _ (by omega) (by omega) (by omega) (by omega)

/-- The bit width of the exponent with the top word `w1`. -/
theorem ex_bw2 (w0 w1 w2 w3 : BitVec 64) (h3 : w3 = 0#64) (h2 : w2 = 0#64) (h1 : ¬w1 = 0#64) :
    128#64 - BitVec.ofNat 64 (if w1 = 0#64 then 64 else 63 - w1.toNat.log2) =
      BitVec.ofNat 64 (Nat.log2 (w0.toNat + 2 ^ 64 * (w1.toNat + 2 ^ 64 * (w2.toNat + 2 ^ 64 * w3.toNat))) + 1) := by
  have h := bit_width_words4 w0 w1 w2 w3
  have := ex_ne_zero_of h1
  have hL := log2_lt_64 h1
  rw [if_neg h1]
  rw [if_neg (by subst h3 h2; simp only [BitVec.toNat_ofNat, Nat.zero_mod]; omega),
    if_neg (show ¬(w3 ≠ 0) by simpa using h3), if_neg (show ¬(w2 ≠ 0) by simpa using h2),
    if_pos (show w1 ≠ 0 from h1)] at h
  exact ex_bw_reg 128 _ _ (by omega) (by omega) (by omega) (by omega)

/-- The bit width of the exponent with the top word `w0`. -/
theorem ex_bw1 (w0 w1 w2 w3 : BitVec 64) (h3 : w3 = 0#64) (h2 : w2 = 0#64) (h1 : w1 = 0#64)
    (h0 : ¬w0 = 0#64) :
    64#64 - BitVec.ofNat 64 (if w0 = 0#64 then 64 else 63 - w0.toNat.log2) =
      BitVec.ofNat 64 (Nat.log2 (w0.toNat + 2 ^ 64 * (w1.toNat + 2 ^ 64 * (w2.toNat + 2 ^ 64 * w3.toNat))) + 1) := by
  have h := bit_width_words4 w0 w1 w2 w3
  have := ex_ne_zero_of h0
  have hL := log2_lt_64 h0
  rw [if_neg h0]
  rw [if_neg (by subst h3 h2 h1; simp only [BitVec.toNat_ofNat, Nat.zero_mod]; omega),
    if_neg (show ¬(w3 ≠ 0) by simpa using h3), if_neg (show ¬(w2 ≠ 0) by simpa using h2),
    if_neg (show ¬(w1 ≠ 0) by simpa using h1), if_pos (show w0 ≠ 0 from h0)] at h
  exact ex_bw_reg 64 _ _ (by omega) (by omega) (by omega) (by omega)

/-- The bit width of a number of 256 bits is at most 256. -/
theorem ex_log2_lt {E : Nat} (h : E < 2 ^ 256) : Nat.log2 E + 1 ≤ 256 := by
  rcases Nat.eq_zero_or_pos E with rfl | hE
  · simp
  · have := (Nat.log2_lt (by omega)).2 h; omega

/-- A number shifted by its bit width is 0. -/
theorem ex_shr_bw (E : Nat) : E >>> (Nat.log2 E + 1) = 0 := by
  rw [Nat.shiftRight_eq_div_pow]
  rcases Nat.eq_zero_or_pos E with rfl | hE
  · simp
  · exact Nat.div_eq_of_lt (Nat.lt_log2_self)

/-- The bit width of the exponent from 31, after the test of the base: the copy of the result 1
for the exponent 0, or the loop from 126 with the bit width of the exponent. -/
theorem ex_bw {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hr : x.get 1#5 &&& 3 = 0) (hpre : exp_256.pre x m) (x' : Regs) (m' : Mem)
    (hF : EXFrame x m x' m') (h10 : x'.get 10#5 = x.get 10#5) (h11 : x'.get 11#5 = x.get 11#5)
    (h12 : x'.get 12#5 = x.get 12#5) (hR : words m' (x.get 2#5 + 18446744073709551512#64) 4 = 1) :
    Reach (exBufs x D) exp_256_image_prog base (pcAt base 31) x' m' (x.get 1#5)
      (exp_256.post x m) := by
  ex_pre
  have hsp := hF.1
  have hew := hF.memWord_arg hpre0 12#5 (by decide)
  have he0 := hew 0#64 (by decide)
  rw [BitVec.add_zero] at he0
  rw [← regs_set_of_get' (by decide) h10, ← regs_set_of_get' (by decide) h11,
    ← regs_set_of_get' (by decide) h12, ← regs_set_of_get' (by decide) hsp]
  rv_exec_cut 97 126
  all_goals try rv_val
  all_goals try simp only [Defn] at *
  all_goals try subst_vars
  all_goals try simp only [BitVec.reduceAdd, BitVec.reduceHShiftLeft, BitVec.reduceShiftLeft,
    BitVec.reduceSub, BitVec.reduceMul] at *
  all_goals try simp only [hew 8#64 (by decide), hew 16#64 (by decide), hew 24#64 (by decide),
    he0] at *
  all_goals try simp only [beq_iff_eq, bne_iff_ne, ne_eq, Bool.not_eq_true, beq_eq_false_iff_ne] at *
  all_goals first | contradiction | skip
  -- The exponent 0, or the contradiction of 64 times the words with the leading zeros.
  all_goals first
    | (rv_not_at 97; skip)
    | (refine ex_ret base x m hr hpre0 _ m' (EXFrame.regs hF ?_ ?_) ?_ ?_
       · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
         exact hsp.symm
       · ex_cs
       · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
       · rw [hR, words4_unfold m (x.get 12#5)]
         simp only [*, BitVec.toNat_ofNat, Nat.zero_mod, Nat.mul_zero, Nat.add_zero, pow_zero]
         norm_num
         done)
    | (exfalso
       rename_i hb
       simp only [← smear_expand, ← swarClz_expand, clz_ite] at hb
       exact ex_bw_ne _ _ (by assumption) (by norm_num) (by norm_num) hb)
  -- The loop with the bit width of the exponent.
  all_goals
    have hE := ex_log2_lt (by simpa using words_lt m 4 (x.get 12#5))
    refine ex_head126 base x m hpre0 (Nat.log2 (words m (x.get 12#5) 4)) _ _
      ⟨EXFrame.regs hF ?_ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hE, ?_⟩ (ex_loop base x m hr hpre0 _)
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      exact hsp.symm
    · ex_cs
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · simp only [← smear_expand, ← swarClz_expand, clz_ite]
      rw [words4_unfold m (x.get 12#5)]
      first
        | exact ex_bw4 _ _ _ _ (by assumption)
        | exact ex_bw3 _ _ _ _ (by assumption) (by assumption)
        | exact ex_bw2 _ _ _ _ (by assumption) (by assumption) (by assumption)
        | exact ex_bw1 _ _ _ _ (by assumption) (by assumption) (by assumption) (by assumption)
    · rw [hR, ex_shr_bw, pow_zero]
      norm_num

/-- A power of 2 by at least 2^64 is 0 modulo 2^256. -/
theorem ex_two_big {E : Nat} (h : 2 ^ 64 ≤ E) : 2 ^ E % 2 ^ 256 = 0 := by
  apply Nat.mod_eq_zero_of_dvd
  exact Nat.pow_dvd_pow 2 (by omega)

/-- The value of a number of 4 words with the words above the low one 0. -/
theorem ex_words_low (m : Mem) (a : BitVec 64) (h1 : memWord m (a + 8#64).toNat = 0#64)
    (h2 : memWord m (a + 16#64).toNat = 0#64) (h3 : memWord m (a + 24#64).toNat = 0#64) :
    words m a 4 = (memWord m a.toNat).toNat := by
  rw [words4_unfold, h1, h2, h3]
  simp

/-- A number of 4 words with a nonzero word above the low one is at least 2^64. -/
theorem ex_words_ge (m : Mem) (a : BitVec 64)
    (h : ¬(memWord m (a + 16#64).toNat ||| memWord m (a + 8#64).toNat |||
      memWord m (a + 24#64).toNat) = 0#64) :
    2 ^ 64 ≤ words m a 4 := by
  rw [words4_unfold]
  simp only [BitVec.or_eq_zero_iff, not_and_or] at h
  have z : ∀ w : BitVec 64, ¬w = 0#64 → 1 ≤ w.toNat := fun w hw => by
    rcases Nat.eq_zero_or_pos w.toNat with h0 | h0
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) hw
    · exact h0
  rcases h with (h | h) | h <;> have := z _ h <;> nlinarith

theorem ex_or3_zero {a b c : BitVec 64} (h : 0#64 = a ||| b ||| c) :
    a = 0#64 ∧ b = 0#64 ∧ c = 0#64 := by
  have h' := h.symm
  simp only [BitVec.or_eq_zero_iff] at h'
  exact ⟨h'.1.1, h'.1.2, h'.2⟩

/-- The paths of `exp()` from 6, after the prologue: the result 1 in the frame, the test of the
base 2 with the shift by the exponent (`operator<<`) or 0 for an exponent of at least 2^64, and the
bit width of the exponent from 31 otherwise. -/
theorem ex_main {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hb3 : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0) (hpre : exp_256.pre x m) (x' : Regs)
    (m' : Mem) (hF : EXFrame x m x' m') (h10 : x'.get 10#5 = x.get 10#5)
    (h11 : x'.get 11#5 = x.get 11#5) (h12 : x'.get 12#5 = x.get 12#5) :
    Reach (exBufs x D) exp_256_image_prog base (pcAt base 6) x' m' (x.get 1#5)
      (exp_256.post x m) := by
  ex_pre
  have hsp := hF.1
  have hbw := hF.memWord_arg hpre0 11#5 (by decide)
  have hew := hF.memWord_arg hpre0 12#5 (by decide)
  have hb0 := hbw 0#64 (by decide)
  have he0 := hew 0#64 (by decide)
  rw [BitVec.add_zero] at hb0 he0
  rw [← regs_set_of_get' (by decide) h10, ← regs_set_of_get' (by decide) h11,
    ← regs_set_of_get' (by decide) h12, ← regs_set_of_get' (by decide) hsp]
  rv_exec_cut 31 105 247
  all_goals try simp only [hbw 8#64 (by decide), hbw 16#64 (by decide), hbw 24#64 (by decide),
    hew 8#64 (by decide), hew 16#64 (by decide), hew 24#64 (by decide), hb0, he0] at *
  all_goals try simp only [Defn] at *
  all_goals try subst_vars
  all_goals try simp only [bne_iff_ne, ne_eq, beq_iff_eq, BitVec.ofNat_eq_ofNat] at *
  -- The base is not 2: the bit width of the exponent.
  all_goals first
    | (rv_not_at 31; skip)
    | (refine ex_bw base x m hr hpre0 _ _ (EXFrame.regs (EXFrame.mem hF hpre0 ?_) ?_ ?_) ?_ ?_ ?_ ?_
       · try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte,
           BitVec.reduceSignExtend]
         simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
         exact unchangedExcept2_refl _ _ _ _ _
       all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
       all_goals try ex_cs
       all_goals try exact hsp.symm
       ex_words
       decide)
  -- The base 2 and an exponent of at least 2^64: 0.
  all_goals first
    | (rv_not_at 105; skip)
    | (refine ex_epi base x m hr _ _ (EXFrame.regs (EXFrame.mem hF hpre0 ?_) ?_ ?_) ?_
       · try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte,
           BitVec.reduceSignExtend]
         simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
         exact unchangedExcept2_refl _ _ _ _ _
       all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
       all_goals try ex_cs
       all_goals try exact hsp.symm
       have hB : words m (x.get 11#5) 4 = 2 := by
         obtain ⟨z2, z1, z3⟩ := ex_or3_zero (a := memWord m (x.get 11#5 + 16#64).toNat)
           (b := memWord m (x.get 11#5 + 8#64).toNat) (c := memWord m (x.get 11#5 + 24#64).toNat)
           (by assumption)
         rw [ex_words_low m (x.get 11#5) z1 z2 z3]
         rw [← (by assumption : 2#64 = memWord m (x.get 11#5).toNat)]; rfl
       rw [hB, ex_two_big (ex_words_ge m (x.get 12#5) (by assumption))]
       ex_words
       decide)
  -- The base 2 and an exponent below 2^64: the call of `operator<<` by the low word.
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.reduceSignExtend]
  rw [show pcAt base 28 + 876#64 = pcAt base 247 by simp only [pcAt]; bv_omega,
    update_aligned (pcAt_aligned hb3 247)]
  have hB : words m (x.get 11#5) 4 = 2 := by
    obtain ⟨z2, z1, z3⟩ := ex_or3_zero (a := memWord m (x.get 11#5 + 16#64).toNat)
      (b := memWord m (x.get 11#5 + 8#64).toNat) (c := memWord m (x.get 11#5 + 24#64).toNat)
      (by assumption)
    rw [ex_words_low m (x.get 11#5) z1 z2 z3]
    rw [← (by assumption : 2#64 = memWord m (x.get 11#5).toNat)]; rfl
  have hE : words m (x.get 12#5) 4 = (memWord m (x.get 12#5).toNat).toNat := by
    obtain ⟨z2, z1, z3⟩ := ex_or3_zero (a := memWord m (x.get 12#5 + 16#64).toNat)
      (b := memWord m (x.get 12#5 + 8#64).toNat) (c := memWord m (x.get 12#5 + 24#64).toNat)
      (by assumption)
    exact ex_words_low m (x.get 12#5) z1 z2 z3
  generalize hM : memStore (memStore (memStore (memStore m' _ _) _ _) _ _) _ _ = M1
  have hone : words M1 (x.get 2#5 + 18446744073709551512#64) 4 = 1 := by
    rw [← hM]
    ex_words
    decide
  have hFM : EXFrame x m x' M1 := EXFrame.mem hF hpre0 (by
    rw [← hM]
    simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
    exact unchangedExcept2_refl _ _ _ _ _)
  refine Reach.call_sub (r := 30) exp_256_image_shl_256_in (by decide)
    (shl_256.reach _ _ _ ?_ ?_) ?_ ?_ ?_
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    exact pcAt_aligned hb3 30
  · simp only [shl_256.pre, Buf, Disjoint]
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    try simp (disch := decide) only [Regs.eq_get x']
    repeat' apply And.intro
    all_goals bv_omega
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · intro a ha
    simp only [shl_256.bufs] at ha
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at ha
    try simp (disch := decide) only [Regs.eq_get x'] at ha
    simp only [List.mem_append] at ha ⊢
    rcases ha with h | h
    · rw [show x.get 2#5 + 18446744073709551512#64 = x.get 2#5 - 112#64 + BitVec.ofNat 64 (8 * 1)
        by bv_omega] at h
      exact Or.inl (Or.inr (mem_bufWords_of_offset (by decide) h))
    · exact Or.inl (Or.inl (Or.inr h))
  · intro x2 m2 hpost
    obtain ⟨hval, hun, hsaved⟩ := hpost
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at hval hun
    try simp (disch := decide) only [Regs.eq_get x'] at hval hun
    have hF2 : EXFrame x m x2 m2 := by
      refine EXFrame.regs (EXFrame.mem hFM hpre0 (fun k hk1 hk2 => hun k hk1)) ?_ ?_
      · rw [get_of_calleeSaved hsaved (by decide)]
        simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
        exact hsp.symm
      · intro r hr' hn
        rw [get_of_calleeSaved hsaved hr']
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl <;> simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
            at hn ⊢
    rv_exec_cut 105
    refine ex_epi base x m hr x2 m2 hF2 ?_
    rw [hval, hone, hB, hE, Nat.one_mul]

end IntxRV.Api
