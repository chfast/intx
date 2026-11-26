import IntxRV.Div512
import IntxRV.Api.submul
import IntxRV.Gen.Api.udivrem_knuth_normalized
/-!
# The blocks of `internal::udivrem_knuth_normalized()` with a dynamic size of d

The code divides a digit in a block from the test of the overflow at 85 to the store of the
quotient digit at 153, as `udivrem_knuth_normalized<3>()` does (`IntxRV/Knuth3.lean`), with
loops over the n words of d: the inlined `udivrem_3by2()` of the top 3 words of the partial
remainder by the top 2 words of d (`kn_div`), then the inlined subtraction of the multiple of the
low n - 2 words of d (`kn_sub_loop`), of the top 2 words, and the add-back loop (`kn_add_loop`)
when it borrows (`kn_normal`, by `kn_digit_nat`). If the top 2 words of the remainder are the top
2 words of d, the digit is `2^64 - 1` by the call of `submul()` (`kn_over`, `kn_overflow`).

The loop runs from its head at 85 by `Reach.loop` with the invariant `knHead`; `kn_tail` runs a
digit from the store of the quotient digit to the next head, or for the last digit to the epilogue
(`kn_exit`), and `kn_loop` routes the overflow and the division to it. The frame is `KNFrame`: ra
and s0 to s11 saved in 144 bytes below sp, and the memory outside q, u and the frame unchanged.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- The registers that the inlined `submul()` of `udivrem_knuth_normalized()` changes. -/
def knSubCl : List (BitVec 5) := [5#5, 6#5, 7#5, 16#5, 17#5, 28#5, 29#5, 30#5, 31#5]

/-- The state at the head of the loop of the inlined `submul()` of `udivrem_knuth_normalized()`,
at 129, from the registers `x0` and the memory `m0` at its start: after `i` of the `n` words of
the divisor at `dp`, subtracted times `q` from the words at `wp`, with the high word in a6 and the
borrow in a7. -/
def knSubLoop (x0 : Regs) (m0 : Mem) (dp wp : BitVec 64) (n : Nat) (q : BitVec 64) (k : Nat)
    (x' : Regs) (m' : Mem) : Prop :=
  ∃ i, i < n ∧ k = n - i ∧
    x'.get 6#5 = dp + BitVec.ofNat 64 (8 * i) ∧ x'.get 7#5 = wp + BitVec.ofNat 64 (8 * i) ∧
    x'.get 5#5 = wp + BitVec.ofNat 64 (8 * n) ∧ x'.get 18#5 = q ∧ (x'.get 17#5).toNat ≤ 1 ∧
    words m' wp i + q.toNat * words m0 dp i =
      words m0 wp i + ((x'.get 16#5).toNat + (x'.get 17#5).toNat) * 2 ^ (64 * i) ∧
    UnchangedExcept m0 m' wp (8 * i) ∧
    x' 0 = x0 0 ∧ ∀ r, r ∉ knSubCl → x' r = x0 r

/-- The state after the loop of the inlined `submul()`, at 145. -/
def knSubExit (x0 : Regs) (m0 : Mem) (dp wp : BitVec 64) (n : Nat) (q : BitVec 64)
    (x' : Regs) (m' : Mem) : Prop :=
  x'.get 18#5 = q ∧ (x'.get 17#5).toNat ≤ 1 ∧
    words m' wp n + q.toNat * words m0 dp n =
      words m0 wp n + ((x'.get 16#5).toNat + (x'.get 17#5).toNat) * 2 ^ (64 * n) ∧
    UnchangedExcept m0 m' wp (8 * n) ∧
    x' 0 = x0 0 ∧ ∀ r, r ∉ knSubCl → x' r = x0 r

/-- The loop of the inlined `submul()` of `udivrem_knuth_normalized()` from 129, with the run from
its end at 145. -/
theorem kn_sub_loop {A : List (BitVec 64)} {hi : BitVec 20} {lo : BitVec 12} {base tgt : BitVec 64}
    {Q : Regs → Mem → Prop} (x0 : Regs) (m0 : Mem) (dp wp : BitVec 64) (n : Nat) (q : BitVec 64)
    (hn : 8 * n < 2 ^ 64) (hdn : dp.toNat + 8 * n ≤ 2 ^ 64) (hwn : wp.toNat + 8 * n ≤ 2 ^ 64)
    (hdis : dp.toNat + 8 * n ≤ wp.toNat ∨ wp.toNat + 8 * n ≤ dp.toNat)
    (hdA : ∀ i < n, dp + BitVec.ofNat 64 (8 * i) ∈ A)
    (hwA : ∀ i < n, wp + BitVec.ofNat 64 (8 * i) ∈ A)
    (hk : ∀ x' m', knSubExit x0 m0 dp wp n q x' m' →
      Reach A (udivrem_knuth_normalized_progAt hi lo) base (pcAt base 145) x' m' tgt Q) :
    ∀ k x' m', knSubLoop x0 m0 dp wp n q k x' m' →
      Reach A (udivrem_knuth_normalized_progAt hi lo) base (pcAt base 129) x' m' tgt Q := by
  apply Reach.loop (knSubLoop x0 m0 dp wp n q)
  intro k x' m' ⟨i, hi, hk', h6, h7, h5, h18, h17, hw, hun, h0, hcl⟩ ih
  subst hk'
  have hi8 : 8 * i < 2 ^ 64 := by omega
  have hd8 : (dp + BitVec.ofNat 64 (8 * i)).toNat = dp.toNat + 8 * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi8]; omega
  have hw8 : (wp + BitVec.ofNat 64 (8 * i)).toNat = wp.toNat + 8 * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi8]; omega
  -- d[i]
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd, BitVec.reduceSignExtend, BitVec.add_zero]
  refine ⟨by rw [h6]; exact hdA i hi, fun wy hwy => ?_⟩
  -- u[i]
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd, BitVec.reduceSignExtend, BitVec.add_zero]
  rv_val
  refine ⟨by rw [h7]; exact hwA i hi, fun wx hwx => ?_⟩
  rv_exec_cut 140
  rename_i t0 ht0 ph hph t1 ht1 c hc k' hk' d hd e he r hr' f hf
  have hm := defn_mul_mulhu ht0 hph
  have hcar := defn_carry_left ht1 hc
  have hkn : k'.toNat = c.toNat + ph.toNat :=
    defn_add_exact hk' (by have := defn_mulhu_le hph; have := defn_bit hc; omega)
  have hwy' : wy = memWord m0 (dp + BitVec.ofNat 64 (8 * i)).toNat := by
    rw [hwy.eq, h6, memWord_of_unchangedExcept hun _ (by rw [hd8]; omega)]
  have hwx' : wx = memWord m0 (wp + BitVec.ofNat 64 (8 * i)).toNat := by
    rw [hwx.eq, h7, memWord_of_unchangedExcept hun _ (by rw [hw8]; omega)]
  rw [h18] at hm
  -- The words after the store of u[i].
  have hR : ∀ v : BitVec 64, words (memStore m' (x'.get 7#5).toNat v) wp (i + 1) =
      words m' wp i + 2 ^ (64 * i) * v.toNat := by
    intro v
    rw [words_succ_top, words_memStore_of_disjoint _ _ _ _ _ (by omega) (by rw [h7, hw8]; omega),
      h7, memWord_memStore_self]
  have hun' : ∀ v : BitVec 64, UnchangedExcept m0 (memStore m' (x'.get 7#5).toNat v)
      wp (8 * (i + 1)) := by
    intro v
    rw [unchangedExcept_memStore _ _ (by rw [h7, hw8]; omega)]
    exact fun k hk => hun k (by omega)
  have hp8 : ∀ a : BitVec 64, a + BitVec.ofNat 64 (8 * i) + 8#64 =
      a + BitVec.ofNat 64 (8 * (i + 1)) := by
    intro a
    rw [BitVec.add_assoc]; congr 1
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  -- The sum of the words after the word i, with the borrow b' of its subtraction.
  have hnext : ∀ b', Defn b' (e ||| f) → b'.toNat ≤ 1 ∧
      words (memStore m' (x'.get 7#5).toNat r) wp (i + 1) + q.toNat * words m0 dp (i + 1) =
      words m0 wp (i + 1) + (k'.toNat + b'.toNat) * 2 ^ (64 * (i + 1)) := by
    intro b' hb'
    have hs := defn_sub_borrow hd he hr' hf hb' h17
    refine ⟨hs.2, ?_⟩
    rw [hR, words_succ_top m0 i dp, words_succ_top m0 i wp, ← hwy', ← hwx',
      show 64 * (i + 1) = 64 * i + 64 by ring, pow_add]
    exact submul_step hm hcar hkn hs.1 hw
  -- The store of u[i].
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd, BitVec.reduceSignExtend, BitVec.add_zero]
  rv_val
  refine ⟨by rw [h7]; exact hwA i hi, ?_⟩
  rv_exec_cut 129 145
  all_goals
    rename_i b' hb' hb
    obtain ⟨hb1, hwords⟩ := hnext b' hb'
  · -- The next word.
    have hi1 : i + 1 < n := by
      rcases Nat.lt_or_ge (i + 1) n with h | h
      · exact h
      · exfalso; apply hb
        rw [h7, h5, hp8, show i + 1 = n by omega]
    refine ih (n - (i + 1)) (by omega) _ _ ?_
    refine ⟨i + 1, hi1, rfl, ?_, ?_, ?_, ?_, ?_, ?_, hun' r, ?_, ?_⟩
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · rw [h6, hp8]
    · rw [h7, hp8]
    · exact h5
    · exact h18
    · exact hb1
    · exact hwords
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]; exact h0
    · intro rr hrr
      have hrr' := hrr
      simp only [knSubCl, List.mem_cons, List.not_mem_nil, or_false, not_or] at hrr'
      obtain ⟨h5', h6', h7', h16', h17', h28', h29', h30', h31'⟩ := hrr'
      simp (config := { decide := true }) only [Regs.set_apply, h5', h6', h7', h16', h17', h28',
        h29', h30', h31', ↓reduceIte]
      exact hcl rr hrr
  · -- The last word: the end of the loop.
    have hin : i + 1 = n := by
      have := congrArg BitVec.toNat hb
      rw [h7, h5, hp8] at this
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
      omega
    refine hk _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · exact h18
    · exact hb1
    · rw [← hin]; exact hwords
    · rw [← hin]; exact hun' r
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]; exact h0
    · intro rr hrr
      have hrr' := hrr
      simp only [knSubCl, List.mem_cons, List.not_mem_nil, or_false, not_or] at hrr'
      obtain ⟨h5', h6', h7', h16', h17', h28', h29', h30', h31'⟩ := hrr'
      simp (config := { decide := true }) only [Regs.set_apply, h5', h6', h7', h16', h17', h28',
        h29', h30', h31', ↓reduceIte]
      exact hcl rr hrr

/-- The registers that the add-back loop of `udivrem_knuth_normalized()` changes. -/
def knAddCl : List (BitVec 5) := [5#5, 12#5, 15#5, 16#5, 17#5]

/-- A bit masked by 1. -/
theorem and_one_of_le {c : BitVec 64} (h : c.toNat ≤ 1) : (c &&& 1#64).toNat = c.toNat := by
  have : c = 0#64 ∨ c = 1#64 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h0 | h1
    · exact Or.inl (BitVec.eq_of_toNat_eq (by simpa using h0))
    · exact Or.inr (BitVec.eq_of_toNat_eq (by simpa using h1))
  rcases this with rfl | rfl <;> rfl

/-- One word of the addition of the add-back loop: the sum of the words after `i + 1` words. -/
theorem add_step {R X Y k wx wy n co P : Nat} (hs : n + 2 ^ 64 * co = wx + wy + k)
    (hinv : R + P * k = X + Y) :
    R + P * n + P * 2 ^ 64 * co = (X + P * wx) + (Y + P * wy) := by
  have e : P * n + P * 2 ^ 64 * co = P * (wx + wy + k) := by rw [← hs]; ring
  calc R + P * n + P * 2 ^ 64 * co = R + P * (wx + wy + k) := by rw [Nat.add_assoc, e]
    _ = (R + P * k) + P * wx + P * wy := by ring
    _ = _ := by rw [hinv]; ring

/-- The state at the head of the add-back loop of `udivrem_knuth_normalized()`, at 192, from the
registers `x0` and the memory `m0` at its start: after `i` of the `n` words of the divisor at `dp`
added to the words at `wp`, with the carry in a6. -/
def knAddLoop (x0 : Regs) (m0 : Mem) (dp wp : BitVec 64) (n : Nat) (k : Nat)
    (x' : Regs) (m' : Mem) : Prop :=
  ∃ i, i < n ∧ k = n - i ∧
    x'.get 12#5 = wp + BitVec.ofNat 64 (8 * i) ∧ x'.get 15#5 = dp + BitVec.ofNat 64 (8 * i) ∧
    x'.get 1#5 = dp + BitVec.ofNat 64 (8 * n) ∧ (x'.get 16#5).toNat ≤ 1 ∧
    words m' wp i + 2 ^ (64 * i) * (x'.get 16#5).toNat = words m0 wp i + words m0 dp i ∧
    UnchangedExcept m0 m' wp (8 * i) ∧
    x' 0 = x0 0 ∧ ∀ r, r ∉ knAddCl → x' r = x0 r

/-- The state after the add-back loop, at 204. -/
def knAddExit (x0 : Regs) (m0 : Mem) (dp wp : BitVec 64) (n : Nat) (x' : Regs) (m' : Mem) :
    Prop :=
  (x'.get 16#5).toNat ≤ 1 ∧
    words m' wp n + 2 ^ (64 * n) * (x'.get 16#5).toNat = words m0 wp n + words m0 dp n ∧
    UnchangedExcept m0 m' wp (8 * n) ∧
    x' 0 = x0 0 ∧ ∀ r, r ∉ knAddCl → x' r = x0 r

/-- The add-back loop of `udivrem_knuth_normalized()` from 192, with the run from its end at
204. -/
theorem kn_add_loop {A : List (BitVec 64)} {hi : BitVec 20} {lo : BitVec 12} {base tgt : BitVec 64}
    {Q : Regs → Mem → Prop} (x0 : Regs) (m0 : Mem) (dp wp : BitVec 64) (n : Nat)
    (hn : 8 * n < 2 ^ 64) (hdn : dp.toNat + 8 * n ≤ 2 ^ 64) (hwn : wp.toNat + 8 * n ≤ 2 ^ 64)
    (hdis : dp.toNat + 8 * n ≤ wp.toNat ∨ wp.toNat + 8 * n ≤ dp.toNat)
    (hdA : ∀ i < n, dp + BitVec.ofNat 64 (8 * i) ∈ A)
    (hwA : ∀ i < n, wp + BitVec.ofNat 64 (8 * i) ∈ A)
    (hk : ∀ x' m', knAddExit x0 m0 dp wp n x' m' →
      Reach A (udivrem_knuth_normalized_progAt hi lo) base (pcAt base 204) x' m' tgt Q) :
    ∀ k x' m', knAddLoop x0 m0 dp wp n k x' m' →
      Reach A (udivrem_knuth_normalized_progAt hi lo) base (pcAt base 192) x' m' tgt Q := by
  apply Reach.loop (knAddLoop x0 m0 dp wp n)
  intro k x' m' ⟨i, hi, hk', h12, h15, h1, h16, hw, hun, h0, hcl⟩ ih
  subst hk'
  have hi8 : 8 * i < 2 ^ 64 := by omega
  have hd8 : (dp + BitVec.ofNat 64 (8 * i)).toNat = dp.toNat + 8 * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi8]; omega
  have hw8 : (wp + BitVec.ofNat 64 (8 * i)).toNat = wp.toNat + 8 * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi8]; omega
  -- u[i]
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd, BitVec.reduceSignExtend, BitVec.add_zero]
  refine ⟨by rw [h12]; exact hwA i hi, fun wu hwu => ?_⟩
  -- d[i]
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd, BitVec.reduceSignExtend, BitVec.add_zero]
  rv_val
  refine ⟨by rw [h15]; exact hdA i hi, fun wd hwd => ?_⟩
  rv_exec_cut 200
  rename_i s hs e he nn hnn f hf
  have hwu' : wu = memWord m0 (wp + BitVec.ofNat 64 (8 * i)).toNat := by
    rw [hwu.eq, h12, memWord_of_unchangedExcept hun _ (by rw [hw8]; omega)]
  have hwd' : wd = memWord m0 (dp + BitVec.ofNat 64 (8 * i)).toNat := by
    rw [hwd.eq, h15, memWord_of_unchangedExcept hun _ (by rw [hd8]; omega)]
  have hc1 := and_one_of_le h16
  have hR : ∀ v : BitVec 64, words (memStore m' (x'.get 12#5).toNat v) wp (i + 1) =
      words m' wp i + 2 ^ (64 * i) * v.toNat := by
    intro v
    rw [words_succ_top, words_memStore_of_disjoint _ _ _ _ _ (by omega) (by rw [h12, hw8]; omega),
      h12, memWord_memStore_self]
  have hun' : ∀ v : BitVec 64, UnchangedExcept m0 (memStore m' (x'.get 12#5).toNat v)
      wp (8 * (i + 1)) := by
    intro v
    rw [unchangedExcept_memStore _ _ (by rw [h12, hw8]; omega)]
    exact fun k hk => hun k (by omega)
  have hp8 : ∀ a : BitVec 64, a + BitVec.ofNat 64 (8 * i) + 8#64 =
      a + BitVec.ofNat 64 (8 * (i + 1)) := by
    intro a
    rw [BitVec.add_assoc]; congr 1
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hnext : ∀ co, Defn co (e ||| f) → co.toNat ≤ 1 ∧
      words (memStore m' (x'.get 12#5).toNat nn) wp (i + 1) + 2 ^ (64 * (i + 1)) * co.toNat =
      words m0 wp (i + 1) + words m0 dp (i + 1) := by
    intro co hco
    obtain ⟨hs', hco1⟩ := defn_add_carry hs he hnn hf hco (by rw [hc1]; exact h16)
    rw [hc1] at hs'
    refine ⟨hco1, ?_⟩
    rw [hR, words_succ_top m0 i wp, words_succ_top m0 i dp, ← hwu', ← hwd',
      show 64 * (i + 1) = 64 * i + 64 by ring, pow_add]
    exact add_step hs' hw
  -- The store of u[i].
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd, BitVec.reduceSignExtend, BitVec.add_zero]
  rv_val
  refine ⟨by rw [h12]; exact hwA i hi, ?_⟩
  rv_exec_cut 192 204
  all_goals
    rename_i co hco hb
    obtain ⟨hco1, hwords⟩ := hnext co hco
  · -- The next word.
    have hi1 : i + 1 < n := by
      rcases Nat.lt_or_ge (i + 1) n with h | h
      · exact h
      · exfalso; apply hb
        rw [h15, h1, hp8, show i + 1 = n by omega]
    refine ih (n - (i + 1)) (by omega) _ _ ?_
    refine ⟨i + 1, hi1, rfl, ?_, ?_, ?_, ?_, ?_, hun' nn, ?_, ?_⟩
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · rw [h12, hp8]
    · rw [h15, hp8]
    · exact h1
    · exact hco1
    · exact hwords
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]; exact h0
    · intro rr hrr
      have hrr' := hrr
      simp only [knAddCl, List.mem_cons, List.not_mem_nil, or_false, not_or] at hrr'
      obtain ⟨h5', h12', h15', h16', h17'⟩ := hrr'
      simp (config := { decide := true }) only [Regs.set_apply, h5', h12', h15', h16', h17',
        ↓reduceIte]
      exact hcl rr hrr
  · -- The last word: the end of the loop.
    have hin : i + 1 = n := by
      have := congrArg BitVec.toNat hb
      rw [h15, h1, hp8] at this
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
      omega
    refine hk _ _ ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · exact hco1
    · rw [← hin]; exact hwords
    · rw [← hin]; exact hun' nn
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]; exact h0
    · intro rr hrr
      have hrr' := hrr
      simp only [knAddCl, List.mem_cons, List.not_mem_nil, or_false, not_or] at hrr'
      obtain ⟨h5', h12', h15', h16', h17'⟩ := hrr'
      simp (config := { decide := true }) only [Regs.set_apply, h5', h12', h15', h16', h17',
        ↓reduceIte]
      exact hcl rr hrr

/-- The inlined `udivrem_3by2()` of `udivrem_knuth_normalized()`, from 93 to 122 (with the
correction at 182): `a6:a5:a2` by `s4:s3` with the reciprocal in s7, to the quotient in s2 and the
remainder in `a5:a2`. -/
theorem kn_div {A : List (BitVec 64)} {hi : BitVec 20} {lo : BitVec 12} (base : BitVec 64)
    (x : Regs) (m : Mem)
    (hd : 2 ^ 127 ≤ (x.get 19#5).toNat + 2 ^ 64 * (x.get 20#5).toNat)
    (hu : (x.get 16#5).toNat * 2 ^ 64 + (x.get 15#5).toNat <
      (x.get 19#5).toNat + 2 ^ 64 * (x.get 20#5).toNat)
    (hv : (x.get 23#5).toNat =
      (2 ^ 192 - 1) / ((x.get 19#5).toNat + 2 ^ 64 * (x.get 20#5).toNat) - 2 ^ 64) :
    Reach A (udivrem_knuth_normalized_progAt hi lo) base (pcAt base 93) x m (pcAt base 122)
      (fun x' m' => m' = m ∧ Div3Out x x' ((x.get 16#5).toNat * 2 ^ 128 +
        (x.get 15#5).toNat * 2 ^ 64 + (x.get 12#5).toNat)
        ((x.get 19#5).toNat + 2 ^ 64 * (x.get 20#5).toNat) 18#5 12#5 15#5
        [5#5, 6#5, 12#5, 15#5, 16#5, 17#5, 18#5]) := by
  by2_div3_paths div3by2BVo_spec true (x.get 16#5) (x.get 15#5) (x.get 12#5) (x.get 19#5)
    (x.get 20#5) (x.get 23#5) hd hu hv

/-- The frame of `udivrem_knuth_normalized()` after its prologue: sp 144 bytes lower, ra and s0 to
s11 saved, and the memory outside q, u and the frame unchanged. -/
def KNFrame (x : Regs) (m : Mem) (x' : Regs) (m' : Mem) : Prop :=
  x'.get 2#5 = x.get 2#5 + 18446744073709551472#64 ∧
  memWord m' (x.get 2#5 + 18446744073709551608#64).toNat = x.get 1#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551600#64).toNat = x.get 8#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551592#64).toNat = x.get 9#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551584#64).toNat = x.get 18#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551576#64).toNat = x.get 19#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551568#64).toNat = x.get 20#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551560#64).toNat = x.get 21#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551552#64).toNat = x.get 22#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551544#64).toNat = x.get 23#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551536#64).toNat = x.get 24#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551528#64).toNat = x.get 25#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551520#64).toNat = x.get 26#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551512#64).toNat = x.get 27#5 ∧
  UnchangedExcept3 m m' (x.get 10#5) (8 * ((x.get 12#5).toNat - (x.get 14#5).toNat)) (x.get 11#5)
    (8 * (x.get 12#5).toNat) (x.get 2#5 - 144#64) 144 ∧
  ∀ r ∈ calleeSaved, r ∉ [2#5, 8#5, 9#5, 18#5, 19#5, 20#5, 21#5, 22#5, 23#5, 24#5, 25#5, 26#5,
    27#5] → x'.get r = x.get r

/-- The epilogue of `udivrem_knuth_normalized()` at 206: the registers restored from the frame and
the return. -/
theorem kn_exit {hi : BitVec 20} {lo : BitVec 12} {Dt : List (BitVec 64)} (base : BitVec 64)
    (x : Regs) (m : Mem) (hr : x.get 1#5 &&& 3 = 0) (x4 : Regs) (m4 : Mem)
    (hF : KNFrame x m x4 m4)
    (hq : words m4 (x.get 10#5) ((x.get 12#5).toNat - (x.get 14#5).toNat) =
      words m (x.get 11#5) (x.get 12#5).toNat / words m (x.get 13#5) (x.get 14#5).toNat)
    (hu : words m4 (x.get 11#5) (x.get 12#5).toNat % 2 ^ (64 * (x.get 14#5).toNat) =
      words m (x.get 11#5) (x.get 12#5).toNat % words m (x.get 13#5) (x.get 14#5).toNat) :
    Reach (bufWords (x.get 13#5) (x.get 14#5).toNat ++
        bufWords (x.get 10#5) ((x.get 12#5).toNat - (x.get 14#5).toNat) ++
        bufWords (x.get 11#5) (x.get 12#5).toNat ++ bufWords (x.get 2#5 - 144#64) 18 ++ Dt)
      (udivrem_knuth_normalized_progAt hi lo) base (pcAt base 206) x4 m4 (x.get 1#5)
      (udivrem_knuth_normalized.post x m) := by
  obtain ⟨hsp, hfra, hfs0, hfs1, hfs2, hfs3, hfs4, hfs5, hfs6, hfs7, hfs8, hfs9, hfs10, hfs11,
    hunF, hcsF⟩ := hF
  rw [← regs_set_of_get' (by decide) hsp]
  rv_exec
  rename_i wra hwra ws0 hws0 ws1 hws1 ws2 hws2 ws3 hws3 ws4 hws4 ws5 hws5 ws6 hws6 ws7 hws7
    ws8 hws8 ws9 hws9 ws10 hws10 ws11 hws11
  rw [hfra] at hwra
  rw [hfs0] at hws0
  rw [hfs1] at hws1
  rw [hfs2] at hws2
  rw [hfs3] at hws3
  rw [hfs4] at hws4
  rw [hfs5] at hws5
  rw [hfs6] at hws6
  rw [hfs7] at hws7
  rw [hfs8] at hws8
  rw [hfs9] at hws9
  rw [hfs10] at hws10
  rw [hfs11] at hws11
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.reduceSignExtend,
    BitVec.add_zero]
  rw [hwra.eq, update_aligned hr]
  refine Reach.refl ?_
  simp only [udivrem_knuth_normalized.post]
  simp (disch := decide) only [Regs.eq_get x]
  refine ⟨hq, hu, hunF, ?_⟩
  intro r hr'
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
  all_goals first
    | exact (Regs.eq_get x (by decide)).symm
    | (rw [Regs.eq_get x4 (by decide), Regs.eq_get x (by decide)]
       exact hcsF _ (by decide) (by decide))
    | (rw [Regs.eq_get x (by decide)]
       first
         | exact hws0 | exact hws1 | exact hws2 | exact hws3 | exact hws4 | exact hws5
         | exact hws6 | exact hws7 | exact hws8 | exact hws9 | exact hws10 | exact hws11)

/-- The registers and the memory at the head of the loop of `udivrem_knuth_normalized()` at 85
for the digit `j` of u: `j` in a2, the pointer to u[j] in s6, the count of the digits done in s1,
the pointers to q, u and d, the end of d in ra, the top words of the divisor in s3 and s4 and its
reciprocal in s7, u - 8 in s5 and `8 u.size() - 24` in s8, the top words u[j + n - 1] and
u[j + n] of the partial remainder in a5 and a6, the words of u up to j unchanged, and the quotient
and the remainder of the digits of u above j by d. -/
def knHead (x : Regs) (m : Mem) (j : Nat) (x' : Regs) (m' : Mem) : Prop :=
  j + (x.get 14#5).toNat + 1 ≤ (x.get 12#5).toNat ∧ KNFrame x m x' m' ∧
  x'.get 12#5 = BitVec.ofNat 64 j ∧ x'.get 22#5 = x.get 11#5 + BitVec.ofNat 64 (8 * j) ∧
  x'.get 9#5 = BitVec.ofNat 64 ((x.get 12#5).toNat - (x.get 14#5).toNat - 1 - j) ∧
  x'.get 10#5 = x.get 10#5 ∧ x'.get 11#5 = x.get 11#5 ∧ x'.get 13#5 = x.get 13#5 ∧
  x'.get 14#5 = x.get 14#5 ∧
  x'.get 1#5 = x.get 13#5 + BitVec.ofNat 64 (8 * (x.get 14#5).toNat) ∧
  x'.get 19#5 = memWord m (x.get 13#5 + BitVec.ofNat 64 (8 * ((x.get 14#5).toNat - 2))).toNat ∧
  x'.get 20#5 = memWord m (x.get 13#5 + BitVec.ofNat 64 (8 * ((x.get 14#5).toNat - 1))).toNat ∧
  x'.get 21#5 = x.get 11#5 + 18446744073709551608#64 ∧
  x'.get 24#5 = BitVec.ofNat 64 (8 * (x.get 12#5).toNat - 24) ∧
  (x'.get 23#5).toNat =
    (2 ^ 192 - 1) / ((x'.get 19#5).toNat + 2 ^ 64 * (x'.get 20#5).toNat) - 2 ^ 64 ∧
  x'.get 15#5 = memWord m' (x.get 11#5 +
    BitVec.ofNat 64 (8 * (j + (x.get 14#5).toNat - 1))).toNat ∧
  x'.get 16#5 = memWord m' (x.get 11#5 + BitVec.ofNat 64 (8 * (j + (x.get 14#5).toNat))).toNat ∧
  (∀ k, k ≤ j → memWord m' (x.get 11#5 + BitVec.ofNat 64 (8 * k)).toNat =
    memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * k)).toNat) ∧
  words m' (x.get 10#5 + BitVec.ofNat 64 (8 * (j + 1)))
      ((x.get 12#5).toNat - (x.get 14#5).toNat - 1 - j) *
      words m (x.get 13#5) (x.get 14#5).toNat +
    words m' (x.get 11#5 + BitVec.ofNat 64 (8 * (j + 1))) (x.get 14#5).toNat =
    words m (x.get 11#5) (x.get 12#5).toNat / 2 ^ (64 * (j + 1)) ∧
  words m' (x.get 11#5 + BitVec.ofNat 64 (8 * (j + 1))) (x.get 14#5).toNat <
    words m (x.get 13#5) (x.get 14#5).toNat

/-- The frame of `udivrem_knuth_normalized()` after a change of words of q and u and of the spill
words below the saved registers. -/
theorem KNFrame.step {x : Regs} {m : Mem} {x' x'' : Regs} {m' m'' : Mem}
    (hpre : udivrem_knuth_normalized.pre x m) (hF : KNFrame x m x' m')
    (h2 : UnchangedExcept3 m' m'' (x.get 10#5) (8 * ((x.get 12#5).toNat - (x.get 14#5).toNat))
      (x.get 11#5) (8 * (x.get 12#5).toNat) (x.get 2#5 - 144#64) 40)
    (hsp : x''.get 2#5 = x'.get 2#5)
    (hcs : ∀ r ∈ calleeSaved, r ∉ [2#5, 8#5, 9#5, 18#5, 19#5, 20#5, 21#5, 22#5, 23#5, 24#5, 25#5,
      26#5, 27#5] → x''.get r = x'.get r) :
    KNFrame x m x'' m'' := by
  simp only [udivrem_knuth_normalized.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨-, -, -, -, -, -, ⟨-, hsn⟩, -, hdsq, hdsu, -⟩ := hpre
  obtain ⟨hsp', h1, h8, h9, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, hun, hcs'⟩ := hF
  have hf : ∀ c : Nat, 40 ≤ c → c < 144 → c % 8 = 0 →
      memWord m'' (x.get 2#5 - 144#64 + BitVec.ofNat 64 c).toNat =
        memWord m' (x.get 2#5 - 144#64 + BitVec.ofNat 64 c).toNat := by
    intro c hc1 hc2 _
    have : (x.get 2#5 - 144#64 + BitVec.ofNat 64 c).toNat = (x.get 2#5 - 144#64).toNat + c :=
      toNat_add8 _ _ (by omega) (by omega)
    exact memWord_of_unchangedExcept3 h2 _ (by rw [this]; omega) (by rw [this]; omega)
      (by rw [this]; omega)
  have e : ∀ c : BitVec 64, x.get 2#5 + c =
      x.get 2#5 - 144#64 + BitVec.ofNat 64 (c + 144#64).toNat := by
    intro c; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub,
      BitVec.toNat_ofNat]; omega
  refine ⟨hsp.trans hsp', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e, hf _ (by decide) (by decide) (by decide), ← e]; exact h1
  · rw [e, hf _ (by decide) (by decide) (by decide), ← e]; exact h8
  · rw [e, hf _ (by decide) (by decide) (by decide), ← e]; exact h9
  · rw [e, hf _ (by decide) (by decide) (by decide), ← e]; exact h18
  · rw [e, hf _ (by decide) (by decide) (by decide), ← e]; exact h19
  · rw [e, hf _ (by decide) (by decide) (by decide), ← e]; exact h20
  · rw [e, hf _ (by decide) (by decide) (by decide), ← e]; exact h21
  · rw [e, hf _ (by decide) (by decide) (by decide), ← e]; exact h22
  · rw [e, hf _ (by decide) (by decide) (by decide), ← e]; exact h23
  · rw [e, hf _ (by decide) (by decide) (by decide), ← e]; exact h24
  · rw [e, hf _ (by decide) (by decide) (by decide), ← e]; exact h25
  · rw [e, hf _ (by decide) (by decide) (by decide), ← e]; exact h26
  · rw [e, hf _ (by decide) (by decide) (by decide), ← e]; exact h27
  · intro k hq hu hs
    rw [h2 k hq hu (by omega)]; exact hun k hq hu hs
  · intro r hr hnr
    rw [hcs r hr hnr]; exact hcs' r hr hnr

/-- The address `8 k + (u - 8)` of the word `k - 1` of u. -/
theorem kn_addr_m8 (u : BitVec 64) (k : Nat) (h1 : 1 ≤ k) (h : u.toNat + 8 * k ≤ 2 ^ 64) :
    u + (18446744073709551608#64 + BitVec.ofNat 64 (8 * k)) = u + BitVec.ofNat 64 (8 * (k - 1)) := by
  bv_omega

/-- The address of the word `k - 2` of u from the word `k`. -/
theorem kn_addr_m16 (u : BitVec 64) (k : Nat) (h2 : 2 ≤ k) (h : u.toNat + 8 * k ≤ 2 ^ 64) :
    u + (BitVec.ofNat 64 (8 * k) + 18446744073709551600#64) = u + BitVec.ofNat 64 (8 * (k - 2)) := by
  bv_omega

/-- The memory after a digit of `udivrem_knuth_normalized()`: the remainder words of u, the spill
words of the frame and q[j] changed. -/
theorem kn_step_unchanged {m' m3 : Mem} {w s q u : BitVec 64} {lw lq lu : Nat} (v : BitVec 64)
    (qj : Nat) (hm3 : UnchangedExcept2 m' m3 w lw s 40)
    (hw : u.toNat ≤ w.toNat ∧ w.toNat + lw ≤ u.toNat + lu)
    (hq : q.toNat ≤ qj ∧ qj + 8 ≤ q.toNat + lq) :
    UnchangedExcept3 m' (memStore m3 qj v) q lq u lu s 40 := by
  intro k hkq hku hks
  rw [getElem?_memStore_of_ne _ _ _ _ (by omega)]
  exact hm3 k (by omega) hks

theorem ofNat_add1 (a : Nat) (h : a + 1 < 2 ^ 64) :
    BitVec.ofNat 64 a + 1#64 = BitVec.ofNat 64 (a + 1) := by
  bv_omega

/-- The registers that the step of a digit keeps from the head for the tail. -/
def knKept : List (BitVec 5) :=
  [1#5, 2#5, 3#5, 4#5, 9#5, 10#5, 11#5, 13#5, 14#5, 19#5, 20#5, 21#5, 22#5, 23#5, 24#5]

/-- From 153, after the digit `j` with the quotient digit in s2 and the remainder in u[j..j+n), to
the head of the loop for the digit `j - 1`, or for `j = 0` to the return. -/
theorem kn_tail {hi : BitVec 20} {lo : BitVec 12} {Dt : List (BitVec 64)} (base : BitVec 64)
    (x : Regs) (m : Mem) (hr : x.get 1#5 &&& 3 = 0) (hpre : udivrem_knuth_normalized.pre x m)
    (j : Nat) (x' : Regs) (m' : Mem) (hh : knHead x m j x' m') (x3 : Regs) (m3 : Mem)
    (h3 : ∀ r ∈ knKept, x3.get r = x'.get r)
    (h8 : x3.get 8#5 = BitVec.ofNat 64 (8 * j)) (h25 : x3.get 25#5 = BitVec.ofNat 64 j)
    (h26 : x3.get 26#5 = x.get 11#5 + BitVec.ofNat 64 (8 * (j + (x.get 14#5).toNat)))
    (h27 : x3.get 27#5 = BitVec.ofNat 64 (8 * (j + (x.get 14#5).toNat)))
    (hm3 : UnchangedExcept2 m' m3 (x.get 11#5 + BitVec.ofNat 64 (8 * j)) (8 * (x.get 14#5).toNat)
      (x.get 2#5 - 144#64) 40)
    (hdig : (x3.get 18#5).toNat * words m (x.get 13#5) (x.get 14#5).toNat +
        words m3 (x.get 11#5 + BitVec.ofNat 64 (8 * j)) (x.get 14#5).toNat =
      words m' (x.get 11#5 + BitVec.ofNat 64 (8 * j)) ((x.get 14#5).toNat + 1))
    (hlt : words m3 (x.get 11#5 + BitVec.ofNat 64 (8 * j)) (x.get 14#5).toNat <
      words m (x.get 13#5) (x.get 14#5).toNat)
    (ih : ∀ k < j, ∀ x' m', knHead x m k x' m' →
      Reach (udivrem_knuth_normalized.bufs x ++ Dt) (udivrem_knuth_normalized_progAt hi lo)
        base (pcAt base 85) x' m' (x.get 1#5) (udivrem_knuth_normalized.post x m)) :
    Reach (udivrem_knuth_normalized.bufs x ++ Dt) (udivrem_knuth_normalized_progAt hi lo)
      base (pcAt base 153) x3 m3 (x.get 1#5) (udivrem_knuth_normalized.post x m) := by
  obtain ⟨hjn, hF, h12, h22, h9, h10, h11, h13, h14, h1, h19, h20, h21, h24, h23, h15, h16, hlow,
    hQR, hRD⟩ := hh
  have hF0 := hF
  have hpre' := hpre
  simp only [udivrem_knuth_normalized.pre, Buf, Disjoint] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hqa, hqn⟩, ⟨hua, hun⟩, ⟨hda, hdn⟩, hdqd, hdqu, hdud, ⟨hsa, hsn⟩, hdsd, hdsq, hdsu,
    hn3, hnu, hD, hU⟩ := hpre'
  have k21 := h3 21#5 (by decide)
  have k10 := h3 10#5 (by decide)
  rw [h21] at k21
  rw [h10] at k10
  simp only [udivrem_knuth_normalized.bufs]
  simp (disch := decide) only [Regs.eq_get x]
  rw [← regs_set_of_get' (by decide) h8, ← regs_set_of_get' (by decide) h25,
    ← regs_set_of_get' (by decide) h26, ← regs_set_of_get' (by decide) h27,
    ← regs_set_of_get' (by decide) k21, ← regs_set_of_get' (by decide) k10]
  rv_exec_cut 155
  rename_i a27 ha27 a8 ha8
  have hus : 8 * (x.get 12#5).toNat < 2 ^ 64 := by omega
  have e27 : a27 = x.get 11#5 + BitVec.ofNat 64 (8 * (j + (x.get 14#5).toNat - 1)) := by
    rw [ha27.eq]; exact kn_addr_m8 _ _ (by omega) (by omega)
  have e8 : a8 = x.get 10#5 + BitVec.ofNat 64 (8 * j) := ha8.eq
  have e26 : x.get 11#5 + (BitVec.ofNat 64 (8 * (j + (x.get 14#5).toNat)) +
      18446744073709551600#64) = x.get 11#5 + BitVec.ofNat 64 (8 * (j + (x.get 14#5).toNat - 2)) :=
    kn_addr_m16 _ _ (by omega) (by omega)
  -- The words u[j + n - 2] and u[j + n - 1] of the next partial remainder.
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  rw [e26]
  refine ⟨List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (mem_bufWords (by omega)))), fun w15 hw15 => ?_⟩
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.add_zero]
  rw [e27]
  refine ⟨List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (mem_bufWords (by omega)))), fun w16 hw16 => ?_⟩
  -- The words of q and u after the store of the quotient digit.
  have hlq : 8 * ((x.get 12#5).toNat - (x.get 14#5).toNat) ≤ 8 * (x.get 12#5).toNat := by omega
  have hqj : (x.get 10#5 + BitVec.ofNat 64 (8 * j)).toNat = (x.get 10#5).toNat + 8 * j :=
    toNat_add8 _ _ (by omega) (by omega)
  have huj : (x.get 11#5 + BitVec.ofNat 64 (8 * j)).toNat = (x.get 11#5).toNat + 8 * j :=
    toNat_add8 _ _ (by omega) (by omega)
  have hq1 : x.get 10#5 + BitVec.ofNat 64 (8 * j) + 8 =
      x.get 10#5 + BitVec.ofNat 64 (8 * (j + 1)) := by
    rw [BitVec.add_assoc, ofNat_add8]
  have hu1 : x.get 11#5 + BitVec.ofNat 64 (8 * j) + 8 =
      x.get 11#5 + BitVec.ofNat 64 (8 * (j + 1)) := by
    rw [BitVec.add_assoc, ofNat_add8]
  have hsp0 : (x.get 2#5 - 144#64).toNat + 144 ≤ 2 ^ 64 := hsn
  set m4 := memStore m3 (x.get 10#5 + BitVec.ofNat 64 (8 * j)).toNat (x3.get 18#5) with hm4
  have hQ3 : words m3 (x.get 10#5 + BitVec.ofNat 64 (8 * (j + 1)))
      ((x.get 12#5).toNat - (x.get 14#5).toNat - 1 - j) =
      words m' (x.get 10#5 + BitVec.ofNat 64 (8 * (j + 1)))
        ((x.get 12#5).toNat - (x.get 14#5).toNat - 1 - j) := by
    rcases Nat.eq_zero_or_pos ((x.get 12#5).toNat - (x.get 14#5).toNat - 1 - j) with h0 | h0
    · rw [h0]; rfl
    · have := toNat_add8 (x.get 10#5) (8 * (j + 1)) (by omega) (by omega)
      exact words_of_unchangedExcept2 hm3 _ _ (by omega) (by rw [huj]; omega) (by omega)
  have hQ4 : words m4 (x.get 10#5 + BitVec.ofNat 64 (8 * j))
      ((x.get 12#5).toNat - (x.get 14#5).toNat - j) =
      (x3.get 18#5).toNat + 2 ^ 64 * words m' (x.get 10#5 + BitVec.ofNat 64 (8 * (j + 1)))
        ((x.get 12#5).toNat - (x.get 14#5).toNat - 1 - j) := by
    rw [hm4, words_memStore_first _ _ _ _ (by omega) (by rw [hqj]; omega), hq1, ← hQ3,
      show (x.get 12#5).toNat - (x.get 14#5).toNat - j - 1 =
        (x.get 12#5).toNat - (x.get 14#5).toNat - 1 - j by omega]
  have hR4 : words m4 (x.get 11#5 + BitVec.ofNat 64 (8 * j)) (x.get 14#5).toNat =
      words m3 (x.get 11#5 + BitVec.ofNat 64 (8 * j)) (x.get 14#5).toNat :=
    words_memStore_of_disjoint _ _ _ _ _ (by rw [huj]; omega) (by rw [huj, hqj]; omega)
  have hmem4 : ∀ b, b + 8 ≤ (x.get 10#5).toNat + 8 * j ∨ (x.get 10#5).toNat + 8 * j + 8 ≤ b →
      memWord m4 b = memWord m3 b := fun b hb =>
    memWord_memStore_of_ne _ _ _ _ (by rw [hqj]; omega)
  -- The digit: the quotient and the remainder of the digits from j.
  have hN : words m' (x.get 11#5 + BitVec.ofNat 64 (8 * j)) ((x.get 14#5).toNat + 1) =
      (memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * j)).toNat).toNat + 2 ^ 64 *
        words m' (x.get 11#5 + BitVec.ofNat 64 (8 * (j + 1))) (x.get 14#5).toNat := by
    rw [words, hu1, hlow j le_rfl]
  have hdigit := knuth_digit hQR (q := (x3.get 18#5).toNat)
    (R' := words m3 (x.get 11#5 + BitVec.ofNat 64 (8 * j)) (x.get 14#5).toNat)
    (by rw [hdig, hN, ← words_digit m (x.get 11#5) (by omega)]; ring)
  have h2 := kn_step_unchanged (q := x.get 10#5) (u := x.get 11#5)
    (lq := 8 * ((x.get 12#5).toNat - (x.get 14#5).toNat)) (lu := 8 * (x.get 12#5).toNat)
    (x3.get 18#5) (x.get 10#5 + BitVec.ofNat 64 (8 * j)).toNat hm3
    ⟨by rw [huj]; omega, by rw [huj]; omega⟩ ⟨by rw [hqj]; omega, by rw [hqj]; omega⟩
  rw [← hm4] at h2
  have hF4 : ∀ x4 : Regs, x4.get 2#5 = x'.get 2#5 → (∀ r ∈ [3#5, 4#5], x4.get r = x'.get r) →
      KNFrame x m x4 m4 := by
    intro x4 h42 h4c
    refine KNFrame.step hpre hF0 h2 h42 (fun r hr hnr => ?_)
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr hnr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;>
      first | (simp at hnr; done) | exact h4c _ (by decide)
  -- The store of the quotient digit q[j].
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.add_zero]
  rw [e8]
  refine ⟨List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (mem_bufWords (by omega))))), ?_⟩
  rv_exec_cut 85 206
  · -- The next digit.
    rename_i hb
    have hj0 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · subst h0; exact absurd rfl hb
      · exact h0
    refine ih (j - 1) (by omega) _ _ ?_
    have ej : j - 1 + 1 = j := Nat.sub_add_cancel hj0
    refine ⟨by omega, hF4 _ ?_ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · exact (h3 2#5 (by decide))
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;>
        simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte] <;>
        exact h3 _ (by decide)
    · rw [ofNat_sub1 _ hj0 (by omega)]
    · rw [h3 22#5 (by decide), h22, ptr_sub8 _ _ hj0 (by omega)]
    · rw [h3 9#5 (by decide), h9, ofNat_add1 _ (by omega)]
      congr 1; omega
    · rw [h3 11#5 (by decide), h11]
    · rw [h3 13#5 (by decide), h13]
    · rw [h3 14#5 (by decide), h14]
    · rw [h3 1#5 (by decide), h1]
    · rw [h3 19#5 (by decide), h19]
    · rw [h3 20#5 (by decide), h20]
    · rw [h3 24#5 (by decide), h24]
    · rw [h3 23#5 (by decide), h3 19#5 (by decide), h3 20#5 (by decide), h23]
    · have := toNat_add8 (x.get 11#5) (8 * (j + (x.get 14#5).toNat - 2)) (by omega) (by omega)
      rw [hw15.eq, show j - 1 + (x.get 14#5).toNat - 1 = j + (x.get 14#5).toNat - 2 by omega,
        hmem4 _ (by rw [this]; omega)]
    · have := toNat_add8 (x.get 11#5) (8 * (j + (x.get 14#5).toNat - 1)) (by omega) (by omega)
      rw [hw16.eq, show j - 1 + (x.get 14#5).toNat = j + (x.get 14#5).toNat - 1 by omega,
        hmem4 _ (by rw [this]; omega)]
    · intro k hk
      have := toNat_add8 (x.get 11#5) (8 * k) (by omega) (by omega)
      rw [hmem4 _ (by rw [this]; omega),
        memWord_of_unchangedExcept2 hm3 _ (by rw [this, huj]; omega) (by rw [this]; omega),
        hlow k (by omega)]
    · rw [ej, show (x.get 12#5).toNat - (x.get 14#5).toNat - 1 - (j - 1) =
        (x.get 12#5).toNat - (x.get 14#5).toNat - j by omega, hQ4, hR4]
      exact hdigit
    · rw [ej, hR4]; exact hlt
  · -- The last digit: the epilogue.
    rename_i hb
    have hj0 : j = 0 := by
      have := congrArg BitVec.toNat hb
      simp only [BitVec.toNat_ofNat] at this
      omega
    have hq0 : x.get 10#5 + BitVec.ofNat 64 (8 * j) = x.get 10#5 := by
      rw [hj0]; exact BitVec.add_zero _
    have hu0 : x.get 11#5 + BitVec.ofNat 64 (8 * j) = x.get 11#5 := by
      rw [hj0]; exact BitVec.add_zero _
    rw [hq0, hj0, Nat.sub_zero] at hQ4
    rw [hu0] at hR4 hdigit hlt
    rw [hj0, Nat.mul_zero, pow_zero, Nat.div_one] at hdigit
    obtain ⟨hq, hr'⟩ := knuth_noborrow ((Nat.add_comm _ _).trans hdigit)
      (hdigit ▸ Nat.add_lt_add_left hlt _)
    refine kn_exit base x m hr _ _ (hF4 _ ?_ ?_) ?_ ?_
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      exact h3 2#5 (by decide)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;>
        simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte] <;>
        exact h3 _ (by decide)
    · rw [hQ4]; exact hq
    · have hs := words_split m4 (x.get 14#5).toNat ((x.get 12#5).toNat - (x.get 14#5).toNat)
        (x.get 11#5)
      rw [show (x.get 14#5).toNat + ((x.get 12#5).toNat - (x.get 14#5).toNat) =
        (x.get 12#5).toNat by omega] at hs
      rw [hs, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (words_lt _ _ _), hR4, ← hr']

/-- The registers that the division of the overflow at 163 may change: the call of `submul()`
changes the registers that are not callee-saved, and the ones it restores from the spill words are
kept. -/
def knOverCl : List (BitVec 5) :=
  [0#5, 5#5, 6#5, 7#5, 12#5, 15#5, 16#5, 17#5, 18#5, 28#5, 29#5, 30#5, 31#5]

theorem knOverCl_saved : ∀ r : BitVec 5, r ∉ knOverCl → r ≠ 1#5 → r ≠ 2#5 → r ≠ 10#5 →
    r ≠ 11#5 → r ≠ 13#5 → r ≠ 14#5 → r ∈ calleeSaved ∧ r ≠ 18#5 := by decide

/-- The division overflows, from 163 to 153: the n words at `u + 8 j` less `2^64 - 1` times d by the
call of `submul()` (at 221), with a1, a0, a3, a4 and ra spilled to the 5 words at sp, and the digit
`2^64 - 1` in s2. -/
theorem kn_over {hi : BitVec 20} {lo : BitVec 12} (base : BitVec 64) (x : Regs) (m : Mem)
    (hb : base &&& 3 = 0) (n : Nat) (hn : x.get 14#5 = BitVec.ofNat 64 n) (hn0 : 0 < n)
    (w : BitVec 64) (hw : x.get 11#5 + x.get 8#5 = w)
    (hwn : w.toNat + 8 * n ≤ 2 ^ 64) (hwa : w.toNat % 8 = 0)
    (hdn : (x.get 13#5).toNat + 8 * n ≤ 2 ^ 64) (hda : (x.get 13#5).toNat % 8 = 0)
    (hsn : (x.get 2#5).toNat + 40 ≤ 2 ^ 64)
    (hwd : Disjoint w (8 * n) (x.get 13#5) (8 * n))
    (hws : Disjoint w (8 * n) (x.get 2#5) 40)
    (hds : Disjoint (x.get 13#5) (8 * n) (x.get 2#5) 40) :
    Reach (bufWords (x.get 13#5) n ++ bufWords w n ++ bufWords (x.get 2#5) 5)
      (udivrem_knuth_normalized_progAt hi lo) base (pcAt base 163) x m (pcAt base 153)
      (fun x' m' =>
        (∃ k, words m' w n + (2 ^ 64 - 1) * words m (x.get 13#5) n = words m w n + k * 2 ^ (64 * n)) ∧
        UnchangedExcept2 m m' w (8 * n) (x.get 2#5) 40 ∧ x'.get 18#5 = 18446744073709551615#64 ∧
        ∀ r, r ∉ knOverCl → x' r = x r) := by
  simp only [Disjoint] at hwd hws hds
  rv_exec_cut 221
  rename_i w12 hw12
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  rw [show pcAt base 174 + BitVec.signExtend 64 188#12 = pcAt base 221 by
      simp only [pcAt, BitVec.reduceSignExtend]; bv_omega,
    update_aligned (by simp only [pcAt]; exact aligned_add hb (by decide))]
  have hw12' : w12 = w := by rw [hw12.eq, ← hw]
  have hnt : (x.get 14#5).toNat = n := by rw [hn, BitVec.toNat_ofNat]; omega
  refine Reach.call_sub (r := 176) udivrem_knuth_normalized_progAt_submul_in
    (by rw [udivrem_knuth_normalized_progAt_length]; decide)
    (submul.reach (pcAt base 221) _ _ ?_ ?_) ?_ ?_ ?_
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    simp only [pcAt]; exact aligned_add hb (by decide)
  · simp only [submul.pre, Buf, Disjoint]
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    try simp (disch := decide) only [Regs.eq_get x]
    rw [hw12', hnt]
    omega
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · intro a ha
    simp only [submul.bufs] at ha
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at ha
    try simp (disch := decide) only [Regs.eq_get x] at ha
    rw [hw12', hnt] at ha
    rcases List.mem_append.mp ha with ha | ha
    · exact List.mem_append_left _ (List.mem_append_left _ ha)
    · exact List.mem_append_left _ (List.mem_append_right _ ha)
  · intro x3 m3 hpost
    simp only [submul.post] at hpost
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at hpost
    try simp (disch := decide) only [Regs.eq_get x] at hpost
    rw [hw12', hnt] at hpost
    obtain ⟨hres, hun, hcs⟩ := hpost
    have hcs' : ∀ r ∈ calleeSaved, r ≠ 18#5 → x3 r = x r := by
      intro r hr h18
      rw [hcs r hr]
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> simp (config := { decide := true }) only [↓reduceIte] <;>
        exact absurd rfl h18
    have h2' : x3.get 2#5 = x.get 2#5 := by
      rw [← Regs.eq_get x3 (by decide), ← Regs.eq_get x (by decide)]
      exact hcs' _ (by decide) (by decide)
    have h18' : x3.get 18#5 = 18446744073709551615#64 := by
      rw [← Regs.eq_get x3 (by decide), hcs _ (by decide)]
      simp (config := { decide := true }) only [↓reduceIte]
    rw [← regs_set_of_get' (by decide) h2']
    rv_exec
    rename_i a1 ha1 a10 ha10 a11 ha11 a13 ha13 a14 ha14
    have s0 : (x.get 2#5).toNat + 0 = (x.get 2#5).toNat := rfl
    have s8 : (x.get 2#5 + 8#64).toNat = (x.get 2#5).toNat + 8 := by
      rw [BitVec.toNat_add]; simp; omega
    have s16 : (x.get 2#5 + 16#64).toNat = (x.get 2#5).toNat + 16 := by
      rw [BitVec.toNat_add]; simp; omega
    have s24 : (x.get 2#5 + 24#64).toNat = (x.get 2#5).toNat + 24 := by
      rw [BitVec.toNat_add]; simp; omega
    have s32 : (x.get 2#5 + 32#64).toNat = (x.get 2#5).toNat + 32 := by
      rw [BitVec.toNat_add]; simp; omega
    have hm1d : words (memStore (memStore (memStore (memStore (memStore m
        (x.get 2#5 + 32#64).toNat (x.get 13#5)) (x.get 2#5 + 24#64).toNat (x.get 10#5))
        (x.get 2#5 + 16#64).toNat (x.get 11#5)) (x.get 2#5 + 8#64).toNat (x.get 14#5))
        (x.get 2#5).toNat (x.get 1#5)) (x.get 13#5) n = words m (x.get 13#5) n := by
      rw [words_memStore_of_disjoint _ _ _ _ _ hdn (by omega),
        words_memStore_of_disjoint _ _ _ _ _ hdn (by omega),
        words_memStore_of_disjoint _ _ _ _ _ hdn (by omega),
        words_memStore_of_disjoint _ _ _ _ _ hdn (by omega),
        words_memStore_of_disjoint _ _ _ _ _ hdn (by omega)]
    have hm1w : words (memStore (memStore (memStore (memStore (memStore m
        (x.get 2#5 + 32#64).toNat (x.get 13#5)) (x.get 2#5 + 24#64).toNat (x.get 10#5))
        (x.get 2#5 + 16#64).toNat (x.get 11#5)) (x.get 2#5 + 8#64).toNat (x.get 14#5))
        (x.get 2#5).toNat (x.get 1#5)) w n = words m w n := by
      rw [words_memStore_of_disjoint _ _ _ _ _ hwn (by omega),
        words_memStore_of_disjoint _ _ _ _ _ hwn (by omega),
        words_memStore_of_disjoint _ _ _ _ _ hwn (by omega),
        words_memStore_of_disjoint _ _ _ _ _ hwn (by omega),
        words_memStore_of_disjoint _ _ _ _ _ hwn (by omega)]
    -- The spill words after submul().
    have hsp : ∀ c, c + 8 ≤ (x.get 2#5).toNat + 40 → (x.get 2#5).toNat ≤ c →
        memWord m3 c = memWord (memStore (memStore (memStore (memStore (memStore m
          (x.get 2#5 + 32#64).toNat (x.get 13#5)) (x.get 2#5 + 24#64).toNat (x.get 10#5))
          (x.get 2#5 + 16#64).toNat (x.get 11#5)) (x.get 2#5 + 8#64).toNat (x.get 14#5))
          (x.get 2#5).toNat (x.get 1#5)) c := fun c h1 h2 =>
      memWord_of_unchangedExcept hun _ (by omega)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hm1d, hm1w] at hres
      exact ⟨_, hres⟩
    · intro k hk1 hk2
      rw [hun k hk1]
      repeat rw [getElem?_memStore_of_ne _ _ _ _ (by omega)]
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      exact h18'
    · intro r hr
      have hr' := hr
      simp only [knOverCl, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
      split_ifs with e14 e13 e11 e10 e1 e2
      · subst e14
        rw [ha14.eq, hsp _ (by omega) (by omega)]
        simp (disch := omega) only [memWord_memStore_self, memWord_memStore_of_ne]
        exact (Regs.eq_get x (by decide)).symm
      · subst e13
        rw [ha13.eq, hsp _ (by omega) (by omega)]
        simp (disch := omega) only [memWord_memStore_self, memWord_memStore_of_ne]
        exact (Regs.eq_get x (by decide)).symm
      · subst e11
        rw [ha11.eq, hsp _ (by omega) (by omega)]
        simp (disch := omega) only [memWord_memStore_self, memWord_memStore_of_ne]
        exact (Regs.eq_get x (by decide)).symm
      · subst e10
        rw [ha10.eq, hsp _ (by omega) (by omega)]
        simp (disch := omega) only [memWord_memStore_self, memWord_memStore_of_ne]
        exact (Regs.eq_get x (by decide)).symm
      · subst e1
        rw [ha1.eq, hsp _ (by omega) (by omega)]
        simp (disch := omega) only [memWord_memStore_self, memWord_memStore_of_ne]
        exact (Regs.eq_get x (by decide)).symm
      · subst e2
        exact (Regs.eq_get x (by decide)).symm
      · obtain ⟨hcs1, h18n⟩ := knOverCl_saved r hr e1 e2 e10 e11 e13 e14
        exact hcs' r hcs1 h18n

/-- The top 2 words `T` of a remainder `R` below `D` are below the top 2 words `dh` of `D` unless
they are equal. -/
theorem kn_top_lt {Rlo T dlo dh P : Nat} (hRlo : Rlo < P) (hdlo : dlo < P)
    (hR : Rlo + P * T < dlo + P * dh) (hne : T ≠ dh) : T < dh := by
  by_contra hc
  have h1 : dh + 1 ≤ T := by omega
  have : P * (dh + 1) ≤ P * T := Nat.mul_le_mul_left _ h1
  nlinarith

/-- The words of `submul()` of the overflow: `S + X` is `N` with `N - X` below `D` and `D ≤ K`. -/
theorem kn_over_nat {S X L N D k K t : Nat} (hS : S < K) (h : S + X = L + k * K)
    (hN : N = L + K * t) (hX : X ≤ N) (hNX : N < X + D) (hDK : D ≤ K) :
    S + X = N ∧ S < D := by
  have hK : 0 < K := by omega
  have e : S + K * t = (N - X) + K * k := by
    have : S + X + K * t = N + K * k := by rw [h, hN]; ring
    omega
  have hm := congrArg (· % K) e
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hS,
    Nat.mod_eq_of_lt (show N - X < K by omega)] at hm
  omega

/-- The quotient digit of the Knuth division without the overflow, with the estimate `qh` and the
remainder `rh` of the 3/2 division of the top words `Nt` of `N` by the top words `dh` of `d`: the
remainder `T * P + L` of the subtraction if it does not borrow (`c = 0`), or `S'` after `d` is
added back to it modulo `K = 2^64 * 2^128 * P` (`c = 1`). -/
theorem kn_digit_nat {N d dh dlo Nt Nlo qh rh L ov T c P : Nat} (hd : d = dlo + P * dh)
    (hdlo : dlo < P) (hP : 2 ^ 64 ≤ dh) (hdh : dh < 2 ^ 128) (hN : N = Nlo + P * Nt) (hNlo : Nlo < P)
    (h32 : qh * dh + rh = Nt) (hrh : rh < dh) (hqh : qh < 2 ^ 64)
    (hL : L + qh * dlo = Nlo + ov * P) (hT : T + ov = rh + c * 2 ^ 128) (hTl : T < 2 ^ 128)
    (hLl : L < P) :
    (c = 0 → qh * d + (T * P + L) = N ∧ T * P + L < d) ∧
    (c = 1 → 1 ≤ qh ∧ ∀ S' co, S' < 2 ^ 128 * P → S' + 2 ^ 128 * P * co = T * P + L + d →
      (qh - 1) * d + S' = N ∧ S' < d) := by
  have hsub := knuth_sub (dhi := dh) (dlo := dlo) (Nt := Nt) (Nlo := Nlo) (rh := rh)
    (hd.trans (by ring)) (hN.trans (by ring)) h32.symm hL hT
  have hest := knuth_est (dhi := dh) (dlo := dlo) (Nt := Nt) (Nlo := Nlo) (rh := rh) (P := P)
    (hd.trans (by ring)) hdlo (Nat.mul_le_mul_right _ hP) (hN.trans (by ring)) hNlo h32.symm hrh hqh
  have hS : T * P + L < 2 ^ 128 * P := by
    have : (T + 1) * P ≤ 2 ^ 128 * P := Nat.mul_le_mul_right _ hTl
    nlinarith
  have hdK : d ≤ 2 ^ 128 * P := by
    rw [hd]
    have : P * (dh + 1) ≤ P * 2 ^ 128 := Nat.mul_le_mul_left _ hdh
    nlinarith
  refine ⟨fun hc => ?_, fun hc => ⟨?_, fun S' co hS'l hadd => ?_⟩⟩
  · subst hc
    simp only [Nat.zero_mul, Nat.add_zero] at hsub
    obtain ⟨hq, hr⟩ := knuth_noborrow (hsub.trans rfl) hest.1
    refine ⟨by rw [Nat.add_comm]; exact hsub, ?_⟩
    rw [hr]; exact Nat.mod_lt _ (by omega)
  · subst hc
    rcases Nat.eq_zero_or_pos qh with h0 | h0
    · subst h0; simp at hsub; omega
    · exact h0
  · subst hc
    simp only [Nat.one_mul] at hsub
    obtain ⟨hq, hr⟩ := knuth_addback hdK hS'l hsub hadd hS hest.2
    refine ⟨?_, ?_⟩
    · rw [hq, hr]; exact Nat.div_add_mod' N d
    · rw [hr]; exact Nat.mod_lt _ (by omega)

/-- The address of a word of a buffer from a word of it. -/
theorem ptr_add_add (u : BitVec 64) (a b : Nat) (h : u.toNat + 8 * (a + b) ≤ 2 ^ 64) :
    u + BitVec.ofNat 64 (8 * a) + BitVec.ofNat 64 (8 * b) = u + BitVec.ofNat 64 (8 * (a + b)) := by
  bv_omega

/-- The words of a buffer with its top 2 words split off. -/
theorem words_top2 (m : Mem) (a : BitVec 64) (k : Nat) :
    words m a (k + 2) = words m a k + 2 ^ (64 * k) *
      ((memWord m (a + BitVec.ofNat 64 (8 * k)).toNat).toNat +
        2 ^ 64 * (memWord m (a + BitVec.ofNat 64 (8 * (k + 1))).toNat).toNat) := by
  rw [show k + 2 = (k + 1) + 1 from rfl, words_succ_top, words_succ_top,
    show 64 * (k + 1) = 64 * k + 64 by ring, pow_add]
  ring

/-- The words of a buffer with its top 3 words split off. -/
theorem words_top3 (m : Mem) (a : BitVec 64) (k : Nat) :
    words m a (k + 3) = words m a k + 2 ^ (64 * k) *
      ((memWord m (a + BitVec.ofNat 64 (8 * k)).toNat).toNat +
        2 ^ 64 * ((memWord m (a + BitVec.ofNat 64 (8 * (k + 1))).toNat).toNat +
          2 ^ 64 * (memWord m (a + BitVec.ofNat 64 (8 * (k + 2))).toNat).toNat)) := by
  rw [show k + 3 = (k + 2) + 1 from rfl, words_succ_top, words_top2,
    show 64 * (k + 2) = 64 * k + 64 + 64 by ring, pow_add, pow_add]
  ring

/-- The address of the word `k - 2` of u from the word `k`, as the load at 92 computes it. -/
theorem kn_addr_m16' (u : BitVec 64) (k : Nat) (h2 : 2 ≤ k) (h : u.toNat + 8 * k ≤ 2 ^ 64) :
    u + BitVec.ofNat 64 (8 * k) + 18446744073709551600#64 = u + BitVec.ofNat 64 (8 * (k - 2)) := by
  bv_omega

/-- The top 2 words of a normalized divisor: at least `2^127`. -/
theorem kn_dh {D dlo dh P n : Nat} (hP : P = 2 ^ (64 * (n - 2))) (hn : 3 ≤ n)
    (hD : 2 ^ (64 * n - 1) ≤ D) (hDs : D = dlo + P * dh) (hdlo : dlo < P) : 2 ^ 127 ≤ dh := by
  have e : 2 ^ (64 * n - 1) = P * 2 ^ 127 := by
    rw [hP, ← pow_add]; congr 1; omega
  by_contra hc
  have : P * (dh + 1) ≤ P * 2 ^ 127 := Nat.mul_le_mul_left _ (by omega)
  nlinarith

/-- The start of the loop of the inlined `submul()` from the registers at 129. -/
theorem kn_sub_start {A : List (BitVec 64)} {hi : BitVec 20} {lo : BitVec 12}
    {base tgt : BitVec 64} {Q : Regs → Mem → Prop} (xs : Regs) (ms : Mem) (dp wp : BitVec 64)
    (n : Nat) (q : BitVec 64) (hn0 : 0 < n)
    (hn : 8 * n < 2 ^ 64) (hdn : dp.toNat + 8 * n ≤ 2 ^ 64) (hwn : wp.toNat + 8 * n ≤ 2 ^ 64)
    (hdis : dp.toNat + 8 * n ≤ wp.toNat ∨ wp.toNat + 8 * n ≤ dp.toNat)
    (hdA : ∀ i < n, dp + BitVec.ofNat 64 (8 * i) ∈ A)
    (hwA : ∀ i < n, wp + BitVec.ofNat 64 (8 * i) ∈ A)
    (h6 : xs.get 6#5 = dp) (h7 : xs.get 7#5 = wp) (h5 : xs.get 5#5 = wp + BitVec.ofNat 64 (8 * n))
    (h18 : xs.get 18#5 = q) (h16 : xs.get 16#5 = 0#64) (h17 : xs.get 17#5 = 0#64)
    (hk : ∀ x' m', knSubExit xs ms dp wp n q x' m' →
      Reach A (udivrem_knuth_normalized_progAt hi lo) base (pcAt base 145) x' m' tgt Q) :
    Reach A (udivrem_knuth_normalized_progAt hi lo) base (pcAt base 129) xs ms tgt Q :=
  kn_sub_loop xs ms dp wp n q hn hdn hwn hdis hdA hwA hk n xs ms
    ⟨0, hn0, by omega, by rw [h6]; simp, by rw [h7]; simp, h5, h18, by rw [h17]; decide,
      by rw [h16, h17]; simp [words], unchangedExcept_refl _ _ _, rfl, fun _ _ => rfl⟩

/-- The start of the add-back loop from the registers at 192. -/
theorem kn_add_start {A : List (BitVec 64)} {hi : BitVec 20} {lo : BitVec 12}
    {base tgt : BitVec 64} {Q : Regs → Mem → Prop} (xs : Regs) (ms : Mem) (dp wp : BitVec 64)
    (n : Nat) (hn0 : 0 < n)
    (hn : 8 * n < 2 ^ 64) (hdn : dp.toNat + 8 * n ≤ 2 ^ 64) (hwn : wp.toNat + 8 * n ≤ 2 ^ 64)
    (hdis : dp.toNat + 8 * n ≤ wp.toNat ∨ wp.toNat + 8 * n ≤ dp.toNat)
    (hdA : ∀ i < n, dp + BitVec.ofNat 64 (8 * i) ∈ A)
    (hwA : ∀ i < n, wp + BitVec.ofNat 64 (8 * i) ∈ A)
    (h12 : xs.get 12#5 = wp) (h15 : xs.get 15#5 = dp) (h1 : xs.get 1#5 = dp + BitVec.ofNat 64 (8 * n))
    (h16 : xs.get 16#5 = 0#64)
    (hk : ∀ x' m', knAddExit xs ms dp wp n x' m' →
      Reach A (udivrem_knuth_normalized_progAt hi lo) base (pcAt base 204) x' m' tgt Q) :
    Reach A (udivrem_knuth_normalized_progAt hi lo) base (pcAt base 192) xs ms tgt Q :=
  kn_add_loop xs ms dp wp n hn hdn hwn hdis hdA hwA hk n xs ms
    ⟨0, hn0, by omega, by rw [h12]; simp, by rw [h15]; simp, h1, by rw [h16]; decide,
      by rw [h16]; simp [words], unchangedExcept_refl _ _ _, rfl, fun _ _ => rfl⟩

/-- The end of the words of u for the inlined `submul()` of the digit `j`, as the code computes it
from `8 u.size() - 24` and the count of the digits done. -/
theorem kn_addr_end (u : BitVec 64) (us n j : Nat) (hn : 3 ≤ n) (hj : j + n + 1 ≤ us)
    (h : u.toNat + 8 * us ≤ 2 ^ 64) :
    u + (BitVec.ofNat 64 (8 * us - 24) - BitVec.ofNat 64 (us - n - 1 - j) <<< 3) =
      u + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 (8 * (n - 2)) := by
  bv_omega

theorem kn_addr_m8' (u : BitVec 64) (k : Nat) (h1 : 1 ≤ k) (h : u.toNat + 8 * k ≤ 2 ^ 64) :
    u + 18446744073709551608#64 + BitVec.ofNat 64 (8 * k) = u + BitVec.ofNat 64 (8 * (k - 1)) := by
  bv_omega

/-- `u - s` and its borrow `u < u - s`, without a definition of the borrow. -/
theorem defn_sub_borrow_ite {r u s : BitVec 64} (hr : Defn r (u - s)) :
    r.toNat + s.toNat = u.toNat + 2 ^ 64 * (if u < r then 1 else 0) := by
  have hb : Defn (if u < r then 1#64 else 0#64) (if u < r then 1#64 else 0#64) := rfl
  have h := defn_sub_borrow0 hr hb
  split_ifs at h ⊢ <;> simpa using h

/-- The words of the remainder of a digit after the stores of its top 2 words. -/
theorem words_store_top2 (m : Mem) (a : BitVec 64) (k : Nat) (v0 v1 : BitVec 64)
    (ha : a.toNat + 8 * (k + 2) ≤ 2 ^ 64) :
    words (memStore (memStore m (a + BitVec.ofNat 64 (8 * k)).toNat v0)
        (a + BitVec.ofNat 64 (8 * (k + 1))).toNat v1) a (k + 2) =
      words m a k + 2 ^ (64 * k) * (v0.toNat + 2 ^ 64 * v1.toNat) := by
  have e0 : (a + BitVec.ofNat 64 (8 * k)).toNat = a.toNat + 8 * k :=
    toNat_add8 _ _ (by omega) (by omega)
  have e1 : (a + BitVec.ofNat 64 (8 * (k + 1))).toNat = a.toNat + 8 * (k + 1) :=
    toNat_add8 _ _ (by omega) (by omega)
  rw [words_top2, words_memStore_of_disjoint _ _ _ _ _ (by omega) (by rw [e1]; omega),
    words_memStore_of_disjoint _ _ _ _ _ (by omega) (by rw [e0]; omega),
    memWord_memStore_of_ne _ _ _ _ (by rw [e0, e1]; omega), memWord_memStore_self,
    memWord_memStore_self]

/-- The words outside the three regions that may change. -/
theorem words_of_unchangedExcept3 {m m' : Mem} {a b s : BitVec 64} {la lb ls : Nat}
    (h : UnchangedExcept3 m m' a la b lb s ls) : ∀ (n : Nat) (c : BitVec 64),
      c.toNat + 8 * n ≤ 2 ^ 64 → (c.toNat + 8 * n ≤ a.toNat ∨ a.toNat + la ≤ c.toNat) →
      (c.toNat + 8 * n ≤ b.toNat ∨ b.toNat + lb ≤ c.toNat) →
      (c.toNat + 8 * n ≤ s.toNat ∨ s.toNat + ls ≤ c.toNat) → words m' c n = words m c n
  | 0, _, _, _, _, _ => rfl
  | n + 1, c, hc, ha, hb, hs => by
    rw [words, words, memWord_of_unchangedExcept3 h c.toNat (by omega) (by omega) (by omega)]
    cases n with
    | zero => rfl
    | succ k =>
      have h8 : (c + 8).toNat = c.toNat + 8 := by
        rw [BitVec.toNat_add]; simp; omega
      rw [words_of_unchangedExcept3 h (k + 1) (c + 8) (by omega) (by omega) (by omega)
        (by omega)]

/-- The digit `j` of `udivrem_knuth_normalized()` without the overflow, from 92: the load of
u[j + n - 2], the inlined `udivrem_3by2()` of the top words, the inlined `submul()` of the low
`n - 2` words of d, the subtraction of its overflow from the remainder of the top words, and the
add-back if it borrows. -/
theorem kn_normal {hi : BitVec 20} {lo : BitVec 12} {Dt : List (BitVec 64)} (base : BitVec 64)
    (x : Regs) (m : Mem) (hb : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0)
    (hpre : udivrem_knuth_normalized.pre x m) (j : Nat) (x' : Regs) (m' : Mem)
    (hh : knHead x m j x' m')
    (h8 : x'.get 8#5 = BitVec.ofNat 64 (8 * j)) (h25 : x'.get 25#5 = BitVec.ofNat 64 j)
    (h26 : x'.get 26#5 = x.get 11#5 + BitVec.ofNat 64 (8 * (j + (x.get 14#5).toNat)))
    (h27 : x'.get 27#5 = BitVec.ofNat 64 (8 * (j + (x.get 14#5).toNat)))
    (hne : ¬(x'.get 15#5 = x'.get 19#5 ∧ x'.get 16#5 = x'.get 20#5))
    (ih : ∀ k < j, ∀ x' m', knHead x m k x' m' →
      Reach (udivrem_knuth_normalized.bufs x ++ Dt) (udivrem_knuth_normalized_progAt hi lo)
        base (pcAt base 85) x' m' (x.get 1#5) (udivrem_knuth_normalized.post x m)) :
    Reach (udivrem_knuth_normalized.bufs x ++ Dt) (udivrem_knuth_normalized_progAt hi lo)
      base (pcAt base 92) x' m' (x.get 1#5) (udivrem_knuth_normalized.post x m) := by
  have hh0 := hh
  obtain ⟨hjn, hF, h12, h22, h9, h10, h11, h13, h14, h1, h19, h20, h21, h24, h23, h15, h16, hlow,
    hQR, hRD⟩ := hh
  have hpre' := hpre
  simp only [udivrem_knuth_normalized.pre, Buf, Disjoint] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hqa, hqn⟩, ⟨hua, hun⟩, ⟨hda, hdn⟩, hdqd, hdqu, hdud, ⟨hsa, hsn⟩, hdsd, hdsq, hdsu,
    hn3, hnu, hD, hU⟩ := hpre'
  have hbufs : udivrem_knuth_normalized.bufs x = bufWords (x.get 13#5) (x.get 14#5).toNat ++
      bufWords (x.get 10#5) ((x.get 12#5).toNat - (x.get 14#5).toNat) ++
      bufWords (x.get 11#5) (x.get 12#5).toNat ++ bufWords (x.get 2#5 - 144#64) 18 := by
    simp only [udivrem_knuth_normalized.bufs]
    simp (disch := decide) only [Regs.eq_get x]
  rw [hbufs]
  -- The divisor: its low n - 2 words and its top 2 words.
  have hDs := words_top2 m (x.get 13#5) ((x.get 14#5).toNat - 2)
  rw [show (x.get 14#5).toNat - 2 + 2 = (x.get 14#5).toNat by omega,
    show (x.get 14#5).toNat - 2 + 1 = (x.get 14#5).toNat - 1 by omega, ← h19, ← h20] at hDs
  -- The partial remainder above u[j]: its low n - 2 words and its top 2 words in a5 and a6.
  have hRs := words_top2 m' (x.get 11#5 + BitVec.ofNat 64 (8 * (j + 1))) ((x.get 14#5).toNat - 2)
  rw [show (x.get 14#5).toNat - 2 + 2 = (x.get 14#5).toNat by omega,
    ptr_add_add _ _ _ (by omega), ptr_add_add _ _ _ (by omega),
    show j + 1 + ((x.get 14#5).toNat - 2) = j + (x.get 14#5).toNat - 1 by omega,
    show j + 1 + ((x.get 14#5).toNat - 2 + 1) = j + (x.get 14#5).toNat by omega, ← h15, ← h16]
    at hRs
  -- The digits of u from u[j]: its low n - 2 words and its top 3 words.
  have hNs := words_top3 m' (x.get 11#5 + BitVec.ofNat 64 (8 * j)) ((x.get 14#5).toNat - 2)
  rw [show (x.get 14#5).toNat - 2 + 3 = (x.get 14#5).toNat + 1 by omega,
    ptr_add_add _ _ _ (by omega), ptr_add_add _ _ _ (by omega), ptr_add_add _ _ _ (by omega),
    show j + ((x.get 14#5).toNat - 2 + 1) = j + (x.get 14#5).toNat - 1 by omega,
    show j + ((x.get 14#5).toNat - 2 + 2) = j + (x.get 14#5).toNat by omega, ← h15, ← h16]
    at hNs
  rw [show j + ((x.get 14#5).toNat - 2) = j + (x.get 14#5).toNat - 2 by omega] at hNs
  have hPpos : 0 < 2 ^ (64 * ((x.get 14#5).toNat - 2)) := Nat.two_pow_pos _
  have hdlo := words_lt m ((x.get 14#5).toNat - 2) (x.get 13#5)
  have hdh := kn_dh rfl hn3 hD hDs hdlo
  have hdh2 : (x'.get 19#5).toNat + 2 ^ 64 * (x'.get 20#5).toNat < 2 ^ 128 := by
    have := (x'.get 19#5).isLt; have := (x'.get 20#5).isLt; omega
  have hu : (x'.get 16#5).toNat * 2 ^ 64 + (x'.get 15#5).toNat <
      (x'.get 19#5).toNat + 2 ^ 64 * (x'.get 20#5).toNat := by
    have hne' : (x'.get 15#5).toNat + 2 ^ 64 * (x'.get 16#5).toNat ≠
        (x'.get 19#5).toNat + 2 ^ 64 * (x'.get 20#5).toNat := by
      intro h
      have := (x'.get 15#5).isLt; have := (x'.get 19#5).isLt
      exact hne ⟨BitVec.eq_of_toNat_eq (by omega), BitVec.eq_of_toNat_eq (by omega)⟩
    have := kn_top_lt (words_lt m' ((x.get 14#5).toNat - 2) _) hdlo
      (by rw [← hRs, ← hDs]; exact hRD) hne'
    omega
  -- The word u[j + n - 2].
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  rw [h26, kn_addr_m16' _ _ (by omega) (by omega)]
  refine ⟨List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (mem_bufWords (i := j + (x.get 14#5).toNat - 2)
      (by clear * - hjn hn3; omega)))), fun w0 hw0 => ?_⟩
  -- The inlined udivrem_3by2() of the top 3 words.
  refine Reach.trans (kn_div base (x'.set 12#5 w0) m' ?_ ?_ ?_) ?_
  all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · omega
  · exact hu
  · exact h23
  intro x2 m2 ⟨hm2, hq2, hr2, h02, hcl2⟩
  subst hm2
  try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte] at hq2 hr2
  rw [regs_eq_sets _ x2 _ h02 hcl2]
  simp only [setRegs]
  rv_exec_cut 129
  rename_i e2 he2 e1 he1 e0 he0
  have huj : (x.get 11#5 + BitVec.ofNat 64 (8 * j)).toNat = (x.get 11#5).toNat + 8 * j :=
    toNat_add8 _ _ (by omega) (by omega)
  refine kn_sub_start _ m2 (x.get 13#5) (x.get 11#5 + BitVec.ofNat 64 (8 * j))
    ((x.get 14#5).toNat - 2) (x2.get 18#5) (by omega) (by omega) (by omega) (by rw [huj]; omega)
    (by rw [huj]; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i hi
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (mem_bufWords (by omega)))))
  · intro i hi
    rw [ptr_add_add _ _ _ (by omega)]
    exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (mem_bufWords (by omega))))
  all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · exact h13
  · exact h22
  · rw [he0.eq, he1.eq, he2.eq, h11, h24, h9]
    exact kn_addr_end _ _ _ _ hn3 hjn (by omega)
  · exact Regs.eq_get x2 (by decide)
  -- The end of the inlined submul() at 145.
  intro x4 m4 ⟨h18', h17', hsub, hun4, h04, hcl4⟩
  rw [regs_eq_sets _ x4 knSubCl h04 hcl4]
  simp only [setRegs, knSubCl]
  rv_exec_cut 150
  rename_i ov hov a17 ha17 T0 hT0 b0 hb0 T1 hT1
  have ea17 : a17 = x.get 11#5 + BitVec.ofNat 64 (8 * (j + (x.get 14#5).toNat - 1)) := by
    rw [ha17.eq, h21, h27]; exact kn_addr_m8' _ _ (by omega) (by omega)
  -- The stores of the top 2 words of the remainder.
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  rw [h26, kn_addr_m16' _ _ (by omega) (by omega)]
  refine ⟨List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (mem_bufWords (i := j + (x.get 14#5).toNat - 2)
      (by clear * - hjn hn3; omega)))), ?_⟩
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.add_zero]
  rw [ea17]
  refine ⟨List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (mem_bufWords (i := j + (x.get 14#5).toNat - 1)
      (by clear * - hjn hn3; omega)))), ?_⟩
  rv_exec_cut 153 189
  all_goals simp only [zopz0zI_u_eq, decide_eq_true_eq, decide_eq_false_iff_not] at *
  -- The words of the digit: the subtraction of ov from the remainder of the top words.
  all_goals
    have hFu := hF.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hdk : ∀ k, k ≤ (x.get 14#5).toNat →
        words m2 (x.get 13#5) k = words m (x.get 13#5) k := fun k hk =>
      words_of_unchangedExcept3 hFu k _ (by omega) (by omega) (by omega) (by omega)
    have hdlo' := hdk ((x.get 14#5).toNat - 2) (by omega)
    have hov' : ov.toNat = (x4.get 16#5).toNat + (x4.get 17#5).toNat := by
      have := submul_high_lt (words_lt _ _ _) (words_lt _ _ _) (x2.get 18#5).isLt hsub
      rw [← Regs.eq_get x4 (show (16#5 : BitVec 5) ≠ 0 by decide),
        ← Regs.eq_get x4 (show (17#5 : BitVec 5) ≠ 0 by decide)] at this ⊢
      exact defn_add_exact hov this
    have hT0' := defn_sub_borrow0 hT0 hb0
    have hT1' := defn_sub_borrow_ite hT1
    rw [hdlo'] at hsub
    -- The 3/2 division of the top words.
    have h32 : (x2.get 18#5).toNat * ((x'.get 19#5).toNat + 2 ^ 64 * (x'.get 20#5).toNat) +
        ((x2.get 12#5).toNat + 2 ^ 64 * (x2.get 15#5).toNat) =
        w0.toNat + 2 ^ 64 * ((x'.get 15#5).toNat + 2 ^ 64 * (x'.get 16#5).toNat) := by
      rw [hq2, hr2, Nat.div_add_mod']; ring
    have hrh : (x2.get 12#5).toNat + 2 ^ 64 * (x2.get 15#5).toNat <
        (x'.get 19#5).toNat + 2 ^ 64 * (x'.get 20#5).toNat := by
      rw [hr2]; exact Nat.mod_lt _ (by omega)
    have hN : words m2 (x.get 11#5 + BitVec.ofNat 64 (8 * j)) ((x.get 14#5).toNat + 1) =
        words m2 (x.get 11#5 + BitVec.ofNat 64 (8 * j)) ((x.get 14#5).toNat - 2) +
          2 ^ (64 * ((x.get 14#5).toNat - 2)) *
            (w0.toNat + 2 ^ 64 * ((x'.get 15#5).toNat + 2 ^ 64 * (x'.get 16#5).toNat)) := by
      rw [hNs, hw0.eq]
    have hT : (T0.toNat + 2 ^ 64 * T1.toNat) + ov.toNat =
        ((x2.get 12#5).toNat + 2 ^ 64 * (x2.get 15#5).toNat) +
          (if x2 15#5 < T1 then 1 else 0) * 2 ^ 128 := by
      rw [← Regs.eq_get x2 (show (12#5 : BitVec 5) ≠ 0 by decide),
        ← Regs.eq_get x2 (show (15#5 : BitVec 5) ≠ 0 by decide)]
      have := b0.isLt
      have hb1 : b0.toNat ≤ 1 := by rw [hb0.eq]; split <;> simp
      split_ifs at hT1' ⊢ <;> omega
    have hTl : T0.toNat + 2 ^ 64 * T1.toNat < 2 ^ 128 := by
      have := T0.isLt; have := T1.isLt; omega
    have hdig := kn_digit_nat hDs hdlo (by omega) hdh2 hN (words_lt _ _ _) h32 hrh
      (x2.get 18#5).isLt (by rw [← hov'] at hsub; exact hsub) hT hTl (words_lt _ _ _)
    -- The words of u after the stores of the top 2 words of the remainder.
    have hW5 := words_store_top2 m4 (x.get 11#5 + BitVec.ofNat 64 (8 * j)) ((x.get 14#5).toNat - 2)
      T0 T1 (by rw [huj]; omega)
    rw [ptr_add_add _ _ _ (by omega), ptr_add_add _ _ _ (by omega),
      show j + ((x.get 14#5).toNat - 2) = j + (x.get 14#5).toNat - 2 by omega,
      show j + ((x.get 14#5).toNat - 2 + 1) = j + (x.get 14#5).toNat - 1 by omega,
      show (x.get 14#5).toNat - 2 + 2 = (x.get 14#5).toNat by omega] at hW5
    have hj2 : (x.get 11#5 + BitVec.ofNat 64 (8 * (j + (x.get 14#5).toNat - 2))).toNat =
        (x.get 11#5).toNat + 8 * (j + (x.get 14#5).toNat - 2) := toNat_add8 _ _ (by omega) (by omega)
    have hj1 : (x.get 11#5 + BitVec.ofNat 64 (8 * (j + (x.get 14#5).toNat - 1))).toNat =
        (x.get 11#5).toNat + 8 * (j + (x.get 14#5).toNat - 1) := toNat_add8 _ _ (by omega) (by omega)
    have hm5 : UnchangedExcept2 m2 (memStore (memStore m4
        (x.get 11#5 + BitVec.ofNat 64 (8 * (j + (x.get 14#5).toNat - 2))).toNat T0)
        (x.get 11#5 + BitVec.ofNat 64 (8 * (j + (x.get 14#5).toNat - 1))).toNat T1)
        (x.get 11#5 + BitVec.ofNat 64 (8 * j)) (8 * (x.get 14#5).toNat) (x.get 2#5 - 144#64) 40 := by
      intro k hk1 _
      rw [getElem?_memStore_of_ne _ _ _ _ (by rw [hj1]; omega),
        getElem?_memStore_of_ne _ _ _ _ (by rw [hj2]; omega)]
      exact hun4 k (by omega)
    rw [← hbufs]
    first
      | (rv_get hc : ¬x2 15#5 < T1
         -- No borrow: the estimate is the digit.
         have hd0 := hdig.1 (by rw [if_neg hc])
         refine kn_tail base x m hr hpre j x' m2 hh0 _ _ ?_ ?_ ?_ ?_ ?_ hm5 ?_ ?_ ih
         all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
         · intro r hr'
           simp only [knKept, List.mem_cons, List.not_mem_nil, or_false] at hr'
           rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
             rfl | rfl | rfl <;>
           simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
         · exact h8
         · exact h25
         · exact h26
         · exact h27
         · rw [hW5, Regs.eq_get x2 (show (18#5 : BitVec 5) ≠ 0 by decide)]; linarith [hd0.1]
         · rw [hW5]; linarith [hd0.2])
      | (rv_get hc : x2 15#5 < T1
         have hd1 := hdig.2 (by rw [if_pos hc])
         rv_exec_cut 192
         have hd5 : ∀ k, k ≤ (x.get 14#5).toNat → words (memStore (memStore m4
             (x.get 11#5 + BitVec.ofNat 64 (8 * (j + (x.get 14#5).toNat - 2))).toNat T0)
             (x.get 11#5 + BitVec.ofNat 64 (8 * (j + (x.get 14#5).toNat - 1))).toNat T1)
             (x.get 13#5) k = words m (x.get 13#5) k := by
           intro k hk
           rw [← hdk k hk]
           exact words_of_unchangedExcept2 hm5 k _ (by omega) (by rw [huj]; omega) (by omega)
         refine kn_add_start _ _ (x.get 13#5) (x.get 11#5 + BitVec.ofNat 64 (8 * j))
           (x.get 14#5).toNat (by omega) (by omega) (by omega) (by rw [huj]; omega)
           (by rw [huj]; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_
         · intro i hi
           rw [hbufs]
           exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
             (List.mem_append_left _ (mem_bufWords (by omega)))))
         · intro i hi
           rw [hbufs, ptr_add_add _ _ _ (by omega)]
           exact List.mem_append_left _ (List.mem_append_left _
             (List.mem_append_right _ (mem_bufWords (by omega))))
         all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
         · exact h22
         · exact h13
         · exact h1
         -- The end of the add-back at 204: the digit one less.
         intro x6 m6 ⟨hco1, hadd, hun6, h06, hcl6⟩
         rw [hd5 _ le_rfl, hW5] at hadd
         rw [regs_eq_sets _ x6 knAddCl h06 hcl6]
         simp only [setRegs, knAddCl]
         rv_exec_cut 153
         have hq1' : (x2 18#5 + 18446744073709551615#64).toNat = (x2.get 18#5).toNat - 1 := by
           rw [Regs.eq_get x2 (show (18#5 : BitVec 5) ≠ 0 by decide)]
           exact toNat_add_neg1 _ hd1.1
         have hK : 2 ^ (64 * (x.get 14#5).toNat) =
             2 ^ 128 * 2 ^ (64 * ((x.get 14#5).toNat - 2)) := by
           rw [show 64 * (x.get 14#5).toNat = 128 + 64 * ((x.get 14#5).toNat - 2) by omega, pow_add]
         rw [hK] at hadd
         obtain ⟨hdq, hdl⟩ := hd1.2 (words m6 (x.get 11#5 + BitVec.ofNat 64 (8 * j))
           (x.get 14#5).toNat) (x6.get 16#5).toNat (by rw [← hK]; exact words_lt _ _ _)
           (by linarith [hadd])
         refine kn_tail base x m hr hpre j x' m2 hh0 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ih
         all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
         · intro r hr'
           simp only [knKept, List.mem_cons, List.not_mem_nil, or_false] at hr'
           rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
             rfl | rfl | rfl <;>
           simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
         · exact h8
         · exact h25
         · exact h26
         · exact h27
         · intro k hk1 hk2
           rw [hun6 k hk1]
           exact hm5 k hk1 hk2
         · rw [hq1']; exact hdq
         · exact hdl)

/-- The state at the head of the loop does not depend on s0, s9, s10 and s11. -/
theorem knHead_of_eq {x : Regs} {m : Mem} {j : Nat} {x0 x' : Regs} {m' : Mem}
    (hh : knHead x m j x0 m') (h : ∀ r, r ∉ [8#5, 25#5, 26#5, 27#5] → r ≠ 0 → x'.get r = x0.get r) :
    knHead x m j x' m' := by
  have g := h
  obtain ⟨hjn, ⟨hsp, f1, f8, f9, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, hun, hcs⟩, h12,
    h22, h9, h10, h11, h13, h14, h1, h19, h20, h21, h24, h23, h15, h16, hlow, hQR, hRD⟩ := hh
  refine ⟨hjn, ⟨?_, f1, f8, f9, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, hun, ?_⟩, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hlow, hQR, hRD⟩
  all_goals try rw [g _ (by decide) (by decide)]
  all_goals try rw [g _ (by decide) (by decide)]
  all_goals try rw [g _ (by decide) (by decide)]
  all_goals try assumption
  intro r hr hnr
  have hr0 : r ≠ 0 := by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> decide
  have hr8 : r ∉ [8#5, 25#5, 26#5, 27#5] := by
    intro hm
    apply hnr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
    rcases hm with rfl | rfl | rfl | rfl <;> simp
  rw [g r hr8 hr0]
  exact hcs r hr hnr

/-- The bounds of the numerator of a digit with its top 2 words equal to the top 2 words of the
divisor: the digit is `2^64 - 1`. -/
theorem kn_over_bounds {N D dlo dh P Nlo w0 R u0 : Nat} (hd : D = dlo + P * dh) (hdlo : dlo < P)
    (hP : 2 ^ 64 ≤ dh) (hN : N = Nlo + P * (w0 + 2 ^ 64 * dh)) (hNR : N = u0 + 2 ^ 64 * R)
    (hu0 : u0 < 2 ^ 64) (hR : R < D) :
    (2 ^ 64 - 1) * D ≤ N ∧ N < (2 ^ 64 - 1) * D + D := by
  constructor
  · have h1 : 2 ^ 64 * P ≤ P * dh := by rw [Nat.mul_comm P]; exact Nat.mul_le_mul_right _ hP
    subst hd hN
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_left_comm P (2 ^ 64) dh]
    omega
  · omega

theorem kn_sp (a : BitVec 64) : a + 18446744073709551472#64 = a - 144#64 := by
  bv_omega

theorem kn_addr_p8 (u : BitVec 64) (j : Nat) :
    u + BitVec.ofNat 64 (8 * j) + (8 : BitVec 64) = u + BitVec.ofNat 64 (8 * (j + 1)) := by
  bv_omega

theorem knKept_not_over : ∀ r ∈ knKept, r ≠ 0 ∧ r ∉ knOverCl := by decide

/-- The digit `j` of `udivrem_knuth_normalized()` with the overflow, from 163. -/
theorem kn_overflow {hi : BitVec 20} {lo : BitVec 12} {Dt : List (BitVec 64)} (base : BitVec 64)
    (x : Regs) (m : Mem) (hb : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0)
    (hpre : udivrem_knuth_normalized.pre x m) (j : Nat) (x' : Regs) (m' : Mem)
    (hh : knHead x m j x' m')
    (h8 : x'.get 8#5 = BitVec.ofNat 64 (8 * j)) (h25 : x'.get 25#5 = BitVec.ofNat 64 j)
    (h26 : x'.get 26#5 = x.get 11#5 + BitVec.ofNat 64 (8 * (j + (x.get 14#5).toNat)))
    (h27 : x'.get 27#5 = BitVec.ofNat 64 (8 * (j + (x.get 14#5).toNat)))
    (heq : x'.get 15#5 = x'.get 19#5 ∧ x'.get 16#5 = x'.get 20#5)
    (ih : ∀ k < j, ∀ x' m', knHead x m k x' m' →
      Reach (udivrem_knuth_normalized.bufs x ++ Dt) (udivrem_knuth_normalized_progAt hi lo)
        base (pcAt base 85) x' m' (x.get 1#5) (udivrem_knuth_normalized.post x m)) :
    Reach (udivrem_knuth_normalized.bufs x ++ Dt) (udivrem_knuth_normalized_progAt hi lo)
      base (pcAt base 163) x' m' (x.get 1#5) (udivrem_knuth_normalized.post x m) := by
  have hh0 := hh
  obtain ⟨hjn, hF, h12, h22, h9, h10, h11, h13, h14, h1, h19, h20, h21, h24, h23, h15, h16, hlow,
    hQR, hRD⟩ := hh
  have hpre' := hpre
  simp only [udivrem_knuth_normalized.pre, Buf, Disjoint] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hqa, hqn⟩, ⟨hua, hun⟩, ⟨hda, hdn⟩, hdqd, hdqu, hdud, ⟨hsa, hsn⟩, hdsd, hdsq, hdsu,
    hn3, hnu, hD, hU⟩ := hpre'
  have hbufs : udivrem_knuth_normalized.bufs x = bufWords (x.get 13#5) (x.get 14#5).toNat ++
      bufWords (x.get 10#5) ((x.get 12#5).toNat - (x.get 14#5).toNat) ++
      bufWords (x.get 11#5) (x.get 12#5).toNat ++ bufWords (x.get 2#5 - 144#64) 18 := by
    simp only [udivrem_knuth_normalized.bufs]
    simp (disch := decide) only [Regs.eq_get x]
  have hsp : x'.get 2#5 = x.get 2#5 - 144#64 := by rw [hF.1]; exact kn_sp _
  have huj : (x.get 11#5 + BitVec.ofNat 64 (8 * j)).toNat = (x.get 11#5).toNat + 8 * j :=
    toNat_add8 _ _ (by omega) (by omega)
  refine Reach.trans (Reach.mono_bufs ?_ (kn_over base x' m' hb (x.get 14#5).toNat ?_ (by omega)
    (x.get 11#5 + BitVec.ofNat 64 (8 * j)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)) ?_
  · rw [h13, hsp, hbufs]
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    rcases List.mem_append.1 ha with ha | ha
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ ha)))
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        (mem_bufWords_of_offset (by omega) ha)))
    · exact List.mem_append_left _ (List.mem_append_right _ (mem_bufWords_of_le (by omega) ha))
  · rw [h14]; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]
    have := (x.get 14#5).isLt; omega
  · rw [h11, h8]
  · rw [huj]; omega
  · rw [huj]; omega
  · rw [h13]; omega
  · rw [h13]; omega
  · rw [hsp]; omega
  · simp only [Disjoint]; rw [huj, h13]; omega
  · simp only [Disjoint]; rw [huj, hsp]; omega
  · simp only [Disjoint]; rw [h13, hsp]; omega
  -- The end of the subtraction at 153.
  intro x3 m3 ⟨⟨k, hk⟩, hun3, h18, hcl3⟩
  rw [hsp] at hun3
  rw [h13] at hk
  have hFu := hF.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hdk : words m' (x.get 13#5) (x.get 14#5).toNat = words m (x.get 13#5) (x.get 14#5).toNat :=
    words_of_unchangedExcept3 hFu _ _ (by omega) (by omega) (by omega) (by omega)
  rw [hdk] at hk
  -- The divisor and the numerator with the top words split off.
  have hDs := words_top2 m (x.get 13#5) ((x.get 14#5).toNat - 2)
  rw [show (x.get 14#5).toNat - 2 + 2 = (x.get 14#5).toNat by omega,
    show (x.get 14#5).toNat - 2 + 1 = (x.get 14#5).toNat - 1 by omega, ← h19, ← h20] at hDs
  have hNs := words_top3 m' (x.get 11#5 + BitVec.ofNat 64 (8 * j)) ((x.get 14#5).toNat - 2)
  rw [show (x.get 14#5).toNat - 2 + 3 = (x.get 14#5).toNat + 1 by omega,
    ptr_add_add _ _ _ (by omega), ptr_add_add _ _ _ (by omega), ptr_add_add _ _ _ (by omega),
    show j + ((x.get 14#5).toNat - 2 + 1) = j + (x.get 14#5).toNat - 1 by omega,
    show j + ((x.get 14#5).toNat - 2 + 2) = j + (x.get 14#5).toNat by omega, ← h15, ← h16,
    heq.1, heq.2] at hNs
  have hdlo := words_lt m ((x.get 14#5).toNat - 2) (x.get 13#5)
  have hdh := kn_dh rfl hn3 hD hDs hdlo
  have hNR : words m' (x.get 11#5 + BitVec.ofNat 64 (8 * j)) ((x.get 14#5).toNat + 1) =
      (memWord m' (x.get 11#5 + BitVec.ofNat 64 (8 * j)).toNat).toNat +
        2 ^ 64 * words m' (x.get 11#5 + BitVec.ofNat 64 (8 * (j + 1))) (x.get 14#5).toNat := by
    rw [words, kn_addr_p8]
  have hbd := kn_over_bounds hDs hdlo (by omega) hNs hNR (BitVec.isLt _) hRD
  have hNt := words_succ_top m' (x.get 14#5).toNat (x.get 11#5 + BitVec.ofNat 64 (8 * j))
  rw [ptr_add_add _ _ _ (by omega), ← h16] at hNt
  obtain ⟨hS1, hS2⟩ := kn_over_nat (words_lt m3 _ _) hk hNt hbd.1 hbd.2
    (words_lt m (x.get 14#5).toNat (x.get 13#5)).le
  refine kn_tail base x m hr hpre j x' m' hh0 x3 m3 ?_ ?_ ?_ ?_ ?_ hun3 ?_ hS2 ih
  · intro r hr'
    obtain ⟨hr0, hro⟩ := knKept_not_over r hr'
    rw [← Regs.eq_get x3 hr0, ← Regs.eq_get x' hr0]; exact hcl3 r hro
  · rw [← Regs.eq_get x3 (by decide), hcl3 8#5 (by decide), Regs.eq_get x' (by decide)]; exact h8
  · rw [← Regs.eq_get x3 (by decide), hcl3 25#5 (by decide), Regs.eq_get x' (by decide)]
    exact h25
  · rw [← Regs.eq_get x3 (by decide), hcl3 26#5 (by decide), Regs.eq_get x' (by decide)]
    exact h26
  · rw [← Regs.eq_get x3 (by decide), hcl3 27#5 (by decide), Regs.eq_get x' (by decide)]
    exact h27
  · rw [h18, show (18446744073709551615#64 : BitVec 64).toNat = 2 ^ 64 - 1 from rfl]
    omega

/-- A shifted index register. -/
theorem kn_shl3 (a : BitVec 64) (k : Nat) (h : a.toNat = k) (hk : 8 * k < 2 ^ 64) :
    a <<< 3 = BitVec.ofNat 64 (8 * k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, h, BitVec.toNat_ofNat]
  omega

/-- The loop of `udivrem_knuth_normalized()` from its head at 85. -/
theorem kn_loop {hi : BitVec 20} {lo : BitVec 12} {Dt : List (BitVec 64)} (base : BitVec 64)
    (x : Regs) (m : Mem) (hb : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0)
    (hpre : udivrem_knuth_normalized.pre x m) :
    ∀ j x' m', knHead x m j x' m' →
    Reach (udivrem_knuth_normalized.bufs x ++ Dt) (udivrem_knuth_normalized_progAt hi lo)
      base (pcAt base 85) x' m' (x.get 1#5) (udivrem_knuth_normalized.post x m) := by
  apply Reach.loop (knHead x m)
  intro j x' m' hh ih
  have hh0 := hh
  obtain ⟨hjn, hF, h12, h22, h9, h10, h11, h13, h14, h1, h19, h20, h21, h24, h23, h15, h16, hlow,
    hQR, hRD⟩ := hh
  have hpre' := hpre
  simp only [udivrem_knuth_normalized.pre, Buf, Disjoint] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hqa, hqn⟩, ⟨hua, hun⟩, ⟨hda, hdn⟩, hdqd, hdqu, hdud, ⟨hsa, hsn⟩, hdsd, hdsq, hdsu,
    hn3, hnu, hD, hU⟩ := hpre'
  rw [← regs_set_of_get' (by decide) h12, ← regs_set_of_get' (by decide) h14,
    ← regs_set_of_get' (by decide) h11]
  rv_exec_cut 90
  rename_i a27 ha27 s27 hs27 a26 ha26 a8 ha8
  have hj8 : 8 * (j + (x.get 14#5).toNat) < 2 ^ 64 := by omega
  have e27 : s27 = BitVec.ofNat 64 (8 * (j + (x.get 14#5).toNat)) := by
    rw [hs27.eq, ha27.eq]
    refine kn_shl3 _ _ ?_ hj8
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have e26 : a26 = x.get 11#5 + BitVec.ofNat 64 (8 * (j + (x.get 14#5).toNat)) := by
    rw [ha26.eq, e27]
  have e8 : a8 = BitVec.ofNat 64 (8 * j) := by
    rw [ha8.eq]; exact kn_shl3 _ _ (by rw [BitVec.toNat_ofNat]; omega) (by omega)
  rv_exec_cut 92 163
  all_goals first
    | (refine kn_overflow base x m hb hr hpre j _ m' (knHead_of_eq hh0 ?_) ?_ ?_ ?_ ?_ ?_ ih
       · intro r hr hr0
         simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
         obtain ⟨h8n, h25n, h26n, h27n⟩ := hr
         simp only [Regs.get_set, hr0, h8n, h25n, h26n, h27n, ↓reduceIte]
         split_ifs <;> first | rfl | (rw [‹r = 12#5›]; exact h12.symm) |
           (rw [‹r = 14#5›]; exact h14.symm) | (rw [‹r = 11#5›]; exact h11.symm)
       all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
       all_goals first | exact e8 | exact e26 | exact e27 | (constructor <;> assumption))
    | (refine kn_normal base x m hb hr hpre j _ m' (knHead_of_eq hh0 ?_) ?_ ?_ ?_ ?_ ?_ ih
       · intro r hr hr0
         simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
         obtain ⟨h8n, h25n, h26n, h27n⟩ := hr
         simp only [Regs.get_set, hr0, h8n, h25n, h26n, h27n, ↓reduceIte]
         split_ifs <;> first | rfl | (rw [‹r = 12#5›]; exact h12.symm) |
           (rw [‹r = 14#5›]; exact h14.symm) | (rw [‹r = 11#5›]; exact h11.symm)
       all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
       all_goals first | exact e8 | exact e26 | exact e27 |
         (rintro ⟨h1', h2'⟩; contradiction))

/-- The memory after the prologue of `udivrem_knuth_normalized()`: ra, s0 to s11 stored in the
frame. -/
abbrev knFrameMem (x : Regs) (m : Mem) : Mem :=
  memStore (memStore (memStore (memStore (memStore (memStore (memStore (memStore (memStore (memStore (memStore (memStore (memStore m
    (x.get 2#5 + 18446744073709551608#64).toNat (x.get 1#5))
    (x.get 2#5 + 18446744073709551600#64).toNat (x.get 8#5))
    (x.get 2#5 + 18446744073709551592#64).toNat (x.get 9#5))
    (x.get 2#5 + 18446744073709551584#64).toNat (x.get 18#5))
    (x.get 2#5 + 18446744073709551576#64).toNat (x.get 19#5))
    (x.get 2#5 + 18446744073709551568#64).toNat (x.get 20#5))
    (x.get 2#5 + 18446744073709551560#64).toNat (x.get 21#5))
    (x.get 2#5 + 18446744073709551552#64).toNat (x.get 22#5))
    (x.get 2#5 + 18446744073709551544#64).toNat (x.get 23#5))
    (x.get 2#5 + 18446744073709551536#64).toNat (x.get 24#5))
    (x.get 2#5 + 18446744073709551528#64).toNat (x.get 25#5))
    (x.get 2#5 + 18446744073709551520#64).toNat (x.get 26#5))
    (x.get 2#5 + 18446744073709551512#64).toNat (x.get 27#5)

/-- The addresses of the saved registers in the frame of 144 bytes below sp. -/
theorem kn_frame_toNat (sp : BitVec 64) (hs : (sp - 144#64).toNat + 144 ≤ 2 ^ 64) :
    (sp + 18446744073709551608#64).toNat = (sp - 144#64).toNat + 136 ∧
    (sp + 18446744073709551600#64).toNat = (sp - 144#64).toNat + 128 ∧
    (sp + 18446744073709551592#64).toNat = (sp - 144#64).toNat + 120 ∧
    (sp + 18446744073709551584#64).toNat = (sp - 144#64).toNat + 112 ∧
    (sp + 18446744073709551576#64).toNat = (sp - 144#64).toNat + 104 ∧
    (sp + 18446744073709551568#64).toNat = (sp - 144#64).toNat + 96 ∧
    (sp + 18446744073709551560#64).toNat = (sp - 144#64).toNat + 88 ∧
    (sp + 18446744073709551552#64).toNat = (sp - 144#64).toNat + 80 ∧
    (sp + 18446744073709551544#64).toNat = (sp - 144#64).toNat + 72 ∧
    (sp + 18446744073709551536#64).toNat = (sp - 144#64).toNat + 64 ∧
    (sp + 18446744073709551528#64).toNat = (sp - 144#64).toNat + 56 ∧
    (sp + 18446744073709551520#64).toNat = (sp - 144#64).toNat + 48 ∧
    (sp + 18446744073709551512#64).toNat = (sp - 144#64).toNat + 40 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_omega

theorem knFrameMem_unchanged (x : Regs) (m : Mem)
    (hs : (x.get 2#5 - 144#64).toNat + 144 ≤ 2 ^ 64) :
    UnchangedExcept m (knFrameMem x m) (x.get 2#5 - 144#64) 144 := by
  obtain ⟨f1, f8, f9, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27⟩ := kn_frame_toNat (x.get 2#5) hs
  simp only [knFrameMem]
  repeat rw [unchangedExcept_memStore _ _ (by omega)]
  exact unchangedExcept_refl _ _ _

theorem knFrameMem_words (x : Regs) (m : Mem) (hs : (x.get 2#5 - 144#64).toNat + 144 ≤ 2 ^ 64) :
    memWord (knFrameMem x m) (x.get 2#5 + 18446744073709551608#64).toNat = x.get 1#5 ∧
    memWord (knFrameMem x m) (x.get 2#5 + 18446744073709551600#64).toNat = x.get 8#5 ∧
    memWord (knFrameMem x m) (x.get 2#5 + 18446744073709551592#64).toNat = x.get 9#5 ∧
    memWord (knFrameMem x m) (x.get 2#5 + 18446744073709551584#64).toNat = x.get 18#5 ∧
    memWord (knFrameMem x m) (x.get 2#5 + 18446744073709551576#64).toNat = x.get 19#5 ∧
    memWord (knFrameMem x m) (x.get 2#5 + 18446744073709551568#64).toNat = x.get 20#5 ∧
    memWord (knFrameMem x m) (x.get 2#5 + 18446744073709551560#64).toNat = x.get 21#5 ∧
    memWord (knFrameMem x m) (x.get 2#5 + 18446744073709551552#64).toNat = x.get 22#5 ∧
    memWord (knFrameMem x m) (x.get 2#5 + 18446744073709551544#64).toNat = x.get 23#5 ∧
    memWord (knFrameMem x m) (x.get 2#5 + 18446744073709551536#64).toNat = x.get 24#5 ∧
    memWord (knFrameMem x m) (x.get 2#5 + 18446744073709551528#64).toNat = x.get 25#5 ∧
    memWord (knFrameMem x m) (x.get 2#5 + 18446744073709551520#64).toNat = x.get 26#5 ∧
    memWord (knFrameMem x m) (x.get 2#5 + 18446744073709551512#64).toNat = x.get 27#5 := by
  obtain ⟨f1, f8, f9, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27⟩ := kn_frame_toNat (x.get 2#5) hs
  simp only [knFrameMem]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := omega) only [memWord_memStore_self, memWord_memStore_of_ne]

theorem memHalf_of_unchangedExcept {m m' : Mem} {a : BitVec 64} {len : Nat}
    (h : UnchangedExcept m m' a len) (b : Nat) (hb : b + 4 ≤ a.toNat ∨ a.toNat + len ≤ b) :
    memHalf m' b = memHalf m b := by
  simp only [memHalf, Std.ExtHashMap.getD_eq_getD_getElem?]
  rw [h b (by omega), h (b + 1) (by omega), h (b + 2) (by omega), h (b + 3) (by omega)]

theorem kn_addr_dn2 (d n : BitVec 64) (h : 2 ≤ n.toNat) (hn : 8 * n.toNat ≤ 2 ^ 64) :
    d + n <<< 3 + 18446744073709551600#64 = d + BitVec.ofNat 64 (8 * (n.toNat - 2)) := by
  bv_omega

theorem kn_addr_dn1 (d n : BitVec 64) (h : 1 ≤ n.toNat) (hn : 8 * n.toNat ≤ 2 ^ 64) :
    d + (n <<< 3 + 18446744073709551608#64) = d + BitVec.ofNat 64 (8 * (n.toNat - 1)) := by
  bv_omega

theorem kn_addr_dn1b (d n : BitVec 64) (h : 1 ≤ n.toNat) (hn : 8 * n.toNat ≤ 2 ^ 64) :
    d + n <<< 3 + 18446744073709551608#64 = d + BitVec.ofNat 64 (8 * (n.toNat - 1)) := by
  bv_omega

theorem kn_j0 (a b : BitVec 64) (h : b.toNat < a.toNat) :
    a + (b ^^^ 18446744073709551615#64) = BitVec.ofNat 64 (a.toNat - b.toNat - 1) := by
  rw [show (18446744073709551615#64) = BitVec.allOnes 64 from rfl, BitVec.xor_allOnes]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_not, BitVec.toNat_ofNat]
  have := b.isLt
  omega

theorem kn_u_j0 (u a b : BitVec 64) (h : b.toNat < a.toNat) (ha : 8 * a.toNat < 2 ^ 64) :
    u + (18446744073709551608#64 + (a <<< 3 - b <<< 3)) =
      u + BitVec.ofNat 64 (8 * (a.toNat - b.toNat - 1)) := by
  bv_omega

theorem kn_24 (a : BitVec 64) (h : 3 ≤ a.toNat) (ha : 8 * a.toNat < 2 ^ 64) :
    a <<< 3 + 18446744073709551592#64 = BitVec.ofNat 64 (8 * a.toNat - 24) := by
  bv_omega

/-- The top `n` words of u. -/
theorem kn_topn (m : Mem) (u : BitVec 64) (us n : Nat) (h : n ≤ us) :
    words m u us / 2 ^ (64 * (us - n)) = words m (u + BitVec.ofNat 64 (8 * (us - n))) n := by
  have hs := words_split m (us - n) n u
  rw [show us - n + n = us by omega] at hs
  rw [hs, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (words_lt _ _ _),
    Nat.zero_add]

/-- The frame of 144 bytes below sp is outside the image: its first and last words are. -/
theorem kn_frame_outside (sp base : BitVec 64) (o : Nat)
    (h0 : (sp - 144#64).toNat + 8 ≤ base.toNat ∨ base.toNat + o ≤ (sp - 144#64).toNat)
    (h17 : (sp - 144#64 + BitVec.ofNat 64 (8 * 17)).toNat + 8 ≤ base.toNat ∨
      base.toNat + o ≤ (sp - 144#64 + BitVec.ofNat 64 (8 * 17)).toNat)
    (hs : (sp - 144#64).toNat + 144 ≤ 2 ^ 64) (ho : 144 ≤ o) :
    (sp - 144#64).toNat + 144 ≤ base.toNat ∨ base.toNat + o ≤ (sp - 144#64).toNat := by
  have : (sp - 144#64 + BitVec.ofNat 64 (8 * 17)).toNat = (sp - 144#64).toNat + 136 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  omega

end IntxRV.Api
