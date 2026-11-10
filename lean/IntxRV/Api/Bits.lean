import IntxRV.Gen.Api
import IntxRV.Arith
import IntxRV.Image
/-!
# The proofs of `bit_test()` and `count_significant_words()` of `uint256`

`count_significant_words()` tests the words from the top: `rv_runm` proves the index of the top
nonzero word, and `count_significant_words4` its relation to `log2`. `bit_test()` loads the word
of the bit at an address computed from the bit index (`shr3_and`); `testBit_words` gives the bit
of the number.
-/

set_option maxRecDepth 100000
-- The paths use different lemmas of the same simp calls.
set_option linter.unusedSimpArgs false

namespace IntxRV

/-- The bit `i` of the number of the `n` words at `a`: the bit `i % 64` of the word `i / 64`. -/
theorem testBit_words (m : Mem) : ∀ (n : Nat) (a : BitVec 64) (i : Nat), i < 64 * n →
    (words m a n).testBit i =
      (memWord m (a + BitVec.ofNat 64 (8 * (i / 64))).toNat).getLsbD (i % 64)
  | 0, _, _, h => by omega
  | n + 1, a, i, h => by
    rw [words, Nat.add_comm, Nat.testBit_two_pow_mul_add _ (BitVec.isLt _)]
    split_ifs with hi
    · rw [Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]; simp [BitVec.getLsbD]
    · rw [testBit_words m n (a + 8) (i - 64) (by omega), show (i - 64) % 64 = i % 64 by omega,
        show a + 8 + BitVec.ofNat 64 (8 * ((i - 64) / 64)) = a + BitVec.ofNat 64 (8 * (i / 64)) by
          rw [BitVec.add_assoc]; congr 1
          rw [show i / 64 = (i - 64) / 64 + 1 by omega, Nat.mul_succ, Nat.add_comm,
            BitVec.ofNat_add]
          rfl]

/-- The word index of the top bit. -/
theorem log2_div_64 {X k : Nat} (h1 : 2 ^ (64 * k) ≤ X) (h2 : X < 2 ^ (64 * (k + 1))) :
    Nat.log2 X / 64 = k := by
  have hX : X ≠ 0 := by have := Nat.one_le_two_pow (n := 64 * k); omega
  have a := (Nat.le_log2 hX).mpr h1
  have b := (Nat.log2_lt hX).mpr h2
  omega

/-- The address of the word of the bit `i`: `(i >> 3) & ~7` is `8 * (i / 64)`. -/
theorem shr3_and (i : BitVec 64) :
    (i >>> 3) &&& 0xfffffffffffffff8#64 = BitVec.ofNat 64 (8 * (i.toNat / 64)) := by
  have : (i >>> 3) &&& 0xfffffffffffffff8#64 = (i >>> 6) <<< 3 := by
    rw [show (0xfffffffffffffff8#64) = ~~~(BitVec.ofNat 64 (2 ^ 3 - 1)) from by decide]
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_not, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one, hj, decide_true,
      Bool.true_and]
    by_cases h3 : j < 3
    · simp [h3]
    · simp only [h3, decide_false, Bool.not_false, Bool.and_true, Bool.true_and]
      rw [show 6 + (j - 3) = 3 + j by omega]
  rw [this]
  have := i.isLt
  bv_omega

/-- The bit `s` of a word as the `and` of its shift with 1. -/
theorem shr_and_one_eq_one (w : BitVec 64) (s : Nat) :
    (w >>> s &&& 1#64) = 1#64 ↔ w.getLsbD s = true := by
  constructor
  · intro h
    have := congrArg (·.getLsbD 0) h
    simpa using this
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    by_cases j0 : j = 0
    · subst j0; simp [h]
    · simp [BitVec.getLsbD_and, j0]

theorem and_one_cases (v : BitVec 64) : (v &&& 1#64) = 0#64 ∨ (v &&& 1#64) = 1#64 := by
  have h : (v &&& 1#64).toNat = v.toNat % 2 := by
    rw [BitVec.toNat_and, show (1#64).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  rcases Nat.mod_two_eq_zero_or_one v.toNat with h2 | h2 <;> rw [h2] at h
  · exact .inl (BitVec.eq_of_toNat_eq (by simpa using h))
  · exact .inr (BitVec.eq_of_toNat_eq (by simpa using h))

/-- The count of the significant words of a number of 4 words. -/
theorem count_significant_words4 (w0 w1 w2 w3 : BitVec 64) :
    (let X := w0.toNat + 2 ^ 64 * (w1.toNat + 2 ^ 64 * (w2.toNat + 2 ^ 64 * w3.toNat))
     if X = 0 then 0 else Nat.log2 X / 64 + 1) =
      if w3 ≠ 0 then 4 else if w2 ≠ 0 then 3 else if w1 ≠ 0 then 2
      else if w0 ≠ 0 then 1 else 0 := by
  have h0 := w0.isLt
  have h1 := w1.isLt
  have h2 := w2.isLt
  have h3 := w3.isLt
  have z : ∀ w : BitVec 64, w ≠ 0 ↔ w.toNat ≠ 0 := fun w => by
    constructor
    · intro h h'; exact h (BitVec.eq_of_toNat_eq (by simpa using h'))
    · intro h h'; exact h (by simp [h'])
  simp only [z]
  split_ifs with e a b c d <;> first
    | omega
    | (rw [log2_div_64 (k := 3) (by omega) (by omega)])
    | (rw [log2_div_64 (k := 2) (by omega) (by omega)])
    | (rw [log2_div_64 (k := 1) (by omega) (by omega)])
    | (rw [log2_div_64 (k := 0) (by omega) (by omega)])

end IntxRV

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 4000000 in
theorem count_significant_words_256.model : RunsM count_significant_words_256_code
    count_significant_words_256.bufs count_significant_words_256.pre fun x m x' m' =>
    x'.get 10#5 = (if memWord m (x 10#5 + 24#64).toNat ≠ 0 then 4#64
      else if memWord m (x 10#5 + 16#64).toNat ≠ 0 then 3#64
      else if memWord m (x 10#5 + 8#64).toNat ≠ 0 then 2#64
      else if memWord m (x 10#5).toNat ≠ 0 then 1#64 else 0#64) ∧
    m' = m ∧ ∀ i ∈ calleeSaved, x' i = x i := by
  rv_runm count_significant_words_256_decodes with count_significant_words_256_code
    count_significant_words_256_prog using [count_significant_words_256.bufs,
    count_significant_words_256.pre, Buf]

theorem count_significant_words_256.proof : count_significant_words_256.spec :=
  count_significant_words_256.model.mono (fun _ _ h => h) fun x m x' m' _ ⟨h, hm, hc⟩ => by
    simp only [count_significant_words_256.post, words, BitVec.add_assoc, BitVec.ofNat_eq_ofNat,
      BitVec.reduceAdd, Nat.mul_zero, Nat.add_zero]
    have h0 := (memWord m (x 10#5).toNat).isLt
    have h1 := (memWord m (x 10#5 + 8#64).toNat).isLt
    have h2 := (memWord m (x 10#5 + 16#64).toNat).isLt
    have h3 := (memWord m (x 10#5 + 24#64).toNat).isLt
    refine ⟨?_, ?_, hm, hc⟩ <;> rw [h]
    all_goals generalize memWord m (x 10#5).toNat = w0 at *
    all_goals generalize memWord m (x 10#5 + 8#64).toNat = w1 at *
    all_goals generalize memWord m (x 10#5 + 16#64).toNat = w2 at *
    all_goals generalize memWord m (x 10#5 + 24#64).toNat = w3 at *
    · rw [count_significant_words4]
      split_ifs <;> rfl
    · split_ifs <;> decide

set_option maxHeartbeats 4000000 in
theorem bit_test_256.reach (base : BitVec 64) (x : Regs) (m : Mem) (hra : x.get 1#5 &&& 3 = 0)
    (hpre : bit_test_256.pre x m) :
    Reach (bit_test_256.bufs x) bit_test_256_prog base (pcAt base 0) x m (x.get 1#5)
      (bit_test_256.post x m) := by
  simp only [bit_test_256.pre, bit_test_256.bufs, Buf] at hpre ⊢
  simp (disch := decide) only [Regs.eq_get x] at hpre ⊢
  rv_exec
  refine Reach.step (by decide) rfl ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  simp only [Defn] at *
  subst_vars
  have hi : (x.get 11#5).toNat / 64 < 4 := by omega
  rw [shr3_and]
  refine ⟨mem_bufWords hi, fun w hw => ?_⟩
  rv_exec
  rv_val
  simp only [update_aligned hra]
  refine Reach.refl ?_
  simp only [bit_test_256.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, and_true, true_and]
  simp (disch := decide) only [Regs.eq_get x]
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  simp only [Defn] at *
  subst_vars
  rw [testBit_words m 4 _ _ (by omega)]
  refine ⟨by simp [shr_and_one_eq_one], and_one_cases _, ?_⟩
  simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte, BitVec.ofNat_eq_ofNat,
    and_self, and_true, true_and]
  simp (disch := decide) only [Regs.eq_get x, and_self]


theorem bit_test_256.proof : bit_test_256.spec :=
  runsM_of_reach bit_test_256_decodes fun base ret _ hr _ x m hx1 hpre => by
    have hx : x.get 1#5 = ret := by rw [← Regs.eq_get x (by decide)]; exact hx1
    have h := bit_test_256.reach base x m (hx ▸ hr) hpre
    rwa [pcAt_zero, hx] at h

end IntxRV.Api
