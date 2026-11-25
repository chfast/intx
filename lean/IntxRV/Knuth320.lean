import IntxRV.Api.udivrem_knuth_normalized
import IntxRV.Clz
import IntxRV.Shift
import IntxRV.Gen.Api.udivrem_knuth_320
/-!
# The blocks of `internal::udivrem_knuth<320, 256>()` with a dynamic size of d

The shift of d into the stack is a loop from the top word (`k320_dn_loop`, from its first word by
`k320_dn_start`): each word is `k320DnWord`, the word shifted left by the count `s` of the leading
zeros of the top word with the top bits of the word below; for `s = 0` the code stores the word as
it is, which `k320DnWord_zero` shows is the same. The shift of the remainder back is a loop from
the bottom word (`k320_r_loop`, `k320_r_start`) of `k320RWord`. `words_shl` and `words_shr` give
the values of the shifted buffers. `k320_tail` runs from the store of the quotient word `m - n` at
133: the call of `udivrem_knuth_normalized()` with the count of the words to divide (`k320_ulen`
gives its preconditions), the loop of the remainder and the return. `k320_at133` and
`k320_chain` give the memory at 133 for both paths of the shift of u, and `k320_unw` the value of
the shifted u.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- A word of a funnel shift right by `s` times `2^s`: the low `s` bits of the word above move to
the top, the low `s` bits of the word lose. -/
theorem shr_word_mul (a b s : Nat) (hs : s < 64) :
    (a * 2 ^ (64 - s) % 2 ^ 64 + b / 2 ^ s) * 2 ^ s + b % 2 ^ s = a % 2 ^ s * 2 ^ 64 + b := by
  have e64 : (2 : Nat) ^ 64 = 2 ^ s * 2 ^ (64 - s) := by
    rw [← pow_add, Nat.add_sub_cancel' hs.le]
  rw [e64, Nat.mul_mod_mul_right, Nat.add_mul, Nat.add_assoc, Nat.div_add_mod']
  ring

/-- The words of a buffer shifted right by `s` with the low bits of the word above, the top word
shifted right alone. -/
theorem words_shr (m mr : Mem) (up rp : BitVec 64) (s n : Nat) (hs : s < 64) (hn : 1 ≤ n)
    (hw : ∀ j, j + 1 < n → (memWord mr (rp + BitVec.ofNat 64 (8 * j)).toNat).toNat =
      (memWord m (up + BitVec.ofNat 64 (8 * (j + 1))).toNat).toNat * 2 ^ (64 - s) % 2 ^ 64 +
        (memWord m (up + BitVec.ofNat 64 (8 * j)).toNat).toNat / 2 ^ s)
    (htop : (memWord mr (rp + BitVec.ofNat 64 (8 * (n - 1))).toNat).toNat =
      (memWord m (up + BitVec.ofNat 64 (8 * (n - 1))).toNat).toNat / 2 ^ s) :
    words mr rp n * 2 ^ s + (memWord m (up + BitVec.ofNat 64 (8 * 0)).toNat).toNat % 2 ^ s =
      words m up n := by
  -- The words below the top one: the low bits of the next word at the top.
  have aux : ∀ k, k + 1 ≤ n → words mr rp k * 2 ^ s +
      (memWord m (up + BitVec.ofNat 64 (8 * 0)).toNat).toNat % 2 ^ s =
      words m up k + 2 ^ (64 * k) * ((memWord m (up + BitVec.ofNat 64 (8 * k)).toNat).toNat % 2 ^ s) := by
    intro k
    induction k with
    | zero => intro _; simp [words]
    | succ k ih =>
      intro hk
      have h := ih (by omega)
      have hk' := hw k (by omega)
      have hsm := shr_word_mul (memWord m (up + BitVec.ofNat 64 (8 * (k + 1))).toNat).toNat
        (memWord m (up + BitVec.ofNat 64 (8 * k)).toNat).toNat s hs
      rw [← hk'] at hsm
      rw [words_succ_top, words_succ_top, show 64 * (k + 1) = 64 * k + 64 by ring, pow_add]
      generalize (memWord mr (rp + BitVec.ofNat 64 (8 * k)).toNat).toNat = R at hsm ⊢
      generalize (memWord m (up + BitVec.ofNat 64 (8 * k)).toNat).toNat = B at hsm h ⊢
      generalize (memWord m (up + BitVec.ofNat 64 (8 * (k + 1))).toNat).toNat = A at hsm ⊢
      generalize words mr rp k = WR at h ⊢
      generalize words m up k = WU at h ⊢
      generalize (2 : Nat) ^ (64 * k) = P at h ⊢
      generalize (memWord m (up + BitVec.ofNat 64 (8 * 0)).toNat).toNat % 2 ^ s = L at h ⊢
      have e : P * (R * 2 ^ s + B % 2 ^ s) = P * (A % 2 ^ s * 2 ^ 64 + B) := by rw [hsm]
      nlinarith [e, h]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h := aux k (by omega)
  rw [show k + 1 - 1 = k by omega] at htop
  rw [words_succ_top, words_succ_top, htop]
  have hd := Nat.div_add_mod' (memWord m (up + BitVec.ofNat 64 (8 * k)).toNat).toNat (2 ^ s)
  generalize (memWord m (up + BitVec.ofNat 64 (8 * k)).toNat).toNat = B at h hd ⊢
  generalize words mr rp k = WR at h ⊢
  generalize words m up k = WU at h ⊢
  generalize (2 : Nat) ^ (64 * k) = P at h ⊢
  generalize (memWord m (up + BitVec.ofNat 64 (8 * 0)).toNat).toNat % 2 ^ s = L at h ⊢
  have e : P * (B / 2 ^ s * 2 ^ s + B % 2 ^ s) = P * B := by rw [hd]
  nlinarith [e, h]

/-- The words of a buffer shifted left by `s` with the top bits of the word below. -/
theorem words_shl (m mb : Mem) (p q : BitVec 64) (s : Nat) (hs : s < 64) :
    ∀ n, (∀ i, i < n → (memWord mb (q + BitVec.ofNat 64 (8 * i)).toNat).toNat =
      (memWord m (p + BitVec.ofNat 64 (8 * i)).toNat).toNat * 2 ^ s % 2 ^ 64 +
        (if i = 0 then 0 else
          (memWord m (p + BitVec.ofNat 64 (8 * (i - 1))).toNat).toNat / 2 ^ (64 - s))) →
    words mb q n + 2 ^ (64 * n) * (if n = 0 then 0 else
      (memWord m (p + BitVec.ofNat 64 (8 * (n - 1))).toNat).toNat / 2 ^ (64 - s)) =
      words m p n * 2 ^ s := by
  intro n
  induction n with
  | zero => intro _; simp [words]
  | succ n ih =>
    intro hw
    have h := ih (fun i hi => hw i (by omega))
    have hn := hw n (by omega)
    have hsp := mul_two_pow_split (memWord m (p + BitVec.ofNat 64 (8 * n)).toNat).toNat s hs
    rw [if_neg (Nat.succ_ne_zero n), show n + 1 - 1 = n by omega, words_succ_top, words_succ_top,
      hn, show 64 * (n + 1) = 64 * n + 64 by ring, pow_add]
    generalize (memWord m (p + BitVec.ofNat 64 (8 * n)).toNat).toNat = A at hsp ⊢
    generalize (if n = 0 then 0 else
      (memWord m (p + BitVec.ofNat 64 (8 * (n - 1))).toNat).toNat / 2 ^ (64 - s)) = C at h ⊢
    generalize words mb q n = WB at h ⊢
    generalize words m p n = WP at h ⊢
    generalize (2 : Nat) ^ (64 * n) = P at h ⊢
    have e : P * (A * 2 ^ s) = P * (A * 2 ^ s % 2 ^ 64 + 2 ^ 64 * (A / 2 ^ (64 - s))) := by
      rw [← hsp]
    nlinarith [e, h]

/-- The registers that the shift loop of the divisor of `udivrem_knuth<320, 256>()` changes. -/
def k320DnCl : List (BitVec 5) := [11#5, 13#5, 15#5]

/-- The word `i` of d shifted left by `S` with the top bits of the word below, as the code of
`udivrem_knuth<320, 256>()` computes it. -/
def k320DnWord (m : Mem) (dp S : BitVec 64) (i : Nat) : BitVec 64 :=
  memWord m (dp + BitVec.ofNat 64 (8 * i)).toNat <<< (S.toNat % 64) |||
    (memWord m (dp + BitVec.ofNat 64 (8 * (i - 1))).toNat >>> 1) >>>
      ((S ^^^ 18446744073709551615#64).toNat % 64)

/-- The state at the head 71 of the shift loop of the divisor before the word `k`: the words above
it shifted and stored. -/
def k320DnLoop (x0 : Regs) (m0 : Mem) (dp np : BitVec 64) (n : Nat) (S : BitVec 64) (k : Nat)
    (x' : Regs) (m' : Mem) : Prop :=
  1 ≤ k ∧ k < n ∧ x'.get 11#5 = BitVec.ofNat 64 (8 * k) ∧
    (∀ i, k < i → i < n →
      memWord m' (np + BitVec.ofNat 64 (8 * i)).toNat = k320DnWord m0 dp S i) ∧
    UnchangedExcept m0 m' np (8 * n) ∧
    x' 0 = x0 0 ∧ ∀ r, r ∉ k320DnCl → x' r = x0 r

/-- The state after the shift loop of the divisor, at 80: the words 1 to n - 1 stored. -/
def k320DnExit (x0 : Regs) (m0 : Mem) (dp np : BitVec 64) (n : Nat) (S : BitVec 64)
    (x' : Regs) (m' : Mem) : Prop :=
  (∀ i, 0 < i → i < n →
      memWord m' (np + BitVec.ofNat 64 (8 * i)).toNat = k320DnWord m0 dp S i) ∧
    UnchangedExcept m0 m' np (8 * n) ∧
    x' 0 = x0 0 ∧ ∀ r, r ∉ k320DnCl → x' r = x0 r

theorem k320_addr_m8 (u : BitVec 64) (k : Nat) (h1 : 1 ≤ k) (h : u.toNat + 8 * k ≤ 2 ^ 64) :
    u + BitVec.ofNat 64 (8 * k) + 18446744073709551608#64 = u + BitVec.ofNat 64 (8 * (k - 1)) := by
  bv_omega

theorem k320_addr_m8' (u : BitVec 64) (k : Nat) (h1 : 1 ≤ k) (h : u.toNat + 8 * k ≤ 2 ^ 64) :
    u + (BitVec.ofNat 64 (8 * k) + 18446744073709551608#64) = u + BitVec.ofNat 64 (8 * (k - 1)) := by
  bv_omega

theorem k320_off_m8 (k : Nat) (h1 : 1 ≤ k) (h : 8 * k < 2 ^ 64) :
    BitVec.ofNat 64 (8 * k) + 18446744073709551608#64 = BitVec.ofNat 64 (8 * (k - 1)) := by
  bv_omega

theorem k320_off_m8_zero (k : Nat) (h1 : 1 ≤ k) (h : 8 * k < 2 ^ 64) :
    BitVec.ofNat 64 (8 * k) + 18446744073709551608#64 = 0#64 ↔ k = 1 := by
  bv_omega

/-- The shift loop of the divisor from the store of the word `k` at 67: the next word at 71 or the
end at 80. -/
theorem k320DnWord_zero (m : Mem) (dp : BitVec 64) (i : Nat) :
    k320DnWord m dp 0#64 i = memWord m (dp + BitVec.ofNat 64 (8 * i)).toNat := by
  have hz : ∀ y : BitVec 64, (y >>> 1) >>> 63 = 0#64 := fun y => by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      Nat.shiftRight_eq_div_pow]
    have := y.isLt
    simp only [BitVec.toNat_ofNat]
    omega
  unfold k320DnWord
  rw [show (0#64 : BitVec 64).toNat % 64 = 0 from rfl,
    show ((0#64 : BitVec 64) ^^^ 18446744073709551615#64).toNat % 64 = 63 from rfl,
    BitVec.shiftLeft_zero, hz, BitVec.or_zero]

theorem k320_dn_tail {A : List (BitVec 64)} {hi : BitVec 20} {lo : BitVec 12} {base tgt : BitVec 64}
    {Q : Regs → Mem → Prop} (x0 : Regs) (m0 : Mem) (dp np : BitVec 64) (n : Nat) (S : BitVec 64)
    (h12 : x0.get 12#5 = np) (hn : n < 2 ^ 60) (hnn : np.toNat + 8 * n ≤ 2 ^ 64)
    (hnA : ∀ i < n, np + BitVec.ofNat 64 (8 * i) ∈ A)
    (hk : ∀ x' m', k320DnExit x0 m0 dp np n S x' m' →
      Reach A (udivrem_knuth_320_progAt hi lo) base (pcAt base 80) x' m' tgt Q)
    (k : Nat) (m' : Mem) (hk1 : 1 ≤ k) (hkn : k < n)
    (hw : ∀ i, k < i → i < n →
      memWord m' (np + BitVec.ofNat 64 (8 * i)).toNat = k320DnWord m0 dp S i)
    (hun : UnchangedExcept m0 m' np (8 * n))
    (xs : Regs) (h0 : xs 0 = x0 0) (hcl : ∀ r, r ∉ k320DnCl → xs r = x0 r)
    (h11 : xs.get 11#5 = BitVec.ofNat 64 (8 * k)) (h13 : xs.get 13#5 = k320DnWord m0 dp S k)
    (ih : ∀ k' < k, ∀ x' m', k320DnLoop x0 m0 dp np n S k' x' m' →
      Reach A (udivrem_knuth_320_progAt hi lo) base (pcAt base 71) x' m' tgt Q) :
    Reach A (udivrem_knuth_320_progAt hi lo) base (pcAt base 67) xs m' tgt Q := by
  have h12' : xs.get 12#5 = np := by
    rw [← Regs.eq_get xs (by decide), hcl _ (by decide), Regs.eq_get x0 (by decide)]; exact h12
  have hk8 : (np + BitVec.ofNat 64 (8 * k)).toNat = np.toNat + 8 * k :=
    toNat_add8 _ _ (by omega) (by omega)
  rw [← regs_set_of_get' (by decide) h11, ← regs_set_of_get' (by decide) h12',
    ← regs_set_of_get' (by decide) h13]
  rv_exec_cut 69
  rename_i wp hwp
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd, BitVec.reduceSignExtend, BitVec.add_zero]
  rv_val
  rw [hwp.eq]
  refine ⟨hnA k hkn, ?_⟩
  have hw' : ∀ i, k - 1 < i → i < n → memWord (memStore m' (np + BitVec.ofNat 64 (8 * k)).toNat
      (k320DnWord m0 dp S k)) (np + BitVec.ofNat 64 (8 * i)).toNat = k320DnWord m0 dp S i := by
    intro i hi1 hi2
    rcases Nat.lt_or_ge k i with hki | hki
    · have hi8 : (np + BitVec.ofNat 64 (8 * i)).toNat = np.toNat + 8 * i :=
        toNat_add8 _ _ (by omega) (by omega)
      rw [memWord_memStore_of_ne _ _ _ _ (by rw [hi8, hk8]; omega)]
      exact hw i hki hi2
    · rw [show i = k by omega, memWord_memStore_self]
  have hun' : UnchangedExcept m0 (memStore m' (np + BitVec.ofNat 64 (8 * k)).toNat
      (k320DnWord m0 dp S k)) np (8 * n) := by
    rw [unchangedExcept_memStore _ _ (by rw [hk8]; omega)]
    exact hun
  have hcl' : ∀ (a b c d : BitVec 64) (r : BitVec 5), r ∉ k320DnCl →
      (((((xs.set 13#5 d).set 12#5 np).set 11#5 a).set 15#5 b).set 11#5 c) r = x0 r := by
    intro a b c d r hr
    have hr' := hr
    simp only [k320DnCl, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    obtain ⟨h11', h13', h15'⟩ := hr'
    simp (config := { decide := true }) only [Regs.set_apply, h11', h13', h15', ↓reduceIte]
    split_ifs with hh
    · subst hh; rw [Regs.eq_get x0 (by decide)]; exact h12.symm
    · exact hcl r hr
  rv_exec_cut 71 80
  · -- The end.
    rename_i hb
    have hk2 : k = 1 := (k320_off_m8_zero k hk1 (by omega)).1 hb
    subst hk2
    refine hk _ _ ⟨fun i hi1 hi2 => hw' i (by omega) hi2, ?_, ?_, hcl' _ _ _ _⟩
    · exact hun'
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]; exact h0
  · -- The next word.
    rename_i hb
    have hk2 : k ≠ 1 := fun h => hb ((k320_off_m8_zero k hk1 (by omega)).2 h)
    refine ih (k - 1) (by omega) _ _ ⟨by omega, by omega, ?_, hw', hun', ?_, hcl' _ _ _ _⟩
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      exact k320_off_m8 k hk1 (by omega)
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]; exact h0

theorem k320_dn_loop {A : List (BitVec 64)} {hi : BitVec 20} {lo : BitVec 12} {base tgt : BitVec 64}
    {Q : Regs → Mem → Prop} (x0 : Regs) (m0 : Mem) (dp np : BitVec 64) (n : Nat) (S : BitVec 64)
    (h12 : x0.get 12#5 = np) (h19 : x0.get 19#5 = dp) (h21 : x0.get 21#5 = S)
    (h22 : x0.get 22#5 = S ^^^ 18446744073709551615#64) (hS : S.toNat < 64)
    (hn : n < 2 ^ 60) (hdn : dp.toNat + 8 * n ≤ 2 ^ 64) (hnn : np.toNat + 8 * n ≤ 2 ^ 64)
    (hdis : dp.toNat + 8 * n ≤ np.toNat ∨ np.toNat + 8 * n ≤ dp.toNat)
    (hdA : ∀ i < n, dp + BitVec.ofNat 64 (8 * i) ∈ A)
    (hnA : ∀ i < n, np + BitVec.ofNat 64 (8 * i) ∈ A)
    (hk : ∀ x' m', k320DnExit x0 m0 dp np n S x' m' →
      Reach A (udivrem_knuth_320_progAt hi lo) base (pcAt base 80) x' m' tgt Q) :
    ∀ k x' m', k320DnLoop x0 m0 dp np n S k x' m' →
      Reach A (udivrem_knuth_320_progAt hi lo) base (pcAt base 71) x' m' tgt Q := by
  apply Reach.loop (k320DnLoop x0 m0 dp np n S)
  intro k x' m' ⟨hk1, hkn, h11, hw, hun, h0, hcl⟩ ih
  have g : ∀ r, r ∉ k320DnCl → r ≠ 0 → x'.get r = x0.get r := by
    intro r hr hr0
    rw [← Regs.eq_get x' hr0, ← Regs.eq_get x0 hr0]; exact hcl r hr
  have h12' : x'.get 12#5 = np := by rw [g _ (by decide) (by decide)]; exact h12
  have h19' : x'.get 19#5 = dp := by rw [g _ (by decide) (by decide)]; exact h19
  have h21' : x'.get 21#5 = S := by rw [g _ (by decide) (by decide)]; exact h21
  have h22' : x'.get 22#5 = S ^^^ 18446744073709551615#64 := by
    rw [g _ (by decide) (by decide)]; exact h22
  rw [← regs_set_of_get' (by decide) h11, ← regs_set_of_get' (by decide) h12',
    ← regs_set_of_get' (by decide) h19', ← regs_set_of_get' (by decide) h21',
    ← regs_set_of_get' (by decide) h22']
  have hk8 : (dp + BitVec.ofNat 64 (8 * k)).toNat = dp.toNat + 8 * k :=
    toNat_add8 _ _ (by omega) (by omega)
  have hk18 : (dp + BitVec.ofNat 64 (8 * (k - 1))).toNat = dp.toNat + 8 * (k - 1) :=
    toNat_add8 _ _ (by omega) (by omega)
  -- The registers outside the loop: the values of x0.
  have hcl1 : ∀ r, r ∉ k320DnCl →
      ((((x'.set 22#5 (S ^^^ 18446744073709551615#64)).set 21#5 S).set 19#5 dp).set 12#5 np) r =
        x0 r := by
    intro r hr
    by_cases e12 : r = 12#5
    · subst e12; simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
      rw [Regs.eq_get x0 (by decide)]; exact h12.symm
    by_cases e19 : r = 19#5
    · subst e19; simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
      rw [Regs.eq_get x0 (by decide)]; exact h19.symm
    by_cases e21 : r = 21#5
    · subst e21; simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
      rw [Regs.eq_get x0 (by decide)]; exact h21.symm
    by_cases e22 : r = 22#5
    · subst e22; simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
      rw [Regs.eq_get x0 (by decide)]; exact h22.symm
    simp (config := { decide := true }) only [Regs.set_apply, e12, e19, e21, e22, ↓reduceIte]
    exact hcl r hr
  rv_exec_cut 72
  rename_i wa hwa
  -- d[k]
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd, BitVec.reduceSignExtend, BitVec.add_zero]
  rv_val
  rw [hwa.eq]
  refine ⟨hdA k hkn, fun wk hwk => ?_⟩
  have hdk : wk = memWord m0 (dp + BitVec.ofNat 64 (8 * k)).toNat := by
    rw [hwk.eq]; exact memWord_of_unchangedExcept hun _ (by rw [hk8]; omega)
  rv_exec_cut 67 74
  · -- S = 0: d[k] as it is.
    rename_i hS0
    subst hS0
    refine k320_dn_tail x0 m0 dp np n 0#64 h12 hn hnn hnA hk k m' hk1 hkn hw hun _ ?_ ?_ ?_ ?_ ih
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]; exact h0
    · intro r hr
      have hr' := hr
      simp only [k320DnCl, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      obtain ⟨h11', h13', h15'⟩ := hr'
      simp (config := { decide := true }) only [Regs.set_apply, h11', h13', h15', ↓reduceIte]
      exact hcl1 r hr
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      rw [k320DnWord_zero]; exact hdk
  · -- S ≠ 0: the funnel shift with d[k - 1].
    rename_i hS0
    refine Reach.step (by decide) (by rv_fetch) ?_
    simp only [StepGoal, Nat.reduceAdd, BitVec.reduceSignExtend, BitVec.add_zero]
    rv_val
    rw [k320_addr_m8' _ _ hk1 (by omega)]
    refine ⟨hdA (k - 1) (by omega), fun wk1 hwk1 => ?_⟩
    have hdk1 : wk1 = memWord m0 (dp + BitVec.ofNat 64 (8 * (k - 1))).toNat := by
      rw [hwk1.eq]; exact memWord_of_unchangedExcept hun _ (by rw [hk18]; omega)
    rv_exec_cut 67
    rename_i a ha b hb c hc d hd
    refine k320_dn_tail x0 m0 dp np n S h12 hn hnn hnA hk k m' hk1 hkn hw hun _ ?_ ?_ ?_ ?_ ih
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]; exact h0
    · intro r hr
      have hr' := hr
      simp only [k320DnCl, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      obtain ⟨h11', h13', h15'⟩ := hr'
      simp (config := { decide := true }) only [Regs.set_apply, h11', h13', h15', ↓reduceIte]
      exact hcl1 r hr
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      rw [hd.eq, ha.eq, hc.eq, hb.eq, hdk, hdk1]
      rfl

/-- The registers that the shift loop of the remainder of `udivrem_knuth<320, 256>()` changes. -/
def k320RCl : List (BitVec 5) := [10#5, 12#5, 13#5, 14#5, 19#5]

/-- The word `i` of the normalized remainder shifted right by `S` with the low bits of the word
above, as the code of `udivrem_knuth<320, 256>()` computes it. -/
def k320RWord (m : Mem) (up S : BitVec 64) (i : Nat) : BitVec 64 :=
  (memWord m (up + BitVec.ofNat 64 (8 * (i + 1))).toNat <<< 1) <<<
      ((S ^^^ 18446744073709551615#64).toNat % 64) |||
    memWord m (up + BitVec.ofNat 64 (8 * i)).toNat >>> (S.toNat % 64)

/-- The state at the head 143 of the shift loop of the remainder before the word `i`: the words
below it shifted and stored. -/
def k320RLoop (x0 : Regs) (m0 : Mem) (up rp : BitVec 64) (n : Nat) (S : BitVec 64) (k : Nat)
    (x' : Regs) (m' : Mem) : Prop :=
  ∃ i, i + 1 < n ∧ k = n - 1 - i ∧
    x'.get 10#5 = rp + BitVec.ofNat 64 (8 * i) ∧
    x'.get 19#5 = up + BitVec.ofNat 64 (8 * (i + 1)) ∧
    x'.get 12#5 = memWord m0 (up + BitVec.ofNat 64 (8 * i)).toNat ∧
    (∀ j, j < i → memWord m' (rp + BitVec.ofNat 64 (8 * j)).toNat = k320RWord m0 up S j) ∧
    UnchangedExcept m0 m' rp (8 * n) ∧
    x' 0 = x0 0 ∧ ∀ r, r ∉ k320RCl → x' r = x0 r

/-- The state after the shift loop of the remainder, at 153: the words 0 to n - 2 stored. -/
def k320RExit (x0 : Regs) (m0 : Mem) (up rp : BitVec 64) (n : Nat) (S : BitVec 64)
    (x' : Regs) (m' : Mem) : Prop :=
  (∀ j, j + 1 < n → memWord m' (rp + BitVec.ofNat 64 (8 * j)).toNat = k320RWord m0 up S j) ∧
    UnchangedExcept m0 m' rp (8 * n) ∧
    x' 0 = x0 0 ∧ ∀ r, r ∉ k320RCl → x' r = x0 r

theorem k320_r_end (i n : Nat) (hi : i + 1 < n) (hn : n < 2 ^ 60) :
    BitVec.ofNat 64 (8 * i) + 8#64 = BitVec.ofNat 64 (8 * (n - 1)) ↔ i + 2 = n := by
  bv_omega

theorem k320_p8 (u : BitVec 64) (i : Nat) :
    u + (BitVec.ofNat 64 (8 * i) + 8#64) = u + BitVec.ofNat 64 (8 * (i + 1)) := by
  bv_omega

theorem k320_r_loop {A : List (BitVec 64)} {hi : BitVec 20} {lo : BitVec 12} {base tgt : BitVec 64}
    {Q : Regs → Mem → Prop} (x0 : Regs) (m0 : Mem) (up rp : BitVec 64) (n : Nat) (S : BitVec 64)
    (h11 : x0.get 11#5 = rp + BitVec.ofNat 64 (8 * (n - 1))) (h21 : x0.get 21#5 = S)
    (h22 : x0.get 22#5 = S ^^^ 18446744073709551615#64)
    (hn : n < 2 ^ 60) (hup : up.toNat + 8 * n ≤ 2 ^ 64) (hrp : rp.toNat + 8 * n ≤ 2 ^ 64)
    (hdis : up.toNat + 8 * n ≤ rp.toNat ∨ rp.toNat + 8 * n ≤ up.toNat)
    (huA : ∀ i < n, up + BitVec.ofNat 64 (8 * i) ∈ A)
    (hrA : ∀ i < n, rp + BitVec.ofNat 64 (8 * i) ∈ A)
    (hk : ∀ x' m', k320RExit x0 m0 up rp n S x' m' →
      Reach A (udivrem_knuth_320_progAt hi lo) base (pcAt base 153) x' m' tgt Q) :
    ∀ k x' m', k320RLoop x0 m0 up rp n S k x' m' →
      Reach A (udivrem_knuth_320_progAt hi lo) base (pcAt base 143) x' m' tgt Q := by
  apply Reach.loop (k320RLoop x0 m0 up rp n S)
  intro k x' m' ⟨i, hin, hk', h10, h19, h12, hw, hun, h0, hcl⟩ ih
  subst hk'
  have g : ∀ r, r ∉ k320RCl → r ≠ 0 → x'.get r = x0.get r := by
    intro r hr hr0
    rw [← Regs.eq_get x' hr0, ← Regs.eq_get x0 hr0]; exact hcl r hr
  have h11' : x'.get 11#5 = rp + BitVec.ofNat 64 (8 * (n - 1)) := by
    rw [g _ (by decide) (by decide)]; exact h11
  have h21' : x'.get 21#5 = S := by rw [g _ (by decide) (by decide)]; exact h21
  have h22' : x'.get 22#5 = S ^^^ 18446744073709551615#64 := by
    rw [g _ (by decide) (by decide)]; exact h22
  have hu1 : (up + BitVec.ofNat 64 (8 * (i + 1))).toNat = up.toNat + 8 * (i + 1) :=
    toNat_add8 _ _ (by omega) (by omega)
  have hri : (rp + BitVec.ofNat 64 (8 * i)).toNat = rp.toNat + 8 * i :=
    toNat_add8 _ _ (by omega) (by omega)
  rw [← regs_set_of_get' (by decide) h10, ← regs_set_of_get' (by decide) h19,
    ← regs_set_of_get' (by decide) h12, ← regs_set_of_get' (by decide) h11',
    ← regs_set_of_get' (by decide) h21', ← regs_set_of_get' (by decide) h22']
  -- un[i + 1]
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd, BitVec.reduceSignExtend, BitVec.add_zero]
  rv_val
  refine ⟨huA (i + 1) hin, fun wu hwu => ?_⟩
  have hdu : wu = memWord m0 (up + BitVec.ofNat 64 (8 * (i + 1))).toNat := by
    rw [hwu.eq]; exact memWord_of_unchangedExcept hun _ (by rw [hu1]; omega)
  rv_exec_cut 148
  rename_i a ha b hb c hc v hv
  have hv' : v = k320RWord m0 up S i := by
    rw [hv.eq, hc.eq, hb.eq, ha.eq, hdu]; rfl
  -- The store of the word i.
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd, BitVec.reduceSignExtend, BitVec.add_zero]
  rv_val
  refine ⟨hrA i (by omega), ?_⟩
  have hw' : ∀ j, j < i + 1 → memWord (memStore m' (rp + BitVec.ofNat 64 (8 * i)).toNat v)
      (rp + BitVec.ofNat 64 (8 * j)).toNat = k320RWord m0 up S j := by
    intro j hj
    rcases Nat.lt_or_ge j i with hji | hji
    · have hj8 : (rp + BitVec.ofNat 64 (8 * j)).toNat = rp.toNat + 8 * j :=
        toNat_add8 _ _ (by omega) (by omega)
      rw [memWord_memStore_of_ne _ _ _ _ (by rw [hj8, hri]; omega)]
      exact hw j hji
    · rw [show j = i by omega, memWord_memStore_self, hv']
  have hun' : UnchangedExcept m0 (memStore m' (rp + BitVec.ofNat 64 (8 * i)).toNat v) rp (8 * n) := by
    rw [unchangedExcept_memStore _ _ (by rw [hri]; omega)]
    exact hun
  have hcl' : ∀ (d e f g h i' j k l mm nn : BitVec 64) (r : BitVec 5), r ∉ k320RCl →
      ((((((((((((((x'.set 22#5 (S ^^^ 18446744073709551615#64)).set 21#5 S).set 11#5 (rp + BitVec.ofNat 64 (8 * (n - 1)))).set 12#5 d).set 19#5 e).set 10#5 f).set 13#5 g).set 12#5 h).set 14#5 i').set 14#5 j).set 12#5 k).set 10#5 l).set 19#5 mm).set 12#5 nn) r =
        x0 r := by
    intro d e f g h i' j k l mm nn r hr
    have hr' := hr
    simp only [k320RCl, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    obtain ⟨e10, e12, e13, e14, e19⟩ := hr'
    by_cases e11 : r = 11#5
    · subst e11; simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
      rw [Regs.eq_get x0 (by decide)]; exact h11.symm
    by_cases e21 : r = 21#5
    · subst e21; simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
      rw [Regs.eq_get x0 (by decide)]; exact h21.symm
    by_cases e22 : r = 22#5
    · subst e22; simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
      rw [Regs.eq_get x0 (by decide)]; exact h22.symm
    simp (config := { decide := true }) only [Regs.set_apply, e10, e11, e12, e13, e14, e19, e21,
      e22, ↓reduceIte]
    exact hcl r hr
  rv_exec_cut 143 153
  · -- The next word.
    rename_i hb
    have hi2 : i + 2 ≠ n := fun h => hb ((k320_r_end i n hin hn).2 h)
    refine ih (n - 1 - (i + 1)) (by omega) _ _ ⟨i + 1, by omega, rfl, ?_, ?_, ?_, hw', hun', ?_,
      hcl' _ _ _ _ _ _ _ _ _ _ _⟩
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact k320_p8 _ _
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact k320_p8 _ _
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact hdu
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]; exact h0
  · -- The end.
    rename_i hb
    have hi2 : i + 2 = n := (k320_r_end i n hin hn).1 hb
    refine hk _ _ ⟨fun j hj => hw' j (by omega), hun', ?_, hcl' _ _ _ _ _ _ _ _ _ _ _⟩
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]; exact h0

/-- The shift loop of the divisor from its first word n - 1 at 71. -/
theorem k320_dn_start {A : List (BitVec 64)} {hi : BitVec 20} {lo : BitVec 12} {base tgt : BitVec 64}
    {Q : Regs → Mem → Prop} (x0 : Regs) (m0 : Mem) (dp np : BitVec 64) (n : Nat) (S : BitVec 64)
    (h11 : x0.get 11#5 = BitVec.ofNat 64 (8 * (n - 1))) (hn2 : 2 ≤ n)
    (h12 : x0.get 12#5 = np) (h19 : x0.get 19#5 = dp) (h21 : x0.get 21#5 = S)
    (h22 : x0.get 22#5 = S ^^^ 18446744073709551615#64) (hS : S.toNat < 64)
    (hn : n < 2 ^ 60) (hdn : dp.toNat + 8 * n ≤ 2 ^ 64) (hnn : np.toNat + 8 * n ≤ 2 ^ 64)
    (hdis : dp.toNat + 8 * n ≤ np.toNat ∨ np.toNat + 8 * n ≤ dp.toNat)
    (hdA : ∀ i < n, dp + BitVec.ofNat 64 (8 * i) ∈ A)
    (hnA : ∀ i < n, np + BitVec.ofNat 64 (8 * i) ∈ A)
    (hk : ∀ x' m', k320DnExit x0 m0 dp np n S x' m' →
      Reach A (udivrem_knuth_320_progAt hi lo) base (pcAt base 80) x' m' tgt Q) :
    Reach A (udivrem_knuth_320_progAt hi lo) base (pcAt base 71) x0 m0 tgt Q :=
  k320_dn_loop x0 m0 dp np n S h12 h19 h21 h22 hS hn hdn hnn hdis hdA hnA hk (n - 1) x0 m0
    ⟨by omega, by omega, h11, fun i h1 h2 => absurd h2 (by omega), unchangedExcept_refl _ _ _,
      rfl, fun _ _ => rfl⟩

/-- The shift loop of the remainder from its first word 0 at 143. -/
theorem k320_r_start {A : List (BitVec 64)} {hi : BitVec 20} {lo : BitVec 12} {base tgt : BitVec 64}
    {Q : Regs → Mem → Prop} (x0 : Regs) (m0 : Mem) (up rp : BitVec 64) (n : Nat) (S : BitVec 64)
    (h10 : x0.get 10#5 = rp) (h19 : x0.get 19#5 = up + 8#64)
    (h12 : x0.get 12#5 = memWord m0 up.toNat) (hn2 : 2 ≤ n)
    (h11 : x0.get 11#5 = rp + BitVec.ofNat 64 (8 * (n - 1))) (h21 : x0.get 21#5 = S)
    (h22 : x0.get 22#5 = S ^^^ 18446744073709551615#64)
    (hn : n < 2 ^ 60) (hup : up.toNat + 8 * n ≤ 2 ^ 64) (hrp : rp.toNat + 8 * n ≤ 2 ^ 64)
    (hdis : up.toNat + 8 * n ≤ rp.toNat ∨ rp.toNat + 8 * n ≤ up.toNat)
    (huA : ∀ i < n, up + BitVec.ofNat 64 (8 * i) ∈ A)
    (hrA : ∀ i < n, rp + BitVec.ofNat 64 (8 * i) ∈ A)
    (hk : ∀ x' m', k320RExit x0 m0 up rp n S x' m' →
      Reach A (udivrem_knuth_320_progAt hi lo) base (pcAt base 153) x' m' tgt Q) :
    Reach A (udivrem_knuth_320_progAt hi lo) base (pcAt base 143) x0 m0 tgt Q :=
  k320_r_loop x0 m0 up rp n S h11 h21 h22 hn hup hrp hdis huA hrA hk (n - 1 - 0) x0 m0
    ⟨0, by omega, rfl, by rw [h10]; try simp, by rw [h19]; try simp, by rw [h12]; try simp,
      fun j hj => absurd hj (by omega), unchangedExcept_refl _ _ _, rfl, fun _ _ => rfl⟩

/-- The memory after the prologue of `udivrem_knuth<320, 256>()`: ra and s0 to s6 stored in the
frame. -/
abbrev k320FrameMem (x : Regs) (m : Mem) : Mem :=
  memStore (memStore (memStore (memStore (memStore (memStore (memStore (memStore m
    (x.get 2#5 + 18446744073709551608#64).toNat (x.get 1#5))
    (x.get 2#5 + 18446744073709551600#64).toNat (x.get 8#5))
    (x.get 2#5 + 18446744073709551592#64).toNat (x.get 9#5))
    (x.get 2#5 + 18446744073709551584#64).toNat (x.get 18#5))
    (x.get 2#5 + 18446744073709551576#64).toNat (x.get 19#5))
    (x.get 2#5 + 18446744073709551568#64).toNat (x.get 20#5))
    (x.get 2#5 + 18446744073709551560#64).toNat (x.get 21#5))
    (x.get 2#5 + 18446744073709551552#64).toNat (x.get 22#5)

/-- The addresses of the saved registers in the stack of 288 bytes below sp. -/
theorem k320_frame_toNat (sp : BitVec 64) (hs : (sp - 288#64).toNat + 288 ≤ 2 ^ 64) :
    (sp + 18446744073709551608#64).toNat = (sp - 288#64).toNat + 280 ∧
    (sp + 18446744073709551600#64).toNat = (sp - 288#64).toNat + 272 ∧
    (sp + 18446744073709551592#64).toNat = (sp - 288#64).toNat + 264 ∧
    (sp + 18446744073709551584#64).toNat = (sp - 288#64).toNat + 256 ∧
    (sp + 18446744073709551576#64).toNat = (sp - 288#64).toNat + 248 ∧
    (sp + 18446744073709551568#64).toNat = (sp - 288#64).toNat + 240 ∧
    (sp + 18446744073709551560#64).toNat = (sp - 288#64).toNat + 232 ∧
    (sp + 18446744073709551552#64).toNat = (sp - 288#64).toNat + 224 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_omega

theorem k320FrameMem_unchanged (x : Regs) (m : Mem)
    (hs : (x.get 2#5 - 288#64).toNat + 288 ≤ 2 ^ 64) :
    UnchangedExcept m (k320FrameMem x m) (x.get 2#5 - 288#64) 288 := by
  obtain ⟨f1, f8, f9, f18, f19, f20, f21, f22⟩ := k320_frame_toNat (x.get 2#5) hs
  simp only [k320FrameMem]
  repeat rw [unchangedExcept_memStore _ _ (by omega)]
  exact unchangedExcept_refl _ _ _

theorem k320FrameMem_words (x : Regs) (m : Mem) (hs : (x.get 2#5 - 288#64).toNat + 288 ≤ 2 ^ 64) :
    memWord (k320FrameMem x m) (x.get 2#5 + 18446744073709551608#64).toNat = x.get 1#5 ∧
    memWord (k320FrameMem x m) (x.get 2#5 + 18446744073709551600#64).toNat = x.get 8#5 ∧
    memWord (k320FrameMem x m) (x.get 2#5 + 18446744073709551592#64).toNat = x.get 9#5 ∧
    memWord (k320FrameMem x m) (x.get 2#5 + 18446744073709551584#64).toNat = x.get 18#5 ∧
    memWord (k320FrameMem x m) (x.get 2#5 + 18446744073709551576#64).toNat = x.get 19#5 ∧
    memWord (k320FrameMem x m) (x.get 2#5 + 18446744073709551568#64).toNat = x.get 20#5 ∧
    memWord (k320FrameMem x m) (x.get 2#5 + 18446744073709551560#64).toNat = x.get 21#5 ∧
    memWord (k320FrameMem x m) (x.get 2#5 + 18446744073709551552#64).toNat = x.get 22#5 := by
  obtain ⟨f1, f8, f9, f18, f19, f20, f21, f22⟩ := k320_frame_toNat (x.get 2#5) hs
  simp only [k320FrameMem]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := omega) only [memWord_memStore_self, memWord_memStore_of_ne]

theorem get_of_cl {x y : Regs} {cl : List (BitVec 5)} (h : ∀ r, r ∉ cl → x r = y r) {r : BitVec 5}
    (hr : r ∉ cl) (hr0 : r ≠ 0) : x.get r = y.get r := by
  rw [← Regs.eq_get x hr0, h r hr, Regs.eq_get y hr0]

theorem k320_sp144 (sp : BitVec 64) (hs : (sp - 288#64).toNat + 288 ≤ 2 ^ 64) :
    sp + 18446744073709551472#64 = sp - 288#64 + BitVec.ofNat 64 (8 * 18) := by
  bv_omega

/-- The numerator has at least as many words as the divisor. -/
theorem k320_n_le_mm {U D n mm : Nat} (hD : 2 ^ (64 * (n - 1)) ≤ D) (hU : U < 2 ^ (64 * mm))
    (htop : D / 2 ^ (64 * (n - 1)) ≤ U / 2 ^ (64 * (n - 1))) : n ≤ mm + 1 - 1 ∧ n - 1 < mm := by
  have h1 : 1 ≤ D / 2 ^ (64 * (n - 1)) := (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).2 (by omega)
  have h2 : 2 ^ (64 * (n - 1)) ≤ U := by
    have := (Nat.le_div_iff_mul_le (Nat.two_pow_pos (64 * (n - 1)))).1 (le_trans h1 htop)
    omega
  have h3 : 64 * (n - 1) < 64 * mm :=
    (Nat.pow_lt_pow_iff_right (by norm_num)).1 (lt_of_le_of_lt h2 hU)
  omega

theorem unchangedExcept2_memStore_in {m m' : Mem} {a b : BitVec 64} {la lb : Nat}
    (h : UnchangedExcept2 m m' a la b lb) (c : Nat) (v : BitVec 64)
    (hc : a.toNat ≤ c ∧ c + 8 ≤ a.toNat + la) : UnchangedExcept2 m (memStore m' c v) a la b lb := by
  intro k hk1 hk2
  rw [getElem?_memStore_of_ne _ _ _ _ (by omega)]
  exact h k hk1 hk2

theorem k320_sp288 (sp : BitVec 64) : sp + 18446744073709551472#64 - 144#64 = sp - 288#64 := by
  bv_omega

/-- The count of the normalized words to divide and the preconditions of the Knuth division. -/
theorem k320_ulen {U D utop dtop mm n s Ulow Dlow ulen : Nat} (hs : s < 64) (hn3 : 3 ≤ n)
    (hnm : n ≤ mm) (hmm : mm ≤ 5)
    (hUs : U = Ulow + 2 ^ (64 * (mm - 1)) * utop) (hUl : Ulow < 2 ^ (64 * (mm - 1)))
    (hut : utop < 2 ^ 64)
    (hDs : D = Dlow + 2 ^ (64 * (n - 1)) * dtop) (hDl : Dlow < 2 ^ (64 * (n - 1)))
    (hU : U < 2 ^ (64 * mm)) (htop : D / 2 ^ (64 * (n - 1)) ≤ U / 2 ^ (64 * (n - 1)))
    (hnorm : 2 ^ 63 ≤ dtop * 2 ^ s) (hnorm' : dtop * 2 ^ s < 2 ^ 64)
    (hl : ulen = mm + if dtop ≤ utop then 1 else 0) :
    n < ulen ∧ ulen ≤ 6 ∧ U * 2 ^ s < 2 ^ (64 * ulen) ∧
      U * 2 ^ s / 2 ^ (64 * (ulen - n)) < D * 2 ^ s ∧ 2 ^ (64 * n - 1) ≤ D * 2 ^ s ∧
      D * 2 ^ s < 2 ^ (64 * n) := by
  have hd0 : 0 < dtop := by
    rcases Nat.eq_zero_or_pos dtop with h | h
    · subst h; simp at hnorm
    · exact h
  have hPpos : 0 < 2 ^ (64 * (n - 1)) := Nat.two_pow_pos _
  have hDdiv : D / 2 ^ (64 * (n - 1)) = dtop := by
    rw [hDs, Nat.add_mul_div_left _ _ hPpos, Nat.div_eq_of_lt hDl, Nat.zero_add]
  have hVb : dtop * 2 ^ (64 * (n - 1)) ≤ D := by rw [hDs]; nlinarith
  have hDlt : D < (dtop + 1) * 2 ^ (64 * (n - 1)) := by rw [hDs]; nlinarith
  have hVs : D * 2 ^ s < 2 ^ (64 * n) := by
    have := norm_top_lt hDlt hnorm' hs
    rwa [show n - 1 + 1 = n by omega] at this
  have hlen : n < ulen := by
    rcases Nat.lt_or_ge n mm with h | h
    · split_ifs at hl <;> omega
    · have hnm' : n = mm := by omega
      subst hnm'
      have hUdiv : U / 2 ^ (64 * (n - 1)) = utop := by
        rw [hUs, Nat.add_mul_div_left _ _ hPpos, Nat.div_eq_of_lt hUl, Nat.zero_add]
      rw [hDdiv, hUdiv] at htop
      rw [if_pos htop] at hl
      omega
  have hUlt : U < (utop + 1) * 2 ^ (64 * (mm - 1)) := by rw [hUs]; nlinarith
  obtain ⟨h1, h2⟩ := knuth_ulen (by omega) (by omega) hut hUlt hVb hVs hs hd0 hl hlen
  refine ⟨hlen, by split_ifs at hl <;> omega, h1, h2, ?_, hVs⟩
  calc 2 ^ (64 * n - 1) = 2 ^ (64 * (n - 1)) * 2 ^ 63 := by
        rw [← pow_add]; congr 1; omega
    _ ≤ 2 ^ (64 * (n - 1)) * (dtop * 2 ^ s) := Nat.mul_le_mul_left _ hnorm
    _ = dtop * 2 ^ (64 * (n - 1)) * 2 ^ s := by ring
    _ ≤ D * 2 ^ s := Nat.mul_le_mul_right _ hVb

theorem k320_sp_offsets (sp : BitVec 64) (hs : (sp - 288#64).toNat + 288 ≤ 2 ^ 64) :
    (sp + 18446744073709551472#64).toNat = (sp - 288#64).toNat + 144 ∧
    (sp + 18446744073709551504#64).toNat = (sp - 288#64).toNat + 176 ∧
    (sp + 18446744073709551512#64).toNat = (sp - 288#64).toNat + 184 := by
  refine ⟨?_, ?_, ?_⟩ <;> bv_omega

theorem k320_sp112 (sp : BitVec 64) (hs : (sp - 288#64).toNat + 288 ≤ 2 ^ 64) :
    sp + 18446744073709551504#64 = sp - 288#64 + BitVec.ofNat 64 (8 * 22) := by
  bv_omega

theorem k320_up8 (sp : BitVec 64) :
    sp + 18446744073709551512#64 = sp + 18446744073709551504#64 + 8#64 := by
  bv_omega

theorem k320_rend (n res : BitVec 64) (h1 : 1 ≤ n.toNat) (hn : 8 * n.toNat < 2 ^ 64) :
    n <<< 3 + res + 32#64 = res + 40#64 + BitVec.ofNat 64 (8 * (n.toNat - 1)) := by
  bv_omega

theorem k320_un_top (sp n : BitVec 64) (h1 : 1 ≤ n.toNat) (hn : 8 * n.toNat < 2 ^ 64) :
    sp + (18446744073709551504#64 + n <<< 3) + 18446744073709551608#64 =
      sp + 18446744073709551504#64 + BitVec.ofNat 64 (8 * (n.toNat - 1)) := by
  bv_omega

/-- `udivrem_knuth<320, 256>()` from the store of the quotient word m - n at 133: the call of
`udivrem_knuth_normalized()`, the shift of the remainder and the return. -/
theorem k320_tail {hi : BitVec 20} {lo : BitVec 12} (base T : BitVec 64) (x : Regs) (m : Mem)
    (hb : base &&& 3 = 0)
    (hT : pcAt base 184 + ((hi ++ 0x000#12).signExtend 64 + lo.signExtend 64) = T)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64) (hr : x.get 1#5 &&& 3 = 0)
    (hstk : (x.get 2#5 - 288#64).toNat + 288 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 288#64).toNat)
    (hrT : (x.get 10#5).toNat + 72 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hpre : udivrem_knuth_320.pre x m)
    (s : Nat) (hs : s < 64)
    (hnorm : 2 ^ 63 ≤ (memWord m (x.get 13#5 + BitVec.ofNat 64 (8 * ((x.get 14#5).toNat - 1))).toNat).toNat * 2 ^ s)
    (hnorm' : (memWord m (x.get 13#5 + BitVec.ofNat 64 (8 * ((x.get 14#5).toNat - 1))).toNat).toNat * 2 ^ s < 2 ^ 64)
    (xs : Regs) (ms : Mem)
    (h2 : xs.get 2#5 = x.get 2#5 + 18446744073709551472#64) (h8 : xs.get 8#5 = x.get 10#5)
    (h9 : xs.get 9#5 = x.get 12#5)
    (h12 : (xs.get 12#5).toNat = (x.get 12#5).toNat +
      if (memWord m (x.get 13#5 + BitVec.ofNat 64 (8 * ((x.get 14#5).toNat - 1))).toNat).toNat ≤
        (memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * ((x.get 12#5).toNat - 1))).toNat).toNat
      then 1 else 0)
    (h13 : xs.get 13#5 = x.get 10#5 + BitVec.ofNat 64 (8 * ((x.get 12#5).toNat - (x.get 14#5).toNat)))
    (h14 : xs.get 14#5 = x.get 14#5) (h18 : xs.get 18#5 = x.get 11#5)
    (h19 : xs.get 19#5 = x.get 2#5 + 18446744073709551512#64)
    (h20 : xs.get 20#5 = x.get 14#5 <<< 3) (h21 : xs.get 21#5 = BitVec.ofNat 64 s)
    (h22 : xs.get 22#5 = BitVec.ofNat 64 s ^^^ 18446744073709551615#64)
    (hcs : ∀ r ∈ [3#5, 4#5, 23#5, 24#5, 25#5, 26#5, 27#5], xs r = x r)
    (hfw : memWord ms (x.get 2#5 + 18446744073709551608#64).toNat = x.get 1#5 ∧
      memWord ms (x.get 2#5 + 18446744073709551600#64).toNat = x.get 8#5 ∧
      memWord ms (x.get 2#5 + 18446744073709551592#64).toNat = x.get 9#5 ∧
      memWord ms (x.get 2#5 + 18446744073709551584#64).toNat = x.get 18#5 ∧
      memWord ms (x.get 2#5 + 18446744073709551576#64).toNat = x.get 19#5 ∧
      memWord ms (x.get 2#5 + 18446744073709551568#64).toNat = x.get 20#5 ∧
      memWord ms (x.get 2#5 + 18446744073709551560#64).toNat = x.get 21#5 ∧
      memWord ms (x.get 2#5 + 18446744073709551552#64).toNat = x.get 22#5)
    (hunc : UnchangedExcept2 m ms (x.get 10#5) 72 (x.get 2#5 - 288#64) 288)
    (hres : ∀ i < 9, memWord ms (x.get 10#5 + BitVec.ofNat 64 (8 * i)).toNat = 0#64)
    (hdnw : words ms (x.get 2#5 + 18446744073709551472#64) (x.get 14#5).toNat =
      words m (x.get 13#5) (x.get 14#5).toNat * 2 ^ s)
    (hunw : words ms (x.get 2#5 + 18446744073709551504#64) 6 = words m (x.get 11#5) 5 * 2 ^ s) :
    Reach (bufWords (x.get 11#5) 5 ++ bufWords (x.get 13#5) (x.get 14#5).toNat ++
        bufWords (x.get 10#5) 9 ++ bufWords (x.get 2#5 - 288#64) 36 ++ bufWords T 256)
      (udivrem_knuth_320_progAt hi lo) base (pcAt base 133) xs ms (x.get 1#5)
      (udivrem_knuth_320.post x m) := by
  have hpre' := hpre
  simp only [udivrem_knuth_320.pre, Buf, Disjoint] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hda, hdn⟩, hdru, hdrd, ⟨hsa, hsn⟩, hdsu, hdsd, hdsr, hn3, hn4,
    hD, hmm, hU, -, htop⟩ := hpre'
  have hnm := k320_n_le_mm hD hU htop
  obtain ⟨hdnT, hunT, hun8T⟩ := k320_sp_offsets (x.get 2#5) hsn
  -- The top words of u and d.
  have hUw : words m (x.get 11#5) (x.get 12#5).toNat = words m (x.get 11#5) 5 := by
    have hs5 := words_split m (x.get 12#5).toNat (5 - (x.get 12#5).toNat) (x.get 11#5)
    rw [show (x.get 12#5).toNat + (5 - (x.get 12#5).toNat) = 5 by omega] at hs5
    exact lo_of_lt hs5 hU
  have hUs := words_succ_top m ((x.get 12#5).toNat - 1) (x.get 11#5)
  rw [show (x.get 12#5).toNat - 1 + 1 = (x.get 12#5).toNat by omega, hUw] at hUs
  have hDs := words_succ_top m ((x.get 14#5).toNat - 1) (x.get 13#5)
  rw [show (x.get 14#5).toNat - 1 + 1 = (x.get 14#5).toNat by omega] at hDs
  obtain ⟨hlen, hl6, hUlt, hUq, hDn, hDlt⟩ := k320_ulen hs hn3 (by omega) hmm hUs
    (words_lt _ _ _) (BitVec.isLt _) hDs (words_lt _ _ _) hU htop hnorm hnorm' h12
  -- The words of the normalized u to divide.
  have hunl : words ms (x.get 2#5 + 18446744073709551504#64) (xs.get 12#5).toNat =
      words m (x.get 11#5) 5 * 2 ^ s := by
    have hs6 := words_split ms (xs.get 12#5).toNat (6 - (xs.get 12#5).toNat)
      (x.get 2#5 + 18446744073709551504#64)
    rw [show (xs.get 12#5).toNat + (6 - (xs.get 12#5).toNat) = 6 by omega, hunw] at hs6
    exact lo_of_lt hs6 hUlt
  rw [← regs_set_of_get' (by decide) h2, ← regs_set_of_get' (by decide) h8,
    ← regs_set_of_get' (by decide) h9, ← regs_set_of_get' (by decide) h13,
    ← regs_set_of_get' (by decide) h14, ← regs_set_of_get' (by decide) h18,
    ← regs_set_of_get' (by decide) h19, ← regs_set_of_get' (by decide) h20,
    ← regs_set_of_get' (by decide) h21, ← regs_set_of_get' (by decide) h22]
  -- The quotient word m - n: 0.
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd, BitVec.reduceSignExtend, BitVec.add_zero]
  rv_val
  try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  refine ⟨List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (mem_bufWords (i := (x.get 12#5).toNat - (x.get 14#5).toNat) (by omega)))), ?_⟩
  rv_exec_cut 168
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.reduceSignExtend]
  rw [show pcAt base 137 + 124#64 = pcAt base 168 by simp only [pcAt]; bv_omega,
    update_aligned (pcAt_aligned hb 168)]
  -- The call of udivrem_knuth_normalized().
  refine Reach.call_sub (r := 139) udivrem_knuth_320_progAt_udivrem_knuth_normalized_in
    (by rw [udivrem_knuth_320_progAt_length]; decide)
    (udivrem_knuth_normalized.reach hi lo (pcAt base 168) T _ _ (pcAt_aligned hb 168) ?_ hw ?_ ?_ ?_
      ?_) ?_ ?_ ?_
  all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · rw [pcAt_pcAt]; exact hT
  · exact pcAt_aligned hb 139
  · rw [k320_sp288]; omega
  · have hq8 : (x.get 10#5 + BitVec.ofNat 64 (8 * ((x.get 12#5).toNat - (x.get 14#5).toNat))).toNat =
        (x.get 10#5).toNat + 8 * ((x.get 12#5).toNat - (x.get 14#5).toNat) :=
      toNat_add8 _ _ (by omega) (by omega)
    refine holdsData_of_unchangedExcept2 (unchangedExcept2_memStore_in hunc _ _ (by rw [hq8]; omega))
      _ _ (by rw [show reciprocal_2by1_image_data.length = 256 from rfl]; exact hw)
      (by rw [show reciprocal_2by1_image_data.length = 256 from rfl]; exact hrT)
      (by rw [show reciprocal_2by1_image_data.length = 256 from rfl]; exact hstk) hhold
  · -- The preconditions of udivrem_knuth_normalized().
    simp only [udivrem_knuth_normalized.pre, Buf, Disjoint]
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    rw [Regs.eq_get xs (by decide)]
    have hq8 : (x.get 10#5 + BitVec.ofNat 64 (8 * ((x.get 12#5).toNat - (x.get 14#5).toNat))).toNat =
        (x.get 10#5).toNat + 8 * ((x.get 12#5).toNat - (x.get 14#5).toNat) :=
      toNat_add8 _ _ (by omega) (by omega)
    rw [words_memStore_of_disjoint _ _ _ _ _ (by rw [hdnT]; omega) (by rw [hq8, hdnT]; omega),
      words_memStore_of_disjoint _ _ _ _ _ (by rw [hunT]; omega) (by rw [hq8, hunT]; omega),
      hdnw, hunl, k320_sp288, hdnT, hunT]
    refine ⟨⟨hra, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega, by omega,
      by omega, ⟨hsa, by omega⟩, by omega, by omega, by omega, hn3, hlen, ?_, hUq⟩
    rwa [show 64 * (x.get 14#5).toNat - 1 = 64 * (x.get 14#5).toNat - 1 from rfl]
  · -- The words of udivrem_knuth_normalized() are in the stack and the result.
    intro a ha
    simp only [udivrem_knuth_normalized.bufs] at ha
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at ha
    rw [Regs.eq_get xs (by decide)] at ha
    simp only [List.mem_append] at ha
    rcases ha with (((ha | ha) | ha) | ha) | ha
    · rw [k320_sp144 _ hsn] at ha
      exact List.mem_append_left _ (List.mem_append_right _ (mem_bufWords_of_offset (by omega) ha))
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        (mem_bufWords_of_le (by omega) ha)))
    · rw [k320_sp112 _ hsn] at ha
      exact List.mem_append_left _ (List.mem_append_right _ (mem_bufWords_of_offset (by omega) ha))
    · rw [k320_sp288] at ha
      exact List.mem_append_left _ (List.mem_append_right _ (mem_bufWords_of_le (by omega) ha))
    · exact List.mem_append_right _ ha
  -- The return from udivrem_knuth_normalized() at 139.
  intro x3 m3 ⟨hq3, hr3, hun3, hcs3⟩
  simp only at hq3 hr3
  simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at hq3 hr3 hun3
  rw [Regs.eq_get xs (by decide)] at hq3 hr3 hun3
  have f2 := get_of_calleeSaved hcs3 (i := 2#5) (by decide)
  have f8 := get_of_calleeSaved hcs3 (i := 8#5) (by decide)
  have f9 := get_of_calleeSaved hcs3 (i := 9#5) (by decide)
  have f18 := get_of_calleeSaved hcs3 (i := 18#5) (by decide)
  have f19 := get_of_calleeSaved hcs3 (i := 19#5) (by decide)
  have f20 := get_of_calleeSaved hcs3 (i := 20#5) (by decide)
  have f21 := get_of_calleeSaved hcs3 (i := 21#5) (by decide)
  have f22 := get_of_calleeSaved hcs3 (i := 22#5) (by decide)
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte] at f2 f8 f9 f18
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte] at f19 f20 f21 f22
  rw [← regs_set_of_get' (by decide) f2, ← regs_set_of_get' (by decide) f8,
    ← regs_set_of_get' (by decide) f9, ← regs_set_of_get' (by decide) f18,
    ← regs_set_of_get' (by decide) f19, ← regs_set_of_get' (by decide) f20,
    ← regs_set_of_get' (by decide) f21, ← regs_set_of_get' (by decide) f22]
  rv_exec_cut 143
  rename_i wu0 hwu0 wre hwre
  have hres40 : (x.get 10#5 + 40#64).toNat = (x.get 10#5).toNat + 40 :=
    toNat_add8 _ 40 (by omega) (by omega)
  -- The shift loop of the remainder.
  refine k320_r_start (A := bufWords (x.get 11#5) 5 ++ bufWords (x.get 13#5) (x.get 14#5).toNat ++
      bufWords (x.get 10#5) 9 ++ bufWords (x.get 2#5 - 288#64) 36 ++ bufWords T 256) _ m3
    (x.get 2#5 + 18446744073709551504#64) (x.get 10#5 + 40#64) (x.get 14#5).toNat
    (BitVec.ofNat 64 s) ?_ ?_ ?_ (by omega) ?_ ?_ ?_ (by omega) (by rw [hunT]; omega)
    (by rw [hres40]; omega) (by rw [hunT, hres40]; omega) ?_ ?_ ?_
  all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · exact k320_up8 _
  · exact hwu0.eq
  · rw [hwre.eq]; exact k320_rend _ _ (by omega) (by omega)
  · intro i hi
    rw [k320_sp112 _ hsn]
    exact List.mem_append_left _ (List.mem_append_right _
      (mem_bufWords_of_offset (by omega) (mem_bufWords hi)))
  · intro i hi
    rw [show x.get 10#5 + 40#64 + BitVec.ofNat 64 (8 * i) = x.get 10#5 + BitVec.ofNat 64 (8 * (5 + i))
      by bv_omega]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (mem_bufWords (by omega))))
  -- The last word of the remainder at 153.
  intro x5 m5 ⟨hrw, hrun, h50, hcl5⟩
  have g2 := get_of_cl hcl5 (r := 2#5) (by decide) (by decide)
  have g8 := get_of_cl hcl5 (r := 8#5) (by decide) (by decide)
  have g20 := get_of_cl hcl5 (r := 20#5) (by decide) (by decide)
  have g21 := get_of_cl hcl5 (r := 21#5) (by decide) (by decide)
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte] at g2 g8 g20 g21
  rw [← regs_set_of_get' (by decide) g2, ← regs_set_of_get' (by decide) g8,
    ← regs_set_of_get' (by decide) g20, ← regs_set_of_get' (by decide) g21]
  rv_exec_cut 155
  rename_i wa hwa
  -- un[n - 1]
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd, BitVec.reduceSignExtend, BitVec.add_zero]
  rv_val
  rw [hwa.eq, k320_un_top _ _ (by omega) (by omega)]
  refine ⟨by
    rw [k320_sp112 _ hsn, ptr_add_add _ _ _ (by omega)]
    exact List.mem_append_left _ (List.mem_append_right _ (mem_bufWords (by omega))),
    fun wl hwl => ?_⟩
  rv_exec_cut 157
  -- The store of the last word of the remainder.
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd, BitVec.reduceSignExtend, BitVec.add_zero]
  rv_val
  rw [hwre.eq, k320_rend _ _ (by omega) (by omega)]
  refine ⟨by
    rw [show x.get 10#5 + 40#64 + BitVec.ofNat 64 (8 * ((x.get 14#5).toNat - 1)) =
      x.get 10#5 + BitVec.ofNat 64 (8 * (5 + ((x.get 14#5).toNat - 1))) by bv_omega]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (mem_bufWords (by omega)))), ?_⟩
  rv_exec
  rename_i wsh hwsh wra hwra ws0 hws0 ws1 hws1 ws2 hws2 ws3 hws3 ws4 hws4 ws5 hws5 ws6 hws6
  -- The frame words: unchanged since the prologue.
  have hq8 : (x.get 10#5 + BitVec.ofNat 64 (8 * ((x.get 12#5).toNat - (x.get 14#5).toNat))).toNat =
      (x.get 10#5).toNat + 8 * ((x.get 12#5).toNat - (x.get 14#5).toNat) :=
    toNat_add8 _ _ (by omega) (by omega)
  have hfr : ∀ b, (x.get 2#5 - 288#64).toNat + 224 ≤ b → b + 8 ≤ (x.get 2#5 - 288#64).toNat + 288 →
      memWord m5 b = memWord ms b := by
    intro b h1 h2
    rw [memWord_of_unchangedExcept hrun b (by rw [hres40]; omega),
      memWord_of_unchangedExcept3 hun3 b (by omega) (by rw [hunT]; omega)
        (by rw [k320_sp288]; omega),
      memWord_memStore_of_ne _ _ _ _ (by rw [hq8]; omega)]
  obtain ⟨f1, f8, f9, f18, f19, f20, f21, f22⟩ := k320_frame_toNat (x.get 2#5) hsn
  obtain ⟨k1, k8, k9, k18, k19, k20, k21, k22⟩ := hfw
  rw [hfr _ (by rw [f1]; try omega) (by rw [f1]; try omega), k1] at hwra
  rw [hfr _ (by rw [f8]; try omega) (by rw [f8]; try omega), k8] at hws0
  rw [hfr _ (by rw [f9]; try omega) (by rw [f9]; try omega), k9] at hws1
  rw [hfr _ (by rw [f18]; try omega) (by rw [f18]; try omega), k18] at hws2
  rw [hfr _ (by rw [f19]; try omega) (by rw [f19]; try omega), k19] at hws3
  rw [hfr _ (by rw [f20]; try omega) (by rw [f20]; try omega), k20] at hws4
  rw [hfr _ (by rw [f21]; try omega) (by rw [f21]; try omega), k21] at hws5
  rw [hfr _ (by rw [f22]; try omega) (by rw [f22]; try omega), k22] at hws6
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.reduceSignExtend,
    BitVec.add_zero]
  rw [hwra.eq, update_aligned hr]
  refine Reach.refl ?_
  simp only [udivrem_knuth_320.post]
  simp (disch := decide) only [Regs.eq_get x]
  have hfin : ∀ (a v : BitVec 64), (x.get 10#5).toNat + 40 ≤ a.toNat → a.toNat + 8 ≤ (x.get 10#5).toNat + 72 →
      UnchangedExcept2 m (memStore m5 a.toNat v) (x.get 10#5) 72 (x.get 2#5 - 288#64) 288 := by
    intro a v ha1 ha2 k hk1 hk2
    rw [getElem?_memStore_of_ne _ _ _ _ (by omega), hrun k (by rw [hres40]; omega),
      hun3 k (by omega) (by rw [hunT]; omega) (by rw [k320_sp288]; omega),
      getElem?_memStore_of_ne _ _ _ _ (by rw [hq8]; omega)]
    exact hunc k hk1 hk2
  have hlast : (x.get 10#5 + (40#64 + BitVec.ofNat 64 (8 * ((x.get 14#5).toNat - 1)))).toNat =
      (x.get 10#5).toNat + 40 + 8 * ((x.get 14#5).toNat - 1) := by
    rw [← BitVec.add_assoc, toNat_add8 _ _ (by omega) (by rw [hres40]; omega), hres40]
  refine ⟨?_, ?_, hfin _ _ (by rw [hlast]; omega) (by rw [hlast]; omega), ?_⟩
  rotate_left 2
  · -- The callee-saved registers: restored from the frame or unchanged.
    intro r hr'
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    all_goals first
      | exact (Regs.eq_get x (by decide)).symm
      | (rw [Regs.eq_get x (by decide)]; exact hws0)
      | (rw [Regs.eq_get x (by decide)]; exact hws1)
      | (rw [Regs.eq_get x (by decide)]; exact hws2)
      | (rw [Regs.eq_get x (by decide)]; exact hws3)
      | (rw [Regs.eq_get x (by decide)]; exact hws4)
      | (rw [Regs.eq_get x (by decide)]; exact hws5)
      | (rw [Regs.eq_get x (by decide)]; exact hws6)
      | (rw [hcl5 _ (by decide)]
         simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
         rw [hcs3 _ (by decide)]
         simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
         exact hcs _ (by decide))
  · -- The quotient: the words of udivrem_knuth_normalized() and the zero words above them.
    have hul6 : (xs.get 12#5).toNat ≤ 6 := hl6
    rw [words_memStore_of_disjoint _ _ _ _ _ (by omega) (by rw [hlast]; omega),
      words_of_unchangedExcept hrun 5 _ (by omega) (by rw [hres40]; omega)]
    have hsplit := words_split m3 ((xs.get 12#5).toNat - (x.get 14#5).toNat)
      (5 - ((xs.get 12#5).toNat - (x.get 14#5).toNat)) (x.get 10#5)
    rw [show (xs.get 12#5).toNat - (x.get 14#5).toNat +
      (5 - ((xs.get 12#5).toNat - (x.get 14#5).toNat)) = 5 by omega] at hsplit
    have hz : words m3 (x.get 10#5 + BitVec.ofNat 64 (8 * ((xs.get 12#5).toNat - (x.get 14#5).toNat)))
        (5 - ((xs.get 12#5).toNat - (x.get 14#5).toNat)) = 0 := by
      refine words_eq_zero _ _ _ (fun i hi => ?_)
      rw [ptr_add_add _ _ _ (by omega)]
      have hi8 : (x.get 10#5 + BitVec.ofNat 64
          (8 * ((xs.get 12#5).toNat - (x.get 14#5).toNat + i))).toNat =
          (x.get 10#5).toNat + 8 * ((xs.get 12#5).toNat - (x.get 14#5).toNat + i) :=
        toNat_add8 _ _ (by omega) (by omega)
      rw [memWord_of_unchangedExcept3 hun3 _ (by rw [hi8]; omega) (by rw [hi8, hunT]; omega)
        (by rw [hi8, k320_sp288]; omega)]
      by_cases he : (xs.get 12#5).toNat - (x.get 14#5).toNat + i =
        (x.get 12#5).toNat - (x.get 14#5).toNat
      · rw [he, memWord_memStore_self]
      · rw [memWord_memStore_of_ne _ _ _ _ (by rw [hi8, hq8]; omega)]
        exact hres _ (by omega)
    rw [hsplit, hz, Nat.mul_zero, Nat.add_zero, hq3,
      words_memStore_of_disjoint _ _ _ _ _ (by rw [hunT]; omega) (by rw [hq8, hunT]; omega),
      words_memStore_of_disjoint _ _ _ _ _ (by rw [hdnT]; omega) (by rw [hq8, hdnT]; omega),
      hunl, hdnw, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos s)]
  · -- The remainder: the words shifted back and the zero words above them.
    have hul6 : (xs.get 12#5).toNat ≤ 6 := hl6
    have hsN : (BitVec.ofNat 64 s).toNat = s := by rw [BitVec.toNat_ofNat]; omega
    have hsplit := words_split (memStore m5 (x.get 10#5 + (40#64 + BitVec.ofNat 64
      (8 * ((x.get 14#5).toNat - 1)))).toNat wsh) (x.get 14#5).toNat (4 - (x.get 14#5).toNat)
      (x.get 10#5 + 40#64)
    rw [show (x.get 14#5).toNat + (4 - (x.get 14#5).toNat) = 4 by omega] at hsplit
    have hz : words (memStore m5 (x.get 10#5 + (40#64 + BitVec.ofNat 64
        (8 * ((x.get 14#5).toNat - 1)))).toNat wsh)
        (x.get 10#5 + 40#64 + BitVec.ofNat 64 (8 * (x.get 14#5).toNat)) (4 - (x.get 14#5).toNat) =
        0 := by
      refine words_eq_zero _ _ _ (fun i hi => ?_)
      rw [ptr_add_add _ _ _ (by rw [hres40]; omega)]
      have hi8 : (x.get 10#5 + 40#64 + BitVec.ofNat 64 (8 * ((x.get 14#5).toNat + i))).toNat =
          (x.get 10#5).toNat + 40 + 8 * ((x.get 14#5).toNat + i) := by
        rw [toNat_add8 _ _ (by omega) (by rw [hres40]; omega), hres40]
      rw [memWord_memStore_of_ne _ _ _ _ (by rw [hi8, hlast]; omega),
        memWord_of_unchangedExcept hrun _ (by rw [hi8, hres40]; omega),
        memWord_of_unchangedExcept3 hun3 _ (by rw [hi8]; omega) (by rw [hi8, hunT]; omega)
          (by rw [hi8, k320_sp288]; omega),
        memWord_memStore_of_ne _ _ _ _ (by rw [hi8, hq8]; omega),
        show x.get 10#5 + 40#64 + BitVec.ofNat 64 (8 * ((x.get 14#5).toNat + i)) =
          x.get 10#5 + BitVec.ofNat 64 (8 * (5 + ((x.get 14#5).toNat + i))) by bv_omega]
      exact hres _ (by omega)
    rw [hsplit, hz, Nat.mul_zero, Nat.add_zero]
    -- The words of the normalized remainder: (u % d) * 2^s.
    have hR : words m3 (x.get 2#5 + 18446744073709551504#64) (x.get 14#5).toNat =
        words m (x.get 11#5) 5 % words m (x.get 13#5) (x.get 14#5).toNat * 2 ^ s := by
      have hs2 := words_split m3 (x.get 14#5).toNat ((xs.get 12#5).toNat - (x.get 14#5).toNat)
        (x.get 2#5 + 18446744073709551504#64)
      rw [show (x.get 14#5).toNat + ((xs.get 12#5).toNat - (x.get 14#5).toNat) =
        (xs.get 12#5).toNat by omega] at hs2
      rw [hs2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (words_lt _ _ _),
        words_memStore_of_disjoint _ _ _ _ _ (by rw [hunT]; omega) (by rw [hq8, hunT]; omega),
        words_memStore_of_disjoint _ _ _ _ _ (by rw [hdnT]; omega) (by rw [hq8, hdnT]; omega),
        hunl, hdnw, Nat.mul_mod_mul_right] at hr3
      exact hr3
    -- The words of the remainder shifted back.
    have hsh := words_shr m3 (memStore m5 (x.get 10#5 + (40#64 + BitVec.ofNat 64
      (8 * ((x.get 14#5).toNat - 1)))).toNat wsh) (x.get 2#5 + 18446744073709551504#64)
      (x.get 10#5 + 40#64) s (x.get 14#5).toNat hs (by omega) ?_ ?_
    · have h0 : (memWord m3 (x.get 2#5 + 18446744073709551504#64 + BitVec.ofNat 64 (8 * 0)).toNat).toNat %
          2 ^ s = 0 := by
        have hw0 : words m3 (x.get 2#5 + 18446744073709551504#64) (x.get 14#5).toNat % 2 ^ 64 =
            (memWord m3 (x.get 2#5 + 18446744073709551504#64).toNat).toNat := by
          obtain ⟨k, hk⟩ : ∃ k, (x.get 14#5).toNat = k + 1 := ⟨(x.get 14#5).toNat - 1, by omega⟩
          rw [hk, words, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (BitVec.isLt _)]
        rw [show 8 * 0 = 0 from rfl, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero,
          ← hw0, hR, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hs.le), Nat.mul_mod_left]
      rw [h0, Nat.add_zero, hR] at hsh
      exact Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos s) hsh
    · intro j hj
      have hj8 : (x.get 10#5 + 40#64 + BitVec.ofNat 64 (8 * j)).toNat =
          (x.get 10#5).toNat + 40 + 8 * j := by
        rw [toNat_add8 _ _ (by omega) (by rw [hres40]; omega), hres40]
      rw [memWord_memStore_of_ne _ _ _ _ (by rw [hj8, hlast]; omega), hrw j hj, k320RWord,
        funnel_shr_val _ _ _ (by rw [hsN]; exact hs), hsN]
    · rw [← BitVec.add_assoc, memWord_memStore_self, hwsh.eq, BitVec.toNat_ushiftRight, hsN,
        Nat.mod_eq_of_lt hs, Nat.shiftRight_eq_div_pow, hwl.eq,
        memWord_of_unchangedExcept hrun _ (by
          rw [toNat_add8 _ _ (by omega) (by rw [hunT]; omega), hunT, hres40]; omega)]

theorem k320_funnel_val (a b : BitVec 64) (s : Nat) (hs0 : 0 < s) (hs : s < 64) :
    ((b >>> ((64#64 - BitVec.ofNat 64 s).toNat % 64)) |||
      (a <<< ((BitVec.ofNat 64 s).toNat % 64))).toNat =
      a.toNat * 2 ^ s % 2 ^ 64 + b.toNat / 2 ^ (64 - s) := by
  have h1 : (64#64 - BitVec.ofNat 64 s).toNat % 64 = 64 - s := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have h2 : (BitVec.ofNat 64 s).toNat % 64 = s := by rw [BitVec.toNat_ofNat]; omega
  rw [h1, h2, BitVec.or_comm, toNat_shl_or_shr a b s hs]

theorem k320_neg_amt : ∀ t < 64, (BitVec.signExtend 64 (BitVec.setWidth 32 0#64 -
    BitVec.setWidth 32 (BitVec.ofNat 64 t))).toNat % 64 = (64 - t) % 64 := by
  decide

theorem k320_un5_val (u4 : BitVec 64) (s : Nat) (hs : s < 64) :
    ((if BitVec.ofNat 64 s = 0#64 then 1#64 else 0#64) + 18446744073709551615#64 &&&
      u4 >>> ((BitVec.signExtend 64 (BitVec.setWidth 32 0#64 -
        BitVec.setWidth 32 (BitVec.ofNat 64 s))).toNat % 64)).toNat =
      u4.toNat / 2 ^ (64 - s) := by
  rw [k320_neg_amt s hs]
  by_cases h0 : s = 0
  · subst h0
    rw [if_pos rfl, show (1#64 : BitVec 64) + 18446744073709551615#64 = 0#64 from rfl,
      BitVec.zero_and]
    have := u4.isLt
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero]
    omega
  · rw [if_neg (by
      intro h; apply h0; have := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat] at this; simp at this; omega),
      show (0#64 : BitVec 64) + 18446744073709551615#64 = BitVec.allOnes 64 from rfl,
      BitVec.allOnes_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (by omega : 64 - s < 64)]

theorem k320_stack_toNat (sp : BitVec 64) (hs : (sp - 288#64).toNat + 288 ≤ 2 ^ 64) :
    (sp + 18446744073709551472#64).toNat = (sp - 288#64).toNat + 144 ∧
    (sp + 18446744073709551544#64).toNat = (sp - 288#64).toNat + 216 ∧
    (sp + 18446744073709551536#64).toNat = (sp - 288#64).toNat + 208 ∧
    (sp + 18446744073709551528#64).toNat = (sp - 288#64).toNat + 200 ∧
    (sp + 18446744073709551520#64).toNat = (sp - 288#64).toNat + 192 ∧
    (sp + 18446744073709551512#64).toNat = (sp - 288#64).toNat + 184 ∧
    (sp + 18446744073709551504#64).toNat = (sp - 288#64).toNat + 176 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_omega

theorem k320_q_addr (r a b : BitVec 64) (h : b.toNat ≤ a.toNat) (ha : 8 * a.toNat < 2 ^ 64) :
    r + (a - b) <<< 3 = r + BitVec.ofNat 64 (8 * (a.toNat - b.toNat)) := by
  bv_omega

/-- The memory of `udivrem_knuth<320, 256>()` at 133: the frame, the result zero, and the
shifted divisor at sp - 144 (the stores after 80 are into the words of the shifted numerator). -/
theorem k320_at133 (x : Regs) (m : Mem) (hpre : udivrem_knuth_320.pre x m) (s : Nat) (hs : s < 64)
    (hnorm' : (memWord m (x.get 13#5 + BitVec.ofNat 64 (8 * ((x.get 14#5).toNat - 1))).toNat).toNat *
      2 ^ s < 2 ^ 64)
    (m80 ms : Mem)
    (hdun : UnchangedExcept (memFill (k320FrameMem x m) (x.get 10#5).toNat 0#8 72) m80
      (x.get 2#5 + 18446744073709551472#64) (8 * (x.get 14#5).toNat))
    (hdw : ∀ i, 0 < i → i < (x.get 14#5).toNat →
      memWord m80 (x.get 2#5 + 18446744073709551472#64 + BitVec.ofNat 64 (8 * i)).toNat =
        k320DnWord (memFill (k320FrameMem x m) (x.get 10#5).toNat 0#8 72) (x.get 13#5)
          (BitVec.ofNat 64 s) i)
    (v0 : BitVec 64) (hv0 : v0 = memWord m (x.get 13#5).toNat <<< ((BitVec.ofNat 64 s).toNat % 64))
    (hU1 : UnchangedExcept (memStore m80 (x.get 2#5 + 18446744073709551472#64).toNat v0) ms
      (x.get 2#5 + 18446744073709551504#64) 48) :
    (memWord ms (x.get 2#5 + 18446744073709551608#64).toNat = x.get 1#5 ∧
      memWord ms (x.get 2#5 + 18446744073709551600#64).toNat = x.get 8#5 ∧
      memWord ms (x.get 2#5 + 18446744073709551592#64).toNat = x.get 9#5 ∧
      memWord ms (x.get 2#5 + 18446744073709551584#64).toNat = x.get 18#5 ∧
      memWord ms (x.get 2#5 + 18446744073709551576#64).toNat = x.get 19#5 ∧
      memWord ms (x.get 2#5 + 18446744073709551568#64).toNat = x.get 20#5 ∧
      memWord ms (x.get 2#5 + 18446744073709551560#64).toNat = x.get 21#5 ∧
      memWord ms (x.get 2#5 + 18446744073709551552#64).toNat = x.get 22#5) ∧
    UnchangedExcept2 m ms (x.get 10#5) 72 (x.get 2#5 - 288#64) 288 ∧
    (∀ i < 9, memWord ms (x.get 10#5 + BitVec.ofNat 64 (8 * i)).toNat = 0#64) ∧
    words ms (x.get 2#5 + 18446744073709551472#64) (x.get 14#5).toNat =
      words m (x.get 13#5) (x.get 14#5).toNat * 2 ^ s := by
  have hpre' := hpre
  simp only [udivrem_knuth_320.pre, Buf, Disjoint] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hda, hdn⟩, hdru, hdrd, ⟨hsa, hsn⟩, hdsu, hdsd, hdsr, hn3, hn4,
    hD, hmm, hU, -, htop⟩ := hpre'
  obtain ⟨t144, t72, t80, t88, t96, t104, t112⟩ := k320_stack_toNat (x.get 2#5) hsn
  have hfun := k320FrameMem_unchanged x m hsn
  -- The memory below the words of the shifted numerator, from the start.
  have hms : ∀ b, b + 8 ≤ (x.get 2#5 - 288#64).toNat + 176 ∨ (x.get 2#5 - 288#64).toNat + 224 ≤ b →
      (b + 8 ≤ (x.get 2#5 - 288#64).toNat + 144 ∨ (x.get 2#5 - 288#64).toNat + 152 ≤ b) →
      (b + 8 ≤ (x.get 2#5 - 288#64).toNat + 144 ∨
        (x.get 2#5 - 288#64).toNat + 144 + 8 * (x.get 14#5).toNat ≤ b) →
      memWord ms b = memWord (memFill (k320FrameMem x m) (x.get 10#5).toNat 0#8 72) b := by
    intro b h1 h2 h3
    rw [memWord_of_unchangedExcept hU1 b (by rw [t112]; omega),
      memWord_memStore_of_ne _ _ _ _ (by rw [t144]; omega),
      memWord_of_unchangedExcept hdun b (by rw [t144]; omega)]
  have hfw := k320FrameMem_words x m hsn
  obtain ⟨f1, f8, f9, f18, f19, f20, f21, f22⟩ := k320_frame_toNat (x.get 2#5) hsn
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals
      rw [hms _ (by omega) (by omega) (by omega),
        memWord_memFill_of_disjoint _ _ _ _ _ (by omega)]
    exacts [hfw.1, hfw.2.1, hfw.2.2.1, hfw.2.2.2.1, hfw.2.2.2.2.1, hfw.2.2.2.2.2.1,
      hfw.2.2.2.2.2.2.1, hfw.2.2.2.2.2.2.2]
  · intro k hk1 hk2
    rw [hU1 k (by rw [t112]; omega), getElem?_memStore_of_ne _ _ _ _ (by rw [t144]; omega),
      hdun k (by rw [t144]; omega),
      unchangedExcept_memFill (k320FrameMem x m) (x.get 10#5) 0#8 72 k (by omega),
      hfun k (by omega)]
  · intro i hi
    have hi8 := toNat_add8 (x.get 10#5) (8 * i) (by omega) (by omega)
    rw [hms _ (by rw [hi8]; omega) (by rw [hi8]; omega) (by rw [hi8]; omega),
      memWord_memFill_zero _ _ _ _ (by rw [hi8]; omega)]
  · have hsN : (BitVec.ofNat 64 s).toNat = s := by rw [BitVec.toNat_ofNat]; omega
    -- The words of d in the memory after the prologue.
    have hmd : ∀ j, j < (x.get 14#5).toNat →
        memWord (memFill (k320FrameMem x m) (x.get 10#5).toNat 0#8 72)
          (x.get 13#5 + BitVec.ofNat 64 (8 * j)).toNat =
        memWord m (x.get 13#5 + BitVec.ofNat 64 (8 * j)).toNat := by
      intro j hj
      have hj8 := toNat_add8 (x.get 13#5) (8 * j) (by omega) (by omega)
      rw [memWord_memFill_of_disjoint _ _ _ _ _ (by rw [hj8]; omega),
        memWord_of_unchangedExcept hfun _ (by rw [hj8]; omega)]
    have hsh := words_shl m ms (x.get 13#5) (x.get 2#5 + 18446744073709551472#64) s hs
      (x.get 14#5).toNat ?_
    · rw [if_neg (by omega)] at hsh
      have hz : (memWord m (x.get 13#5 + BitVec.ofNat 64 (8 * ((x.get 14#5).toNat - 1))).toNat).toNat /
          2 ^ (64 - s) = 0 := by
        apply Nat.div_eq_of_lt
        have e64 : (2 : Nat) ^ 64 = 2 ^ (64 - s) * 2 ^ s := by
          rw [← pow_add, Nat.sub_add_cancel hs.le]
        rw [e64] at hnorm'
        exact Nat.lt_of_mul_lt_mul_right hnorm'
      rw [hz, Nat.mul_zero, Nat.add_zero] at hsh
      exact hsh
    · intro i hi
      have hi8 : (x.get 2#5 + 18446744073709551472#64 + BitVec.ofNat 64 (8 * i)).toNat =
          (x.get 2#5 - 288#64).toNat + 144 + 8 * i := by
        rw [toNat_add8 _ _ (by omega) (by rw [t144]; omega), t144]
      rw [memWord_of_unchangedExcept hU1 _ (by rw [hi8, t112]; omega)]
      by_cases hi0 : i = 0
      · subst hi0
        simp only [Nat.mul_zero, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero,
          memWord_memStore_self, if_true]
        rw [hv0, BitVec.toNat_shiftLeft, hsN, Nat.mod_eq_of_lt hs, Nat.shiftLeft_eq, Nat.add_zero]
      · rw [memWord_memStore_of_ne _ _ _ _ (by rw [hi8, t144]; omega), hdw i (by omega) hi,
          k320DnWord, funnel_shl_val _ _ _ (by rw [hsN]; exact hs), hsN, hmd i hi,
          hmd (i - 1) (by omega), if_neg hi0]

/-- The stores of `udivrem_knuth<320, 256>()` after 80: the word 0 of the shifted divisor, then the
words of the shifted numerator. -/
abbrev k320Chain (m80 : Mem) (sp v0 v5 v4 v3 v2 w0 w1 : BitVec 64) : Mem :=
  memStore (memStore (memStore (memStore (memStore (memStore (memStore m80
    (sp + 18446744073709551472#64).toNat v0) (sp + 18446744073709551544#64).toNat v5)
    (sp + 18446744073709551536#64).toNat v4) (sp + 18446744073709551528#64).toNat v3)
    (sp + 18446744073709551520#64).toNat v2) (sp + 18446744073709551504#64).toNat w0)
    (sp + 18446744073709551512#64).toNat w1

theorem k320_chain (m80 : Mem) (sp : BitVec 64) (hs : (sp - 288#64).toNat + 288 ≤ 2 ^ 64)
    (v0 v5 v4 v3 v2 w0 w1 : BitVec 64) :
    UnchangedExcept (memStore m80 (sp + 18446744073709551472#64).toNat v0)
      (k320Chain m80 sp v0 v5 v4 v3 v2 w0 w1) (sp + 18446744073709551504#64) 48 ∧
    memWord (k320Chain m80 sp v0 v5 v4 v3 v2 w0 w1)
      (sp + 18446744073709551504#64 + BitVec.ofNat 64 (8 * 0)).toNat = w0 ∧
    memWord (k320Chain m80 sp v0 v5 v4 v3 v2 w0 w1)
      (sp + 18446744073709551504#64 + BitVec.ofNat 64 (8 * 1)).toNat = w1 ∧
    memWord (k320Chain m80 sp v0 v5 v4 v3 v2 w0 w1)
      (sp + 18446744073709551504#64 + BitVec.ofNat 64 (8 * 2)).toNat = v2 ∧
    memWord (k320Chain m80 sp v0 v5 v4 v3 v2 w0 w1)
      (sp + 18446744073709551504#64 + BitVec.ofNat 64 (8 * 3)).toNat = v3 ∧
    memWord (k320Chain m80 sp v0 v5 v4 v3 v2 w0 w1)
      (sp + 18446744073709551504#64 + BitVec.ofNat 64 (8 * 4)).toNat = v4 ∧
    memWord (k320Chain m80 sp v0 v5 v4 v3 v2 w0 w1)
      (sp + 18446744073709551504#64 + BitVec.ofNat 64 (8 * 5)).toNat = v5 := by
  obtain ⟨t144, t72, t80, t88, t96, t104, t112⟩ := k320_stack_toNat sp hs
  have a0 : sp + 18446744073709551504#64 + BitVec.ofNat 64 (8 * 0) = sp + 18446744073709551504#64 := by
    bv_omega
  have a1 : sp + 18446744073709551504#64 + BitVec.ofNat 64 (8 * 1) = sp + 18446744073709551512#64 := by
    bv_omega
  have a2 : sp + 18446744073709551504#64 + BitVec.ofNat 64 (8 * 2) = sp + 18446744073709551520#64 := by
    bv_omega
  have a3 : sp + 18446744073709551504#64 + BitVec.ofNat 64 (8 * 3) = sp + 18446744073709551528#64 := by
    bv_omega
  have a4 : sp + 18446744073709551504#64 + BitVec.ofNat 64 (8 * 4) = sp + 18446744073709551536#64 := by
    bv_omega
  have a5 : sp + 18446744073709551504#64 + BitVec.ofNat 64 (8 * 5) = sp + 18446744073709551544#64 := by
    bv_omega
  rw [a0, a1, a2, a3, a4, a5]
  simp only [k320Chain]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · repeat rw [unchangedExcept_memStore _ _ (by omega)]
    exact unchangedExcept_refl _ _ _
  all_goals simp (disch := omega) only [memWord_memStore_self, memWord_memStore_of_ne]

/-- The words of the shifted numerator from their values. -/
theorem k320_unw (m ms : Mem) (u unp : BitVec 64) (s : Nat) (hs : s < 64)
    (hw : ∀ i, i < 5 → (memWord ms (unp + BitVec.ofNat 64 (8 * i)).toNat).toNat =
      (memWord m (u + BitVec.ofNat 64 (8 * i)).toNat).toNat * 2 ^ s % 2 ^ 64 +
        (if i = 0 then 0 else
          (memWord m (u + BitVec.ofNat 64 (8 * (i - 1))).toNat).toNat / 2 ^ (64 - s)))
    (h5 : (memWord ms (unp + BitVec.ofNat 64 (8 * 5)).toNat).toNat =
      (memWord m (u + BitVec.ofNat 64 (8 * 4)).toNat).toNat / 2 ^ (64 - s)) :
    words ms unp 6 = words m u 5 * 2 ^ s := by
  have h := words_shl m ms u unp s hs 5 hw
  rw [if_neg (by omega), show 5 - 1 = 4 from rfl] at h
  rw [show (6 : Nat) = 5 + 1 from rfl, words_succ_top, h5, ← h]

end IntxRV.Api
