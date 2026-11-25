import IntxRV.Gen.Api.udivrem_by1
import IntxRV.Arith
import IntxRV.EnvImage
import IntxRV.Reciprocal
import IntxRV.Clz
import IntxRV.Shift
import IntxRV.Loop
import IntxRV.Div2by1
import IntxRV.DivWords
import IntxRV.Call
/-!
# The division of a span by a word

The lemmas of the proof of `internal::udivrem_by1()` (`IntxRV/Api/udivrem_by1.lean`): the table
entry of the normalized divisor in the image, the top digits of the normalized numerator and the
first quotient word, and the loop. `by1Head` is the state at the head of the loop before the
quotient word `i`: the quotient words above `i` stored, and the normalized remainder `rem` of the
digits above `i`, `Qhi * dn + rem = (u * 2^s) / 2^(64 * (i + 1))`. `by1_loop` runs the loop by
`Reach.loop` on `i`: each iteration divides the digit `i` (`div2by1BV`, `norm_digit`, `div_step`),
stores the quotient word and reaches the head with `i - 1` or the exit. `by1Exit` is the state at
the exit, and `by1_exit` the division of the last digit and the result (`by1_final`).
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
-- The guards that select the paths do not change the goals.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- The address of the table entry of `d` in the table at `T`. -/
theorem table_addr_by1 (d T : BitVec 64) (hd : 2 ^ 63 ≤ d.toNat) :
    (d >>> 52 &&& 18446744073709551608#64) + T + 18446744073709549568#64 =
      T + BitVec.ofNat 64 (8 * (d.toNat / 2 ^ 55 - 256)) := by
  rw [show (18446744073709551608#64) = 0xfffffffffffffff8#64 from rfl, shr52_and]
  have := d.isLt
  bv_omega

theorem table_addr_by1_hi (d T : BitVec 64) (hd : 2 ^ 63 ≤ d.toNat) :
    (d >>> 52 &&& 18446744073709551608#64) + T + 18446744073709549572#64 =
      T + BitVec.ofNat 64 (8 * (d.toNat / 2 ^ 55 - 256)) + 4 := by
  rw [show (18446744073709551608#64) = 0xfffffffffffffff8#64 from rfl, shr52_and]
  have := d.isLt
  bv_omega

/-- The offset of the word `n - 2` of a buffer of `n` words. -/
theorem off_sub2 (n : BitVec 64) (h : 2 ≤ n.toNat) (hn : 8 * n.toNat ≤ 2 ^ 64) :
    (n + 18446744073709551614#64) <<< 3 = BitVec.ofNat 64 (8 * (n.toNat - 2)) := by
  bv_omega

/-- The offset of the word `n - 1` of a buffer of `n` words. -/
theorem off_sub1 (n : BitVec 64) (h : 1 ≤ n.toNat) (hn : 8 * n.toNat ≤ 2 ^ 64) :
    n <<< 3 + 18446744073709551608#64 = BitVec.ofNat 64 (8 * (n.toNat - 1)) := by
  bv_omega

/-- The index of the table entry of a normalized `d`. -/
theorem index_lt_256 {d : BitVec 64} (h : 2 ^ 63 ≤ d.toNat) : d.toNat / 2 ^ 55 - 256 < 256 := by
  have := d.isLt; omega

/-- The address of the high half of the table entry, 4 bytes above the entry. -/
theorem table_entry_add4 (T : BitVec 64) {d : BitVec 64} (h : 2 ^ 63 ≤ d.toNat)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64) :
    (T + BitVec.ofNat 64 (8 * (d.toNat / 2 ^ 55 - 256)) + 4).toNat =
      (T + BitVec.ofNat 64 (8 * (d.toNat / 2 ^ 55 - 256))).toNat + 4 := by
  have := index_lt_256 h
  bv_omega

/-- The normalized divisor: `d` shifted left by the count of its leading zeros. -/
theorem norm_shift (d : BitVec 64) (hd : d ≠ 0) :
    (d <<< ((BitVec.ofNat 64 (63 - Nat.log2 d.toNat)).toNat % 64)).toNat =
      d.toNat * 2 ^ (63 - Nat.log2 d.toNat) ∧
    2 ^ 63 ≤ d.toNat * 2 ^ (63 - Nat.log2 d.toNat) := by
  have hd0 : d.toNat ≠ 0 := fun h => hd (BitVec.eq_of_toNat_eq (by simpa using h))
  have hL := (Nat.log2_lt hd0).mpr d.isLt
  have h1 := Nat.lt_log2_self (n := d.toNat)
  have h2 := Nat.log2_self_le hd0
  have hS : (BitVec.ofNat 64 (63 - Nat.log2 d.toNat)).toNat % 64 = 63 - Nat.log2 d.toNat := by
    simp; omega
  rw [hS, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have hp : d.toNat * 2 ^ (63 - Nat.log2 d.toNat) < 2 ^ 64 := by
    calc d.toNat * 2 ^ (63 - Nat.log2 d.toNat) < 2 ^ (Nat.log2 d.toNat + 1) *
          2 ^ (63 - Nat.log2 d.toNat) := Nat.mul_lt_mul_of_pos_right h1 (by positivity)
      _ = 2 ^ 64 := by rw [← pow_add]; congr 1; omega
  have hq : 2 ^ 63 ≤ d.toNat * 2 ^ (63 - Nat.log2 d.toNat) := by
    calc 2 ^ 63 = 2 ^ Nat.log2 d.toNat * 2 ^ (63 - Nat.log2 d.toNat) := by
          rw [← pow_add]; congr 1; omega
      _ ≤ _ := Nat.mul_le_mul_right _ h2
  exact ⟨Nat.mod_eq_of_lt hp, hq⟩

/-- The first word of a buffer. -/
theorem mem_bufWords_zero {a : BitVec 64} {n : Nat} (h : 0 < n) : a ∈ bufWords a n := by
  have := mem_bufWords (a := a) h
  simpa using this

/-- The low word of the normalized numerator. -/
theorem words_mul_mod (m : Mem) (a : BitVec 64) (n S : Nat) (hn : 0 < n) :
    words m a n * 2 ^ S % 2 ^ 64 = (memWord m a.toNat).toNat * 2 ^ S % 2 ^ 64 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [words, Nat.add_mul, Nat.mul_assoc, Nat.add_mul_mod_self_left]

/-- The quotient and the remainder from the division of the numerator shifted left by `S`. -/
theorem div_of_norm {U d S Q r : Nat} (hd : 0 < d) (h : U * 2 ^ S = d * 2 ^ S * Q + r)
    (hr : r < d * 2 ^ S) : Q = U / d ∧ r / 2 ^ S = U % d := by
  have hp : 0 < 2 ^ S := by positivity
  have h1 : d * Q ≤ U := by
    apply Nat.le_of_mul_le_mul_right _ hp
    calc d * Q * 2 ^ S = d * 2 ^ S * Q := by ring
      _ ≤ U * 2 ^ S := by omega
  obtain ⟨t, rfl⟩ : ∃ t, U = d * Q + t := ⟨U - d * Q, by omega⟩
  have hrt : r = t * 2 ^ S := by
    have : (d * Q + t) * 2 ^ S = d * 2 ^ S * Q + t * 2 ^ S := by ring
    omega
  subst hrt
  have ht : t < d := by
    by_contra hc
    have := Nat.mul_le_mul_right (2 ^ S) (show d ≤ t by omega)
    omega
  obtain ⟨h2, h3⟩ := (Nat.div_mod_unique (a := d * Q + t) (c := t) (d := Q) hd).mpr ⟨by ring, ht⟩
  refine ⟨h2.symm, ?_⟩
  rw [Nat.mul_div_cancel _ hp, h3]

/-- The quotient and the remainder of `udivrem_by1()` from the division of its last digit. -/
theorem by1_final {U d S Qhi rem q0 r1 dig : Nat} (hd : 0 < d)
    (hq : Qhi * (d * 2 ^ S) + rem = U * 2 ^ S / 2 ^ 64) (hdig : dig = U * 2 ^ S % 2 ^ 64)
    (hq0 : q0 = (2 ^ 64 * rem + dig) / (d * 2 ^ S))
    (hr1 : r1 = (2 ^ 64 * rem + dig) % (d * 2 ^ S)) :
    q0 + 2 ^ 64 * Qhi = U / d ∧ r1 / 2 ^ S = U % d := by
  have hD : 0 < d * 2 ^ S := by positivity
  refine div_of_norm hd ?_ (hr1 ▸ Nat.mod_lt _ hD)
  have e1 := Nat.div_add_mod (U * 2 ^ S) (2 ^ 64)
  have e2 := Nat.div_add_mod (2 ^ 64 * rem + dig) (d * 2 ^ S)
  rw [← hq0, ← hr1] at e2
  rw [← hq, ← hdig] at e1
  linarith

theorem defn_shr_toNat {w a : BitVec 64} {n : Nat} (h : Defn w (a >>> n)) :
    w.toNat = a.toNat / 2 ^ n := by
  rw [h.eq, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem defn_shl_toNat {w a : BitVec 64} {n : Nat} (h : Defn w (a <<< n)) :
    w.toNat = a.toNat * 2 ^ n % 2 ^ 64 := by
  rw [h.eq, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

/-- The words of a buffer after a store of its first word. -/
theorem words_memStore_first (m : Mem) (a v : BitVec 64) (n : Nat) (hn : 0 < n)
    (ha : a.toNat + 8 * n ≤ 2 ^ 64) :
    words (memStore m a.toNat v) a n = v.toNat + 2 ^ 64 * words m (a + 8) (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [words, memWord_memStore_self, Nat.add_sub_cancel]
  cases k with
  | zero => rfl
  | succ k =>
    have h8 : (a + 8).toNat = a.toNat + 8 := by rw [BitVec.toNat_add]; simp; omega
    rw [words_memStore_of_disjoint m a.toNat v (k + 1) (a + 8) (by omega) (by omega)]

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

theorem ofNat_add8 (i : Nat) : BitVec.ofNat 64 (8 * i) + 8 = BitVec.ofNat 64 (8 * (i + 1)) := by
  bv_omega

theorem ofNat_sub1 (i : Nat) (h : 1 ≤ i) (hi : i < 2 ^ 64) :
    BitVec.ofNat 64 i + 18446744073709551615#64 = BitVec.ofNat 64 (i - 1) := by
  bv_omega

theorem ptr_sub8 (p : BitVec 64) (k : Nat) (h : 1 ≤ k) (hk : 8 * k < 2 ^ 64) :
    p + BitVec.ofNat 64 (8 * k) + 18446744073709551608#64 = p + BitVec.ofNat 64 (8 * (k - 1)) := by
  bv_omega

theorem ofNat_sub1_eq_zero (i : Nat) (hi : i < 2 ^ 64)
    (h : BitVec.ofNat 64 i + 18446744073709551615#64 = 0#64) : i = 1 := by
  bv_omega

/-- The table entry of the normalized `d` in the run: `v0 * v0` and `2^11 * v0 - 1`. -/
theorem table_LH {d wL wH : BitVec 64} (h : 2 ^ 63 ≤ d.toNat)
    (hwL : Defn wL (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64
      (523520 / (d.toNat / 2 ^ 55 - 256 + 256) * (523520 / (d.toNat / 2 ^ 55 - 256 + 256)) +
        2 ^ 32 * (2 ^ 11 * (523520 / (d.toNat / 2 ^ 55 - 256 + 256)) - 1))))))
    (hwH : Defn wH (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64
      (523520 / (d.toNat / 2 ^ 55 - 256 + 256) * (523520 / (d.toNat / 2 ^ 55 - 256 + 256)) +
        2 ^ 32 * (2 ^ 11 * (523520 / (d.toNat / 2 ^ 55 - 256 + 256)) - 1)) >>> 32)))) :
    wL.toNat = 523520 / (d.toNat / 2 ^ 55) * (523520 / (d.toNat / 2 ^ 55)) ∧
      wH.toNat = 2 ^ 11 * (523520 / (d.toNat / 2 ^ 55)) - 1 := by
  have hi := index_lt_256 h
  have hV := Intx.Model.reciprocal_table_entry _ hi
  rw [show d.toNat / 2 ^ 55 - 256 + 256 = d.toNat / 2 ^ 55 by have := d.isLt; omega] at hV hwL hwH
  obtain ⟨-, hv0b, -, -⟩ := hV
  have hVV := Nat.mul_le_mul hv0b hv0b
  rw [hwL.eq, hwH.eq]
  constructor
  · simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  · simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    omega

/-- The shift amount of `srl` by `negw s`: `64 - s` for `0 < s < 64`. -/
theorem negw_shift : ∀ k < 64, 0 < k →
    (BitVec.signExtend 64 (BitVec.setWidth 32 0#64 - BitVec.setWidth 32 (BitVec.ofNat 64 k))).toNat
      % 64 = 64 - k := by
  decide

/-- The top digits of the numerator shifted left by `S` with the top word `uT` and the word below it
`uT1`: the bits above the words, and the digit of the top word. -/
theorem by1_top (m : Mem) (a : BitVec 64) (n S : Nat) (hS : S < 64) (hn : 2 ≤ n) :
    words m a n * 2 ^ S / 2 ^ (64 * (n - 1)) = 2 ^ 64 * (wordAt m a (n - 1) / 2 ^ (64 - S)) +
      (wordAt m a (n - 1) * 2 ^ S + wordAt m a (n - 1 - 1) / 2 ^ (64 - S)) % 2 ^ 64 := by
  rw [← norm_top m a n S hS (by omega), ← norm_digit m a n S (n - 1) hS (by omega) (by omega)]
  have h := Nat.div_add_mod (words m a n * 2 ^ S / 2 ^ (64 * (n - 1))) (2 ^ 64)
  rw [Nat.div_div_eq_div_mul, ← pow_add, show 64 * (n - 1) + 64 = 64 * n by omega] at h
  omega

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

/-- The first quotient word and the remainder with the division of the top digits. -/
theorem top_div {Un D qT rem hi lo : Nat} (hD : 0 < D) (hU : Un = 2 ^ 64 * hi + lo)
    (hq : qT = (2 ^ 64 * hi + lo) / D) (hr : rem = (2 ^ 64 * hi + lo) % D) :
    qT * D + rem = Un ∧ rem < D := by
  subst hq hr hU
  exact ⟨by rw [Nat.mul_comm]; exact Nat.div_add_mod _ _, Nat.mod_lt _ hD⟩

/-- The first quotient word 0 and the remainder for the top word below the divisor. -/
theorem top_zero {Un d S uT uT1 lo : Nat} (hS : S < 64) (hd : d * 2 ^ S < 2 ^ 64)
    (huT : uT < d) (hU : Un = 2 ^ 64 * (uT / 2 ^ (64 - S)) + lo)
    (hlo : lo = (uT * 2 ^ S + uT1 / 2 ^ (64 - S)) % 2 ^ 64) (huT1 : uT1 < 2 ^ 64) :
    0 * (d * 2 ^ S) + lo = Un ∧ lo < d * 2 ^ S := by
  have e64 : (2 : Nat) ^ 64 = 2 ^ S * 2 ^ (64 - S) := by rw [← pow_add]; congr 1; omega
  have hd' : d < 2 ^ (64 - S) := by
    by_contra hc
    have := Nat.mul_le_mul_right (2 ^ S) (show 2 ^ (64 - S) ≤ d by omega)
    rw [Nat.mul_comm (2 ^ (64 - S)), ← e64] at this
    omega
  have h0 : uT / 2 ^ (64 - S) = 0 := Nat.div_eq_of_lt (by omega)
  have hb : uT1 / 2 ^ (64 - S) < 2 ^ S := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← e64]; exact huT1
  have h1 : uT * 2 ^ S + 2 ^ S ≤ d * 2 ^ S := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ huT
  rw [h0, Nat.mul_zero, Nat.zero_add] at hU
  refine ⟨by omega, ?_⟩
  rw [hlo]
  exact lt_of_le_of_lt (Nat.mod_le _ _) (by omega)

theorem ofNat_S_toNat {S : Nat} (h : S < 64) : (BitVec.ofNat 64 S).toNat = S := by
  rw [BitVec.toNat_ofNat]; omega

theorem ofNat_S_ne {S : Nat} (h : S < 64) (hne : ¬BitVec.ofNat 64 S = 0#64) : 0 < S := by
  rcases Nat.eq_zero_or_pos S with rfl | h0
  · exact absurd rfl hne
  · exact h0

theorem ofNat_S_eq {S : Nat} (h : S < 64) (he : BitVec.ofNat 64 S = 0#64) : S = 0 := by
  have := congrArg BitVec.toNat he
  rwa [ofNat_S_toNat h] at this

theorem cnt_sub2 (n : BitVec 64) (h : 2 ≤ n.toNat) :
    n + 18446744073709551614#64 = BitVec.ofNat 64 (n.toNat - 2) := by
  bv_omega

theorem cnt_sub2_eq_zero (n : BitVec 64) (h : 2 ≤ n.toNat)
    (he : n + 18446744073709551614#64 = 0#64) : n.toNat = 2 := by
  bv_omega

/-- The top digits for the shift 0: the top word. -/
theorem top_s0 (u v : Nat) (hu : u < 2 ^ 64) (hv : v < 2 ^ 64) :
    2 ^ 64 * (u / 2 ^ (64 - 0)) + (u * 2 ^ 0 + v / 2 ^ (64 - 0)) % 2 ^ 64 = u := by
  simp only [Nat.sub_zero, pow_zero, Nat.mul_one, Nat.div_eq_of_lt hu, Nat.div_eq_of_lt hv,
    Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.mod_eq_of_lt hu]

theorem cnt_sub2_zero (n : BitVec 64) (h : n.toNat = 2) : n + 18446744073709551614#64 = 0#64 := by
  bv_omega

theorem ptr_sub16 (p n : BitVec 64) (h : 2 ≤ n.toNat) (hn : 8 * n.toNat ≤ 2 ^ 64) :
    p + n <<< 3 + 18446744073709551600#64 = p + BitVec.ofNat 64 (8 * (n.toNat - 2)) := by
  bv_omega

theorem ptr_sub24 (p n : BitVec 64) (h : 3 ≤ n.toNat) (hn : 8 * n.toNat ≤ 2 ^ 64) :
    p + n <<< 3 + 18446744073709551592#64 = p + BitVec.ofNat 64 (8 * (n.toNat - 2 - 1)) := by
  bv_omega

/-- The words of one word after its store. -/
theorem words_one_memStore (m : Mem) (a v : BitVec 64) : words (memStore m a.toNat v) a 1 = v.toNat := by
  simp [words, memWord_memStore_self]

/-- The state of `udivrem_by1()` from the entry `x`, `m` at the exit of the loop (the instruction
167): the word `u[0]` in t0 and the normalized remainder `rem` of the words above it in t1, with
the quotient words above the word 0 stored. -/
def by1Exit (x : Regs) (m : Mem) (x' : Regs) (m' : Mem) : Prop :=
  let n := (x.get 11#5).toNat
  let S := 63 - Nat.log2 (x.get 14#5).toNat
  let D := (x.get 14#5).toNat * 2 ^ S
  x'.get 10#5 = x.get 10#5 ∧ (x'.get 11#5).toNat = S ∧ (x'.get 12#5).toNat = D ∧
  (x'.get 15#5).toNat = (2 ^ 128 - 1) / D - 2 ^ 64 ∧
  x'.get 5#5 = memWord m (x.get 12#5).toNat ∧ (x'.get 6#5).toNat < D ∧
  words m' (x.get 10#5 + 8#64) (n - 1) * D + (x'.get 6#5).toNat =
    words m (x.get 12#5) n * 2 ^ S / 2 ^ 64 ∧
  UnchangedExcept m m' (x.get 10#5) (8 * n) ∧
  x'.get 1#5 = x.get 1#5 ∧ x'.get 2#5 = x.get 2#5 ∧ (∀ r ∈ calleeSaved, x'.get r = x.get r)

theorem by1_exit {hi : BitVec 20} {lo : BitVec 12} {D : List (BitVec 64)} (base : BitVec 64)
    (x : Regs) (m : Mem) (hpre : udivrem_by1.pre x m)
    (hr : x.get 1#5 &&& 3 = 0) (x' : Regs) (m' : Mem) (h : by1Exit x m x' m') :
    Reach (bufWords (x.get 12#5) (x.get 13#5).toNat ++ bufWords (x.get 10#5) (x.get 11#5).toNat ++
        D) (udivrem_by1_progAt hi lo) base (pcAt base 167) x' m' (x.get 1#5)
      (udivrem_by1.post x m) := by
  obtain ⟨h10, h11, h12, h15, h5, h6, hq, hu, h1, h2, hcs⟩ := h
  have hd0 : (x.get 14#5).toNat ≠ 0 := by
    simp only [udivrem_by1.pre] at hpre; simp (disch := decide) only [Regs.eq_get x] at hpre; omega
  have hL : Nat.log2 (x.get 14#5).toNat < 64 := (Nat.log2_lt hd0).mpr (x.get 14#5).isLt
  have hS : (x'.get 11#5).toNat % 64 = 63 - Nat.log2 (x.get 14#5).toNat := by rw [h11]; omega
  have hd63 : 2 ^ 63 ≤ (x'.get 12#5).toNat := by
    rw [h12]; have := Nat.log2_self_le hd0
    calc 2 ^ 63 = 2 ^ Nat.log2 (x.get 14#5).toNat * 2 ^ (63 - Nat.log2 (x.get 14#5).toNat) := by
          rw [← pow_add]; congr 1; omega
      _ ≤ _ := Nat.mul_le_mul_right _ this
  have hv : (x'.get 15#5).toNat = (2 ^ 128 - 1) / (x'.get 12#5).toNat - 2 ^ 64 := by rw [h15, h12]
  rv_exec_cut
  all_goals
    have hs := div2by1BV_spec (x'.get 6#5) (x'.get 5#5 <<< ((x'.get 11#5).toNat % 64))
      (x'.get 12#5) (x'.get 15#5) hd63 (by rw [h12]; exact h6) hv
    simp only [div2by1BV] at hs
    rw [BitVec.mul_comm (x'.get 6#5) (x'.get 15#5), mulhu_comm (x'.get 6#5)] at hs
    rv_fold hs
    try simp only [zopz0zI_u_eq, decide_eq_true_eq, decide_eq_false_iff_not] at *
    try simp (disch := assumption) only [if_pos, if_neg] at hs
    try simp only [BitVec.add_assoc] at hs
    rv_fold hs
    -- The word q[0] and the return.
    refine Reach.step (by decide) (by rv_fetch) ?_
    simp only [StepGoal, Nat.reduceAdd]
    rv_val
    rw [h10]
    refine ⟨List.mem_append_left _ (List.mem_append_right _
      (mem_bufWords_zero (by simp only [udivrem_by1.pre, Buf] at hpre
                             simp (disch := decide) only [Regs.eq_get x] at hpre; omega))), ?_⟩
    rv_exec_cut
    rv_val
    rw [h1, update_aligned hr]
    refine Reach.refl ?_
    have hres := defn_shr_toNat ‹Defn _ ((_ : BitVec 64) >>> ((x'.get 11#5).toNat % 64))›
    have hdig := defn_shl_toNat ‹Defn _ (x'.get 5#5 <<< ((x'.get 11#5).toNat % 64))›
    rw [hS] at hres hdig
    rw [h5] at hdig
    simp only [udivrem_by1.pre, Buf, Disjoint] at hpre
    simp only [udivrem_by1.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    simp (disch := decide) only [Regs.eq_get x] at hpre ⊢
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    obtain ⟨⟨hqa, hqn⟩, ⟨hua, hun⟩, hdis, hn2, h1113, hdpos⟩ := hpre
    rw [← h1113]
    rw [h12] at hs
    have hn1 : 0 < (x.get 11#5).toNat := by omega
    have hdig' := hdig.trans (words_mul_mod m (x.get 12#5) (x.get 11#5).toNat
      (63 - Nat.log2 (x.get 14#5).toNat) hn1).symm
    obtain ⟨hfq, hfr⟩ := by1_final hdpos hq hdig' hs.1 hs.2
    rw [words_memStore_first _ _ _ _ hn1 hqn]
    refine ⟨hfq, hres.trans hfr, (unchangedExcept_memStore _ _ ⟨le_refl _, by omega⟩).mpr hu, ?_⟩
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte, BitVec.ofNat_eq_ofNat]
    simp (disch := decide) only [Regs.eq_get x']
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hcs
    exact hcs

/-- The state of `udivrem_by1()` from the entry `x`, `m` at the head of its loop (the instruction
148) before the quotient word `i`: the counter `i`, the pointers to `q[i]` and `u[i - 1]`, the word
`u[i]` and the normalized remainder `rem` of the words above it, with the quotient words above `i`
stored. -/
def by1Head (x : Regs) (m : Mem) (i : Nat) (x' : Regs) (m' : Mem) : Prop :=
  let n := (x.get 11#5).toNat
  let S := 63 - Nat.log2 (x.get 14#5).toNat
  let D := (x.get 14#5).toNat * 2 ^ S
  1 ≤ i ∧ i + 2 ≤ n ∧
  x'.get 10#5 = x.get 10#5 ∧ (x'.get 11#5).toNat = S ∧
  x'.get 16#5 = x'.get 11#5 ^^^ 18446744073709551615#64 ∧
  (x'.get 12#5).toNat = D ∧ (x'.get 15#5).toNat = (2 ^ 128 - 1) / D - 2 ^ 64 ∧
  x'.get 13#5 = BitVec.ofNat 64 i ∧ x'.get 14#5 = x.get 10#5 + BitVec.ofNat 64 (8 * i) ∧
  x'.get 7#5 = x.get 12#5 + BitVec.ofNat 64 (8 * (i - 1)) ∧
  x'.get 17#5 = memWord m (x.get 12#5 + BitVec.ofNat 64 (8 * i)).toNat ∧
  (x'.get 6#5).toNat < D ∧
  words m' (x.get 10#5 + BitVec.ofNat 64 (8 * (i + 1))) (n - 1 - i) * D + (x'.get 6#5).toNat =
    words m (x.get 12#5) n * 2 ^ S / 2 ^ (64 * (i + 1)) ∧
  UnchangedExcept m m' (x.get 10#5) (8 * n) ∧
  x'.get 1#5 = x.get 1#5 ∧ x'.get 2#5 = x.get 2#5 ∧ (∀ r ∈ calleeSaved, x'.get r = x.get r)

theorem by1_loop {hi : BitVec 20} {lo : BitVec 12} {D : List (BitVec 64)} (base : BitVec 64)
    (x : Regs) (m : Mem) (hpre : udivrem_by1.pre x m)
    (hr : x.get 1#5 &&& 3 = 0) :
    ∀ i x' m', by1Head x m i x' m' →
    Reach (bufWords (x.get 12#5) (x.get 13#5).toNat ++ bufWords (x.get 10#5) (x.get 11#5).toNat ++
        D) (udivrem_by1_progAt hi lo) base (pcAt base 148) x' m' (x.get 1#5)
      (udivrem_by1.post x m) := by
  apply Reach.loop (by1Head x m)
  intro i x' m' h ih
  obtain ⟨hi1, hin, h10, h11, h16, h12, h15, h13, h14, h7, h17, h6, hq, hu, h1, h2, hcs⟩ := h
  have hpre' := hpre
  simp only [udivrem_by1.pre, Buf, Disjoint] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hqa, hqn⟩, ⟨hua, hun⟩, hdis, hn2, h1113, hdpos⟩ := hpre'
  -- The word u[i - 1].
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  rw [h7]
  refine ⟨List.mem_append_left _ (List.mem_append_left _ (mem_bufWords (by omega))),
    fun wlo hwlo => ?_⟩
  rv_exec_cut 148 167
  -- The quotient word q[i].
  all_goals
    refine Reach.step (by decide) (by rv_fetch) ?_
    simp only [StepGoal, Nat.reduceAdd]
    rv_val
    rw [h14]
    refine ⟨List.mem_append_left _ (List.mem_append_right _ (mem_bufWords (by omega))), ?_⟩
    rv_exec_cut 148 167
  -- The quotient word and the remainder of the digit i.
  all_goals
    have hL : Nat.log2 (x.get 14#5).toNat < 64 :=
      (Nat.log2_lt (by omega)).mpr (x.get 14#5).isLt
    have hS64 : (x'.get 11#5).toNat < 64 := by omega
    have hd63 : 2 ^ 63 ≤ (x'.get 12#5).toNat := by
      rw [h12]; have := Nat.log2_self_le (show (x.get 14#5).toNat ≠ 0 by omega)
      calc 2 ^ 63 = 2 ^ Nat.log2 (x.get 14#5).toNat * 2 ^ (63 - Nat.log2 (x.get 14#5).toNat) := by
            rw [← pow_add]; congr 1; omega
        _ ≤ _ := Nat.mul_le_mul_right _ this
    have hv : (x'.get 15#5).toNat = (2 ^ 128 - 1) / (x'.get 12#5).toNat - 2 ^ 64 := by
      rw [h15, h12]
    have hrem : (x'.get 6#5).toNat < (x'.get 12#5).toNat := by rw [h12]; exact h6
    have hu8 : (x.get 12#5 + BitVec.ofNat 64 (8 * (i - 1))).toNat = (x.get 12#5).toNat + 8 * (i - 1) := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have hlo : wlo = memWord m (x.get 12#5 + BitVec.ofNat 64 (8 * (i - 1))).toNat :=
      hwlo.eq.trans (memWord_of_unchangedExcept hu _ (by rw [hu8]; omega))
    first
      | (rv_has x'.get 11#5 = 0#64
         have hs := div2by1BV_spec (x'.get 6#5) (x'.get 17#5) (x'.get 12#5) (x'.get 15#5) hd63
           hrem hv
         simp only [div2by1BV] at hs
         rv_fold hs
         try simp only [zopz0zI_u_eq, decide_eq_true_eq, decide_eq_false_iff_not] at *
         try simp (disch := assumption) only [if_pos, if_neg] at hs
         try simp only [BitVec.add_assoc] at hs
         rv_fold hs
         rv_get hz : x'.get 11#5 = 0#64
         have hS0 : 63 - Nat.log2 (x.get 14#5).toNat = 0 := by
           rw [← h11, hz]; rfl
         have hdig : (x'.get 17#5).toNat = words m (x.get 12#5) (x.get 11#5).toNat *
             2 ^ (63 - Nat.log2 (x.get 14#5).toNat) / 2 ^ (64 * i) % 2 ^ 64 := by
           rw [norm_digit m (x.get 12#5) (x.get 11#5).toNat (63 - Nat.log2 (x.get 14#5).toNat) i
             (by omega) hi1 (by omega), hS0, h17]
           simp only [pow_zero, Nat.mul_one, Nat.sub_zero, wordAt]
           rw [Nat.div_eq_of_lt (BitVec.isLt _), Nat.add_zero, Nat.mod_eq_of_lt (BitVec.isLt _)]
         rw [hdig, h12] at hs)
      | (have hs := div2by1BV_spec (x'.get 6#5) ((x'.get 17#5 <<< ((x'.get 11#5).toNat % 64)) |||
           ((wlo >>> 1) >>> ((x'.get 16#5).toNat % 64))) (x'.get 12#5) (x'.get 15#5) hd63 hrem hv
         simp only [div2by1BV] at hs
         have hf := toNat_fshl_code (x'.get 17#5) wlo (x'.get 11#5) hS64
         rw [← h16] at hf
         rv_fold hs
         rv_fold hf
         try simp only [zopz0zI_u_eq, decide_eq_true_eq, decide_eq_false_iff_not] at *
         try simp (disch := assumption) only [if_pos, if_neg] at hs
         try simp only [BitVec.add_assoc] at hs
         rv_fold hs
         rw [hlo, h17, h11, ← norm_digit m (x.get 12#5) (x.get 11#5).toNat
           (63 - Nat.log2 (x.get 14#5).toNat) i (by omega) hi1 (by omega)] at hf
         rw [hf, h12] at hs)
  -- The cut points: the exit after the word 1, the head before the word i - 1.
  all_goals
    obtain ⟨hqi, hri⟩ := hs
    have hstep := div_step i hq hqi hri
    have hD : 0 < (x.get 14#5).toNat * 2 ^ (63 - Nat.log2 (x.get 14#5).toNat) :=
      Nat.mul_pos hdpos (Nat.two_pow_pos _)
    have hri' := hri ▸ Nat.mod_lt _ hD
    have hq8 : (x.get 10#5 + BitVec.ofNat 64 (8 * i)).toNat = (x.get 10#5).toNat + 8 * i := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have hq8' : x.get 10#5 + BitVec.ofNat 64 (8 * i) + 8 = x.get 10#5 + BitVec.ofNat 64 (8 * (i + 1)) := by
      rw [BitVec.add_assoc, ofNat_add8]
    have hwq : ∀ v : BitVec 64, words (memStore m' (x.get 10#5 + BitVec.ofNat 64 (8 * i)).toNat v)
        (x.get 10#5 + BitVec.ofNat 64 (8 * i)) ((x.get 11#5).toNat - i) = v.toNat + 2 ^ 64 *
          words m' (x.get 10#5 + BitVec.ofNat 64 (8 * (i + 1))) ((x.get 11#5).toNat - 1 - i) := by
      intro v
      rw [words_memStore_first m' _ v _ (by omega) (by rw [hq8]; omega), hq8',
        show (x.get 11#5).toNat - i - 1 = (x.get 11#5).toNat - 1 - i by omega]
    have hun' : ∀ v : BitVec 64, UnchangedExcept m
        (memStore m' (x.get 10#5 + BitVec.ofNat 64 (8 * i)).toNat v) (x.get 10#5)
        (8 * (x.get 11#5).toNat) :=
      fun v => (unchangedExcept_memStore _ v ⟨by omega, by omega⟩).mpr hu
  all_goals first
    | (rv_not_at 167; skip)
    | (rv_get heq : x'.get 13#5 + 18446744073709551615#64 = 0#64
       have hi : i = 1 := ofNat_sub1_eq_zero i (by omega) (h13 ▸ heq)
       subst hi
       refine by1_exit base x m hpre hr _ _ ?_
       simp only [by1Exit]
       simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
       simp only [Nat.mul_one, Nat.sub_self, Nat.mul_zero] at hwq hstep hlo
       rw [show x.get 12#5 + BitVec.ofNat 64 0 = x.get 12#5 by simp] at hlo
       refine ⟨h10, h11, h12, h15, hlo, hri', ?_, hun' _, h1, h2, ?_⟩
       · rw [show x.get 10#5 + 8#64 = x.get 10#5 + BitVec.ofNat 64 8 from rfl, hwq]; exact hstep
       · intro r hr
         simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
         rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
           rfl | rfl <;>
         simp (config := { decide := true }) only [↓reduceIte] <;>
         exact hcs _ (by decide))
  all_goals first
    | (rv_not_at 148; skip)
    | (rv_get hne : ¬x'.get 13#5 + 18446744073709551615#64 = 0#64
       have hi : i ≠ 1 := by
         rintro rfl; rw [h13] at hne; exact hne (by decide)
       refine ih (i - 1) (by omega) _ _ ?_
       simp only [by1Head]
       simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
       rw [show i - 1 + 1 = i by omega, show (x.get 11#5).toNat - 1 - (i - 1) =
         (x.get 11#5).toNat - i by omega]
       refine ⟨by omega, by omega, h10, h11, h16, h12, h15, ?_, ?_, ?_, hlo, hri', ?_, hun' _, h1,
         h2, ?_⟩
       · rw [h13]; exact ofNat_sub1 i (by omega) (by omega)
       · rw [h14]; exact ptr_sub8 _ i (by omega) (by omega)
       · rw [h7]; exact ptr_sub8 _ (i - 1) (by omega) (by omega)
       · rw [hwq]; exact hstep
       · intro r hr
         simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
         rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
           rfl | rfl <;>
         simp (config := { decide := true }) only [↓reduceIte] <;>
         exact hcs _ (by decide))

end IntxRV.Api
