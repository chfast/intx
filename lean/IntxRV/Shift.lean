import IntxRV.Values
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
/-!
# Shifts of words

The lemmas of the proofs of the shifts of `uint256`: the words that clang computes for a shift by
`s = 64 * k + t`, `t < 64`, as funnel shifts, `(a <<< t) ||| (b >>> (64 - t))` for the shift left
and `(a >>> t) ||| (b <<< (64 - t))` for the shift right, their numbers, and the value of the
words.
-/

open Sail LeanRV64D LeanRV64D.Functions LeanRV64D.Defs

-- The powers of the specifications use the `Nat` power of the core (`instPowNat`), not the one of
-- Mathlib's monoids: the same terms, so that `omega` takes them for the same atoms.
attribute [local instance high] instPowNat

namespace IntxRV

/-- The unsigned comparison of `bgeu`. -/
theorem zopz0zKzJ_u_eq (a b : BitVec 64) : zopz0zKzJ_u a b = decide (b ≤ a) := by
  simp [zopz0zKzJ_u, Sail.BitVec.toNatInt, BitVec.le_def]

/-! ## The shift left -/

/-- The funnel shift of `a:b` left by `t < 64` as a number, also for `t = 0`. -/
theorem toNat_shl_or_shr (a b : BitVec 64) (t : Nat) (h : t < 64) :
    ((a <<< t) ||| (b >>> (64 - t))).toNat = a.toNat * 2 ^ t % 2 ^ 64 + b.toNat / 2 ^ (64 - t) := by
  have e64 : (2 : Nat) ^ 64 = 2 ^ t * 2 ^ (64 - t) := by rw [← pow_add]; congr 1; omega
  have hb : b.toNat / 2 ^ (64 - t) < 2 ^ t := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← e64]; exact b.isLt
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, e64, Nat.mul_comm a.toNat, Nat.mul_mod_mul_left,
    ← Nat.two_pow_add_eq_or_of_lt hb]

theorem toNat_shr_or_shl (a b : BitVec 64) (t : Nat) (h : t < 64) :
    ((b >>> (64 - t)) ||| (a <<< t)).toNat = b.toNat / 2 ^ (64 - t) + a.toNat * 2 ^ t % 2 ^ 64 := by
  rw [BitVec.or_comm, toNat_shl_or_shr a b t h, Nat.add_comm]

theorem toNat_shl (a : BitVec 64) (t : Nat) : (a <<< t).toNat = a.toNat * 2 ^ t % 2 ^ 64 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

/-- The low word and the high word of a word shifted left by `t < 64`. -/
theorem mul_two_pow_split (a t : Nat) (h : t < 64) :
    a * 2 ^ t = a * 2 ^ t % 2 ^ 64 + 2 ^ 64 * (a / 2 ^ (64 - t)) := by
  have e64 : (2 : Nat) ^ 64 = 2 ^ t * 2 ^ (64 - t) := by rw [← pow_add]; congr 1; omega
  have : a * 2 ^ t / 2 ^ 64 = a / 2 ^ (64 - t) := by
    rw [e64, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ (Nat.two_pow_pos t)]
  rw [← this]; exact (Nat.mod_add_div _ _).symm

/-- `(b >>> 1) >>> (63 - t)` is `b >>> (64 - t)`. -/
theorem ushiftRight_one_ushiftRight (b : BitVec 64) (t : Nat) (h : t < 64) :
    (b >>> 1) >>> (63 - t) = b >>> (64 - t) := by
  rw [← BitVec.shiftRight_add]; congr 1; omega

/-- `(b >>> (63 - t)) >>> 1` is `b >>> (64 - t)`. -/
theorem ushiftRight_ushiftRight_one (b : BitVec 64) (t : Nat) (h : t < 64) :
    (b >>> (63 - t)) >>> 1 = b >>> (64 - t) := by
  rw [← BitVec.shiftRight_add]; congr 1; omega

/-- The funnel shift that clang computes from `(b <<< 1) <<< t`, with the top bit put back. -/
theorem shl_funnel_top (a b : BitVec 64) (t : Nat) (h : t < 64) :
    ((b >>> (63 - t)) <<< 63) ||| ((((b <<< 1) <<< t) ||| (a >>> (63 - t))) >>> 1) =
      (b <<< t) ||| (a >>> (64 - t)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  by_cases h63 : i = 63
  · subst h63
    have ha : a.getLsbD (64 - t + 63) = false := BitVec.getLsbD_of_ge a _ (by omega)
    have hb : (b <<< 1 <<< t ||| a >>> (63 - t)).getLsbD (1 + 63) = false :=
      BitVec.getLsbD_of_ge _ _ (by omega)
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight] at hb
    rw [ha, show 63 - t + (63 - 63) = 63 - t by omega]
    simp_all
    omega
  · have hlt : i < 63 := by omega
    simp only [hlt, decide_true, Bool.not_true, Bool.false_and, Bool.false_or,
      show 1 + i < 64 by omega, show i < 64 by omega, decide_true, Bool.true_and,
      show 63 - t + (1 + i) = 64 - t + i by omega]
    by_cases hit : i < t
    · simp only [hit, decide_true, Bool.not_true, Bool.false_and, Bool.false_or]
      by_cases h1 : 1 + i < t
      · simp [h1]
      · simp [h1, show 1 + i - t < 1 by omega]
    · simp [hit, show ¬ 1 + i < t by omega, show ¬ 1 + i - t < 1 by omega,
        show 1 + i - t - 1 = i - t by omega, show 1 + i - t < 64 by omega]
/-- `x ||| 0`, with the `0` that `li` and `x0` leave. -/
theorem or_zero' (a : BitVec 64) : a ||| 0 = a := by simp

theorem zero_or' (a : BitVec 64) : 0 ||| a = a := by simp

/-- The shift amounts of `srl` by the complement of `s` and of `sll` by `s - 128`. -/
theorem toNat_xor_allOnes_mod_64 (s : BitVec 64) :
    (s ^^^ 18446744073709551615#64).toNat % 64 = 63 - s.toNat % 64 := by
  rw [show (18446744073709551615#64) = BitVec.allOnes 64 by decide, BitVec.xor_allOnes,
    BitVec.toNat_not]
  omega

theorem toNat_add_neg128_mod_64 (s : BitVec 64) :
    (s + 18446744073709551488#64).toNat % 64 = s.toNat % 64 := by
  rw [BitVec.toNat_add]; simp; omega

/-- A funnel shift fits in a word. -/
theorem funnel_lt (a b t : Nat) (hb : b < 2 ^ 64) (ht : t < 64) :
    a * 2 ^ t % 2 ^ 64 + b / 2 ^ (64 - t) < 2 ^ 64 := by
  have e64 : (2 : Nat) ^ 64 = 2 ^ t * 2 ^ (64 - t) := by rw [← pow_add]; congr 1; omega
  have hq : b / 2 ^ (64 - t) < 2 ^ t := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← e64]; exact hb
  have hm : a * 2 ^ t % 2 ^ 64 = 2 ^ t * (a % 2 ^ (64 - t)) := by
    rw [e64, Nat.mul_comm a, Nat.mul_mod_mul_left]
  have hr : a % 2 ^ (64 - t) + 1 ≤ 2 ^ (64 - t) := Nat.mod_lt _ (by positivity)
  have := Nat.mul_le_mul_left (2 ^ t) hr
  rw [Nat.mul_add, Nat.mul_one, ← e64] at this
  omega

/-! The value of the words of `x * 2 ^ s % 2 ^ 256` for `s = 64 * k + t`: the words below `k` are
zero, the word `k` is the low word shifted left by `t`, the others the funnel shifts. The lemmas
take the same arguments, for `shl_close` of the proof of `operator<<`. -/

theorem shl_val_0 (a0 a1 a2 a3 s t : Nat) (h0 : a0 < 2 ^ 64) (h1 : a1 < 2 ^ 64)
    (h2 : a2 < 2 ^ 64) (_h3 : a3 < 2 ^ 64) (ht : t < 64) (hs : s = t) :
    a0 * 2 ^ t % 2 ^ 64 + 2 ^ 64 * ((a1 * 2 ^ t % 2 ^ 64 + a0 / 2 ^ (64 - t)) +
      2 ^ 64 * ((a2 * 2 ^ t % 2 ^ 64 + a1 / 2 ^ (64 - t)) +
        2 ^ 64 * (a3 * 2 ^ t % 2 ^ 64 + a2 / 2 ^ (64 - t)))) =
    (a0 + 2 ^ 64 * (a1 + 2 ^ 64 * (a2 + 2 ^ 64 * a3))) * 2 ^ s % 2 ^ 256 := by
  rw [hs]
  have s0 := mul_two_pow_split a0 t ht
  have s1 := mul_two_pow_split a1 t ht
  have s2 := mul_two_pow_split a2 t ht
  have s3 := mul_two_pow_split a3 t ht
  have b1 := funnel_lt a1 a0 t h0 ht
  have b2 := funnel_lt a2 a1 t h1 ht
  have b3 := funnel_lt a3 a2 t h2 ht
  have b0 : a0 * 2 ^ t % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by positivity)
  rw [show (a0 + 2 ^ 64 * (a1 + 2 ^ 64 * (a2 + 2 ^ 64 * a3))) * 2 ^ t =
    a0 * 2 ^ t + 2 ^ 64 * (a1 * 2 ^ t) + 2 ^ 128 * (a2 * 2 ^ t) + 2 ^ 192 * (a3 * 2 ^ t) by ring]
  omega

theorem shl_val_1 (a0 a1 a2 a3 s t : Nat) (h0 : a0 < 2 ^ 64) (h1 : a1 < 2 ^ 64)
    (_h2 : a2 < 2 ^ 64) (_h3 : a3 < 2 ^ 64) (ht : t < 64) (hs : s = 64 + t) :
    2 ^ 64 * (a0 * 2 ^ t % 2 ^ 64 + 2 ^ 64 * ((a1 * 2 ^ t % 2 ^ 64 + a0 / 2 ^ (64 - t)) +
      2 ^ 64 * (a2 * 2 ^ t % 2 ^ 64 + a1 / 2 ^ (64 - t)))) =
    (a0 + 2 ^ 64 * (a1 + 2 ^ 64 * (a2 + 2 ^ 64 * a3))) * 2 ^ s % 2 ^ 256 := by
  rw [hs, pow_add]
  have s0 := mul_two_pow_split a0 t ht
  have s1 := mul_two_pow_split a1 t ht
  have s2 := mul_two_pow_split a2 t ht
  have b1 := funnel_lt a1 a0 t h0 ht
  have b2 := funnel_lt a2 a1 t h1 ht
  rw [show (a0 + 2 ^ 64 * (a1 + 2 ^ 64 * (a2 + 2 ^ 64 * a3))) * (2 ^ 64 * 2 ^ t) =
    2 ^ 64 * (a0 * 2 ^ t) + 2 ^ 128 * (a1 * 2 ^ t) + 2 ^ 192 * (a2 * 2 ^ t) +
      2 ^ 256 * (a3 * 2 ^ t) by ring]
  omega

theorem shl_val_2 (a0 a1 a2 a3 s t : Nat) (h0 : a0 < 2 ^ 64) (_h1 : a1 < 2 ^ 64)
    (_h2 : a2 < 2 ^ 64) (_h3 : a3 < 2 ^ 64) (ht : t < 64) (hs : s = 128 + t) :
    2 ^ 64 * (2 ^ 64 * (a0 * 2 ^ t % 2 ^ 64 + 2 ^ 64 * (a1 * 2 ^ t % 2 ^ 64 + a0 / 2 ^ (64 - t)))) =
    (a0 + 2 ^ 64 * (a1 + 2 ^ 64 * (a2 + 2 ^ 64 * a3))) * 2 ^ s % 2 ^ 256 := by
  rw [hs, pow_add]
  have s0 := mul_two_pow_split a0 t ht
  have s1 := mul_two_pow_split a1 t ht
  have b1 := funnel_lt a1 a0 t h0 ht
  rw [show (a0 + 2 ^ 64 * (a1 + 2 ^ 64 * (a2 + 2 ^ 64 * a3))) * (2 ^ 128 * 2 ^ t) =
    2 ^ 128 * (a0 * 2 ^ t) + 2 ^ 192 * (a1 * 2 ^ t) +
      2 ^ 256 * (a2 * 2 ^ t + 2 ^ 64 * (a3 * 2 ^ t)) by ring]
  omega

theorem shl_val_3 (a0 a1 a2 a3 s t : Nat) (_h0 : a0 < 2 ^ 64) (_h1 : a1 < 2 ^ 64)
    (_h2 : a2 < 2 ^ 64) (_h3 : a3 < 2 ^ 64) (ht : t < 64) (hs : s = 192 + t) :
    2 ^ 64 * (2 ^ 64 * (2 ^ 64 * (a0 * 2 ^ t % 2 ^ 64))) =
    (a0 + 2 ^ 64 * (a1 + 2 ^ 64 * (a2 + 2 ^ 64 * a3))) * 2 ^ s % 2 ^ 256 := by
  rw [hs, pow_add]
  have s0 := mul_two_pow_split a0 t ht
  rw [show (a0 + 2 ^ 64 * (a1 + 2 ^ 64 * (a2 + 2 ^ 64 * a3))) * (2 ^ 192 * 2 ^ t) =
    2 ^ 192 * (a0 * 2 ^ t) +
      2 ^ 256 * (a1 * 2 ^ t + 2 ^ 64 * (a2 * 2 ^ t) + 2 ^ 128 * (a3 * 2 ^ t)) by ring]
  omega

/-- The shift by 256 or more. -/
theorem shl_val_ge (x s : Nat) (hs : 256 ≤ s) : 0 = x * 2 ^ s % 2 ^ 256 :=
  (Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_left (Nat.pow_dvd_pow 2 hs) x)).symm


/-! ## The shift right -/

theorem toNat_ushiftRight' (a : BitVec 64) (t : Nat) : (a >>> t).toNat = a.toNat / 2 ^ t := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- `(b <<< 1) <<< (63 - t)` is `b <<< (64 - t)`. -/
theorem shiftLeft_one_shiftLeft (b : BitVec 64) (t : Nat) (h : t < 64) :
    (b <<< 1) <<< (63 - t) = b <<< (64 - t) := by
  rw [← BitVec.shiftLeft_add]; congr 1; omega

/-- `(b <<< (63 - t)) <<< 1` is `b <<< (64 - t)`. -/
theorem shiftLeft_shiftLeft_one (b : BitVec 64) (t : Nat) (h : t < 64) :
    (b <<< (63 - t)) <<< 1 = b <<< (64 - t) := by
  rw [← BitVec.shiftLeft_add]; congr 1; omega

/-- The funnel shift that clang computes from `(a >>> 1) >>> t`, with the bottom bit put back. -/
theorem shr_funnel_bot (a b : BitVec 64) (t : Nat) (h : t < 64) :
    ((((a >>> 1) >>> t) ||| (b <<< (63 - t))) <<< 1) ||| ((a <<< (63 - t)) >>> 63) =
      (a >>> t) ||| (b <<< (64 - t)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  by_cases h0 : i = 0
  · subst h0
    simp [show 63 - t ≤ 63 by omega, show 63 - (63 - t) = t by omega, show 0 < 64 - t by omega]
  · have ht : (a <<< (63 - t)).getLsbD (63 + i) = false := BitVec.getLsbD_of_ge _ _ (by omega)
    simp only [BitVec.getLsbD_shiftLeft] at ht
    rw [ht]
    simp only [show i < 64 by omega, decide_true, Bool.true_and, Bool.or_false,
      show ¬ i < 1 by omega, decide_false, Bool.not_false, show i - 1 < 64 by omega,
      show (i - 1 < 63 - t) = (i < 64 - t) from propext (by omega),
      show i - 1 - (63 - t) = i - (64 - t) by omega]
    rw [show 1 + (t + (i - 1)) = t + i by omega]

/-- The funnel shift of `b:a` right by `t < 64` as a number, also for `t = 0`. -/
theorem toNat_shr_funnel (a b : BitVec 64) (t : Nat) (h : t < 64) :
    ((a >>> t) ||| (b <<< (64 - t))).toNat = a.toNat / 2 ^ t + b.toNat * 2 ^ (64 - t) % 2 ^ 64 := by
  have e64 : (2 : Nat) ^ 64 = 2 ^ (64 - t) * 2 ^ t := by rw [← pow_add]; congr 1; omega
  have ha : a.toNat / 2 ^ t < 2 ^ (64 - t) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← e64]; exact a.isLt
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, e64, Nat.mul_comm b.toNat, Nat.mul_mod_mul_left, Nat.or_comm,
    ← Nat.two_pow_add_eq_or_of_lt ha]
  ring

theorem toNat_shl_or_shr' (a b : BitVec 64) (t : Nat) (h : t < 64) :
    ((b <<< (64 - t)) ||| (a >>> t)).toNat = b.toNat * 2 ^ (64 - t) % 2 ^ 64 + a.toNat / 2 ^ t := by
  rw [BitVec.or_comm, toNat_shr_funnel a b t h, Nat.add_comm]

/-- The words of `x / 2 ^ t`, `t < 64`, as funnel shifts: their value. -/
theorem shr_val4 (a0 a1 a2 a3 t : Nat) (ht : t < 64) :
    (a0 / 2 ^ t + a1 * 2 ^ (64 - t) % 2 ^ 64) +
      2 ^ 64 * ((a1 / 2 ^ t + a2 * 2 ^ (64 - t) % 2 ^ 64) +
        2 ^ 64 * ((a2 / 2 ^ t + a3 * 2 ^ (64 - t) % 2 ^ 64) + 2 ^ 64 * (a3 / 2 ^ t))) =
    (a0 + 2 ^ 64 * (a1 + 2 ^ 64 * (a2 + 2 ^ 64 * a3))) / 2 ^ t := by
  have hPP : 2 ^ t * 2 ^ (64 - t) = (2 : Nat) ^ 64 := by rw [← pow_add]; congr 1; omega
  have hu : ∀ a, a * 2 ^ (64 - t) % 2 ^ 64 = a % 2 ^ t * 2 ^ (64 - t) := fun a => by
    rw [← hPP, Nat.mul_mod_mul_right]
  have hP : 0 < 2 ^ t := Nat.two_pow_pos t
  rw [hu, hu, hu]
  have d0 := Nat.div_add_mod a0 (2 ^ t)
  have d1 := Nat.div_add_mod a1 (2 ^ t)
  have d2 := Nat.div_add_mod a2 (2 ^ t)
  have d3 := Nat.div_add_mod a3 (2 ^ t)
  generalize a0 / 2 ^ t = q0 at *
  generalize a1 / 2 ^ t = q1 at *
  generalize a2 / 2 ^ t = q2 at *
  generalize a3 / 2 ^ t = q3 at *
  have m0 := Nat.mod_lt a0 hP
  generalize a0 % 2 ^ t = r0 at *
  generalize a1 % 2 ^ t = r1 at *
  generalize a2 % 2 ^ t = r2 at *
  generalize a3 % 2 ^ t = r3 at *
  generalize (2 : Nat) ^ (64 - t) = P' at *
  generalize (2 : Nat) ^ t = P at *
  subst d0 d1 d2 d3
  have key :
      P * q0 + r0 + 2 ^ 64 * (P * q1 + r1 + 2 ^ 64 * (P * q2 + r2 + 2 ^ 64 * (P * q3 + r3))) =
        P * (q0 + r1 * P' + 2 ^ 64 * (q1 + r2 * P' + 2 ^ 64 * (q2 + r3 * P' + 2 ^ 64 * q3))) +
          r0 := by
    rw [← hPP]; ring
  rw [key, Nat.mul_add_div hP, Nat.div_eq_of_lt m0, Nat.add_zero]

theorem shr_val3 (a1 a2 a3 t : Nat) (ht : t < 64) :
    (a1 / 2 ^ t + a2 * 2 ^ (64 - t) % 2 ^ 64) +
      2 ^ 64 * ((a2 / 2 ^ t + a3 * 2 ^ (64 - t) % 2 ^ 64) + 2 ^ 64 * (a3 / 2 ^ t)) =
    (a1 + 2 ^ 64 * (a2 + 2 ^ 64 * a3)) / 2 ^ t := by
  have h := shr_val4 a1 a2 a3 0 t ht
  simpa using h

theorem shr_val2 (a2 a3 t : Nat) (ht : t < 64) :
    (a2 / 2 ^ t + a3 * 2 ^ (64 - t) % 2 ^ 64) + 2 ^ 64 * (a3 / 2 ^ t) =
    (a2 + 2 ^ 64 * a3) / 2 ^ t := by
  have h := shr_val4 a2 a3 0 0 t ht
  simpa using h

/-- The words above the low one of a number. -/
theorem div_two_pow_64 (a Y : Nat) (h : a < 2 ^ 64) : (a + 2 ^ 64 * Y) / 2 ^ 64 = Y := by
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos 64), Nat.div_eq_of_lt h, Nat.zero_add]

/-! The value of the words of `x / 2 ^ s` for `s = 64 * k + t`: the funnel shifts of the words from
`k`, the top word shifted right by `t`, and zero words. -/

theorem shr_val_0 (a0 a1 a2 a3 s t : Nat) (_h0 : a0 < 2 ^ 64) (_h1 : a1 < 2 ^ 64)
    (_h2 : a2 < 2 ^ 64) (_h3 : a3 < 2 ^ 64) (ht : t < 64) (hs : s = t) :
    (a0 / 2 ^ t + a1 * 2 ^ (64 - t) % 2 ^ 64) +
      2 ^ 64 * ((a1 / 2 ^ t + a2 * 2 ^ (64 - t) % 2 ^ 64) +
        2 ^ 64 * ((a2 / 2 ^ t + a3 * 2 ^ (64 - t) % 2 ^ 64) + 2 ^ 64 * (a3 / 2 ^ t))) =
    (a0 + 2 ^ 64 * (a1 + 2 ^ 64 * (a2 + 2 ^ 64 * a3))) / 2 ^ s := by
  rw [hs]; exact shr_val4 a0 a1 a2 a3 t ht

theorem shr_val_1 (a0 a1 a2 a3 s t : Nat) (h0 : a0 < 2 ^ 64) (_h1 : a1 < 2 ^ 64)
    (_h2 : a2 < 2 ^ 64) (_h3 : a3 < 2 ^ 64) (ht : t < 64) (hs : s = 64 + t) :
    (a1 / 2 ^ t + a2 * 2 ^ (64 - t) % 2 ^ 64) +
      2 ^ 64 * ((a2 / 2 ^ t + a3 * 2 ^ (64 - t) % 2 ^ 64) + 2 ^ 64 * (a3 / 2 ^ t)) =
    (a0 + 2 ^ 64 * (a1 + 2 ^ 64 * (a2 + 2 ^ 64 * a3))) / 2 ^ s := by
  rw [hs, pow_add, ← Nat.div_div_eq_div_mul, div_two_pow_64 _ _ h0]
  exact shr_val3 a1 a2 a3 t ht

theorem shr_val_2 (a0 a1 a2 a3 s t : Nat) (h0 : a0 < 2 ^ 64) (h1 : a1 < 2 ^ 64)
    (_h2 : a2 < 2 ^ 64) (_h3 : a3 < 2 ^ 64) (ht : t < 64) (hs : s = 128 + t) :
    (a2 / 2 ^ t + a3 * 2 ^ (64 - t) % 2 ^ 64) + 2 ^ 64 * (a3 / 2 ^ t) =
    (a0 + 2 ^ 64 * (a1 + 2 ^ 64 * (a2 + 2 ^ 64 * a3))) / 2 ^ s := by
  rw [hs, show 128 + t = 64 + (64 + t) by omega, pow_add, ← Nat.div_div_eq_div_mul,
    div_two_pow_64 _ _ h0, pow_add, ← Nat.div_div_eq_div_mul, div_two_pow_64 _ _ h1]
  exact shr_val2 a2 a3 t ht

theorem shr_val_3 (a0 a1 a2 a3 s t : Nat) (h0 : a0 < 2 ^ 64) (h1 : a1 < 2 ^ 64)
    (h2 : a2 < 2 ^ 64) (_h3 : a3 < 2 ^ 64) (_ht : t < 64) (hs : s = 192 + t) :
    a3 / 2 ^ t = (a0 + 2 ^ 64 * (a1 + 2 ^ 64 * (a2 + 2 ^ 64 * a3))) / 2 ^ s := by
  rw [hs, show 192 + t = 64 + (64 + (64 + t)) by omega, pow_add, ← Nat.div_div_eq_div_mul,
    div_two_pow_64 _ _ h0, pow_add, ← Nat.div_div_eq_div_mul, div_two_pow_64 _ _ h1, pow_add,
    ← Nat.div_div_eq_div_mul, div_two_pow_64 _ _ h2]

/-- The shift right by 256 or more. -/
theorem shr_val_ge (a0 a1 a2 a3 s : Nat) (h0 : a0 < 2 ^ 64) (h1 : a1 < 2 ^ 64)
    (h2 : a2 < 2 ^ 64) (h3 : a3 < 2 ^ 64) (hs : 256 ≤ s) :
    0 = (a0 + 2 ^ 64 * (a1 + 2 ^ 64 * (a2 + 2 ^ 64 * a3))) / 2 ^ s := by
  symm
  apply Nat.div_eq_of_lt
  calc _ < 2 ^ 256 := by omega
    _ ≤ 2 ^ s := Nat.pow_le_pow_right (by decide) hs

end IntxRV
