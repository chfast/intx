import Mathlib.Data.BitVec
/-!
# The count of the leading zeros

Without the Zbb extension, clang computes `std::countl_zero(x)` of a 64-bit word by spreading the
highest set bit down (`smear`) and counting the zero bits by the SWAR population count
(`swarClz`). `clz_eq`: for `x ≠ 0` this is `63 - log2 x`, the `clz_nonzero` of `Intx.Model`. The
smear of `x` is `2^(log2 x + 1) - 1` (by its bits); the count of the 64 such words is checked by
`decide`.
-/

namespace IntxRV

/-- The highest set bit of `x` spread down, as the compiler computes it. -/
def smear (x : BitVec 64) : BitVec 64 :=
  let s1 := x ||| x >>> 1
  let s2 := s1 ||| s1 >>> 2
  let s3 := s2 ||| s2 >>> 4
  let s4 := s3 ||| s3 >>> 8
  let s5 := s4 ||| s4 >>> 16
  s5 ||| s5 >>> 32

theorem getLsbD_or_shift (y : BitVec 64) (n i : Nat) :
    (y ||| y >>> n).getLsbD i = (y.getLsbD i || y.getLsbD (i + n)) := by
  simp [BitVec.getLsbD_ushiftRight, Nat.add_comm]

/-- A stage of the smear: the bit `i` is set if a bit of `x` within `2^k` above it is. -/
theorem stage (y x : BitVec 64) (k : Nat)
    (hy : ∀ i, y.getLsbD i = true ↔ ∃ d < 2 ^ k, x.getLsbD (i + d) = true) :
    ∀ i, (y ||| y >>> 2 ^ k).getLsbD i = true ↔ ∃ d < 2 ^ (k + 1), x.getLsbD (i + d) = true := by
  intro i
  rw [getLsbD_or_shift, Bool.or_eq_true, hy, hy]
  constructor
  · rintro (⟨d, hd, h⟩ | ⟨d, hd, h⟩)
    · exact ⟨d, by rw [pow_succ]; omega, h⟩
    · exact ⟨2 ^ k + d, by rw [pow_succ]; omega, by rwa [← Nat.add_assoc]⟩
  · rintro ⟨d, hd, h⟩
    by_cases hdk : d < 2 ^ k
    · exact .inl ⟨d, hdk, h⟩
    · refine .inr ⟨d - 2 ^ k, by rw [pow_succ] at hd; omega, ?_⟩
      rwa [Nat.add_assoc, Nat.add_sub_cancel' (by omega)]

theorem smear_getLsbD (x : BitVec 64) (i : Nat) :
    (smear x).getLsbD i = true ↔ ∃ d < 64, x.getLsbD (i + d) = true := by
  have h0 : ∀ i, x.getLsbD i = true ↔ ∃ d < 2 ^ 0, x.getLsbD (i + d) = true := by
    intro i; constructor
    · intro h; exact ⟨0, by decide, by simpa using h⟩
    · rintro ⟨d, hd, h⟩; obtain rfl : d = 0 := by simpa using hd
      simpa using h
  have h1 := stage _ _ _ h0
  have h2 := stage _ _ _ h1
  have h3 := stage _ _ _ h2
  have h4 := stage _ _ _ h3
  have h5 := stage _ _ _ h4
  have h6 := stage _ _ _ h5
  exact h6 i

/-- The smear of a nonzero word: the ones up to its top bit. -/
theorem smear_eq (x : BitVec 64) (hx : x ≠ 0) :
    smear x = BitVec.ofNat 64 (2 ^ (Nat.log2 x.toNat + 1) - 1) := by
  have hL : Nat.log2 x.toNat < 64 := by
    have := x.isLt
    exact (Nat.log2_lt (by
      intro h; apply hx; exact BitVec.eq_of_toNat_eq (by simpa using h))).mpr this
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [Bool.eq_iff_iff, smear_getLsbD, BitVec.getLsbD_ofNat]
  simp only [hi, decide_true, Bool.true_and, Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
  have hx0 : x.toNat ≠ 0 := fun h => hx (BitVec.eq_of_toNat_eq (by simpa using h))
  have htop : x.toNat.testBit (Nat.log2 x.toNat) = true := Nat.testBit_log2 hx0
  have habove : ∀ j, Nat.log2 x.toNat < j → x.toNat.testBit j = false := by
    intro j hj
    apply Nat.testBit_lt_two_pow
    calc x.toNat < 2 ^ (Nat.log2 x.toNat + 1) := Nat.lt_log2_self
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hj
  constructor
  · rintro ⟨d, hd, h⟩
    rw [BitVec.getLsbD] at h
    by_contra hc
    rw [habove (i + d) (by omega)] at h
    exact absurd h (by simp)
  · intro h
    refine ⟨Nat.log2 x.toNat - i, by omega, ?_⟩
    rw [BitVec.getLsbD, show i + (Nat.log2 x.toNat - i) = Nat.log2 x.toNat by omega]
    exact htop

/-- The population count of `~s` by the SWAR steps of the compiler. -/
def swarClz (s : BitVec 64) : BitVec 64 :=
  let n := ~~~s
  let a := n - ((n >>> 1) &&& 0x5555555555555555#64)
  let b := (a &&& 0x3333333333333333#64) + ((a >>> 2) &&& 0x3333333333333333#64)
  let c := (b + (b >>> 4)) &&& 0x0f0f0f0f0f0f0f0f#64
  (c * 0x0101010101010101#64) >>> 56

theorem swarClz_ones : ∀ L < 64,
    swarClz (BitVec.ofNat 64 (2 ^ (L + 1) - 1)) = BitVec.ofNat 64 (63 - L) := by
  decide

theorem clz_eq (x : BitVec 64) (hx : x ≠ 0) :
    swarClz (smear x) = BitVec.ofNat 64 (63 - Nat.log2 x.toNat) := by
  have hx0 : x.toNat ≠ 0 := fun h => hx (BitVec.eq_of_toNat_eq (by simpa using h))
  rw [smear_eq x hx, swarClz_ones _ ((Nat.log2_lt hx0).mpr x.isLt)]

end IntxRV
