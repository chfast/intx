import Intx.ProofSupport.Basic
set_option warningAsError true
/-!
# Proofs: the word operations

What the word operations of `Intx.Model` compute, as numbers.
-/

namespace Intx.Model

/-- The number of a `uint128`. -/
def U128.toNat (a : U128) : Nat := a.lo.toNat + 2 ^ 64 * a.hi.toNat

@[simp] theorem U128.getElem_zero (p : U128) : p[0] = p.lo := rfl
@[simp] theorem U128.getElem_one (p : U128) : p[1] = p.hi := rfl

theorem U128.toNat_lt (a : U128) : a.toNat < 2 ^ 128 := by
  have := a.lo.toNat_lt
  have := a.hi.toNat_lt
  simp only [U128.toNat]
  omega

@[simp] theorem U128.toNat_ofWord (x : Word) : (U128.ofWord x).toNat = x.toNat := by
  simp [U128.ofWord, U128.toNat]

@[simp] theorem U128.toNat_mk (lo hi : Word) :
    (⟨lo, hi⟩ : U128).toNat = lo.toNat + 2 ^ 64 * hi.toNat := rfl

theorem toNat_ite_bool (c : Bool) : (if c then (1 : Word) else 0).toNat = c.toNat := by
  cases c <;> rfl

theorem addc_spec (x y : Word) (c : Bool) :
    (addc x y c).1.toNat + 2 ^ 64 * (addc x y c).2.toNat = x.toNat + y.toNat + c.toNat := by
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  unfold addc
  by_cases h1 : x + y < x <;> by_cases h2 : x + y + (if c then 1 else 0) < x + y <;>
    simp only [h1, h2, decide_true, decide_false, Bool.or_true, Bool.or_false,
      Bool.toNat_true, Bool.toNat_false] <;>
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at h1 h2 <;>
    rw [UInt64.toNat_add] at h2 ⊢ <;> rw [UInt64.toNat_add] <;> cases c <;> simp at h2 ⊢ <;> omega

theorem subc_spec (x y : Word) (c : Bool) :
    (subc x y c).1.toNat + y.toNat + c.toNat = x.toNat + 2 ^ 64 * (subc x y c).2.toNat := by
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  unfold subc
  by_cases h1 : x < y <;> by_cases h2 : x - y < (if c then 1 else 0) <;>
    simp only [h1, h2, decide_true, decide_false, Bool.or_true, Bool.or_false,
      Bool.toNat_true, Bool.toNat_false] <;>
    rw [UInt64.lt_iff_toNat_lt] at h1 h2 <;>
    rw [UInt64.toNat_sub] at h2 ⊢ <;> rw [UInt64.toNat_sub] <;> cases c <;> simp at h2 ⊢ <;> omega

theorem U128.toNat_add (a b : U128) : (a + b).toNat = (a.toNat + b.toNat) % 2 ^ 128 := by
  have h1 := addc_spec a.lo b.lo false
  have h2 := addc_spec a.hi b.hi (addc a.lo b.lo false).2
  have := (addc a.hi b.hi (addc a.lo b.lo false).2).1.toNat_lt
  have := (addc a.lo b.lo false).1.toNat_lt
  have : (addc a.hi b.hi (addc a.lo b.lo false).2).2.toNat ≤ 1 := Bool.toNat_le _
  show (U128.add a b).toNat = _
  simp only [U128.add, U128.toNat] at *
  simp only [Bool.toNat_false, Nat.add_zero] at h1
  omega

theorem U128.lt_eq (a b : U128) : U128.lt a b = decide (a.toNat < b.toNat) := by
  have := a.lo.toNat_lt
  have := b.lo.toNat_lt
  simp only [U128.lt, U128.toNat, U128.getElem_zero, U128.getElem_one, UInt64.lt_iff_toNat_lt,
    ← UInt64.toNat_inj]
  by_cases h1 : a.hi.toNat < b.hi.toNat <;> by_cases h2 : a.hi.toNat = b.hi.toNat <;>
    by_cases h3 : a.lo.toNat < b.lo.toNat <;> simp [h1, h2, h3] <;> omega

theorem toNat_and_low32 (x : Word) : (x &&& 0xffffffff).toNat = x.toNat % 2 ^ 32 := by
  rw [UInt64.toNat_and]
  have : (0xffffffff : Word).toNat = 2 ^ 32 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

theorem toNat_shr32 (x : Word) : (x >>> 32).toNat = x.toNat / 2 ^ 32 := by
  rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; rfl

/-- The portable `umul()` computes the 128-bit product. -/
theorem umul_spec (x y : Word) :
    (umul x y).lo.toNat + 2 ^ 64 * (umul x y).hi.toNat = x.toNat * y.toNat := by
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  -- The 32-bit halves.
  have hxa := toNat_and_low32 x
  have hxb := toNat_shr32 x
  have hya := toNat_and_low32 y
  have hyb := toNat_shr32 y
  generalize ha : x.toNat % 2 ^ 32 = a at hxa
  generalize hb : x.toNat / 2 ^ 32 = b at hxb
  generalize hc : y.toNat % 2 ^ 32 = c at hya
  generalize he : y.toNat / 2 ^ 32 = e at hyb
  have hx' : x.toNat = 2 ^ 32 * b + a := by rw [← ha, ← hb]; exact (Nat.div_add_mod _ _).symm
  have hy' : y.toNat = 2 ^ 32 * e + c := by rw [← hc, ← he]; exact (Nat.div_add_mod _ _).symm
  have ha' : a < 2 ^ 32 := by rw [← ha]; exact Nat.mod_lt _ (by positivity)
  have hc' : c < 2 ^ 32 := by rw [← hc]; exact Nat.mod_lt _ (by positivity)
  have hb' : b < 2 ^ 32 := by rw [← hb]; exact Nat.div_lt_of_lt_mul (by simpa using hx)
  have he' : e < 2 ^ 32 := by rw [← he]; exact Nat.div_lt_of_lt_mul (by simpa using hy)
  have hac : a * c ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have hbc : b * c ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have hae : a * e ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have hbe : b * e ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
  simp only [umul]
  -- The products and sums do not wrap.
  have ht0 : ((x &&& (0xffffffff : Word)) * (y &&& (0xffffffff : Word)) : Word).toNat = a * c := by
    rw [UInt64.toNat_mul, hxa, hya, Nat.mod_eq_of_lt (by omega)]
  have ht1 : ((x >>> (32 : Word)) * (y &&& (0xffffffff : Word)) : Word).toNat = b * c := by
    rw [UInt64.toNat_mul, hxb, hya, Nat.mod_eq_of_lt (by omega)]
  have ht2 : ((x &&& (0xffffffff : Word)) * (y >>> (32 : Word)) : Word).toNat = a * e := by
    rw [UInt64.toNat_mul, hxa, hyb, Nat.mod_eq_of_lt (by omega)]
  have ht3 : ((x >>> (32 : Word)) * (y >>> (32 : Word)) : Word).toNat = b * e := by
    rw [UInt64.toNat_mul, hxb, hyb, Nat.mod_eq_of_lt (by omega)]
  generalize ((x &&& (0xffffffff : Word)) * (y &&& (0xffffffff : Word)) : Word) = t0 at ht0 ⊢
  generalize ((x >>> (32 : Word)) * (y &&& (0xffffffff : Word)) : Word) = t1 at ht1 ⊢
  generalize ((x &&& (0xffffffff : Word)) * (y >>> (32 : Word)) : Word) = t2 at ht2 ⊢
  generalize ((x >>> (32 : Word)) * (y >>> (32 : Word)) : Word) = t3 at ht3 ⊢
  have hu1 : (t1 + (t0 >>> (32 : Word)) : Word).toNat = b * c + a * c / 2 ^ 32 := by
    rw [UInt64.toNat_add, toNat_shr32, ht1, ht0]
    have : a * c / 2 ^ 32 < 2 ^ 32 := Nat.div_lt_of_lt_mul (by omega)
    exact Nat.mod_eq_of_lt (by omega)
  generalize (t1 + (t0 >>> (32 : Word)) : Word) = u1 at hu1 ⊢
  have hu2 : (t2 + (u1 &&& (0xffffffff : Word)) : Word).toNat = a * e + (b * c + a * c / 2 ^ 32) % 2 ^ 32 := by
    rw [UInt64.toNat_add, toNat_and_low32, ht2, hu1]
    have : (b * c + a * c / 2 ^ 32) % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by positivity)
    exact Nat.mod_eq_of_lt (by omega)
  generalize (t2 + (u1 &&& (0xffffffff : Word)) : Word) = u2 at hu2 ⊢
  have hu1l : b * c + a * c / 2 ^ 32 < 2 ^ 64 := by
    have : a * c / 2 ^ 32 < 2 ^ 32 := Nat.div_lt_of_lt_mul (by omega)
    omega
  have hlo : (u2 <<< (32 : Word) ||| t0 &&& (0xffffffff : Word)).toNat =
      2 ^ 32 * (u2.toNat % 2 ^ 32) + a * c % 2 ^ 32 := by
    rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, toNat_and_low32, ht0, Nat.shiftLeft_eq]
    have e32 : (32 : Word).toNat % 64 = 32 := rfl
    rw [e32, show (2 : ℕ) ^ 64 = 2 ^ 32 * 2 ^ 32 by norm_num, Nat.mul_comm u2.toNat,
      Nat.mul_mod_mul_left]
    exact (Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt _ (by positivity)) _).symm
  have hhi : (t3 + u2 >>> (32 : Word) + u1 >>> (32 : Word)).toNat =
      b * e + u2.toNat / 2 ^ 32 + u1.toNat / 2 ^ 32 := by
    rw [UInt64.toNat_add, UInt64.toNat_add, toNat_shr32, toNat_shr32, ht3, hu2, hu1]
    have h1 : (a * e + (b * c + a * c / 2 ^ 32) % 2 ^ 32) / 2 ^ 32 < 2 ^ 32 := by
      have : (b * c + a * c / 2 ^ 32) % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by positivity)
      exact Nat.div_lt_of_lt_mul (by omega)
    have h2 : (b * c + a * c / 2 ^ 32) / 2 ^ 32 < 2 ^ 32 := Nat.div_lt_of_lt_mul (by omega)
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hR : (2 ^ 32 * b + a) * (2 ^ 32 * e + c) =
      2 ^ 64 * (b * e) + 2 ^ 32 * (b * c) + 2 ^ 32 * (a * e) + a * c := by ring
  rw [hlo, hhi, hu2, hu1, hx', hy', hR]
  omega

theorem umul_toNat (x y : Word) : (umul x y).toNat = x.toNat * y.toNat := umul_spec x y

/-- The sum of a product and two words fits in `uint128`. -/
theorem umul_add_add_toNat (x y a b : Word) :
    (umul x y + U128.ofWord a + U128.ofWord b).toNat = x.toNat * y.toNat + a.toNat + b.toNat := by
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have : x.toNat * y.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  rw [U128.toNat_add, U128.toNat_add, umul_toNat, U128.toNat_ofWord, U128.toNat_ofWord,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem umul_add_toNat (x y a : Word) :
    (umul x y + U128.ofWord a).toNat = x.toNat * y.toNat + a.toNat := by
  have h := umul_add_add_toNat x y a 0
  have : (U128.ofWord a + U128.ofWord 0) = U128.ofWord a + U128.ofWord 0 := rfl
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  have ha := a.toNat_lt
  have : x.toNat * y.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  rw [U128.toNat_add, umul_toNat, U128.toNat_ofWord, Nat.mod_eq_of_lt (by omega)]

theorem toNat_fshl (hi lo : Word) (s : Fin 64) :
    (fshl hi lo s).toNat = hi.toNat * 2 ^ s.val % 2 ^ 64 + lo.toNat / 2 ^ (64 - s.val) := by
  have hs := s.isLt
  have hl := lo.toNat_lt
  unfold fshl
  split_ifs with h0
  · subst h0
    simp [Nat.mod_eq_of_lt hi.toNat_lt, Nat.div_eq_of_lt hl]
  · have hs0 : s.val ≠ 0 := fun h => h0 (Fin.ext h)
    rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight]
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (show s.val < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show s.val < 64 by omega),
      Nat.mod_eq_of_lt (show 64 - s.val < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show 64 - s.val < 64 by omega)]
    have e : (2 : Nat) ^ 64 = 2 ^ s.val * 2 ^ (64 - s.val) := by rw [← pow_add]; congr 1; omega
    have hb : lo.toNat / 2 ^ (64 - s.val) < 2 ^ s.val := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show s.val + (64 - s.val) = 64 by omega]
      exact hl
    rw [e, Nat.mul_comm hi.toNat, Nat.mul_mod_mul_left, Nat.two_pow_add_eq_or_of_lt hb]

theorem toNat_fshr (hi lo : Word) (s : Fin 64) :
    (fshr hi lo s).toNat = lo.toNat / 2 ^ s.val + hi.toNat * 2 ^ (64 - s.val) % 2 ^ 64 := by
  have hs := s.isLt
  have hl := lo.toNat_lt
  unfold fshr
  split_ifs with h0
  · subst h0
    simp [Nat.mul_mod_left]
  · have hs0 : s.val ≠ 0 := fun h => h0 (Fin.ext h)
    rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight]
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (show s.val < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show s.val < 64 by omega),
      Nat.mod_eq_of_lt (show 64 - s.val < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show 64 - s.val < 64 by omega)]
    have e : (2 : Nat) ^ 64 = 2 ^ (64 - s.val) * 2 ^ s.val := by rw [← pow_add]; congr 1; omega
    have hb : lo.toNat / 2 ^ s.val < 2 ^ (64 - s.val) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show 64 - s.val + s.val = 64 by omega]
      exact hl
    rw [e, Nat.mul_comm hi.toNat, Nat.mul_mod_mul_left, Nat.add_comm,
      Nat.two_pow_add_eq_or_of_lt hb, Nat.lor_comm]

theorem clz_nonzero_spec (x : Word) (h : x ≠ 0) :
    ∃ s, clz_nonzero x = some s ∧ 2 ^ 63 ≤ x.toNat * 2 ^ s.val ∧ x.toNat * 2 ^ s.val < 2 ^ 64 := by
  have hx := x.toNat_lt
  have hx0 : x.toNat ≠ 0 := fun h0 => h (UInt64.toNat_inj.mp (by simpa using h0))
  have hL : Nat.log2 x.toNat < 64 := (Nat.log2_lt hx0).mpr hx
  have h1 := Nat.log2_self_le hx0
  have h2 : x.toNat < 2 ^ (Nat.log2 x.toNat + 1) := Nat.lt_log2_self
  refine ⟨⟨63 - Nat.log2 x.toNat, by omega⟩, by simp [clz_nonzero, h], ?_, ?_⟩
  · calc 2 ^ 63 = 2 ^ Nat.log2 x.toNat * 2 ^ (63 - Nat.log2 x.toNat) := by
          rw [← pow_add]; congr 1; omega
      _ ≤ x.toNat * 2 ^ (63 - Nat.log2 x.toNat) := Nat.mul_le_mul_right _ h1
  · calc x.toNat * 2 ^ (63 - Nat.log2 x.toNat)
        < 2 ^ (Nat.log2 x.toNat + 1) * 2 ^ (63 - Nat.log2 x.toNat) :=
          Nat.mul_lt_mul_of_pos_right h2 (by positivity)
      _ = 2 ^ 64 := by rw [← pow_add]; congr 1; omega

end Intx.Model
