import IntxRV.Div3by2
import Intx.Proofs.Div
/-!
# The reciprocal of a two-word divisor

`recip3BV` is what the RV64 code of `reciprocal_3by2()` computes, as operations on the words, from
the table entry `L` (`v0 * v0`) and `H` (`2^11 * v0 - 1`) that it loads: `v2` of Algorithm 2 for
the top word, the Newton step against the whole divisor and the exact correction with the carries of
its sum. `recip3BV_spec` gives the reciprocal: `v2` is the one of the model
`Intx.Model.reciprocal_approx`, whose bounds `Intx.recip3_nat` takes.
-/

-- omega reduces the powers of 2 in the bounds.
set_option maxRecDepth 100000

namespace IntxRV

/-- The reciprocal of `d1:d0` as the RV64 code of `reciprocal_3by2()` computes it, from the table
entry `L`, `H` of `d1`. -/
def recip3BV (d0 d1 L H : BitVec 64) : BitVec 64 :=
  let v1 := H - ((d1 >>> 24 + 1#64) * L) >>> 40
  let v2 := ((1152921504606846976#64 - v1 * (d1 >>> 24 + 1#64)) * v1) >>> 47 + v1 <<< 13
  let s0 := d0 + d1
  let c1 := if s0 < d0 then 1#64 else 0#64
  let e := (((0 : BitVec 64) - (d1 &&& 1#64)) &&& v2 >>> 1) +
    (v2 * (d1 >>> 1 + (d1 &&& 1#64)) ^^^ 18446744073709551615#64)
  let e' := e - mulhu v2 d0 >>> 1
  let v3 := v2 <<< 31 + mulhu e' v2 >>> 1
  let p1lo := v3 * d1
  let p0lo := v3 * d0
  let p0hi := mulhu v3 d0
  let p1hi := mulhu v3 d1
  let c := if d0 ^^^ 18446744073709551615#64 < p0lo then 1#64 else 0#64
  let s1 := s0 + p1lo
  let c2 := if s1 < s0 then 1#64 else 0#64
  let s2 := s1 + p0hi
  let c3 := if s2 < s1 then 1#64 else 0#64
  let s3 := s2 + c
  let c4 := if s3 < s2 then 1#64 else 0#64
  v3 - c1 - (d1 + p1hi) - c2 - c3 - c4

/-- The carry of `(~~~a + 1) + b`, which `sltu` computes as `~~~a < b`: the carry of `b + a`. -/
theorem toNat_carry_not (a b : BitVec 64) :
    (if a ^^^ 18446744073709551615#64 < b then 1#64 else 0#64).toNat =
      (b.toNat + a.toNat) / 2 ^ 64 := by
  rw [show (18446744073709551615#64) = BitVec.allOnes 64 from rfl, BitVec.xor_allOnes,
    toNat_ite_lt, BitVec.toNat_not]
  have := a.isLt
  have := b.isLt
  split <;> omega

/-- The carry of `a + b`, which `sltu` computes as `a + b < a`. -/
theorem toNat_carry (a b : BitVec 64) :
    (if a + b < a then 1#64 else 0#64).toNat = (a.toNat + b.toNat) / 2 ^ 64 := by
  rw [toNat_ite_lt, BitVec.toNat_add]
  have := a.isLt
  have := b.isLt
  split <;> omega

set_option maxHeartbeats 4000000 in
theorem recip3BV_spec (d0 d1 L H : BitVec 64) (hd : 2 ^ 63 ≤ d1.toNat)
    (hL : L.toNat = 523520 / (d1.toNat / 2 ^ 55) * (523520 / (d1.toNat / 2 ^ 55)))
    (hH : H.toNat = 2 ^ 11 * (523520 / (d1.toNat / 2 ^ 55)) - 1) :
    (recip3BV d0 d1 L H).toNat = (2 ^ 192 - 1) / (d0.toNat + 2 ^ 64 * d1.toNat) - 2 ^ 64 := by
  have hd1l := d1.isLt
  have hd0l := d0.isLt
  -- v2 is the one of the model.
  obtain ⟨v2m, hv2m, h2a, h2b, h2c⟩ :=
    Intx.Model.reciprocal_approx_spec (.ofBitVec d1) (by simpa using hd)
  have hmax : d1.toNat = 2 ^ 64 - 1 → v2m.toNat = 2 ^ 33 - 1 := by
    intro h
    have : UInt64.ofBitVec d1 = 0xffffffffffffffff :=
      UInt64.toNat_inj.mp (by rw [UInt64.toNat_ofBitVec, h]; rfl)
    rw [this, Intx.Model.reciprocal_approx_max, Option.some.injEq] at hv2m
    rw [← hv2m]
    rfl
  simp only [Intx.Model.reciprocal_approx, Intx.Model.require] at hv2m
  have hi : d1.toNat / 2 ^ 55 - 256 < 256 := by omega
  obtain ⟨hv0a, hv0b, hsq, hsc⟩ := Intx.Model.reciprocal_table_entry _ hi
  have hidx : UInt64.toNat (UInt64.ofBitVec d1 >>> 55 - 256) = d1.toNat / 2 ^ 55 - 256 := by
    show (d1 >>> 55 - 256#64).toNat = _
    bv_omega
  have hreq : UInt64.ofBitVec d1 &&& 9223372036854775808 ≠ 0 :=
    Intx.Model.and_top_ne_zero _ (by simpa using hd)
  simp only [hidx, Vector.getElem?_eq_getElem hi, hreq, dite_true, Option.bind_some,
    Option.pure_def, bind, Option.some.injEq, ne_eq, not_false_eq_true] at hv2m
  rw [show d1.toNat / 2 ^ 55 - 256 + 256 = d1.toNat / 2 ^ 55 by omega] at hsq hsc hv0a hv0b
  have hLm : L = Intx.Model.RECIPROCAL_TABLE[d1.toNat / 2 ^ 55 - 256].1.toUInt64.toBitVec := by
    apply BitVec.eq_of_toNat_eq
    show L.toNat = (Intx.Model.RECIPROCAL_TABLE[d1.toNat / 2 ^ 55 - 256].1.toUInt64).toNat
    rw [UInt32.toNat_toUInt64, hsq, hL]
  have hHm : H = Intx.Model.RECIPROCAL_TABLE[d1.toNat / 2 ^ 55 - 256].2.toUInt64.toBitVec := by
    apply BitVec.eq_of_toNat_eq
    show H.toNat = (Intx.Model.RECIPROCAL_TABLE[d1.toNat / 2 ^ 55 - 256].2.toUInt64).toNat
    rw [UInt32.toNat_toUInt64, hsc, hH]
  have hv' := congrArg UInt64.toBitVec hv2m
  simp only [UInt64.toBitVec_sub, UInt64.toBitVec_add, UInt64.toBitVec_mul,
    UInt64.toBitVec_shiftRight, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_ofNat,
    BitVec.reduceMod, BitVec.ushiftRight_eq', BitVec.shiftLeft_eq', BitVec.reduceToNat] at hv'
  rw [← hLm, ← hHm, BitVec.mul_comm L (d1 >>> 24 + 1#64)] at hv'
  unfold recip3BV
  simp only []
  generalize H - ((d1 >>> 24 + 1#64) * L) >>> 40 = v1 at hv' ⊢
  rw [BitVec.mul_comm v1 (1152921504606846976#64 - v1 * (d1 >>> 24 + 1#64)),
    BitVec.add_comm (v1 <<< 13)] at hv'
  rw [hv']
  have h2b' : 2 ^ 97 < v2m.toBitVec.toNat * d1.toNat + 873 * 2 ^ 53 + d1.toNat + 2 ^ 24 := h2b
  have h2c' : v2m.toBitVec.toNat * d1.toNat + v2m.toBitVec.toNat < 2 ^ 97 := h2c
  have hmax' : d1.toNat = 2 ^ 64 - 1 → v2m.toBitVec.toNat = 2 ^ 33 - 1 := hmax
  generalize v2m.toBitVec = v2 at h2b' h2c' hmax' ⊢
  clear hv' hv2m h2a h2b h2c hmax hLm hHm hsq hsc hidx hreq hv0a hv0b hL hH hi
  have hV2 : v2.toNat < 2 ^ 34 := by
    by_contra h
    have : 2 ^ 34 * d1.toNat ≤ v2.toNat * d1.toNat := Nat.mul_le_mul_right _ (by omega)
    omega
  -- e = floor(e2 / 2) - 1 with e2 = 2^97 - v2 * d1: the mask of the odd d1 and the complement.
  have hmask : (((0 : BitVec 64) - (d1 &&& 1#64)) &&& v2 >>> 1).toNat =
      v2.toNat / 2 * (d1.toNat % 2) := by
    have hodd : (d1 &&& 1#64).toNat = d1.toNat % 2 := by
      rw [BitVec.toNat_and, show (1#64).toNat = 1 from rfl, Nat.and_one_is_mod]
    rcases Nat.mod_two_eq_zero_or_one d1.toNat with h | h
    · have : d1 &&& 1#64 = 0#64 := BitVec.eq_of_toNat_eq (by rw [hodd, h]; rfl)
      rw [this, h, show (0 : BitVec 64) - 0#64 = 0#64 from rfl, BitVec.zero_and]
      rfl
    · have : d1 &&& 1#64 = 1#64 := BitVec.eq_of_toNat_eq (by rw [hodd, h]; rfl)
      rw [this, h, BitVec.toNat_and, show ((0 : BitVec 64) - 1#64).toNat = 2 ^ 64 - 1 from rfl,
        Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ushiftRight,
        Nat.shiftRight_eq_div_pow]
      omega
  have hd63 : (d1 >>> 1 + (d1 &&& 1#64)).toNat = d1.toNat / 2 + d1.toNat % 2 := by
    rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_and,
      show (1#64).toNat = 1 from rfl, Nat.and_one_is_mod]
    omega
  have hXY : 2 * (v2.toNat * (d1.toNat / 2 + d1.toNat % 2)) =
      v2.toNat * d1.toNat + v2.toNat * (d1.toNat % 2) := by
    have : 2 * (d1.toNat / 2 + d1.toNat % 2) = d1.toNat + d1.toNat % 2 := by omega
    calc 2 * (v2.toNat * (d1.toNat / 2 + d1.toNat % 2)) =
        v2.toNat * (2 * (d1.toNat / 2 + d1.toNat % 2)) := by ring
      _ = _ := by rw [this, Nat.mul_add]
  obtain ⟨h3w, -, -⟩ := Intx.recip3_e3 v2.toNat d1.toNat d0.toNat h2c' h2b' hd hd1l hd0l
  have he : ((((0 : BitVec 64) - (d1 &&& 1#64)) &&& v2 >>> 1) +
      (v2 * (d1 >>> 1 + (d1 &&& 1#64)) ^^^ 18446744073709551615#64)).toNat =
      (2 ^ 97 - v2.toNat * d1.toNat) / 2 - 1 := by
    rw [show (18446744073709551615#64) = BitVec.allOnes 64 from rfl, BitVec.xor_allOnes,
      BitVec.toNat_add, BitVec.toNat_not, BitVec.toNat_mul, hmask, hd63]
    rcases Nat.mod_two_eq_zero_or_one d1.toNat with h | h <;> rw [h] at hXY ⊢ <;>
      simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero] at hXY ⊢ <;> omega
  generalize (((0 : BitVec 64) - (d1 &&& 1#64)) &&& v2 >>> 1) +
      (v2 * (d1 >>> 1 + (d1 &&& 1#64)) ^^^ 18446744073709551615#64) = e at he ⊢
  clear hmask hd63 hXY
  -- e' = e - floor(floor(v2 * d0 / 2^64) / 2), which does not wrap.
  have he' : (e - mulhu v2 d0 >>> 1).toNat =
      (2 ^ 97 - v2.toNat * d1.toNat) / 2 - 1 - v2.toNat * d0.toNat / 2 ^ 64 / 2 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ushiftRight, toNat_mulhu, Nat.shiftRight_eq_div_pow, he]
    omega
  generalize e - mulhu v2 d0 >>> 1 = e' at he' ⊢
  -- v3 = V3 mod 2^64.
  have hv3 : (v2 <<< 31 + mulhu e' v2 >>> 1).toNat =
      (2 ^ 31 * v2.toNat + v2.toNat * e'.toNat / 2 ^ 65) % 2 ^ 64 := by
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, toNat_mulhu,
      Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.mul_comm e'.toNat]
    omega
  generalize v2 <<< 31 + mulhu e' v2 >>> 1 = v3 at hv3 ⊢
  -- The correction: v3 - F, F = floor((2^64 + v3 + 1) * d / 2^128) = d1 + p1[1] + the carries
  -- of d0 + d1 + p1[0] + p0[1] + c.
  have hp1 : (v3 * d1).toNat + 2 ^ 64 * (mulhu v3 d1).toNat = v3.toNat * d1.toNat := by
    rw [BitVec.toNat_mul, toNat_mulhu]; omega
  have hp0 : (v3 * d0).toNat + 2 ^ 64 * (mulhu v3 d0).toNat = v3.toNat * d0.toNat := by
    rw [BitVec.toNat_mul, toNat_mulhu]; omega
  have hc := toNat_carry_not d0 (v3 * d0)
  generalize v3 * d1 = p1lo at hp1 hc ⊢
  generalize mulhu v3 d1 = p1hi at hp1 ⊢
  generalize v3 * d0 = p0lo at hp0 hc ⊢
  generalize mulhu v3 d0 = p0hi at hp0 ⊢
  generalize (if d0 ^^^ 18446744073709551615#64 < p0lo then 1#64 else 0#64) = c at hc ⊢
  -- The four carries add up to the high word of d0 + d1 + p1lo + p0hi + c.
  have hk1 := toNat_carry d0 d1
  have hk2 := toNat_carry (d0 + d1) p1lo
  have hk3 := toNat_carry (d0 + d1 + p1lo) p0hi
  have hk4 := toNat_carry (d0 + d1 + p1lo + p0hi) c
  have hs0 := BitVec.toNat_add d0 d1
  have hs1 := BitVec.toNat_add (d0 + d1) p1lo
  have hs2 := BitVec.toNat_add (d0 + d1 + p1lo) p0hi
  generalize (if d0 + d1 < d0 then 1#64 else 0#64) = k1 at hk1 ⊢
  generalize (if d0 + d1 + p1lo < d0 + d1 then 1#64 else 0#64) = k2 at hk2 ⊢
  generalize (if d0 + d1 + p1lo + p0hi < d0 + d1 + p1lo then 1#64 else 0#64) = k3 at hk3 ⊢
  generalize (if d0 + d1 + p1lo + p0hi + c < d0 + d1 + p1lo + p0hi then 1#64 else 0#64) = k4
    at hk4 ⊢
  rw [show v3 - k1 - (d1 + p1hi) - k2 - k3 - k4 = v3 - (d1 + p1hi + (k1 + k2 + k3 + k4)) by ring,
    BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add,
    BitVec.toNat_add]
  have hksum : k1.toNat + k2.toNat + k3.toNat + k4.toNat =
      (d0.toNat + d1.toNat + p1lo.toNat + p0hi.toNat + c.toNat) / 2 ^ 64 := by
    have h1 := p1lo.isLt
    have h2 := p0hi.isLt
    have h3 := c.isLt
    clear * - hk1 hk2 hk3 hk4 hs0 hs1 hs2 hd0l hd1l h1 h2 h3
    omega
  have hF : (2 ^ 64 + v3.toNat + 1) * (2 ^ 64 * d1.toNat + d0.toNat) / 2 ^ 128 =
      d1.toNat + p1hi.toNat +
        (d0.toNat + d1.toNat + p1lo.toNat + p0hi.toNat + c.toNat) / 2 ^ 64 := by
    have hexp : (2 ^ 64 + v3.toNat + 1) * (2 ^ 64 * d1.toNat + d0.toNat) = 2 ^ 128 * d1.toNat +
        2 ^ 64 * d0.toNat + 2 ^ 64 * (v3.toNat * d1.toNat) + 2 ^ 64 * d1.toNat +
        v3.toNat * d0.toNat + d0.toNat := by ring
    rw [hexp]
    have := p1lo.isLt
    have := p1hi.isLt
    have := p0lo.isLt
    have := p0hi.isLt
    clear * - hp1 hp0 hc this hd0l hd1l
    omega
  rw [show d0.toNat + 2 ^ 64 * d1.toNat = 2 ^ 64 * d1.toNat + d0.toNat by ring]
  have hpb : p1hi.toNat ≤ v3.toNat := by
    have hm := Nat.mul_le_mul_left v3.toNat (show d1.toNat ≤ 2 ^ 64 - 1 by omega)
    have hl := p1lo.isLt
    clear * - hp1 hm hl
    omega
  have hcl : c.toNat ≤ 1 := by
    have := p0lo.isLt
    clear * - hc this hd0l
    omega
  have hcb : (d0.toNat + d1.toNat + p1lo.toNat + p0hi.toNat + c.toNat) / 2 ^ 64 ≤ 3 := by
    have := p1lo.isLt
    have := p0hi.isLt
    clear * - hcl this hd0l hd1l
    omega
  have hv3l := v3.isLt
  have hval := (Intx.recip3_nat d1.toNat d0.toNat v2.toNat e'.toNat v3.toNat _ hd hd1l hd0l h2b'
    h2c' hmax' he' hv3 rfl)
  rw [hF] at hval
  have hk : k1.toNat + k2.toNat + k3.toNat + k4.toNat ≤ 3 := by
    clear * - hksum hcb
    omega
  have hp1h := p1hi.isLt
  -- The value: (2^64 + r) * d < 2^192 ≤ (2^64 + r + 1) * d determines r.
  obtain ⟨hv1, hv2⟩ := hval
  generalize hrd : (v3.toNat + 2 ^ 65 - (d1.toNat + p1hi.toNat +
    (d0.toNat + d1.toNat + p1lo.toNat + p0hi.toNat + c.toNat) / 2 ^ 64)) % 2 ^ 64 = r at hv1 hv2
  have hr : (2 ^ 192 - 1) / (2 ^ 64 * d1.toNat + d0.toNat) - 2 ^ 64 = r := by
    rw [Nat.div_eq_of_lt_le (k := 2 ^ 64 + r) (by clear * - hv1; omega)
      (by clear * - hv2; omega)]
    omega
  rw [hr, ← hrd, ← hksum]
  have := k1.isLt
  have := k2.isLt
  have := k3.isLt
  have := k4.isLt
  clear * - hk hpb hp1h hd1l hv3l this
  omega

end IntxRV
