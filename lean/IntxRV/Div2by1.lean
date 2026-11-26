import IntxRV.Div3by2
import IntxRV.Reciprocal
import Intx.Proofs.Div
/-!
# The division of two words by one and the reciprocal, inlined

`div2by1BV` is what the RV64 code of `udivrem_2by1()` computes where clang inlines it, as in
`udivrem_by1()`: the quotient approximation from the reciprocal, the branch between `q1` and
`q1 + 1` and the masks of the corrections. `div2by1BV_spec` gives the quotient and the remainder
through `Intx.div2by1N_spec`. `recip2BV` is the inlined `reciprocal_2by1()` from the table entry,
and `recip2BV_spec` its value through the model `Intx.Model.reciprocal`.
-/

set_option maxRecDepth 100000

namespace IntxRV

/-- The quotient and the remainder of `u1:u0` by the normalized `d` with its reciprocal `v`, as the
RV64 code of `udivrem_2by1()` inlined in `udivrem_by1()` computes them: the quotient
approximation, the selection of `q1` or `q1 + 1` by the branch on the remainder, and the masks of
the corrections. -/
def div2by1BV (u1 u0 d v : BitVec 64) : BitVec 64 × BitVec 64 :=
  let p0 := u1 * v
  let p1 := mulhu u1 v
  let q0 := p0 + u0
  let q1 := u1 + p1 + (if q0 < p0 then 1#64 else 0#64)
  let r := u0 - (q1 + 1#64) * d
  let q2 := if q0 < r then q1 else q1 + 1#64
  let r2 := ((0#64 - if q0 < r then 1#64 else 0#64) &&& d) + r
  let k := if r2 < d then 1#64 else 0#64
  (q2 + (k ^^^ 1#64), r2 - ((k + 18446744073709551615#64) &&& d))

theorem div2by1BV_spec (u1 u0 d v : BitVec 64) (hd : 2 ^ 63 ≤ d.toNat)
    (hu : u1.toNat < d.toNat) (hv : v.toNat = (2 ^ 128 - 1) / d.toNat - 2 ^ 64) :
    (div2by1BV u1 u0 d v).1.toNat = (2 ^ 64 * u1.toNat + u0.toNat) / d.toNat ∧
      (div2by1BV u1 u0 d v).2.toNat = (2 ^ 64 * u1.toNat + u0.toNat) % d.toNat := by
  have hdl := d.isLt
  have hu0 := u0.isLt
  have hq : 2 ^ 64 ≤ (2 ^ 128 - 1) / d.toNat :=
    (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hv1 : (2 ^ 64 + v.toNat) * d.toNat < 2 ^ 128 := by
    have := Nat.div_mul_le_self (2 ^ 128 - 1) d.toNat
    rw [show 2 ^ 64 + v.toNat = (2 ^ 128 - 1) / d.toNat by omega]
    omega
  have hv2 : 2 ^ 128 ≤ (2 ^ 64 + v.toNat + 1) * d.toNat := by
    have := Nat.lt_mul_div_succ (2 ^ 128 - 1) (show 0 < d.toNat by omega)
    rw [show 2 ^ 64 + v.toNat = (2 ^ 128 - 1) / d.toNat by omega, Nat.mul_comm]
    omega
  have hsim : ((div2by1BV u1 u0 d v).1.toNat, (div2by1BV u1 u0 d v).2.toNat) =
      Intx.div2by1N u0.toNat u1.toNat d.toNat v.toNat := by
    have hQl : v.toNat * u1.toNat + (2 ^ 64 * u1.toNat + u0.toNat) < 2 ^ 128 := by
      have : (2 ^ 64 + v.toNat) * u1.toNat + (2 ^ 64 + v.toNat) ≤ (2 ^ 64 + v.toNat) * d.toNat := by
        rw [← Nat.mul_add_one]; exact Nat.mul_le_mul_left _ hu
      nlinarith
    unfold div2by1BV Intx.div2by1N
    simp only []
    -- The words of the quotient approximation: 2^64 * q1 + q0 = v * u1 + 2^64 * u1 + u0.
    have hp : (u1 * v).toNat + 2 ^ 64 * (mulhu u1 v).toNat = v.toNat * u1.toNat := by
      rw [BitVec.toNat_mul, toNat_mulhu, Nat.mul_comm u1.toNat]; omega
    generalize u1 * v = p0 at hp ⊢
    generalize mulhu u1 v = p1 at hp ⊢
    have hq0 : (p0 + u0).toNat = (v.toNat * u1.toNat + (2 ^ 64 * u1.toNat + u0.toNat)) % 2 ^ 64 := by
      rw [BitVec.toNat_add]; omega
    have hq1 : (u1 + p1 + if p0 + u0 < p0 then 1#64 else 0#64).toNat =
        (v.toNat * u1.toNat + (2 ^ 64 * u1.toNat + u0.toNat)) / 2 ^ 64 := by
      have := p0.isLt
      have := p1.isLt
      rw [BitVec.toNat_add, BitVec.toNat_add, toNat_ite_lt, BitVec.toNat_add]
      split <;> omega
    generalize p0 + u0 = q0 at hq0 hq1 ⊢
    generalize (u1 + p1 + if q0 < p0 then 1#64 else 0#64) = q1 at hq1 ⊢
    clear hp
    rw [← hq0, ← hq1]
    have hqt : (q1.toNat + 1) % 2 ^ 64 = (q1 + 1#64).toNat := by rw [BitVec.toNat_add]; rfl
    rw [hqt]
    generalize q1 + 1#64 = qt at hqt ⊢
    rw [show (u0.toNat + 2 ^ 64 - qt.toNat * d.toNat % 2 ^ 64) % 2 ^ 64 = (u0 - qt * d).toNat by
      rw [BitVec.toNat_sub, BitVec.toNat_mul]; omega]
    generalize u0 - qt * d = r at ⊢
    have hr := r.isLt
    have hq0l := q0.isLt
    have hq1l := q1.isLt
    have hqtl := qt.isLt
    have hm1 : (18446744073709551615#64 &&& d) = d := by
      rw [show (18446744073709551615#64) = BitVec.allOnes 64 from rfl, BitVec.allOnes_and]
    by_cases hc : q0 < r
    · have hc' : q0.toNat < r.toNat := hc
      simp only [hc, hc', if_pos]
      rw [show (0#64 - 1#64) &&& d = d by rw [show 0#64 - 1#64 = BitVec.allOnes 64 from rfl,
        BitVec.allOnes_and]]
      by_cases hk : d + r < d
      · have hk' : (d.toNat + r.toNat) % 2 ^ 64 < d.toNat := by
          simpa only [BitVec.lt_def, BitVec.toNat_add] using hk
        rw [if_pos hk, show (1#64 ^^^ 1#64) = 0#64 from rfl,
          show (1#64 + 18446744073709551615#64) = 0#64 from rfl, BitVec.zero_and,
          BitVec.add_zero, BitVec.sub_zero, if_neg (by omega), Prod.mk.injEq, BitVec.toNat_add]
        omega
      · have hk' : ¬(d.toNat + r.toNat) % 2 ^ 64 < d.toNat := by
          simpa only [BitVec.lt_def, BitVec.toNat_add] using hk
        rw [if_neg hk, show (0#64 ^^^ 1#64) = 1#64 from rfl, BitVec.zero_add, hm1,
          show d + r - d = r by bv_omega, if_pos (by omega), Prod.mk.injEq, BitVec.toNat_add,
          BitVec.toNat_ofNat]
        omega
    · have hc' : ¬q0.toNat < r.toNat := hc
      simp only [hc, hc', if_neg, not_false_eq_true]
      rw [BitVec.sub_self, BitVec.zero_and, BitVec.zero_add]
      by_cases hk : r < d
      · have hk' : r.toNat < d.toNat := hk
        rw [if_pos hk, show (1#64 ^^^ 1#64) = 0#64 from rfl,
          show (1#64 + 18446744073709551615#64) = 0#64 from rfl, BitVec.zero_and,
          BitVec.add_zero, BitVec.sub_zero, if_neg (by omega)]
      · have hk' : ¬r.toNat < d.toNat := hk
        rw [if_neg hk, show (0#64 ^^^ 1#64) = 1#64 from rfl, BitVec.zero_add, hm1,
          if_pos (by omega), Prod.mk.injEq, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
        omega
  rw [Intx.div2by1N_spec u0.toNat u1.toNat d.toNat v.toNat hu0 hu hd hdl hv1 hv2,
    Prod.mk.injEq] at hsim
  exact hsim

/-- The reciprocal `(2^128 - 1) / d - 2^64` of the normalized `d` as the RV64 code of
`reciprocal_2by1()` inlined in `udivrem_by1()` computes it, from the table entry `L` (`v0 * v0`) and
`H` (`2^11 * v0 - 1`). -/
def recip2BV (d L H : BitVec 64) : BitVec 64 :=
  let d40 := d >>> 24 + 1#64
  let v1 := H - (d40 * L) >>> 40
  let d0 := d &&& 1#64
  let v2 := ((1152921504606846976#64 - v1 * d40) * v1) >>> 47 + v1 <<< 13
  let e := ((0#64 - d0) &&& v2 >>> 1) - v2 * (d >>> 1 + d0)
  let v3 := v2 <<< 31 + mulhu e v2 >>> 1
  v3 - (d + mulhu v3 d) - (if d ^^^ 18446744073709551615#64 < v3 * d then 1#64 else 0#64)

set_option maxHeartbeats 4000000 in
theorem recip2BV_spec (d L H : BitVec 64) (hd : 2 ^ 63 ≤ d.toNat)
    (hL : L.toNat = 523520 / (d.toNat / 2 ^ 55) * (523520 / (d.toNat / 2 ^ 55)))
    (hH : H.toNat = 2 ^ 11 * (523520 / (d.toNat / 2 ^ 55)) - 1) :
    (recip2BV d L H).toNat = (2 ^ 128 - 1) / d.toNat - 2 ^ 64 := by
  have hi : d.toNat / 2 ^ 55 - 256 < 256 := by have := d.isLt; omega
  obtain ⟨v, hv, hv1, hv2⟩ := Intx.Model.reciprocal_spec (.ofBitVec d) (by simpa using hd)
  simp only [Intx.Model.reciprocal, Intx.Model.reciprocal_approx, Intx.Model.require] at hv
  rw [show d.toNat / 2 ^ 55 = d.toNat / 2 ^ 55 - 256 + 256 by omega] at hL hH
  generalize hI : d.toNat / 2 ^ 55 - 256 = i at *
  obtain ⟨hv0a, hv0b, hsq, hsc⟩ := Intx.Model.reciprocal_table_entry i hi
  have hidx : UInt64.toNat (UInt64.ofBitVec d >>> 55 - 256) = i := by
    show (d >>> 55 - 256#64).toNat = i
    rw [← hI]; bv_omega
  have hreq : ({ toBitVec := d } : UInt64) &&& 9223372036854775808 ≠ 0 :=
    Intx.Model.and_top_ne_zero _ (by simpa using hd)
  simp only [hidx, Vector.getElem?_eq_getElem hi, hreq, dite_true, Option.bind_some,
    Option.pure_def, bind, Option.some.injEq, ne_eq, not_false_eq_true] at hv
  have hLm : L = Intx.Model.RECIPROCAL_TABLE[i].1.toUInt64.toBitVec := by
    apply BitVec.eq_of_toNat_eq
    show L.toNat = (Intx.Model.RECIPROCAL_TABLE[i].1.toUInt64).toNat
    rw [UInt32.toNat_toUInt64, hsq, hL]
  have hHm : H = Intx.Model.RECIPROCAL_TABLE[i].2.toUInt64.toBitVec := by
    apply BitVec.eq_of_toNat_eq
    show H.toNat = (Intx.Model.RECIPROCAL_TABLE[i].2.toUInt64).toNat
    rw [UInt32.toNat_toUInt64, hsc, hH]
  rw [hLm, hHm]
  generalize Intx.Model.RECIPROCAL_TABLE[i].1.toUInt64 = L' at *
  generalize Intx.Model.RECIPROCAL_TABLE[i].2.toUInt64 = H' at *
  have hv' := congrArg UInt64.toBitVec hv
  simp only [UInt64.toBitVec_sub, UInt64.toBitVec_add, UInt64.toBitVec_mul,
    UInt64.toBitVec_shiftRight, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_and,
    Intx.Model.U128.getElem_one, Intx.Model.U128.getElem_zero, umul_hi_toBitVec,
    umul_lo_toBitVec, apply_ite UInt64.toBitVec, UInt64.lt_iff_toBitVec_lt,
    UInt64.toBitVec_ofNat, BitVec.reduceMod, BitVec.ushiftRight_eq',
    BitVec.shiftLeft_eq', BitVec.reduceToNat] at hv'
  have hdv : (2 ^ 128 - 1) / d.toNat - 2 ^ 64 = v.toBitVec.toNat := by
    have hdl := d.isLt
    simp only [UInt64.toNat_ofBitVec] at hv1 hv2
    rw [Nat.div_eq_of_lt_le (k := 2 ^ 64 + v.toNat) (by omega) (by omega)]
    simp
  rw [hdv]
  refine congrArg BitVec.toNat ?_
  clear hv hdv hv1 hv2 hsq hsc hidx hreq hLm hHm hL hH
  unfold recip2BV
  simp only []
  generalize d >>> 24 + 1#64 = D at *
  rw [BitVec.mul_comm L'.toBitVec D] at hv'
  generalize H'.toBitVec - (D * L'.toBitVec) >>> 40 = v1 at *
  rw [BitVec.mul_comm v1 (1152921504606846976#64 - v1 * D), BitVec.add_comm (v1 <<< 13)] at hv'
  generalize ((1152921504606846976#64 - v1 * D) * v1) >>> 47 + v1 <<< 13 = v2 at *
  rw [BitVec.and_comm (v2 >>> 1), mulhu_comm v2] at hv'
  generalize ((0#64 - (d &&& 1#64) &&& v2 >>> 1) - v2 * (d >>> 1 + (d &&& 1#64))) = e at *
  rw [BitVec.add_comm (mulhu e v2 >>> 1)] at hv'
  generalize v2 <<< 31 + mulhu e v2 >>> 1 = v3 at *
  simp only [Api.add_lt_iff_not_lt] at hv'
  generalize (if d ^^^ 18446744073709551615#64 < v3 * d then 1#64 else 0#64) = c at *
  rw [← hv']
  ring

end IntxRV
