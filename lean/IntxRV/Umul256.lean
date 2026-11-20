import IntxRV.Arith
/-!
# The 512-bit product of `uint256`

`umul()` of `uint<N>` adds the products of the words with `mac()`, `a + x * y + c` of words, whose
high word does not overflow: `(2^64 - 1) + (2^64 - 1)^2 + (2^64 - 1) = 2^128 - 1`. The RV64 code of
clang 21 for `uint256` adds the low words with `add` and their carries with `sltu`, and the high
words without carries. The carry word of the last `mac()` of a row, the high word of its product
plus the carries, is not a value of the code: clang adds its summands to the low word of a product
of the next row one at a time (`defn_carry3`).

`umul256_words` proves the product from the definitions of the values of the run, row by row: the
high word of each `mac()` is exact by the bound of its sum (`mac_hi_lt`). The last `mac()` of a row
adds the carry word of the row before, which is exact by the bound of that `mac()`.
-/

namespace IntxRV

/-- The carry of `a + b + d` that `sltu` computes against `a`, when `b + d` does not overflow: the
code adds the high word of a product `b` and a carry `d` to the low word `a` of another one. -/
theorem defn_carry3 {s' s c a b d : BitVec 64} (hs' : Defn s' (a + b)) (hs : Defn s (s' + d))
    (hc : Defn c (if s < a then 1#64 else 0#64)) (hb : b.toNat + d.toNat < 2 ^ 64) :
    s.toNat + 2 ^ 64 * c.toNat = a.toNat + (b.toNat + d.toNat) := by
  rw [hc.eq]
  have h : s.toNat = (a.toNat + b.toNat + d.toNat) % 2 ^ 64 := by
    rw [hs.eq, hs'.eq, BitVec.toNat_add, BitVec.toNat_add]; omega
  have := a.isLt
  split <;> rename_i hlt <;> simp only [BitVec.lt_def] at hlt <;> simp <;> omega

/-- The high word of `mac()`, `a + x * y + c` for the words `a` and `c`: the carries `c1` of the
low word of the product plus `a` and `c2` of that plus `c` added to the high word `ph` of the
product make a word. -/
theorem mac_hi_lt {p pl ph a c lo1 c1 lo2 c2 : Nat} (hp : pl + 2 ^ 64 * ph = p)
    (hpb : p ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) (ha : a < 2 ^ 64) (hc : c < 2 ^ 64)
    (h1 : lo1 + 2 ^ 64 * c1 = pl + a) (h2 : lo2 + 2 ^ 64 * c2 = lo1 + c) :
    c1 + ph + c2 < 2 ^ 64 := by
  omega

theorem bit_add_lt {c h : Nat} (hc : c ≤ 1) (hh : h ≤ 2 ^ 64 - 2) : c + h < 2 ^ 64 := by omega

theorem add_bit_lt {c h : Nat} (hh : h ≤ 2 ^ 64 - 2) (hc : c ≤ 1) : h + c < 2 ^ 64 := by omega

set_option maxHeartbeats 4000000 in
/-- The product of the words of the RV64 code of `umul()` of `uint256`, from the definitions of its
values (in the reverse order of the run, so that `apply` and `assumption` find them by the names
of the results): `lij`, `hij` the words of the product of `yi` and `xj`, `s` the sums and `c` the
carries, by the offsets of their instructions. -/
theorem umul256_words {x0 x1 x2 x3 y0 y1 y2 y3 l00 h00 l01 h01 l02 h02 l03 h03 l10 h10 l11 h11 l12
    h12 l13 h13 l20 h20 l21 h21 l22 h22 l23 h23 l30 h30 l31 h31 l32 h32 l33 h33 s0f4 s0f8 c0fc s100
    s104 c108 s10c s110 c114 s118 s11c c120 s124 s128 c12c s130 s134 c138 s13c s140 c144 s148 s14c
    c150 s154 c158 s160 s164 c168 s16c s170 c174 s17c s180 c184 s188 s18c c190 s1a8 s1ac c1b0 s1b4
    s1bc s1c0 c1c4 s1cc s1d0 c1d4 c1d8 s1dc s1e0 s1e8 c1ec s1f0 s1f4 s1f8 c1fc s200 c204 s208 s20c
    c210 s214 s218 s21c c220 c224 s228 s22c s230 c234 s238 : BitVec 64}
    (hs238 : Defn s238 (s22c + c234))
    (hc234 : Defn c234 (if s230 < s218 then 1#64 else 0#64))
    (hs230 : Defn s230 (s218 + s228))
    (hs22c : Defn s22c (c224 + h33))
    (hs228 : Defn s228 (s21c + c220))
    (hc224 : Defn c224 (if s218 < l33 then 1#64 else 0#64))
    (hc220 : Defn c220 (if s214 < s20c then 1#64 else 0#64))
    (hs21c : Defn s21c (c210 + h32))
    (hs218 : Defn s218 (s200 + c204))
    (hs214 : Defn s214 (s20c + s208))
    (hc210 : Defn c210 (if s20c < l32 then 1#64 else 0#64))
    (hs20c : Defn s20c (l32 + s1f4))
    (hs208 : Defn s208 (s1f8 + c1fc))
    (hc204 : Defn c204 (if s1f4 < s1b4 then 1#64 else 0#64))
    (hs200 : Defn s200 (l33 + s1e8))
    (hc1fc : Defn c1fc (if s1f0 < s1dc then 1#64 else 0#64))
    (hs1f8 : Defn s1f8 (c1ec + h31))
    (hs1f4 : Defn s1f4 (s1b4 + s1e0))
    (hs1f0 : Defn s1f0 (s1dc + s1bc))
    (hc1ec : Defn c1ec (if s1dc < l31 then 1#64 else 0#64))
    (hs1e8 : Defn s1e8 (c1d8 + h23))
    (hs1e0 : Defn s1e0 (s1cc + c1d4))
    (hs1dc : Defn s1dc (l31 + s1d0))
    (hc1d8 : Defn c1d8 (if s1b4 < l23 then 1#64 else 0#64))
    (hc1d4 : Defn c1d4 (if s1d0 < s1c0 then 1#64 else 0#64))
    (hs1d0 : Defn s1d0 (s1c0 + s188))
    (hs1cc : Defn s1cc (c1c4 + h22))
    (hc1c4 : Defn c1c4 (if s1c0 < l22 then 1#64 else 0#64))
    (hs1c0 : Defn s1c0 (l22 + s1ac))
    (hs1bc : Defn s1bc (c190 + h30))
    (hs1b4 : Defn s1b4 (s1a8 + c1b0))
    (hc1b0 : Defn c1b0 (if s1ac < s13c then 1#64 else 0#64))
    (hs1ac : Defn s1ac (s13c + s16c))
    (hs1a8 : Defn s1a8 (l23 + s160))
    (hc190 : Defn c190 (if s18c < l30 then 1#64 else 0#64))
    (hs18c : Defn s18c (l30 + s180))
    (hs188 : Defn s188 (s17c + c184))
    (hc184 : Defn c184 (if s180 < s170 then 1#64 else 0#64))
    (hs180 : Defn s180 (s170 + s154))
    (hs17c : Defn s17c (c174 + h21))
    (hc174 : Defn c174 (if s170 < l21 then 1#64 else 0#64))
    (hs170 : Defn s170 (l21 + s164))
    (hs16c : Defn s16c (s148 + c168))
    (hc168 : Defn c168 (if s164 < s140 then 1#64 else 0#64))
    (hs164 : Defn s164 (s140 + s130))
    (hs160 : Defn s160 (c158 + h13))
    (hc158 : Defn c158 (if s13c < l13 then 1#64 else 0#64))
    (hs154 : Defn s154 (c150 + h20))
    (hc150 : Defn c150 (if s14c < l20 then 1#64 else 0#64))
    (hs14c : Defn s14c (l20 + s128))
    (hs148 : Defn s148 (c144 + h12))
    (hc144 : Defn c144 (if s140 < l12 then 1#64 else 0#64))
    (hs140 : Defn s140 (l12 + s118))
    (hs13c : Defn s13c (s134 + c138))
    (hc138 : Defn c138 (if s118 < l03 then 1#64 else 0#64))
    (hs134 : Defn s134 (l13 + h03))
    (hs130 : Defn s130 (s124 + c12c))
    (hc12c : Defn c12c (if s128 < s11c then 1#64 else 0#64))
    (hs128 : Defn s128 (s11c + s10c))
    (hs124 : Defn s124 (c120 + h11))
    (hc120 : Defn c120 (if s11c < l11 then 1#64 else 0#64))
    (hs11c : Defn s11c (l11 + s100))
    (hs118 : Defn s118 (s110 + c114))
    (hc114 : Defn c114 (if s100 < l02 then 1#64 else 0#64))
    (hs110 : Defn s110 (l03 + h02))
    (hs10c : Defn s10c (c108 + h10))
    (hc108 : Defn c108 (if s104 < l10 then 1#64 else 0#64))
    (hs104 : Defn s104 (l10 + s0f4))
    (hs100 : Defn s100 (s0f8 + c0fc))
    (hc0fc : Defn c0fc (if s0f4 < l01 then 1#64 else 0#64))
    (hs0f8 : Defn s0f8 (l02 + h01))
    (hs0f4 : Defn s0f4 (l01 + h00))
    (hh33 : Defn h33 (mulhu y3 x3))
    (hl33 : Defn l33 (y3 * x3))
    (hh32 : Defn h32 (mulhu y3 x2))
    (hl32 : Defn l32 (y3 * x2))
    (hh31 : Defn h31 (mulhu y3 x1))
    (hl31 : Defn l31 (y3 * x1))
    (hh30 : Defn h30 (mulhu y3 x0))
    (hl30 : Defn l30 (y3 * x0))
    (hh23 : Defn h23 (mulhu y2 x3))
    (hl23 : Defn l23 (y2 * x3))
    (hh22 : Defn h22 (mulhu y2 x2))
    (hl22 : Defn l22 (y2 * x2))
    (hh21 : Defn h21 (mulhu y2 x1))
    (hl21 : Defn l21 (y2 * x1))
    (hh20 : Defn h20 (mulhu y2 x0))
    (hl20 : Defn l20 (y2 * x0))
    (hh13 : Defn h13 (mulhu y1 x3))
    (hl13 : Defn l13 (y1 * x3))
    (hh12 : Defn h12 (mulhu y1 x2))
    (hl12 : Defn l12 (y1 * x2))
    (hh11 : Defn h11 (mulhu y1 x1))
    (hl11 : Defn l11 (y1 * x1))
    (hh10 : Defn h10 (mulhu y1 x0))
    (hl10 : Defn l10 (y1 * x0))
    (hh03 : Defn h03 (mulhu y0 x3))
    (hl03 : Defn l03 (y0 * x3))
    (hh02 : Defn h02 (mulhu y0 x2))
    (hl02 : Defn l02 (y0 * x2))
    (hh01 : Defn h01 (mulhu y0 x1))
    (hl01 : Defn l01 (y0 * x1))
    (hh00 : Defn h00 (mulhu y0 x0))
    (hl00 : Defn l00 (y0 * x0)) :
    l00.toNat + 2 ^ 64 * (s104.toNat + 2 ^ 64 * (s14c.toNat + 2 ^ 64 * (s18c.toNat +
      2 ^ 64 * (s1f0.toNat + 2 ^ 64 * (s214.toNat + 2 ^ 64 * (s230.toNat +
      2 ^ 64 * s238.toNat)))))) =
    (x0.toNat + 2 ^ 64 * (x1.toNat + 2 ^ 64 * (x2.toNat + 2 ^ 64 * x3.toNat))) *
      (y0.toNat + 2 ^ 64 * (y1.toNat + 2 ^ 64 * (y2.toNat + 2 ^ 64 * y3.toNat))) := by
  -- The products of the words.
  have p00 := defn_mul_mulhu hl00 hh00
  have p01 := defn_mul_mulhu hl01 hh01
  have p02 := defn_mul_mulhu hl02 hh02
  have p03 := defn_mul_mulhu hl03 hh03
  have p10 := defn_mul_mulhu hl10 hh10
  have p11 := defn_mul_mulhu hl11 hh11
  have p12 := defn_mul_mulhu hl12 hh12
  have p13 := defn_mul_mulhu hl13 hh13
  have p20 := defn_mul_mulhu hl20 hh20
  have p21 := defn_mul_mulhu hl21 hh21
  have p22 := defn_mul_mulhu hl22 hh22
  have p23 := defn_mul_mulhu hl23 hh23
  have p30 := defn_mul_mulhu hl30 hh30
  have p31 := defn_mul_mulhu hl31 hh31
  have p32 := defn_mul_mulhu hl32 hh32
  have p33 := defn_mul_mulhu hl33 hh33
  -- Row 0: y0 times x, the carry word of each product added to the next.
  have f0fc := defn_carry_left hs0f4 hc0fc
  have f114 := defn_carry3 hs0f8 hs100 hc114 (add_bit_lt (defn_mulhu_le hh01) (defn_bit hc0fc))
  have f138 := defn_carry3 hs110 hs118 hc138 (add_bit_lt (defn_mulhu_le hh02) (defn_bit hc114))
  -- Row 1.
  have f108 := defn_carry_left hs104 hc108
  have e10c := defn_add_exact hs10c (bit_add_lt (defn_bit hc108) (defn_mulhu_le hh10))
  have f120 := defn_carry_left hs11c hc120
  have f12c := defn_carry_left hs128 hc12c
  have e124 := defn_add_exact hs124 (bit_add_lt (defn_bit hc120) (defn_mulhu_le hh11))
  have m11 := mac_hi_lt p11 (toNat_mul_le y1 x1) s100.isLt s10c.isLt f120 f12c
  have e130 := defn_add_exact hs130 (e124 ▸ m11)
  have f144 := defn_carry_left hs140 hc144
  have f168 := defn_carry_left hs164 hc168
  have e148 := defn_add_exact hs148 (bit_add_lt (defn_bit hc144) (defn_mulhu_le hh12))
  have m12 := mac_hi_lt p12 (toNat_mul_le y1 x2) s118.isLt s130.isLt f144 f168
  have e16c := defn_add_exact hs16c (e148 ▸ m12)
  have b03 := add_bit_lt (defn_mulhu_le hh03) (defn_bit hc138)
  have f158 := defn_carry3 hs134 hs13c hc158 b03
  have f1b0 := defn_carry_left hs1ac hc1b0
  have e160 := defn_add_exact hs160 (bit_add_lt (defn_bit hc158) (defn_mulhu_le hh13))
  have m13 := mac_hi_lt p13 (toNat_mul_le y1 x3) b03 s16c.isLt f158 f1b0
  -- Row 2.
  have f150 := defn_carry_left hs14c hc150
  have e154 := defn_add_exact hs154 (bit_add_lt (defn_bit hc150) (defn_mulhu_le hh20))
  have f174 := defn_carry_left hs170 hc174
  have f184 := defn_carry_left hs180 hc184
  have e17c := defn_add_exact hs17c (bit_add_lt (defn_bit hc174) (defn_mulhu_le hh21))
  have m21 := mac_hi_lt p21 (toNat_mul_le y2 x1) s164.isLt s154.isLt f174 f184
  have e188 := defn_add_exact hs188 (e17c ▸ m21)
  have f1c4 := defn_carry_left hs1c0 hc1c4
  have f1d4 := defn_carry_left hs1d0 hc1d4
  have e1cc := defn_add_exact hs1cc (bit_add_lt (defn_bit hc1c4) (defn_mulhu_le hh22))
  have m22 := mac_hi_lt p22 (toNat_mul_le y2 x2) s1ac.isLt s188.isLt f1c4 f1d4
  have e1e0 := defn_add_exact hs1e0 (e1cc ▸ m22)
  have b13 : s160.toNat + c1b0.toNat < 2 ^ 64 := e160 ▸ m13
  have f1d8 := defn_carry3 hs1a8 hs1b4 hc1d8 b13
  have f204 := defn_carry_left hs1f4 hc204
  have e1e8 := defn_add_exact hs1e8 (bit_add_lt (defn_bit hc1d8) (defn_mulhu_le hh23))
  have m23 := mac_hi_lt p23 (toNat_mul_le y2 x3) b13 s1e0.isLt f1d8 f204
  -- Row 3.
  have f190 := defn_carry_left hs18c hc190
  have e1bc := defn_add_exact hs1bc (bit_add_lt (defn_bit hc190) (defn_mulhu_le hh30))
  have f1ec := defn_carry_left hs1dc hc1ec
  have f1fc := defn_carry_left hs1f0 hc1fc
  have e1f8 := defn_add_exact hs1f8 (bit_add_lt (defn_bit hc1ec) (defn_mulhu_le hh31))
  have m31 := mac_hi_lt p31 (toNat_mul_le y3 x1) s1d0.isLt s1bc.isLt f1ec f1fc
  have e208 := defn_add_exact hs208 (e1f8 ▸ m31)
  have f210 := defn_carry_left hs20c hc210
  have f220 := defn_carry_left hs214 hc220
  have e21c := defn_add_exact hs21c (bit_add_lt (defn_bit hc210) (defn_mulhu_le hh32))
  have m32 := mac_hi_lt p32 (toNat_mul_le y3 x2) s1f4.isLt s208.isLt f210 f220
  have e228 := defn_add_exact hs228 (e21c ▸ m32)
  have b23 : s1e8.toNat + c204.toNat < 2 ^ 64 := e1e8 ▸ m23
  have f224 := defn_carry3 hs200 hs218 hc224 b23
  have f234 := defn_carry_left hs230 hc234
  have e22c := defn_add_exact hs22c (bit_add_lt (defn_bit hc224) (defn_mulhu_le hh33))
  have m33 := mac_hi_lt p33 (toNat_mul_le y3 x3) b23 s228.isLt f224 f234
  have e238 := defn_add_exact hs238 (e22c ▸ m33)
  rw [Nat.mul_comm, mul_words4]
  linarith only [p00, p01, p02, p03, p10, p11, p12, p13, p20, p21, p22, p23, p30, p31, p32, p33,
    f0fc, f114, f138, f108, e10c, f120, f12c, e124, e130, f144, f168, e148, e16c, f158, f1b0,
    e160, f150, e154, f174, f184, e17c, e188, f1c4, f1d4, e1cc, e1e0, f1d8, f204, e1e8, f190,
    e1bc, f1ec, f1fc, e1f8, e208, f210, f220, e21c, e228, f224, f234, e22c, e238]

end IntxRV
