import IntxRV.Umul256
/-!
# The product of `uint256` modulo `2^256`

`operator*` of `uint<N>` adds the rows `y[j] * x` of the product with `mac()` to the words below the
top one, and adds the low word of the last product of each row and its carry word to the top word,
modulo `2^64`. The RV64 code of clang 21 for `uint256` runs these loops, which `rv_exec_loop`
unrolls: their counters and pointers run to constant bounds. `mul256_words` proves the product from the
definitions of the values of the run: the three low words are exact, as the words of `umul()`
(`mac_hi_lt2` for the `mac()` that adds a word and a carry word), and the top word is the sum of
the carry words of the rows and the low words of the column 3 modulo `2^64`.
-/

namespace IntxRV

/-- The carry of `a + 0` that `sltu` computes as `a < a`. -/
theorem defn_lt_self {c a : BitVec 64} (h : Defn c (if a < a then 1#64 else 0#64)) :
    c.toNat = 0 := by
  rw [h.eq, if_neg (by simp)]; rfl

/-- The low word of a product, with the high word as a number. -/
theorem defn_mul_lo {lo a b : BitVec 64} (h : Defn lo (a * b)) :
    ∃ q, lo.toNat + 2 ^ 64 * q = a.toNat * b.toNat :=
  ⟨a.toNat * b.toNat / 2 ^ 64, by rw [defn_mul h]; exact Nat.mod_add_div _ _⟩

/-- The high word of `mac()` as `operator*` computes it: the sum `s` of the word `a` and the carry
word `c` first, then the low word of the product plus `s`. -/
theorem mac_hi_lt2 {p pl ph a c s c1 lo c2 : Nat} (hp : pl + 2 ^ 64 * ph = p)
    (hpb : p ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)) (ha : a < 2 ^ 64) (hc : c < 2 ^ 64)
    (h1 : s + 2 ^ 64 * c1 = a + c) (h2 : lo + 2 ^ 64 * c2 = pl + s) : ph + c1 + c2 < 2 ^ 64 := by
  omega

/-- The words of a product modulo `2^256`: three exact low words and the top word modulo `2^64`. -/
theorem words_mod_top {a b c T R : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hc : c < 2 ^ 64) :
    a + 2 ^ 64 * (b + 2 ^ 64 * (c + 2 ^ 64 * (T % 2 ^ 64))) =
      (a + 2 ^ 64 * (b + 2 ^ 64 * c) + 2 ^ 192 * T + 2 ^ 256 * R) % 2 ^ 256 := by
  omega

set_option maxHeartbeats 4000000 in
/-- The product modulo `2^256` of the words of the RV64 code of `operator*` of `uint256`, from the
definitions of its values (in the reverse order of the run, for `apply` and `assumption`): `lij`,
`hij` the words of the product of `xi` and `yj`, `sij` the word `i + j` after the row `j`, `a11`
the word plus the carry word, `c`, `d`, `e` the carries, `u` and `k` the carry words, and `t` the
sums of the top word. -/
theorem mul256_words {x0 x1 x2 x3 y0 y1 y2 y3 l00 c00 h00 k01 l10 h10 s10 c10 k02 l20 h20 s20 c20
    k03 l30 t03 l01 h01 d01 s01 e01 u01 k11 a11 d11 l11 h11 s11 e11 u11 k12 t13a l21 t13 l02 h02
    d02 s02 e02 u02 k22 t23a l12 t23 l03 t33 : BitVec 64}
    (ht33 : Defn t33 (t23 + l03))
    (hl03 : Defn l03 (x0 * y3))
    (ht23 : Defn t23 (t23a + l12))
    (hl12 : Defn l12 (x1 * y2))
    (ht23a : Defn t23a (k22 + t13))
    (hk22 : Defn k22 (u02 + e02))
    (hu02 : Defn u02 (h02 + d02))
    (he02 : Defn e02 (if s02 < l02 then 1#64 else 0#64))
    (hs02 : Defn s02 (l02 + s11))
    (hd02 : Defn d02 (if s11 < s11 then 1#64 else 0#64))
    (hh02 : Defn h02 (mulhu x0 y2))
    (hl02 : Defn l02 (x0 * y2))
    (ht13 : Defn t13 (t13a + l21))
    (hl21 : Defn l21 (x2 * y1))
    (ht13a : Defn t13a (k12 + t03))
    (hk12 : Defn k12 (u11 + e11))
    (hu11 : Defn u11 (h11 + d11))
    (he11 : Defn e11 (if s11 < l11 then 1#64 else 0#64))
    (hs11 : Defn s11 (l11 + a11))
    (hh11 : Defn h11 (mulhu x1 y1))
    (hl11 : Defn l11 (x1 * y1))
    (hd11 : Defn d11 (if a11 < s20 then 1#64 else 0#64))
    (ha11 : Defn a11 (s20 + k11))
    (hk11 : Defn k11 (u01 + e01))
    (hu01 : Defn u01 (h01 + d01))
    (he01 : Defn e01 (if s01 < l01 then 1#64 else 0#64))
    (hs01 : Defn s01 (l01 + s10))
    (hd01 : Defn d01 (if s10 < s10 then 1#64 else 0#64))
    (hh01 : Defn h01 (mulhu x0 y1))
    (hl01 : Defn l01 (x0 * y1))
    (ht03 : Defn t03 (k03 + l30))
    (hl30 : Defn l30 (x3 * y0))
    (hk03 : Defn k03 (h20 + c20))
    (hc20 : Defn c20 (if s20 < l20 then 1#64 else 0#64))
    (hs20 : Defn s20 (l20 + k02))
    (hh20 : Defn h20 (mulhu x2 y0))
    (hl20 : Defn l20 (x2 * y0))
    (hk02 : Defn k02 (h10 + c10))
    (hc10 : Defn c10 (if s10 < l10 then 1#64 else 0#64))
    (hs10 : Defn s10 (l10 + k01))
    (hh10 : Defn h10 (mulhu x1 y0))
    (hl10 : Defn l10 (x1 * y0))
    (hk01 : Defn k01 (h00 + c00))
    (hh00 : Defn h00 (mulhu x0 y0))
    (hc00 : Defn c00 (if l00 < l00 then 1#64 else 0#64))
    (hl00 : Defn l00 (x0 * y0)) :
    l00.toNat + 2 ^ 64 * (s01.toNat + 2 ^ 64 * (s02.toNat + 2 ^ 64 * t33.toNat)) =
    (x0.toNat + 2 ^ 64 * (x1.toNat + 2 ^ 64 * (x2.toNat + 2 ^ 64 * x3.toNat))) *
      (y0.toNat + 2 ^ 64 * (y1.toNat + 2 ^ 64 * (y2.toNat + 2 ^ 64 * y3.toNat))) % 2 ^ 256 := by
  -- The products of the words: whole in the columns 0 to 2, the low words in the column 3.
  have p00 := defn_mul_mulhu hl00 hh00
  have p10 := defn_mul_mulhu hl10 hh10
  have p20 := defn_mul_mulhu hl20 hh20
  have p01 := defn_mul_mulhu hl01 hh01
  have p11 := defn_mul_mulhu hl11 hh11
  have p02 := defn_mul_mulhu hl02 hh02
  obtain ⟨q30, p30⟩ := defn_mul_lo hl30
  obtain ⟨q21, p21⟩ := defn_mul_lo hl21
  obtain ⟨q12, p12⟩ := defn_mul_lo hl12
  obtain ⟨q03, p03⟩ := defn_mul_lo hl03
  -- The carries of the sums with the word 0.
  have z00 := defn_lt_self hc00
  have z01 := defn_lt_self hd01
  have z02 := defn_lt_self hd02
  -- Row 0.
  have ek01 := defn_add_exact hk01 (add_bit_lt (defn_mulhu_le hh00) (defn_bit hc00))
  have f10 := defn_carry_left hs10 hc10
  have ek02 := defn_add_exact hk02 (add_bit_lt (defn_mulhu_le hh10) (defn_bit hc10))
  have f20 := defn_carry_left hs20 hc20
  have ek03 := defn_add_exact hk03 (add_bit_lt (defn_mulhu_le hh20) (defn_bit hc20))
  -- Row 1.
  have f01 := defn_carry_left hs01 he01
  have eu01 := defn_add_exact hu01 (add_bit_lt (defn_mulhu_le hh01) (defn_bit hd01))
  have ek11 := defn_add_exact hk11
    (add_bit_lt (by rw [eu01, z01, Nat.add_zero]; exact defn_mulhu_le hh01) (defn_bit he01))
  have fa11 := defn_carry_left ha11 hd11
  have f11 := defn_carry_left hs11 he11
  have eu11 := defn_add_exact hu11 (add_bit_lt (defn_mulhu_le hh11) (defn_bit hd11))
  have m11 := mac_hi_lt2 p11 (toNat_mul_le x1 y1) s20.isLt k11.isLt fa11 f11
  have ek12 := defn_add_exact hk12 (eu11 ▸ m11)
  -- Row 2.
  have f02 := defn_carry_left hs02 he02
  have eu02 := defn_add_exact hu02 (add_bit_lt (defn_mulhu_le hh02) (defn_bit hd02))
  have ek22 := defn_add_exact hk22
    (add_bit_lt (by rw [eu02, z02, Nat.add_zero]; exact defn_mulhu_le hh02) (defn_bit he02))
  -- The top word: the sum of the carry words of the rows and the low words of the column 3.
  have hT : t33.toNat = (k03.toNat + l30.toNat + k12.toNat + l21.toNat + k22.toNat + l12.toNat +
      l03.toNat) % 2 ^ 64 := by
    rw [defn_add ht33, defn_add ht23, defn_add ht23a, defn_add ht13, defn_add ht13a, defn_add ht03]
    simp only [Nat.mod_add_mod, Nat.add_mod_mod]
    congr 1
    ring
  have hXY : (x0.toNat + 2 ^ 64 * (x1.toNat + 2 ^ 64 * (x2.toNat + 2 ^ 64 * x3.toNat))) *
      (y0.toNat + 2 ^ 64 * (y1.toNat + 2 ^ 64 * (y2.toNat + 2 ^ 64 * y3.toNat))) =
      l00.toNat + 2 ^ 64 * (s01.toNat + 2 ^ 64 * s02.toNat) +
      2 ^ 192 * (k03.toNat + l30.toNat + k12.toNat + l21.toNat + k22.toNat + l12.toNat +
        l03.toNat) +
      2 ^ 256 * (q30 + q21 + q12 + q03 + (x3.toNat * y1.toNat + x2.toNat * y2.toNat +
        x1.toNat * y3.toNat) + 2 ^ 64 * (x3.toNat * y2.toNat + x2.toNat * y3.toNat) +
        2 ^ 128 * (x3.toNat * y3.toNat)) := by
    rw [mul_words4]
    linarith only [p00, p10, p20, p01, p11, p02, p30, p21, p12, p03, z00, z01, z02, ek01, f10,
      ek02, f20, ek03, f01, eu01, ek11, fa11, f11, eu11, ek12, f02, eu02, ek22]
  rw [hT, hXY]
  exact words_mod_top l00.isLt s01.isLt s02.isLt

end IntxRV
