import IntxRV.Arith
/-!
# The Knuth division

The steps of `internal::udivrem_knuth_normalized()`: the quotient digit of the partial remainder
`N` by the normalized divisor `d` from the estimate `qh` of the 3/2 division of the top words of
`N` by the top 2 words of `d` (`knuth_sub`, `knuth_est`), or `2^64 - 1` if the top words of the
remainder are those of `d` (`knuth_overflow`); the digit is the estimate if `N - qh * d` does not
borrow (`knuth_noborrow`), else one less, with `d` added back (`knuth_addback`). `knuth_digit`
is the invariant of the loop over the digits.
-/

namespace IntxRV

/-- One step of the Knuth division by the `n`-word `d = dhi * P + dlo` (`P = 2^(64 (n - 2))`), with
the estimate `qh` of the quotient digit of `N = Nt * P + Nlo` from the 3/2 division of the top
words `Nt = qh * dhi + rh`: the code subtracts `qh * dlo` from the low words (`L`, borrow `ov`)
and `ov` from `rh` (`T`, borrow `c`), so that `S = T * P + L` is `N - qh * d` modulo `2^(64 n)`. -/
theorem knuth_sub {N d dhi dlo Nt Nlo qh rh L ov T c P : Nat} (hd : d = dhi * P + dlo)
    (hN : N = Nt * P + Nlo) (h32 : Nt = qh * dhi + rh)
    (hL : L + qh * dlo = Nlo + ov * P) (hT : T + ov = rh + c * 2 ^ 128) :
    T * P + L + qh * d = N + c * (2 ^ 128 * P) := by
  subst hd hN h32
  have hTP : T * P + ov * P = rh * P + c * 2 ^ 128 * P := by rw [← add_mul, hT, add_mul]
  linarith

/-- The estimate is the quotient digit, or one more: `N - qh * d` is in `[-d, d)`. -/
theorem knuth_est {N d dhi dlo Nt Nlo qh rh P : Nat} (hd : d = dhi * P + dlo) (hdlo : dlo < P)
    (hP : 2 ^ 64 * P ≤ dhi * P) (hN : N = Nt * P + Nlo) (hNlo : Nlo < P)
    (h32 : Nt = qh * dhi + rh) (hrh : rh < dhi) (hqh : qh < 2 ^ 64) :
    N < qh * d + d ∧ qh * d ≤ N + d := by
  subst hd hN h32
  constructor
  · -- rh * P + Nlo < dhi * P ≤ d.
    have h1 : rh * P + Nlo < dhi * P := by
      have : (rh + 1) * P ≤ dhi * P := Nat.mul_le_mul_right _ hrh
      nlinarith
    nlinarith
  · -- qh * dlo < 2^64 * P ≤ dhi * P ≤ d.
    have h1 : qh * dlo ≤ 2 ^ 64 * P := by
      have := Nat.mul_le_mul (le_of_lt hqh) (le_of_lt hdlo)
      nlinarith
    nlinarith

/-- The division overflows (the top two words of the remainder `R` are the top two words `dhi` of
`d`): the quotient digit of `N = R * 2^64 + u` is `2^64 - 1`. -/
theorem knuth_overflow {N R u d dhi dlo P : Nat} (hd : d = dhi * P + dlo) (hdlo : dlo < P)
    (hdhi : 2 ^ 64 ≤ dhi) (hR : R < d) (hRt : dhi * P ≤ R) (hu : u < 2 ^ 64)
    (hN : N = R * 2 ^ 64 + u) :
    (2 ^ 64 - 1) * d ≤ N ∧ N < (2 ^ 64 - 1) * d + d := by
  subst hN hd
  have e1 : 2 ^ 64 * P ≤ dhi * P := Nat.mul_le_mul_right _ hdhi
  have e2 : (2 ^ 64 - 1) * dlo ≤ (2 ^ 64 - 1) * P := Nat.mul_le_mul_left _ hdlo.le
  norm_num at e2 ⊢
  constructor <;> nlinarith

/-- The invariant of the loop of the Knuth division: the quotient `Q` and the remainder `R` of the
top digits of `U` above the digit `j + 1`, and the next digit. -/
theorem knuth_digit {U d Q R q R' j : Nat} (h : Q * d + R = U / 2 ^ (64 * (j + 1)))
    (hq : q * d + R' = R * 2 ^ 64 + U / 2 ^ (64 * j) % 2 ^ 64) :
    (q + 2 ^ 64 * Q) * d + R' = U / 2 ^ (64 * j) := by
  have hdm := Nat.div_add_mod (U / 2 ^ (64 * j)) (2 ^ 64)
  rw [Nat.div_div_eq_div_mul, ← pow_add, show 64 * j + 64 = 64 * (j + 1) by ring, ← h] at hdm
  nlinarith

/-- The step without the borrow: the estimate `qh` is the quotient digit of `N` and `S` the
remainder. -/
theorem knuth_noborrow {N d S qh : Nat} (h : S + qh * d = N) (hest : N < qh * d + d) :
    qh = N / d ∧ S = N % d := by
  have hd : 0 < d := by omega
  have hS : S < d := by omega
  constructor
  · rw [← h, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt hS, Nat.zero_add]
  · rw [← h, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hS]

/-- The step with the borrow: `S` is `N - qh * d + K`, the words `S'` of `S + d` modulo `K` are the
remainder and `qh - 1` the quotient digit. -/
theorem knuth_addback {N d S S' qh K co : Nat} (hdK : d ≤ K) (hS' : S' < K)
    (h : S + qh * d = N + K) (hadd : S' + K * co = S + d) (hS : S < K) (hest : qh * d ≤ N + d) :
    qh - 1 = N / d ∧ S' = N % d := by
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · subst h0; omega
    · exact h0
  have hq : 1 ≤ qh := by
    rcases Nat.eq_zero_or_pos qh with h0 | h0
    · subst h0; omega
    · exact h0
  have hqd : (qh - 1) * d + d = qh * d := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hq]
  -- S' + K * co + (qh - 1) * d = N + K: co = 1 as N - (qh - 1) * d < K.
  have hco : co = 1 := by
    rcases Nat.lt_or_ge co 1 with h0 | h0
    · have : co = 0 := by omega
      subst this; nlinarith
    · rcases Nat.lt_or_ge co 2 with h1 | h1
      · omega
      · nlinarith
  subst hco
  have hr : S' + (qh - 1) * d = N := by nlinarith
  exact knuth_noborrow hr (by nlinarith)

/-- `u - s - b` and its borrow `u < u - s - b`, for `s + b < 2^64`: the subtraction of the high
word of a product and the borrow of the word before it. -/
theorem defn_sub2_borrow {d r c u s b : BitVec 64} (hd : Defn d (u - s)) (hr : Defn r (d - b))
    (hc : Defn c (if u < r then 1#64 else 0#64)) (hsb : s.toNat + b.toNat < 2 ^ 64) :
    r.toNat + s.toNat + b.toNat = u.toNat + 2 ^ 64 * c.toNat := by
  rw [hc.eq, hr.eq, hd.eq]
  have hu := u.isLt
  have h1 : (u - s - b).toNat = (u.toNat + (2 ^ 64 - s.toNat) + (2 ^ 64 - b.toNat)) % 2 ^ 64 := by
    rw [BitVec.toNat_sub, BitVec.toNat_sub]; omega
  split <;> rename_i h <;> simp only [BitVec.lt_def] at h <;> simp <;> omega

/-- A step of the Knuth division by 3 words `D = d0 + 2^64 * Dhi` in the words of the code: the
low word `s` of `N - qh * D` with the borrow `b1` (`hL`), the product `qh * d0` (`hm`), the
subtraction of its high word and of `b1` from the low word of the remainder `rh` (`hT1`) and of the
borrow `c1` of that from its high word (`hT`), with the borrow `c` out of `N - qh * D`. -/
theorem knuth3_words {Nt uj D d0 Dhi q s p ph b1 t h c1 rlo rhi c : Nat}
    (hD : D = d0 + 2 ^ 64 * Dhi) (hd0 : d0 < 2 ^ 64) (hDhi : 2 ^ 127 ≤ Dhi)
    (hq : q * Dhi + (rlo + 2 ^ 64 * rhi) = Nt) (hr : rlo + 2 ^ 64 * rhi < Dhi) (hqB : q < 2 ^ 64)
    (huj : uj < 2 ^ 64)
    (hL : s + p = uj + 2 ^ 64 * b1) (hm : p + 2 ^ 64 * ph = d0 * q)
    (hT1 : t + ph + b1 = rlo + 2 ^ 64 * c1) (hT : h + c1 = rhi + 2 ^ 64 * c) :
    s + 2 ^ 64 * (t + 2 ^ 64 * h) + q * D = Nt * 2 ^ 64 + uj + c * 2 ^ 192 ∧
      Nt * 2 ^ 64 + uj < q * D + D ∧ q * D ≤ Nt * 2 ^ 64 + uj + D := by
  have hsub := knuth_sub (N := Nt * 2 ^ 64 + uj) (Nlo := uj) (P := 2 ^ 64) (c := c)
    (dhi := Dhi) (dlo := d0) (hD.trans (by ring)) rfl hq.symm (L := s) (ov := ph + b1)
    (by rw [Nat.mul_comm q d0]; omega) (T := t + 2 ^ 64 * h) (by omega)
  have hest := knuth_est (N := Nt * 2 ^ 64 + uj) (Nlo := uj) (P := 2 ^ 64) (dhi := Dhi)
    (hD.trans (by ring)) hd0 (Nat.mul_le_mul_right _ (by omega)) rfl huj hq.symm hr hqB
  refine ⟨?_, hest⟩
  have e : c * (2 ^ 128 * 2 ^ 64) = c * 2 ^ 192 := by norm_num
  rw [e] at hsub
  linarith

/-- `knuth3_words` without the borrow: the estimate is the digit and `s:t:h` the remainder. -/
theorem knuth3_noborrow {Nt uj D d0 Dhi q s p ph b1 t h c1 rlo rhi : Nat}
    (hD : D = d0 + 2 ^ 64 * Dhi) (hd0 : d0 < 2 ^ 64) (hDhi : 2 ^ 127 ≤ Dhi)
    (hq : q * Dhi + (rlo + 2 ^ 64 * rhi) = Nt) (hr : rlo + 2 ^ 64 * rhi < Dhi) (hqB : q < 2 ^ 64)
    (huj : uj < 2 ^ 64)
    (hL : s + p = uj + 2 ^ 64 * b1) (hm : p + 2 ^ 64 * ph = d0 * q)
    (hT1 : t + ph + b1 = rlo + 2 ^ 64 * c1) (hT : h + c1 = rhi) :
    q * D + (s + 2 ^ 64 * (t + 2 ^ 64 * h)) = Nt * 2 ^ 64 + uj ∧
      s + 2 ^ 64 * (t + 2 ^ 64 * h) < D := by
  obtain ⟨h1, h2, -⟩ := knuth3_words (c := 0) hD hd0 hDhi hq hr hqB huj hL hm hT1 (by omega)
  omega

/-- `knuth3_words` with the borrow: `d` added back to `s:t:h` (the words `S'` and the carry `co`)
is the remainder and `q - 1` the digit. -/
theorem knuth3_addback {Nt uj D d0 Dhi q s p ph b1 t h c1 rlo rhi S' co : Nat}
    (hD : D = d0 + 2 ^ 64 * Dhi) (hd0 : d0 < 2 ^ 64) (hDhi : 2 ^ 127 ≤ Dhi)
    (hq : q * Dhi + (rlo + 2 ^ 64 * rhi) = Nt) (hr : rlo + 2 ^ 64 * rhi < Dhi) (hqB : q < 2 ^ 64)
    (huj : uj < 2 ^ 64) (hs : s < 2 ^ 64) (ht : t < 2 ^ 64) (hh : h < 2 ^ 64)
    (hL : s + p = uj + 2 ^ 64 * b1) (hm : p + 2 ^ 64 * ph = d0 * q)
    (hT1 : t + ph + b1 = rlo + 2 ^ 64 * c1) (hT : h + c1 = rhi + 2 ^ 64)
    (hDhi' : Dhi < 2 ^ 128) (hS' : S' < 2 ^ 192)
    (hadd : S' + 2 ^ 192 * co = s + 2 ^ 64 * (t + 2 ^ 64 * h) + D) :
    1 ≤ q ∧ (q - 1) * D + S' = Nt * 2 ^ 64 + uj ∧ S' < D := by
  obtain ⟨h1, -, h3⟩ := knuth3_words (c := 1) hD hd0 hDhi hq hr hqB huj hL hm hT1 (by omega)
  have hDK : D ≤ 2 ^ 192 := by omega
  have hSK : s + 2 ^ 64 * (t + 2 ^ 64 * h) < 2 ^ 192 := by
    have : t + 2 ^ 64 * h < 2 ^ 128 := by omega
    omega
  have h1' : s + 2 ^ 64 * (t + 2 ^ 64 * h) + q * D = Nt * 2 ^ 64 + uj + 2 ^ 192 := by
    rw [h1, Nat.one_mul]
  obtain ⟨hq1, hS1⟩ := knuth_addback (N := Nt * 2 ^ 64 + uj) (K := 2 ^ 192)
    (S := s + 2 ^ 64 * (t + 2 ^ 64 * h)) (qh := q) (d := D) hDK hS' h1' hadd hSK h3
  have hD0 : 0 < D := by omega
  have hq0 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · subst h0; omega
    · exact h0
  refine ⟨hq0, ?_, ?_⟩
  · rw [hq1, hS1]; exact Nat.div_add_mod' _ _
  · rw [hS1]; exact Nat.mod_lt _ hD0

/-- The high word of the product of 2 words by a word is at most 2^64 - 2. -/
theorem knuth4_hi_le {d0 d1 q lo0 hi0 lo1 hi1 p1 c k1 : Nat} (hd0 : d0 < 2 ^ 64)
    (hd1 : d1 < 2 ^ 64) (hq : q < 2 ^ 64) (hm0 : lo0 + 2 ^ 64 * hi0 = d0 * q)
    (hm1 : lo1 + 2 ^ 64 * hi1 = d1 * q) (hp : p1 + 2 ^ 64 * c = hi0 + lo1) (hk : k1 = hi1 + c) :
    k1 ≤ 2 ^ 64 - 2 := by
  have e : lo0 + 2 ^ 64 * p1 + 2 ^ 128 * k1 = (d0 + 2 ^ 64 * d1) * q := by
    rw [show (d0 + 2 ^ 64 * d1) * q = d0 * q + 2 ^ 64 * (d1 * q) by ring, ← hm0, ← hm1]
    subst hk; omega
  have hb : (d0 + 2 ^ 64 * d1) * q ≤ (2 ^ 128 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

/-- A step of the Knuth division by 4 words `D = d0 + 2^64 * d1 + 2^128 * Dhi` in the words of the
code: the low words `s0`, `s1` of `N - qh * D` with the borrows `b0`, `b1`, the products of `d0` and
`d1` by `qh` with the carry `c` of their middle words, and the subtraction of their high word `k1`
and of `b1` from the low word of the remainder `rh` (`hT1`) and of the borrow `c1` of that from its
high word (`hT`), with the borrow `c2` out of `N - qh * D`. -/
theorem knuth4_words {Nt u0 u1 D d0 d1 Dhi q s0 s1 lo0 hi0 lo1 hi1 p1 c k1 b0 b1 t h c1 rlo rhi
    c2 : Nat}
    (hD : D = d0 + 2 ^ 64 * d1 + 2 ^ 128 * Dhi) (hd0 : d0 < 2 ^ 64) (hd1 : d1 < 2 ^ 64)
    (hDhi : 2 ^ 127 ≤ Dhi) (hq : q * Dhi + (rlo + 2 ^ 64 * rhi) = Nt)
    (hr : rlo + 2 ^ 64 * rhi < Dhi) (hqB : q < 2 ^ 64) (hu0 : u0 < 2 ^ 64) (hu1 : u1 < 2 ^ 64)
    (hm0 : lo0 + 2 ^ 64 * hi0 = d0 * q) (hm1 : lo1 + 2 ^ 64 * hi1 = d1 * q)
    (hp : p1 + 2 ^ 64 * c = hi0 + lo1) (hk : k1 = hi1 + c)
    (hs0 : s0 + lo0 = u0 + 2 ^ 64 * b0) (hs1 : s1 + p1 + b0 = u1 + 2 ^ 64 * b1)
    (hT1 : t + k1 + b1 = rlo + 2 ^ 64 * c1) (hT : h + c1 = rhi + 2 ^ 64 * c2) :
    s0 + 2 ^ 64 * (s1 + 2 ^ 64 * (t + 2 ^ 64 * h)) + q * D =
        Nt * 2 ^ 128 + (u0 + 2 ^ 64 * u1) + c2 * 2 ^ 256 ∧
      Nt * 2 ^ 128 + (u0 + 2 ^ 64 * u1) < q * D + D ∧
      q * D ≤ Nt * 2 ^ 128 + (u0 + 2 ^ 64 * u1) + D := by
  have hL : (s0 + 2 ^ 64 * s1) + q * (d0 + 2 ^ 64 * d1) =
      (u0 + 2 ^ 64 * u1) + (k1 + b1) * 2 ^ 128 := by
    rw [show q * (d0 + 2 ^ 64 * d1) = d0 * q + 2 ^ 64 * (d1 * q) by ring, ← hm0, ← hm1]
    subst hk; omega
  have hsub := knuth_sub (N := Nt * 2 ^ 128 + (u0 + 2 ^ 64 * u1)) (Nlo := u0 + 2 ^ 64 * u1)
    (P := 2 ^ 128) (c := c2) (dhi := Dhi) (dlo := d0 + 2 ^ 64 * d1) (hD.trans (by ring)) rfl
    hq.symm (L := s0 + 2 ^ 64 * s1) (ov := k1 + b1) hL (T := t + 2 ^ 64 * h) (by omega)
  have hest := knuth_est (N := Nt * 2 ^ 128 + (u0 + 2 ^ 64 * u1)) (Nlo := u0 + 2 ^ 64 * u1)
    (P := 2 ^ 128) (dhi := Dhi) (dlo := d0 + 2 ^ 64 * d1) (hD.trans (by ring)) (by omega)
    (Nat.mul_le_mul_right _ (by omega)) rfl (by omega) hq.symm hr hqB
  refine ⟨?_, hest⟩
  have e : c2 * (2 ^ 128 * 2 ^ 128) = c2 * 2 ^ 256 := by norm_num
  rw [e] at hsub
  linarith

/-- `knuth4_words` without the borrow: the estimate is the digit and `s0:s1:t:h` the remainder. -/
theorem knuth4_noborrow {Nt u0 u1 D d0 d1 Dhi q s0 s1 lo0 hi0 lo1 hi1 p1 c k1 b0 b1 t h c1 rlo
    rhi : Nat}
    (hD : D = d0 + 2 ^ 64 * d1 + 2 ^ 128 * Dhi) (hd0 : d0 < 2 ^ 64) (hd1 : d1 < 2 ^ 64)
    (hDhi : 2 ^ 127 ≤ Dhi) (hq : q * Dhi + (rlo + 2 ^ 64 * rhi) = Nt)
    (hr : rlo + 2 ^ 64 * rhi < Dhi) (hqB : q < 2 ^ 64) (hu0 : u0 < 2 ^ 64) (hu1 : u1 < 2 ^ 64)
    (hm0 : lo0 + 2 ^ 64 * hi0 = d0 * q) (hm1 : lo1 + 2 ^ 64 * hi1 = d1 * q)
    (hp : p1 + 2 ^ 64 * c = hi0 + lo1) (hk : k1 = hi1 + c)
    (hs0 : s0 + lo0 = u0 + 2 ^ 64 * b0) (hs1 : s1 + p1 + b0 = u1 + 2 ^ 64 * b1)
    (hT1 : t + k1 + b1 = rlo + 2 ^ 64 * c1) (hT : h + c1 = rhi) :
    q * D + (s0 + 2 ^ 64 * (s1 + 2 ^ 64 * (t + 2 ^ 64 * h))) = Nt * 2 ^ 128 + (u0 + 2 ^ 64 * u1) ∧
      s0 + 2 ^ 64 * (s1 + 2 ^ 64 * (t + 2 ^ 64 * h)) < D := by
  obtain ⟨h1, h2, -⟩ := knuth4_words (c2 := 0) hD hd0 hd1 hDhi hq hr hqB hu0 hu1 hm0 hm1 hp hk hs0
    hs1 hT1 (by omega)
  omega

/-- `knuth4_words` with the borrow: `d` added back to `s0:s1:t:h` (the words `S'` and the carry
`co`) is the remainder and `q - 1` the digit. -/
theorem knuth4_addback {Nt u0 u1 D d0 d1 Dhi q s0 s1 lo0 hi0 lo1 hi1 p1 c k1 b0 b1 t h c1 rlo rhi
    S' co : Nat}
    (hD : D = d0 + 2 ^ 64 * d1 + 2 ^ 128 * Dhi) (hd0 : d0 < 2 ^ 64) (hd1 : d1 < 2 ^ 64)
    (hDhi : 2 ^ 127 ≤ Dhi) (hDhi' : Dhi < 2 ^ 128) (hq : q * Dhi + (rlo + 2 ^ 64 * rhi) = Nt)
    (hr : rlo + 2 ^ 64 * rhi < Dhi) (hqB : q < 2 ^ 64) (hu0 : u0 < 2 ^ 64) (hu1 : u1 < 2 ^ 64)
    (hs0' : s0 < 2 ^ 64) (hs1' : s1 < 2 ^ 64) (ht : t < 2 ^ 64) (hh : h < 2 ^ 64)
    (hm0 : lo0 + 2 ^ 64 * hi0 = d0 * q) (hm1 : lo1 + 2 ^ 64 * hi1 = d1 * q)
    (hp : p1 + 2 ^ 64 * c = hi0 + lo1) (hk : k1 = hi1 + c)
    (hs0 : s0 + lo0 = u0 + 2 ^ 64 * b0) (hs1 : s1 + p1 + b0 = u1 + 2 ^ 64 * b1)
    (hT1 : t + k1 + b1 = rlo + 2 ^ 64 * c1) (hT : h + c1 = rhi + 2 ^ 64)
    (hS' : S' < 2 ^ 256) (hadd : S' + 2 ^ 256 * co = s0 + 2 ^ 64 * (s1 + 2 ^ 64 * (t + 2 ^ 64 * h)) + D) :
    1 ≤ q ∧ (q - 1) * D + S' = Nt * 2 ^ 128 + (u0 + 2 ^ 64 * u1) ∧ S' < D := by
  obtain ⟨h1, -, h3⟩ := knuth4_words (c2 := 1) hD hd0 hd1 hDhi hq hr hqB hu0 hu1 hm0 hm1 hp hk hs0
    hs1 hT1 (by omega)
  have hDK : D ≤ 2 ^ 256 := by omega
  have hSK : s0 + 2 ^ 64 * (s1 + 2 ^ 64 * (t + 2 ^ 64 * h)) < 2 ^ 256 := by
    have : t + 2 ^ 64 * h < 2 ^ 128 := by omega
    have : s1 + 2 ^ 64 * (t + 2 ^ 64 * h) < 2 ^ 192 := by omega
    omega
  have h1' : s0 + 2 ^ 64 * (s1 + 2 ^ 64 * (t + 2 ^ 64 * h)) + q * D =
      Nt * 2 ^ 128 + (u0 + 2 ^ 64 * u1) + 2 ^ 256 := by rw [h1, Nat.one_mul]
  obtain ⟨hq1, hS1⟩ := knuth_addback (N := Nt * 2 ^ 128 + (u0 + 2 ^ 64 * u1)) (K := 2 ^ 256)
    (S := s0 + 2 ^ 64 * (s1 + 2 ^ 64 * (t + 2 ^ 64 * h))) (qh := q) (d := D) hDK hS' h1' hadd hSK h3
  have hD0 : 0 < D := by omega
  have hq0 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · subst h0; omega
    · exact h0
  refine ⟨hq0, ?_, ?_⟩
  · rw [hq1, hS1]; exact Nat.div_add_mod' _ _
  · rw [hS1]; exact Nat.mod_lt _ hD0

end IntxRV
