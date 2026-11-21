import IntxRV.Loop
import Mathlib.Tactic
/-!
# The words of a division by a word

The numerator shifted left by `S < 64` to normalize the divisor, as the division by a word
computes it a word at a time: its digit `i` is the funnel shift of the words `i` and `i - 1`
(`norm_digit`), and the bits above its words are the top bits of its top word (`norm_top`).
`div_step` is one step of the division: the quotient words above `i` and the remainder, extended by
the quotient word and the remainder of the digit `i`.
-/

namespace IntxRV

/-- The word `k` of the buffer at `a`. -/
abbrev wordAt (m : Mem) (a : BitVec 64) (k : Nat) : Nat :=
  (memWord m (a + BitVec.ofNat 64 (8 * k)).toNat).toNat

/-- The words of a buffer split at the word `k`. -/
theorem words_split (m : Mem) : ∀ (k n : Nat) (a : BitVec 64),
    words m a (k + n) = words m a k + 2 ^ (64 * k) * words m (a + BitVec.ofNat 64 (8 * k)) n
  | 0, n, a => by simp [words]
  | k + 1, n, a => by
    rw [show k + 1 + n = (k + n) + 1 by omega, words, words_split m k n (a + 8), words]
    rw [show a + 8 + BitVec.ofNat 64 (8 * k) = a + BitVec.ofNat 64 (8 * (k + 1)) by
      rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega]
    rw [show 64 * (k + 1) = 64 + 64 * k by ring, pow_add]
    ring

theorem words_lt (m : Mem) : ∀ (n : Nat) (a : BitVec 64), words m a n < 2 ^ (64 * n)
  | 0, _ => by simp [words]
  | n + 1, a => by
    have := words_lt m n (a + 8)
    have := (memWord m a.toNat).isLt
    rw [words, show 64 * (n + 1) = 64 + 64 * n by ring, pow_add]
    nlinarith

/-- The words `k` and `k + 1` of a buffer of more than `k + 1` words. -/
theorem words_two (m : Mem) (a : BitVec 64) (k n : Nat) (h : k + 2 ≤ n) :
    ∃ R, words m (a + BitVec.ofNat 64 (8 * k)) (n - k) =
      wordAt m a k + 2 ^ 64 * (wordAt m a (k + 1) + 2 ^ 64 * R) := by
  obtain ⟨j, hj⟩ : ∃ j, n - k = j + 2 := ⟨n - k - 2, by omega⟩
  refine ⟨words m (a + BitVec.ofNat 64 (8 * k) + 8 + 8) j, ?_⟩
  rw [hj, words, words]
  simp only [wordAt]
  rw [show a + BitVec.ofNat 64 (8 * k) + 8 = a + BitVec.ofNat 64 (8 * (k + 1)) by
    rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega]

/-- The digit `i` of the numerator shifted left by `S < 64`: the funnel shift of its words `i` and
`i - 1`. -/
theorem norm_digit (m : Mem) (a : BitVec 64) (n S i : Nat) (hS : S < 64) (hi : 1 ≤ i)
    (hin : i < n) :
    words m a n * 2 ^ S / 2 ^ (64 * i) % 2 ^ 64 =
      (wordAt m a i * 2 ^ S + wordAt m a (i - 1) / 2 ^ (64 - S)) % 2 ^ 64 := by
  obtain ⟨R, hR⟩ := words_two m a (i - 1) n (by omega)
  rw [show i - 1 + 1 = i by omega] at hR
  have hsplit := words_split m (i - 1) (n - (i - 1)) a
  rw [show i - 1 + (n - (i - 1)) = n by omega, hR] at hsplit
  have hA := words_lt m (i - 1) a
  have hu0 := (memWord m (a + BitVec.ofNat 64 (8 * (i - 1))).toNat).isLt
  rw [hsplit]
  simp only [wordAt] at hR ⊢
  generalize words m a (i - 1) = A at *
  generalize (memWord m (a + BitVec.ofNat 64 (8 * (i - 1))).toNat).toNat = u0 at *
  generalize (memWord m (a + BitVec.ofNat 64 (8 * i)).toNat).toNat = u1 at *
  clear hR hsplit
  have hK : 0 < 2 ^ (64 * (i - 1)) := by positivity
  have h64i : 2 ^ (64 * i) = 2 ^ (64 * (i - 1)) * 2 ^ 64 := by rw [← pow_add]; congr 1; omega
  rw [h64i, ← Nat.div_div_eq_div_mul,
    show (A + 2 ^ (64 * (i - 1)) * (u0 + 2 ^ 64 * (u1 + 2 ^ 64 * R))) * 2 ^ S =
      A * 2 ^ S + 2 ^ (64 * (i - 1)) * ((u0 + 2 ^ 64 * (u1 + 2 ^ 64 * R)) * 2 ^ S) by ring,
    Nat.add_mul_div_left _ _ hK]
  have he : A * 2 ^ S / 2 ^ (64 * (i - 1)) < 2 ^ S := by
    apply Nat.div_lt_of_lt_mul
    calc A * 2 ^ S < 2 ^ (64 * (i - 1)) * 2 ^ S := Nat.mul_lt_mul_of_pos_right hA (by positivity)
      _ = _ := by ring
  generalize A * 2 ^ S / 2 ^ (64 * (i - 1)) = e at *
  have hPQ : 2 ^ S * 2 ^ (64 - S) = 2 ^ 64 := by rw [← pow_add]; congr 1; omega
  have hQ0 : 0 < 2 ^ (64 - S) := by positivity
  generalize 2 ^ S = P at *
  generalize 2 ^ (64 - S) = Q at *
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < Q ∧ u0 = Q * q + r :=
    ⟨u0 / Q, u0 % Q, Nat.mod_lt _ hQ0, (Nat.div_add_mod u0 Q).symm⟩
  rw [show (Q * q + r) / Q = q by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hQ0, Nat.div_eq_of_lt hr, Nat.zero_add]]
  have hbp : e + r * P < 2 ^ 64 := by
    have := Nat.mul_le_mul_right P (show r + 1 ≤ Q by omega)
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm Q P, hPQ] at this
    omega
  rw [show e + (Q * q + r + 2 ^ 64 * (u1 + 2 ^ 64 * R)) * P =
      (e + r * P) + 2 ^ 64 * (q + u1 * P + 2 ^ 64 * (R * P)) by rw [← hPQ]; ring,
    Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt hbp, Nat.zero_add]
  omega

/-- The bits of the numerator shifted left by `S < 64` above its words: the top bits of its top
word. -/
theorem norm_top (m : Mem) (a : BitVec 64) (n S : Nat) (hS : S < 64) (hn : 1 ≤ n) :
    words m a n * 2 ^ S / 2 ^ (64 * n) = wordAt m a (n - 1) / 2 ^ (64 - S) := by
  have hsplit := words_split m (n - 1) 1 a
  rw [show n - 1 + 1 = n by omega] at hsplit
  have hA := words_lt m (n - 1) a
  rw [hsplit]
  simp only [words, wordAt, Nat.mul_zero, Nat.add_zero]
  generalize words m a (n - 1) = A at *
  generalize (memWord m (a + BitVec.ofNat 64 (8 * (n - 1))).toNat).toNat = u at *
  have hK : 0 < 2 ^ (64 * (n - 1)) := by positivity
  have h64 : 2 ^ (64 * n) = 2 ^ (64 * (n - 1)) * 2 ^ 64 := by rw [← pow_add]; congr 1; omega
  rw [h64, ← Nat.div_div_eq_div_mul,
    show (A + 2 ^ (64 * (n - 1)) * u) * 2 ^ S = A * 2 ^ S + 2 ^ (64 * (n - 1)) * (u * 2 ^ S) by
      ring, Nat.add_mul_div_left _ _ hK]
  have he : A * 2 ^ S / 2 ^ (64 * (n - 1)) < 2 ^ S := by
    apply Nat.div_lt_of_lt_mul
    calc A * 2 ^ S < 2 ^ (64 * (n - 1)) * 2 ^ S := Nat.mul_lt_mul_of_pos_right hA (by positivity)
      _ = _ := by ring
  generalize A * 2 ^ S / 2 ^ (64 * (n - 1)) = e at *
  have hPQ : 2 ^ S * 2 ^ (64 - S) = 2 ^ 64 := by rw [← pow_add]; congr 1; omega
  have hQ0 : 0 < 2 ^ (64 - S) := by positivity
  generalize 2 ^ S = P at *
  generalize 2 ^ (64 - S) = Q at *
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < Q ∧ u = Q * q + r :=
    ⟨u / Q, u % Q, Nat.mod_lt _ hQ0, (Nat.div_add_mod u Q).symm⟩
  rw [show (Q * q + r) / Q = q by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hQ0, Nat.div_eq_of_lt hr, Nat.zero_add]]
  have hbp : e + r * P < 2 ^ 64 := by
    have := Nat.mul_le_mul_right P (show r + 1 ≤ Q by omega)
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm Q P, hPQ] at this
    omega
  rw [show e + (Q * q + r) * P = (e + r * P) + 2 ^ 64 * q by rw [← hPQ]; ring,
    Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt hbp, Nat.zero_add]

/-- One step of the division by a word: the quotient words above `i` and the remainder, with the
quotient word and the remainder of the digit `i`. -/
theorem div_step {Un D Qhi rem qi rem' : Nat} (i : Nat)
    (hq : Qhi * D + rem = Un / 2 ^ (64 * (i + 1)))
    (hqi : qi = (2 ^ 64 * rem + Un / 2 ^ (64 * i) % 2 ^ 64) / D)
    (hr : rem' = (2 ^ 64 * rem + Un / 2 ^ (64 * i) % 2 ^ 64) % D) :
    (qi + 2 ^ 64 * Qhi) * D + rem' = Un / 2 ^ (64 * i) := by
  have h1 : Un / 2 ^ (64 * (i + 1)) = Un / 2 ^ (64 * i) / 2 ^ 64 := by
    rw [Nat.div_div_eq_div_mul, ← pow_add]; congr 2
  have e1 := Nat.div_add_mod (Un / 2 ^ (64 * i)) (2 ^ 64)
  have e2 := Nat.div_add_mod (2 ^ 64 * rem + Un / 2 ^ (64 * i) % 2 ^ 64) D
  rw [← hqi, ← hr] at e2
  rw [← h1, ← hq] at e1
  linarith

end IntxRV
