import IntxRV.Words
import IntxRV.Reach
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
/-!
# Bytes in memory

`bytes m a k` are the `k` bytes at `a` in the memory `m`, of any alignment, `bigEndian` their
number in big-endian order: the values of the buffers of bytes of the specifications, as of
`be::load()` and `be::store()`, with `BufBytes` and the addresses of their words `bufBytes`
(`IntxRV/Words.lean`).

The code converts between the bytes and the words with shifts, masks and ors (byte swaps without
Zbb). `rv_bytes` proves that such a word is `beWord` of its bytes by comparing its 8 bytes
(`byteAt`): the lemmas move `byteAt` through the operations to the loaded bytes, much faster than
by its 64 bits.
-/

namespace IntxRV

/-- The `k` bytes at the address `a`. -/
def bytesAt (m : Mem) (a : Nat) : Nat → List (BitVec 8)
  | 0 => []
  | k + 1 => memByte m a :: bytesAt m (a + 1) k

/-- The `k` bytes at `a`. -/
def bytes (m : Mem) (a : BitVec 64) (k : Nat) : List (BitVec 8) := bytesAt m a.toNat k

/-- The number of the bytes in big-endian order: the first byte is the most significant. -/
def bigEndian (l : List (BitVec 8)) : Nat := l.foldl (fun v b => 256 * v + b.toNat) 0

/-- The word of up to 8 bytes in big-endian order: the first byte is the most significant. -/
def beWord (l : List (BitVec 8)) : BitVec 64 := l.foldl (fun v b => v <<< 8 ||| b.setWidth 64) 0#64

/-- The byte `k` of a word, the lowest byte 0. -/
def byteAt (v : BitVec 64) (k : Nat) : BitVec 8 := (v >>> (8 * k)).setWidth 8

theorem bytesAt_add (m : Mem) :
    ∀ (a n k : Nat), bytesAt m a (n + k) = bytesAt m a n ++ bytesAt m (a + n) k
  | a, 0, k => by simp [bytesAt]
  | a, n + 1, k => by
    rw [Nat.add_right_comm, bytesAt, bytesAt_add m (a + 1) n k, bytesAt, List.cons_append,
      Nat.add_assoc, Nat.add_comm 1 n]

theorem length_bytesAt (m : Mem) : ∀ (a k : Nat), (bytesAt m a k).length = k
  | _, 0 => rfl
  | a, k + 1 => by simp [bytesAt, length_bytesAt m (a + 1) k]

theorem foldl_bigEndian : ∀ (l : List (BitVec 8)) (v : Nat),
    l.foldl (fun v b => 256 * v + b.toNat) v =
      v * 256 ^ l.length + l.foldl (fun v b => 256 * v + b.toNat) 0
  | [], v => by simp
  | b :: l, v => by
    simp only [List.foldl_cons, List.length_cons]
    rw [foldl_bigEndian l (256 * v + b.toNat), foldl_bigEndian l (256 * 0 + b.toNat), Nat.pow_succ]
    ring

theorem bigEndian_foldl (l : List (BitVec 8)) (v : Nat) :
    l.foldl (fun v b => 256 * v + b.toNat) v = v * 256 ^ l.length + bigEndian l :=
  foldl_bigEndian l v

theorem bigEndian_append (l₁ l₂ : List (BitVec 8)) :
    bigEndian (l₁ ++ l₂) = bigEndian l₁ * 256 ^ l₂.length + bigEndian l₂ := by
  rw [bigEndian, List.foldl_append, bigEndian_foldl, ← bigEndian]

theorem bigEndian_lt : ∀ l : List (BitVec 8), bigEndian l < 256 ^ l.length
  | [] => by simp [bigEndian]
  | b :: l => by
    rw [show b :: l = [b] ++ l from rfl, bigEndian_append, List.length_append, Nat.pow_add]
    have h1 : bigEndian [b] < 256 := by simp [bigEndian]; exact b.isLt
    have h2 := bigEndian_lt l
    simp only [List.length_singleton, Nat.pow_one]
    nlinarith

theorem toNat_foldl_beWord : ∀ (l : List (BitVec 8)) (v : BitVec 64), l.length ≤ 8 →
    v.toNat < 256 ^ (8 - l.length) →
    (l.foldl (fun (v : BitVec 64) (b : BitVec 8) => v <<< 8 ||| b.setWidth 64) v).toNat =
      v.toNat * 256 ^ l.length + bigEndian l
  | [], v, _, _ => by simp [bigEndian]
  | b :: l, v, hl, hv => by
    simp only [List.foldl_cons, List.length_cons] at hl hv ⊢
    have hb := b.isLt
    have hp : 256 ^ (8 - l.length) = 256 ^ (8 - (l.length + 1)) * 256 := by
      rw [← Nat.pow_succ]; congr 1; omega
    have hp8 : 256 ^ (8 - l.length) ≤ 2 ^ 64 :=
      (Nat.pow_le_pow_right (by decide) (by omega : 8 - l.length ≤ 8)).trans (by decide)
    have e : (v <<< 8 ||| b.setWidth 64).toNat = v.toNat * 256 + b.toNat := by
      rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
        Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 64), Nat.shiftLeft_eq,
        Nat.mod_eq_of_lt (by omega : v.toNat * 2 ^ 8 < 2 ^ 64), ← Nat.shiftLeft_eq,
        ← Nat.shiftLeft_add_eq_or_of_lt (by omega : b.toNat < 2 ^ 8), Nat.shiftLeft_eq]
    rw [toNat_foldl_beWord l _ (by omega) (by rw [e]; omega), e]
    have hbl : bigEndian (b :: l) = b.toNat * 256 ^ l.length + bigEndian l := by
      rw [bigEndian, List.foldl_cons, bigEndian_foldl]; simp
    rw [hbl, Nat.pow_succ]
    ring

theorem toNat_beWord (l : List (BitVec 8)) (h : l.length ≤ 8) :
    (beWord l).toNat = bigEndian l := by
  rw [beWord, toNat_foldl_beWord l 0#64 h (by simp)]
  simp

theorem byteAt_or (x y : BitVec 64) (k : Nat) :
    byteAt (x ||| y) k = byteAt x k ||| byteAt y k := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  simp [byteAt, BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or]

theorem byteAt_and (x y : BitVec 64) (k : Nat) :
    byteAt (x &&& y) k = byteAt x k &&& byteAt y k := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  simp [byteAt, BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and]

theorem byteAt_shiftLeft (x : BitVec 64) (n k : Nat) (hn : n % 8 = 0) (hk : k < 8) :
    byteAt (x <<< n) k = if n / 8 ≤ k then byteAt x (k - n / 8) else 0#8 := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  split
  · simp only [byteAt, BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_shiftLeft]
    have h1 : 8 * k + i < 64 := by omega
    have h2 : ¬ 8 * k + i < n := by omega
    have h3 : 8 * k + i - n = 8 * (k - n / 8) + i := by omega
    simp [h1, h2, h3]
  · simp only [byteAt, BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_shiftLeft, BitVec.getElem_zero]
    have h2 : 8 * k + i < n := by omega
    simp [h2]

theorem byteAt_ushiftRight (x : BitVec 64) (n k : Nat) (hn : n % 8 = 0) :
    byteAt (x >>> n) k = if k + n / 8 < 8 then byteAt x (k + n / 8) else 0#8 := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  split
  · simp only [byteAt, BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight]
    have h3 : n + (8 * k + i) = 8 * (k + n / 8) + i := by omega
    rw [h3]
  · simp only [byteAt, BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getElem_zero]
    apply BitVec.getLsbD_of_ge
    omega

theorem byteAt_setWidth (b : BitVec 8) (k : Nat) (hk : k < 8) :
    byteAt (b.setWidth 64) k = if k = 0 then b else 0#8 := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  split
  · subst_vars; simp [byteAt]
  · simp only [byteAt, BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_setWidth, BitVec.getElem_zero]
    simp only [decide_eq_true_eq, Bool.and_eq_false_imp]
    intro h; apply BitVec.getLsbD_of_ge; omega

theorem byteAt_ofNat (c k : Nat) :
    byteAt (BitVec.ofNat 64 c) k = BitVec.ofNat 8 (c % 2 ^ 64 / 2 ^ (8 * k)) := by
  apply BitVec.eq_of_toNat_eq
  simp [byteAt, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem byteAt_memWord (m : Mem) (a k : Nat) (hk : k < 8) :
    byteAt (memWord m a) k = memByte m (a + k) := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  simp only [byteAt, memWord, memByte, BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight]
  interval_cases k <;> interval_cases i <;> simp only [BitVec.getLsbD_append] <;> simp

/-- `srliw` by n > 0: the 32-bit result has the top bit 0. -/
theorem srliw_eq (x : BitVec 64) (n : Nat) (hn : 0 < n) :
    (x.setWidth 32 >>> n).signExtend 64 = (x <<< 32) >>> (32 + n) := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  simp only [BitVec.getElem_signExtend, BitVec.getElem_ushiftRight, BitVec.getLsbD_shiftLeft,
    BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  have e : 32 + n + i - 32 = n + i := by omega
  by_cases h : i < 32
  · by_cases hc : n + i < 32 <;> simp [h, hc, e]
    · intro; omega
    · intro; omega
  · simp [h, show ¬ n + 31 < 32 by omega, show ¬ 32 + n + i < 64 by omega]

theorem and_ff (b : BitVec 8) : b &&& 255#8 = b := by
  rw [show (255#8 : BitVec 8) = BitVec.allOnes 8 from rfl, BitVec.and_allOnes]

open Sail LeanRV64D LeanRV64D.Functions LeanRV64D.Defs in
theorem shiftiwopVal_slliw (sh : BitVec 5) (a : BitVec 64) :
    shiftiwopVal .SLLIW sh a = (a.setWidth 32 <<< sh.toNat).signExtend 64 := by
  have ha : Sail.BitVec.extractLsb a 31 0 = a.setWidth 32 := BitVec.eq_of_toNat_eq rfl
  simp only [shiftiwopVal, ha, shift_bits_left, Sail.shift_bits_left]
  rfl

/-- The low byte of `lb`. -/
theorem byteAt_signExtend8 (b : BitVec 8) : byteAt (b.signExtend 64) 0 = b := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  simp [byteAt, BitVec.getElem_setWidth, BitVec.getLsbD_signExtend, hi, BitVec.getLsbD_eq_getElem]
  intro; omega

/-- The low 4 bytes of `slliw`. -/
theorem byteAt_slliw (z : BitVec 64) (n k : Nat) (hk : k < 4) :
    byteAt ((z.setWidth 32 <<< n).signExtend 64) k = byteAt ((z <<< (32 + n)) >>> 32) k := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  simp only [byteAt, BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_signExtend, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  have h1 : 8 * k + i < 32 := by omega
  by_cases h2 : 8 * k + i < n
  · simp [h1, h2, show 32 + (8 * k + i) < 32 + n by omega]
  · simp [h1, h2, show ¬ 32 + (8 * k + i) < 32 + n by omega,
      show 32 + (8 * k + i) - (32 + n) = 8 * k + i - n by omega]
    simp [show 8 * k + i < 64 by omega, show 8 * k + i - n < 32 by omega,
      show 32 + (8 * k + i) < 64 by omega]

/-- Two words with the same low 4 bytes have the same low 32 bits. -/
theorem setWidth32_eq_of_byteAt (x y : BitVec 64) (h : ∀ k < 4, byteAt x k = byteAt y k) :
    x.setWidth 32 = y.setWidth 32 := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  have := congrArg (fun b : BitVec 8 => b.getLsbD (i % 8)) (h (i / 8) (by omega))
  simp only [byteAt, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight] at this
  have e : 8 * (i / 8) + i % 8 = i := by omega
  simp only [e, show i % 8 < 8 by omega, decide_true, Bool.true_and] at this
  simpa [BitVec.getElem_setWidth] using this

/-- The or of a 32-bit value sign-extended and a value below `2^31` is sign-extended. -/
theorem signExtend_or (y : BitVec 32) (a : BitVec 64) (ha : a.toNat < 2 ^ 31) :
    y.signExtend 64 ||| a = ((y.signExtend 64 ||| a).setWidth 32).signExtend 64 := by
  have hb : ∀ i, 31 ≤ i → a.getLsbD i = false := fun i hi => by
    rw [BitVec.getLsbD]
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) hi))
  apply BitVec.eq_of_getElem_eq; intro i hi
  simp only [BitVec.getElem_or, BitVec.getElem_signExtend, BitVec.getElem_setWidth,
    BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_or, BitVec.getLsbD_signExtend,
    BitVec.getLsbD_setWidth]
  by_cases h : i < 32
  · simp [h, hi, BitVec.getLsbD_eq_getElem]
  · have hb' : ∀ j (hj : j < 64), 31 ≤ j → a[j] = false := fun j hj h31 => by
      rw [← BitVec.getLsbD_eq_getElem]; exact hb j h31
    simp [h, hb' i hi (by omega), hb' 31 (by omega) (by omega)]

/-- Two words with the same bytes are equal. -/
theorem eq_of_byteAt (x y : BitVec 64) (h : ∀ k < 8, byteAt x k = byteAt y k) : x = y := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  have := congrArg (fun b : BitVec 8 => b.getLsbD (i % 8)) (h (i / 8) (by omega))
  simp only [byteAt, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight] at this
  have e : 8 * (i / 8) + i % 8 = i := by omega
  simp only [e, show i % 8 < 8 by omega, decide_true, Bool.true_and] at this
  simpa [BitVec.getLsbD_eq_getElem, hi] using this

/-- The byte that `sb` stores of a shifted word. -/
theorem setWidth_ushiftRight_eq_byteAt (w : BitVec 64) (n : Nat) (hn : n % 8 = 0) :
    (w >>> n).setWidth 8 = byteAt w (n / 8) := by
  rw [byteAt, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hn)]

theorem setWidth_eq_byteAt (w : BitVec 64) : w.setWidth 8 = byteAt w 0 := by
  simp [byteAt]

theorem memByte_memStoreByte (m : Mem) (a b : Nat) (v : BitVec 8) :
    memByte (memStoreByte m a v) b = if a = b then v else memByte m b := by
  simp only [memByte, memStoreByte, Std.ExtHashMap.getD_insert, beq_iff_eq]

/-- A byte at an offset from `n` after a store of a byte at an offset from `n`. -/
theorem memByte_memStoreByte_add (m : Mem) (n i j : Nat) (v : BitVec 8) :
    memByte (memStoreByte m (n + i) v) (n + j) = if i = j then v else memByte m (n + j) := by
  rw [memByte_memStoreByte]; simp

theorem memByte_memStoreByte_add_zero (m : Mem) (n j : Nat) (v : BitVec 8) :
    memByte (memStoreByte m n v) (n + j) = if 0 = j then v else memByte m (n + j) := by
  rw [memByte_memStoreByte]; simp [eq_comm]

theorem memByte_memStoreByte_zero_add (m : Mem) (n i : Nat) (v : BitVec 8) :
    memByte (memStoreByte m (n + i) v) n = if i = 0 then v else memByte m n := by
  rw [memByte_memStoreByte]; simp

theorem memByte_memStoreByte_self (m : Mem) (n : Nat) (v : BitVec 8) :
    memByte (memStoreByte m n v) n = v := by
  rw [memByte_memStoreByte]; simp

/-- A word outside a stored byte. -/
theorem memWord_memStoreByte_of_ne (m : Mem) (a b : Nat) (v : BitVec 8) (h : a < b ∨ b + 8 ≤ a) :
    memWord (memStoreByte m a v) b = memWord m b := by
  simp only [memWord, memStoreByte, Std.ExtHashMap.getD_insert, beq_iff_eq]
  repeat rw [if_neg (by omega)]

theorem unchangedExcept_memStoreByte {m m' : Mem} {a : BitVec 64} {len : Nat} (b : Nat)
    (v : BitVec 8) (hb : a.toNat ≤ b ∧ b < a.toNat + len) :
    UnchangedExcept m (memStoreByte m' b v) a len ↔ UnchangedExcept m m' a len := by
  constructor <;> intro h k hk
  · have := h k hk
    rwa [memStoreByte, Std.ExtHashMap.getElem?_insert, if_neg (by simp; omega)] at this
  · rw [memStoreByte, Std.ExtHashMap.getElem?_insert, if_neg (by simp; omega)]; exact h k hk

theorem unchangedExcept2_memStoreByte {m m' : Mem} {a b : BitVec 64} {la lb : Nat} (c : Nat)
    (v : BitVec 8) (hc : a.toNat ≤ c ∧ c < a.toNat + la ∨ b.toNat ≤ c ∧ c < b.toNat + lb) :
    UnchangedExcept2 m (memStoreByte m' c v) a la b lb ↔ UnchangedExcept2 m m' a la b lb := by
  constructor <;> intro h k hka hkb
  · have := h k hka hkb
    rwa [memStoreByte, Std.ExtHashMap.getElem?_insert, if_neg (by simp; omega)] at this
  · rw [memStoreByte, Std.ExtHashMap.getElem?_insert, if_neg (by simp; omega)]; exact h k hka hkb

/-- The word of the bytes of a word in big-endian order is the word. -/
theorem beWord_byteAt (w : BitVec 64) :
    beWord [byteAt w 7, byteAt w 6, byteAt w 5, byteAt w 4, byteAt w 3, byteAt w 2, byteAt w 1,
      byteAt w 0] = w := by
  apply eq_of_byteAt; intro k hk
  simp only [beWord, List.foldl]
  interval_cases k <;>
    simp (config := { decide := true }) (disch := decide) only [byteAt_or, byteAt_shiftLeft,
      byteAt_setWidth, Nat.reduceDiv,
      Nat.reduceSub, ↓reduceIte, BitVec.or_zero, BitVec.zero_or]

theorem toNat_byteAt (w : BitVec 64) (k : Nat) :
    (byteAt w k).toNat = w.toNat / 2 ^ (8 * k) % 256 := by
  simp [byteAt, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- The low `k` bytes of a word in big-endian order: the word modulo `256^k`. -/
theorem bigEndian_byteAt_low (w : BitVec 64) : ∀ k,
    bigEndian ((List.range k).reverse.map (byteAt w)) = w.toNat % 256 ^ k
  | 0 => by simp [bigEndian, Nat.mod_one]
  | k + 1 => by
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.map_cons, show ∀ b l, b :: l = [b] ++ l from fun _ _ => rfl, bigEndian_append,
      bigEndian_byteAt_low w k, List.length_map, List.length_reverse, List.length_range]
    simp only [bigEndian, List.foldl_cons, List.foldl_nil, Nat.mul_zero, Nat.zero_add, toNat_byteAt]
    rw [show 2 ^ (8 * k) = 256 ^ k by rw [Nat.pow_mul], Nat.pow_succ, Nat.mod_mul]
    ring

theorem bigEndian_byteAt (w : BitVec 64) :
    bigEndian [byteAt w 7, byteAt w 6, byteAt w 5, byteAt w 4, byteAt w 3, byteAt w 2, byteAt w 1,
      byteAt w 0] = w.toNat := by
  rw [← toNat_beWord _ (by simp), beWord_byteAt]

/-- The 32 bytes at `n` in big-endian order as the 4 words of a `uint256`, the low word of the
last 8 bytes. -/
theorem bigEndian_bytesAt32 (m : Mem) (n : Nat) :
    bigEndian (bytesAt m n 32) =
      (beWord (bytesAt m (n + 24) 8)).toNat + 2 ^ 64 * ((beWord (bytesAt m (n + 16) 8)).toNat +
        2 ^ 64 * ((beWord (bytesAt m (n + 8) 8)).toNat +
          2 ^ 64 * (beWord (bytesAt m n 8)).toNat)) := by
  have hb : ∀ k, (beWord (bytesAt m k 8)).toNat = bigEndian (bytesAt m k 8) :=
    fun k => toNat_beWord _ (by rw [length_bytesAt])
  rw [show 32 = 8 + (8 + (8 + 8)) from rfl, bytesAt_add, bytesAt_add, bytesAt_add,
    bigEndian_append, bigEndian_append, bigEndian_append]
  simp only [length_bytesAt, List.length_append, hb, Nat.add_assoc, Nat.reduceAdd]
  ring

/-- The bytes of 4 words in big-endian order, the bytes of the top word first: the number of the
words. -/
theorem bigEndian_byteAt32 (w0 w1 w2 w3 : BitVec 64) :
    bigEndian [byteAt w3 7, byteAt w3 6, byteAt w3 5, byteAt w3 4, byteAt w3 3, byteAt w3 2,
      byteAt w3 1, byteAt w3 0, byteAt w2 7, byteAt w2 6, byteAt w2 5, byteAt w2 4, byteAt w2 3,
      byteAt w2 2, byteAt w2 1, byteAt w2 0, byteAt w1 7, byteAt w1 6, byteAt w1 5, byteAt w1 4,
      byteAt w1 3, byteAt w1 2, byteAt w1 1, byteAt w1 0, byteAt w0 7, byteAt w0 6, byteAt w0 5,
      byteAt w0 4, byteAt w0 3, byteAt w0 2, byteAt w0 1, byteAt w0 0] =
      w0.toNat + 2 ^ 64 * (w1.toNat + 2 ^ 64 * (w2.toNat + 2 ^ 64 * w3.toNat)) := by
  let wb := fun w : BitVec 64 => [byteAt w 7, byteAt w 6, byteAt w 5, byteAt w 4, byteAt w 3,
    byteAt w 2, byteAt w 1, byteAt w 0]
  have h := congrArg id (show bigEndian (wb w3 ++ (wb w2 ++ (wb w1 ++ wb w0))) =
      w0.toNat + 2 ^ 64 * (w1.toNat + 2 ^ 64 * (w2.toNat + 2 ^ 64 * w3.toNat)) by
    simp only [bigEndian_append, List.length_append, wb, List.length_cons, List.length_nil,
      bigEndian_byteAt]
    ring)
  simpa only [id, wb, List.cons_append, List.nil_append] using h

/-- The bytes of the low 160 bits of 3 words in big-endian order (`be::trunc()` to 20 bytes). -/
theorem bigEndian_byteAt20 (w0 w1 w2 : BitVec 64) :
    bigEndian [byteAt w2 3, byteAt w2 2, byteAt w2 1, byteAt w2 0, byteAt w1 7, byteAt w1 6,
      byteAt w1 5, byteAt w1 4, byteAt w1 3, byteAt w1 2, byteAt w1 1, byteAt w1 0, byteAt w0 7,
      byteAt w0 6, byteAt w0 5, byteAt w0 4, byteAt w0 3, byteAt w0 2, byteAt w0 1, byteAt w0 0] =
      w0.toNat + 2 ^ 64 * (w1.toNat + 2 ^ 64 * (w2.toNat % 2 ^ 32)) := by
  let wb := fun w : BitVec 64 => [byteAt w 7, byteAt w 6, byteAt w 5, byteAt w 4, byteAt w 3,
    byteAt w 2, byteAt w 1, byteAt w 0]
  have h4 : bigEndian [byteAt w2 3, byteAt w2 2, byteAt w2 1, byteAt w2 0] = w2.toNat % 2 ^ 32 := by
    simpa [List.range_succ] using bigEndian_byteAt_low w2 4
  have h := congrArg id (show bigEndian ([byteAt w2 3, byteAt w2 2, byteAt w2 1, byteAt w2 0] ++
      (wb w1 ++ wb w0)) = w0.toNat + 2 ^ 64 * (w1.toNat + 2 ^ 64 * (w2.toNat % 2 ^ 32)) by
    simp only [bigEndian_append, List.length_append, wb, List.length_cons, List.length_nil,
      bigEndian_byteAt, h4]
    ring)
  simpa only [id, wb, List.cons_append, List.nil_append] using h

/-- The number of 4 words from the equalities of the words, without `congr`, which would unfold
`beWord`. -/
theorem words4_congr {a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64} (h0 : a0 = b0) (h1 : a1 = b1)
    (h2 : a2 = b2) (h3 : a3 = b3) :
    a0.toNat + 2 ^ 64 * (a1.toNat + 2 ^ 64 * (a2.toNat + 2 ^ 64 * a3.toNat)) =
      b0.toNat + 2 ^ 64 * (b1.toNat + 2 ^ 64 * (b2.toNat + 2 ^ 64 * b3.toNat)) := by
  rw [h0, h1, h2, h3]

/-- An address at an offset in a buffer that does not wrap around, in `Nat`. -/
theorem toNat_add_ofNat (a : BitVec 64) (k : Nat) (h : a.toNat + k < 2 ^ 64) :
    (a + BitVec.ofNat 64 k).toNat = a.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
    Nat.mod_eq_of_lt h]

/-- An address in the stack frame of `n` bytes below sp, `a + c` with a negative offset `c`, in
`Nat` from the start of the frame: sp may be 0, with the frame at the end of the address space. -/
theorem toNat_add_frame (a c : BitVec 64) (n : Nat) (hc : 2 ^ 64 - n ≤ c.toNat) (hn : n < 2 ^ 64)
    (ha : (a - BitVec.ofNat 64 n).toNat + n ≤ 2 ^ 64) :
    (a + c).toNat = (a - BitVec.ofNat 64 n).toNat + (c.toNat + n - 2 ^ 64) := by
  have h1 := a.isLt; have h2 := c.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at ha ⊢
  rw [BitVec.toNat_add]
  by_cases h : n ≤ a.toNat
  · rw [Nat.mod_eq_sub_mod (by omega : 2 ^ 64 ≤ 2 ^ 64 - n + a.toNat),
      Nat.mod_eq_of_lt (by omega : 2 ^ 64 - n + a.toNat - 2 ^ 64 < 2 ^ 64),
      Nat.mod_eq_sub_mod (by omega : 2 ^ 64 ≤ a.toNat + c.toNat),
      Nat.mod_eq_of_lt (by omega : a.toNat + c.toNat - 2 ^ 64 < 2 ^ 64)]
    omega
  · rw [Nat.mod_eq_of_lt (by omega : 2 ^ 64 - n + a.toNat < 2 ^ 64)] at ha ⊢
    rw [Nat.mod_eq_of_lt (by omega : a.toNat + c.toNat < 2 ^ 64)]
    omega

open LeanRV64D.Defs in
/-- A run from the memory `m` by the facts `P` of it: the code after the stores of bytes runs on
a memory with the facts that the proof needs, not on the term of all the stores. -/
theorem Reach.of_mem {A : List (BitVec 64)} {prog : List instruction} {base pc tgt : BitVec 64}
    {x : Regs} {m : Mem} {Q : Regs → Mem → Prop} (P : Mem → Prop) (hm : P m)
    (h : ∀ m', P m' → Reach A prog base pc x m' tgt Q) : Reach A prog base pc x m tgt Q :=
  h m hm

/-- Moves `byteAt` through the operations of the code to the bytes: the bytes loaded or the
bytes of the loaded words. -/
macro "rv_bytes_simp" : tactic => `(tactic|
  simp (config := { decide := true }) (disch := decide) only [byteAt_or, byteAt_and,
    byteAt_shiftLeft, byteAt_ushiftRight, byteAt_setWidth, byteAt_ofNat, byteAt_memWord,
    byteAt_slliw, byteAt_signExtend8, srliw_eq, Nat.reduceDiv, Nat.reduceMod, Nat.reducePow,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, ↓reduceIte, BitVec.ofNat_eq_ofNat, and_ff,
    BitVec.and_zero, BitVec.zero_and, BitVec.or_zero, BitVec.zero_or, BitVec.reduceOfNat,
    Nat.add_zero])

/-- A word of the operations of the code on the bytes is the word of the bytes `beWord`: compares
the 8 bytes. -/
macro "rv_bytes" : tactic => `(tactic| (
  apply eq_of_byteAt; intro k hk
  simp only [beWord, List.foldl]
  interval_cases k <;> rv_bytes_simp))

end IntxRV
