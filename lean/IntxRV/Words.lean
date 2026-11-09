import IntxRV.RunM
/-!
# Numbers in memory

`words m a k` is the number that the `k` 64-bit words at `a` in the memory `m` store,
little-endian: the value of a `uint<64 k>` at `a`. `bufWords a k` are the addresses of these
words. The lemmas evaluate `memWord` after `memStore`.
-/

namespace IntxRV

/-- The number of the `k` words at `a` in `m`, the lowest word first. -/
def words (m : Mem) (a : BitVec 64) : Nat → Nat
  | 0 => 0
  | k + 1 => (memWord m a.toNat).toNat + 2 ^ 64 * words m (a + 8) k

/-- The addresses of the `k` words at `a`. -/
def bufWords (a : BitVec 64) : Nat → List (BitVec 64)
  | 0 => []
  | k + 1 => a :: bufWords (a + 8) k

theorem getElem?_memStore_of_ne (m : Mem) (a : Nat) (v : BitVec 64) (k : Nat)
    (h : k < a ∨ a + 8 ≤ k) : (memStore m a v)[k]? = m[k]? := by
  simp only [memStore, Std.ExtHashMap.getElem?_insert, beq_iff_eq]
  repeat rw [if_neg (by omega)]

theorem getD_memStore_of_ne (m : Mem) (a : Nat) (v : BitVec 64) (k : Nat)
    (h : k < a ∨ a + 8 ≤ k) : (memStore m a v).getD k 0 = m.getD k 0 := by
  simp only [Std.ExtHashMap.getD_eq_getD_getElem?, getElem?_memStore_of_ne m a v k h]

theorem memWord_memStore_of_ne (m : Mem) (a b : Nat) (v : BitVec 64) (h : a + 8 ≤ b ∨ b + 8 ≤ a) :
    memWord (memStore m a v) b = memWord m b := by
  simp only [memWord]
  repeat rw [getD_memStore_of_ne _ _ _ _ (by omega)]

theorem append_extractLsb'_8 (v : BitVec 64) :
    @Eq (BitVec 64) (v.extractLsb' 56 8 ++ v.extractLsb' 48 8 ++ v.extractLsb' 40 8 ++
      v.extractLsb' 32 8 ++ v.extractLsb' 24 8 ++ v.extractLsb' 16 8 ++ v.extractLsb' 8 8 ++
      v.extractLsb' 0 8) v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  have hd : ∀ (c : Prop) [Decidable c] (b : Bool), c → (decide c && b) = b := by
    intro c _ b hc; simp [hc]
  repeat' split
  all_goals rw [hd]
  all_goals first | (congr 1; omega) | omega

theorem memWord_memStore_self (m : Mem) (a : Nat) (v : BitVec 64) :
    memWord (memStore m a v) a = v := by
  simp only [memWord, memStore, Std.ExtHashMap.getD_insert, beq_iff_eq]
  simp only [Nat.add_left_cancel_iff, Nat.add_eq_left, ↓reduceIte,
    show (7 : Nat) ≠ 0 by decide, show (6 : Nat) ≠ 0 by decide, show (5 : Nat) ≠ 0 by decide,
    show (4 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 0 by decide,
    show (1 : Nat) ≠ 0 by decide]
  simp (config := { decide := true }) only [↓reduceIte]
  exact append_extractLsb'_8 v

/-! ## The vocabulary of the specifications -/

/-! ## The vocabulary of the specifications in the documentation of intx.hpp -/

/-- A `result_with_carry<uint64_t>`. -/
structure ResultWithCarry where
  value : Nat
  carry : Bool

/-- A `div_result<uint64_t>`. -/
structure DivResult where
  quot : Nat
  rem : Nat

/-- The value of the `N`-bit number `x` as a two's complement signed number. -/
def signed (N x : Nat) : Int := if x < 2 ^ (N - 1) then x else (x : Int) - 2 ^ N

/-- The `len` bytes at `a` are a buffer of words: `a` is aligned to 8 bytes and the buffer does
not wrap around the address space. -/
def Buf (a : BitVec 64) (len : Nat) : Prop := a.toNat % 8 = 0 ∧ a.toNat + len ≤ 2 ^ 64

/-- The `la` bytes at `a` and the `lb` bytes at `b` do not overlap. -/
def Disjoint (a : BitVec 64) (la : Nat) (b : BitVec 64) (lb : Nat) : Prop :=
  a.toNat + la ≤ b.toNat ∨ b.toNat + lb ≤ a.toNat

/-- The memory `m'` is `m` except for the `len` bytes at `a`. -/
def UnchangedExcept (m m' : Mem) (a : BitVec 64) (len : Nat) : Prop :=
  ∀ k, k < a.toNat ∨ a.toNat + len ≤ k → m'[k]? = m[k]?

theorem unchangedExcept_refl (m : Mem) (a : BitVec 64) (len : Nat) : UnchangedExcept m m a len :=
  fun _ _ => rfl

theorem unchangedExcept_memStore {m m' : Mem} {a : BitVec 64} {len : Nat} (b : Nat)
    (v : BitVec 64) (hb : a.toNat ≤ b ∧ b + 8 ≤ a.toNat + len) :
    UnchangedExcept m (memStore m' b v) a len ↔ UnchangedExcept m m' a len := by
  constructor <;> intro h k hk
  · rw [← getElem?_memStore_of_ne m' b v k (by omega)]; exact h k hk
  · rw [getElem?_memStore_of_ne _ _ _ _ (by omega)]; exact h k hk

/-- The memory `m'` is `m` except for the `la` bytes at `a` and the `lb` bytes at `b`. -/
def UnchangedExcept2 (m m' : Mem) (a : BitVec 64) (la : Nat) (b : BitVec 64) (lb : Nat) : Prop :=
  ∀ k, k < a.toNat ∨ a.toNat + la ≤ k → k < b.toNat ∨ b.toNat + lb ≤ k → m'[k]? = m[k]?

theorem unchangedExcept2_refl (m : Mem) (a : BitVec 64) (la : Nat) (b : BitVec 64) (lb : Nat) :
    UnchangedExcept2 m m a la b lb :=
  fun _ _ _ => rfl

theorem unchangedExcept2_memStore {m m' : Mem} {a b : BitVec 64} {la lb : Nat} (c : Nat)
    (v : BitVec 64)
    (hc : a.toNat ≤ c ∧ c + 8 ≤ a.toNat + la ∨ b.toNat ≤ c ∧ c + 8 ≤ b.toNat + lb) :
    UnchangedExcept2 m (memStore m' c v) a la b lb ↔ UnchangedExcept2 m m' a la b lb := by
  constructor <;> intro h k hka hkb
  · rw [← getElem?_memStore_of_ne m' c v k (by omega)]; exact h k hka hkb
  · rw [getElem?_memStore_of_ne _ _ _ _ (by omega)]; exact h k hka hkb

end IntxRV
