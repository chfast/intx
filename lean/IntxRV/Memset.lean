import IntxRV.Loop
import IntxRV.Arith
import IntxRV.Gen.Code.memset
/-!
# `memset()`

clang calls `memset()` to zero the results of more than 64 bytes, as the results of `udivrem()`
for `addmod()` and `mulmod()`. `IntxRV/Api.cpp` defines it with a loop of `sb` that writes the low
byte of c to the n bytes at dst, one at a time, and returns dst; the images of its callers hold its
code (`Gen.memset_prog`). `memset.reach` is its run for the buffers `A` that hold the words of the
bytes: the memory after it is `memFill`, with the n bytes set, and the registers that a function
keeps are kept. The loop runs by `Reach.loop` with the bytes left as the measure (`memsetLoop`).
For the callers, the words outside the bytes keep their values (`memWord_memFill_of_disjoint`,
`unchangedExcept_memFill`) and the words inside are 0 for c = 0 (`memWord_memFill_zero`).
-/

namespace IntxRV
open IntxRV.Gen

/-- The memory `m` with the `n` bytes from `a` set to `v`. -/
def memFill (m : Mem) (a : Nat) (v : BitVec 8) : Nat → Mem
  | 0 => m
  | n + 1 => memStoreByte (memFill m a v n) (a + n) v

theorem getElem?_memFill (m : Mem) (a : Nat) (v : BitVec 8) : ∀ (n k : Nat),
    (memFill m a v n)[k]? = if a ≤ k ∧ k < a + n then some v else m[k]?
  | 0, k => by rw [if_neg (by omega)]; rfl
  | n + 1, k => by
    rw [memFill, memStoreByte, Std.ExtHashMap.getElem?_insert, getElem?_memFill m a v n k]
    by_cases h : a + n = k
    · subst h; simp
    · have h' : (a + n == k) = false := by simpa using h
      rw [h', if_neg Bool.false_ne_true]
      by_cases hk : a ≤ k ∧ k < a + n
      · rw [if_pos hk, if_pos (by omega)]
      · rw [if_neg hk, if_neg (by omega)]

/-- `memset()` changes only the `n` bytes at `a`. -/
theorem unchangedExcept_memFill (m : Mem) (a : BitVec 64) (v : BitVec 8) (n : Nat) :
    UnchangedExcept m (memFill m a.toNat v n) a n := by
  intro k hk
  rw [getElem?_memFill, if_neg (by omega)]

/-- A word outside the bytes that `memset()` sets. -/
theorem memWord_memFill_of_disjoint (m : Mem) (a b : Nat) (v : BitVec 8) (n : Nat)
    (h : b + 8 ≤ a ∨ a + n ≤ b) : memWord (memFill m a v n) b = memWord m b := by
  simp only [memWord, Std.ExtHashMap.getD_eq_getD_getElem?, getElem?_memFill]
  repeat rw [if_neg (by omega)]

/-- A word inside the bytes that `memset()` sets to 0. -/
theorem memWord_memFill_zero (m : Mem) (a b n : Nat) (h : a ≤ b ∧ b + 8 ≤ a + n) :
    memWord (memFill m a 0#8 n) b = 0#64 := by
  simp only [memWord, Std.ExtHashMap.getD_eq_getD_getElem?, getElem?_memFill]
  repeat rw [if_pos (by omega)]
  rfl

/-- The registers and the memory at the head of the loop of `memset()` after `i` of the `n` bytes
at `a0`: the pointer a3 at byte `i` and the end a2. -/
def memsetLoop (x : Regs) (m : Mem) (k : Nat) (x' : Regs) (m' : Mem) : Prop :=
  ∃ i, i < (x.get 12#5).toNat ∧ k = (x.get 12#5).toNat - i ∧
    x'.get 13#5 = x.get 10#5 + BitVec.ofNat 64 i ∧
    x'.get 12#5 = x.get 10#5 + x.get 12#5 ∧
    (∀ r, r ≠ 12#5 → r ≠ 13#5 → x' r = x r) ∧
    m' = memFill m (x.get 10#5).toNat ((x.get 11#5).setWidth 8) i

/-- The run of `memset()`: the n bytes at dst (a2 and a0) set to the low byte of c (a1), with the
words of the bytes in `A` and the bytes below 2^64. -/
theorem memset.reach (base : BitVec 64) (x : Regs) (m : Mem) {A : List (BitVec 64)}
    (hr : x.get 1#5 &&& 3 = 0)
    (hn : (x.get 10#5).toNat + (x.get 12#5).toNat ≤ 2 ^ 64)
    (hA : ∀ i < (x.get 12#5).toNat, (x.get 10#5 + BitVec.ofNat 64 i) &&& ~~~7#64 ∈ A) :
    Reach A memset_prog base (pcAt base 0) x m (x.get 1#5) (fun x' m' =>
      m' = memFill m (x.get 10#5).toNat ((x.get 11#5).setWidth 8) (x.get 12#5).toNat ∧
      x'.get 10#5 = x.get 10#5 ∧ ∀ i ∈ calleeSaved, x' i = x i) := by
  rv_exec_cut 3
  · -- n = 0: the return.
    rename_i h0
    rw [show (0#5 : BitVec 5) = 0 from rfl, Regs.get_zero] at h0
    simp only [BitVec.reduceSignExtend, BitVec.add_zero, update_aligned hr]
    refine Reach.refl ?_
    simp only [h0, Regs.get_set]
    refine ⟨rfl, by simp, fun i _ => ?_⟩
    simp [Regs.set_apply]
  · -- The loop.
    rename_i h0 w hw
    unfold Defn at hw
    subst hw
    rw [show (0#5 : BitVec 5) = 0 from rfl, Regs.get_zero] at h0
    have hn0 : 0 < (x.get 12#5).toNat := by
      rcases Nat.eq_zero_or_pos (x.get 12#5).toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) h0
      · exact h
    refine Reach.loop (memsetLoop x m) ?_ (x.get 12#5).toNat _ _
      ⟨0, hn0, by omega, by simp [Regs.get_set], by simp [Regs.get_set],
        fun r h12 h13 => by simp [Regs.set_apply, h12, h13], rfl⟩
    intro k x' m' ⟨i, hi, hk, h13, h12, hx', hm'⟩ ih
    subst hk hm'
    -- sb a1, 0(a3)
    refine Reach.step (by decide) rfl ?_
    simp only [StepGoal, Nat.reduceAdd, BitVec.reduceSignExtend, BitVec.add_zero]
    refine ⟨by rw [h13]; exact hA i hi, ?_⟩
    have h13n : (x'.get 13#5).toNat = (x.get 10#5).toNat + i := by
      rw [h13, BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by have := (x.get 12#5).isLt; omega : i < 2 ^ 64),
        Nat.mod_eq_of_lt (by omega)]
    have h11 : x'.get 11#5 = x.get 11#5 := by
      rw [← Regs.eq_get x' (by decide), ← Regs.eq_get x (by decide)]
      exact hx' _ (by decide) (by decide)
    have h1 : x'.get 1#5 = x.get 1#5 := by
      rw [← Regs.eq_get x' (by decide), ← Regs.eq_get x (by decide)]
      exact hx' _ (by decide) (by decide)
    have hfill : memStoreByte (memFill m (x.get 10#5).toNat (BitVec.setWidth 8 (x.get 11#5)) i)
        (x'.get 13#5).toNat (BitVec.setWidth 8 (x'.get 11#5)) =
        memFill m (x.get 10#5).toNat (BitVec.setWidth 8 (x.get 11#5)) (i + 1) := by
      rw [h13n, h11]; rfl
    rv_exec_cut 3
    · -- The next byte.
      rename_i hb
      rw [h13, h12] at hb
      have hi1 : i + 1 < (x.get 12#5).toNat := by
        rcases Nat.lt_or_ge (i + 1) (x.get 12#5).toNat with h | h
        · exact h
        · exfalso
          apply hb
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
          have := (x.get 12#5).isLt
          omega
      rw [hfill]
      refine ih ((x.get 12#5).toNat - (i + 1)) (by omega) _ _
        ⟨i + 1, hi1, rfl, ?_, ?_, fun r r12 r13 => ?_, rfl⟩
      · simp only [Regs.get_set, show (13#5 : BitVec 5) ≠ 0 by decide, if_false, if_true, h13]
        rw [BitVec.add_assoc]; congr 1
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        have := (x.get 12#5).isLt
        omega
      · simp only [Regs.get_set, show (12#5 : BitVec 5) ≠ 0 by decide,
          show (12#5 : BitVec 5) ≠ 13#5 by decide, if_false, h12]
      · rw [Regs.set_apply, if_neg (by decide), if_neg r13]
        exact hx' r r12 r13
    · -- The last byte: the return.
      rename_i hb
      rw [h13, h12] at hb
      have hin : i + 1 = (x.get 12#5).toNat := by
        have := congrArg BitVec.toNat hb
        simp only [BitVec.add_assoc, BitVec.toNat_add, BitVec.toNat_ofNat] at this
        have := (x.get 12#5).isLt
        omega
      simp only [Regs.get_set, show (1#5 : BitVec 5) ≠ 0 by decide,
        show (1#5 : BitVec 5) ≠ 13#5 by decide, if_false, h1, BitVec.reduceSignExtend,
        BitVec.add_zero, update_aligned hr]
      refine Reach.refl ⟨by rw [hfill, hin], ?_, fun r hr' => ?_⟩
      · simp only [Regs.get_set, show (10#5 : BitVec 5) ≠ 0 by decide,
          show (10#5 : BitVec 5) ≠ 13#5 by decide, if_false]
        rw [← Regs.eq_get x' (by decide), ← Regs.eq_get x (by decide)]
        exact hx' _ (by decide) (by decide)
      · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl <;>
          simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] <;>
          exact hx' _ (by decide) (by decide)

end IntxRV
