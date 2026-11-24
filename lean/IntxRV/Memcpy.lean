import IntxRV.Loop
import IntxRV.Arith
import IntxRV.Gen.Code
/-!
# `memcpy()`

clang calls `memcpy()` to copy the bytes of a buffer of any alignment to its stack frame, as in
`be::load()` of `uint256` from bytes. `IntxRV/Api.cpp` defines it with a loop of `lbu` and `sb`
that copies the n bytes at src to dst, one at a time, and returns dst; the images of its callers
hold its code (`Gen.memcpy_prog`). `memcpy.reach` is its run for the buffers `A` that hold the words
of the bytes, which do not overlap: the memory after it is `memCopy`, and the registers that a
function keeps are kept. The loop runs by `Reach.loop` with the bytes left as the measure
(`memcpyLoop`). For the callers, the memory outside the n bytes at dst is unchanged
(`unchangedExcept_memCopy`, `memWord_memCopy_of_disjoint`) and a word inside them is the word of
the bytes at src (`memWord_memCopy`).
-/

namespace IntxRV
open IntxRV.Gen

/-- The memory `m` with the `n` bytes at `s` copied to `d`. -/
def memCopy (m : Mem) (d s : Nat) : Nat → Mem
  | 0 => m
  | n + 1 => memStoreByte (memCopy m d s n) (d + n) (memByte m (s + n))

theorem getElem?_memCopy (m : Mem) (d s : Nat) : ∀ (n k : Nat),
    (memCopy m d s n)[k]? = if d ≤ k ∧ k < d + n then some (memByte m (s + (k - d))) else m[k]?
  | 0, k => by rw [if_neg (by omega)]; rfl
  | n + 1, k => by
    rw [memCopy, memStoreByte, Std.ExtHashMap.getElem?_insert, getElem?_memCopy m d s n k]
    by_cases h : d + n = k
    · subst h
      rw [if_pos (by simp), if_pos (by omega), Nat.add_sub_cancel_left]
    · have h' : (d + n == k) = false := by simpa using h
      rw [h', if_neg Bool.false_ne_true]
      by_cases hk : d ≤ k ∧ k < d + n
      · rw [if_pos hk, if_pos (by omega)]
      · rw [if_neg hk, if_neg (by omega)]

/-- `memcpy()` changes only the `n` bytes at `d`. -/
theorem unchangedExcept_memCopy (m : Mem) (d : BitVec 64) (s n : Nat) :
    UnchangedExcept m (memCopy m d.toNat s n) d n := by
  intro k hk
  rw [getElem?_memCopy, if_neg (by omega)]

/-- A word outside the bytes that `memcpy()` writes. -/
theorem memWord_memCopy_of_disjoint (m : Mem) (d s n b : Nat) (h : b + 8 ≤ d ∨ d + n ≤ b) :
    memWord (memCopy m d s n) b = memWord m b := by
  simp only [memWord, Std.ExtHashMap.getD_eq_getD_getElem?, getElem?_memCopy]
  repeat rw [if_neg (by omega)]

/-- A word inside the bytes that `memcpy()` writes: the word of the bytes at the source. -/
theorem memWord_memCopy (m : Mem) (d s n b : Nat) (h : d ≤ b ∧ b + 8 ≤ d + n) :
    memWord (memCopy m d s n) b = memWord m (s + (b - d)) := by
  simp only [memWord, Std.ExtHashMap.getD_eq_getD_getElem?, getElem?_memCopy]
  repeat rw [if_pos (by omega)]
  simp only [memByte, Std.ExtHashMap.getD_eq_getD_getElem?, Option.getD_some]
  have e : ∀ t, s + (b + t - d) = s + (b - d) + t := fun t => by omega
  simp only [e]

/-- The registers and the memory at the head of the loop of `memcpy()` after `i` of the `n` bytes
from a1 to a0: the pointers a3 and a1 at byte `i` and the end a2. -/
def memcpyLoop (x : Regs) (m : Mem) (k : Nat) (x' : Regs) (m' : Mem) : Prop :=
  ∃ i, i < (x.get 12#5).toNat ∧ k = (x.get 12#5).toNat - i ∧
    x'.get 13#5 = x.get 10#5 + BitVec.ofNat 64 i ∧
    x'.get 11#5 = x.get 11#5 + BitVec.ofNat 64 i ∧
    x'.get 12#5 = x.get 10#5 + x.get 12#5 ∧
    (∀ r, r ≠ 11#5 → r ≠ 12#5 → r ≠ 13#5 → r ≠ 14#5 → x' r = x r) ∧
    m' = memCopy m (x.get 10#5).toNat (x.get 11#5).toNat i

theorem toNat_add_ofNat_of_lt {a : BitVec 64} {i n : Nat} (hn : a.toNat + n ≤ 2 ^ 64) (hi : i < n) :
    (a + BitVec.ofNat 64 i).toNat = a.toNat + i := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega)]

/-- The run of `memcpy()`: the n bytes (a2) at src (a1) copied to dst (a0), with the words of the
bytes in `A`, the bytes below 2^64 and the bytes at src and dst disjoint. -/
theorem memcpy.reach (base : BitVec 64) (x : Regs) (m : Mem) {A : List (BitVec 64)}
    (hr : x.get 1#5 &&& 3 = 0)
    (hn : (x.get 10#5).toNat + (x.get 12#5).toNat ≤ 2 ^ 64)
    (hns : (x.get 11#5).toNat + (x.get 12#5).toNat ≤ 2 ^ 64)
    (hd : (x.get 10#5).toNat + (x.get 12#5).toNat ≤ (x.get 11#5).toNat ∨
      (x.get 11#5).toNat + (x.get 12#5).toNat ≤ (x.get 10#5).toNat)
    (hA : ∀ i < (x.get 12#5).toNat, (x.get 10#5 + BitVec.ofNat 64 i) &&& ~~~7#64 ∈ A)
    (hS : ∀ i < (x.get 12#5).toNat, (x.get 11#5 + BitVec.ofNat 64 i) &&& ~~~7#64 ∈ A) :
    Reach A memcpy_prog base (pcAt base 0) x m (x.get 1#5) (fun x' m' =>
      m' = memCopy m (x.get 10#5).toNat (x.get 11#5).toNat (x.get 12#5).toNat ∧
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
    refine Reach.loop (memcpyLoop x m) ?_ (x.get 12#5).toNat _ _
      ⟨0, hn0, by omega, by simp [Regs.get_set], by simp [Regs.get_set], by simp [Regs.get_set],
        fun r h11 h12 h13 _ => by simp [Regs.set_apply, h12, h13], rfl⟩
    intro k x' m' ⟨i, hi, hk, h13, h11, h12, hx', hm'⟩ ih
    subst hk hm'
    -- lbu a4, 0(a1)
    refine Reach.step (by decide) rfl ?_
    simp only [StepGoal, Nat.reduceAdd, BitVec.reduceSignExtend, BitVec.add_zero]
    refine ⟨by rw [h11]; exact hS i hi, fun w hw => ?_⟩
    unfold Defn at hw
    subst hw
    -- sb a4, 0(a3)
    refine Reach.step (by decide) rfl ?_
    simp only [StepGoal, Nat.reduceAdd, BitVec.reduceSignExtend, BitVec.add_zero, Regs.get_set,
      show (13#5 : BitVec 5) ≠ 0 by decide, show (13#5 : BitVec 5) ≠ 14#5 by decide,
      show (14#5 : BitVec 5) ≠ 0 by decide, if_false, if_true, ite_true]
    refine ⟨by rw [h13]; exact hA i hi, ?_⟩
    have h13n : (x'.get 13#5).toNat = (x.get 10#5).toNat + i := by
      rw [h13]; exact toNat_add_ofNat_of_lt hn hi
    have h11n : (x'.get 11#5).toNat = (x.get 11#5).toNat + i := by
      rw [h11]; exact toNat_add_ofNat_of_lt hns hi
    have h1 : x'.get 1#5 = x.get 1#5 := by
      rw [← Regs.eq_get x' (by decide), ← Regs.eq_get x (by decide)]
      exact hx' _ (by decide) (by decide) (by decide) (by decide)
    have hcopy : memStoreByte (memCopy m (x.get 10#5).toNat (x.get 11#5).toNat i)
        (x'.get 13#5).toNat (BitVec.setWidth 8 (BitVec.setWidth 64
          (memByte (memCopy m (x.get 10#5).toNat (x.get 11#5).toNat i) (x'.get 11#5).toNat))) =
        memCopy m (x.get 10#5).toNat (x.get 11#5).toNat (i + 1) := by
      rw [h13n, h11n, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
      rw [memCopy]
      congr 1
      simp only [memByte, Std.ExtHashMap.getD_eq_getD_getElem?, getElem?_memCopy]
      rw [if_neg (by omega)]
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
      rw [hcopy]
      refine ih ((x.get 12#5).toNat - (i + 1)) (by omega) _ _
        ⟨i + 1, hi1, rfl, ?_, ?_, ?_, fun r r11 r12 r13 r14 => ?_, rfl⟩
      · simp only [Regs.get_set, show (13#5 : BitVec 5) ≠ 0 by decide,
          show (13#5 : BitVec 5) ≠ 11#5 by decide, if_false, if_true, h13]
        rw [BitVec.add_assoc]; congr 1
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        have := (x.get 12#5).isLt
        omega
      · simp only [Regs.get_set, show (11#5 : BitVec 5) ≠ 0 by decide, if_false, if_true, h11]
        rw [BitVec.add_assoc]; congr 1
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        have := (x.get 12#5).isLt
        omega
      · simp only [Regs.get_set, show (12#5 : BitVec 5) ≠ 0 by decide,
          show (12#5 : BitVec 5) ≠ 11#5 by decide, show (12#5 : BitVec 5) ≠ 13#5 by decide,
          show (12#5 : BitVec 5) ≠ 14#5 by decide, if_false, h12]
      · simp (config := { decide := true }) only [Regs.set_apply, r11, r13, r14, ↓reduceIte]
        exact hx' r r11 r12 r13 r14
    · -- The last byte: the return.
      rename_i hb
      rw [h13, h12] at hb
      have hin : i + 1 = (x.get 12#5).toNat := by
        have := congrArg BitVec.toNat hb
        simp only [BitVec.add_assoc, BitVec.toNat_add, BitVec.toNat_ofNat] at this
        have := (x.get 12#5).isLt
        omega
      simp only [Regs.get_set, show (1#5 : BitVec 5) ≠ 0 by decide,
        show (1#5 : BitVec 5) ≠ 11#5 by decide, show (1#5 : BitVec 5) ≠ 13#5 by decide,
        show (1#5 : BitVec 5) ≠ 14#5 by decide, if_false, h1, BitVec.reduceSignExtend,
        BitVec.add_zero, update_aligned hr]
      refine Reach.refl ⟨by rw [hcopy, hin], ?_, fun r hr' => ?_⟩
      · simp only [Regs.get_set, show (10#5 : BitVec 5) ≠ 0 by decide,
          show (10#5 : BitVec 5) ≠ 11#5 by decide, show (10#5 : BitVec 5) ≠ 13#5 by decide,
          show (10#5 : BitVec 5) ≠ 14#5 by decide, if_false]
        rw [← Regs.eq_get x' (by decide), ← Regs.eq_get x (by decide)]
        exact hx' _ (by decide) (by decide) (by decide) (by decide)
      · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl <;>
          simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] <;>
          exact hx' _ (by decide) (by decide) (by decide) (by decide)

end IntxRV
