import IntxRV.Api.udivrem_by1
import IntxRV.Api.udivrem_by2
import IntxRV.Api.udivrem_top1_2
import IntxRV.Api.udivrem_top1_3
import IntxRV.Api.udivrem_top2_3
import IntxRV.Gen.Api.udivrem_256

/-!
# The paths of `udivrem<256, 256>()`

`udivrem<256, 256>()` saves ra and s0 in a frame of 16 bytes, selects a path by the significant
words of u and v, and ends in the epilogue at 0x1c (`u256_epi`). Each path from its first
instruction is a lemma that the proof takes as one step: the calls of `udivrem_top1<3>()`,
`udivrem_top1<2>()` and `udivrem_top2<3>()` (`u256_top13`, `u256_top12`, `u256_top23`), the
return of 0 and u for u < v (`u256_ult`) and of 0 and 0 for v = 0 (`u256_vzero`). The paths that
zero the result and call `udivrem_by2()` or `udivrem_by1()` are in `IntxRV/Div256By2.lean` and
`IntxRV/Div256By1.lean`. The memory after a call is the memory before it outside the bytes that
the callee writes (`u256_by2_mem`, `u256_by1_mem`, `u256_top_mem`), and the callees read the table
of the reciprocal at any address `T` (`holdsData_table_memStore`), with the immediates of `T` in
each callee as parameters of the code (`udivrem_256_progAt`).
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
-- The guards that select the paths do not change the goals.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {hi0 hi1 hi2 hi3 hi4 : BitVec 20} {lo0 lo1 lo2 lo3 lo4 : BitVec 12} {T : BitVec 64}

-- The instructions of `udivrem<256, 256>()` and its callees with the immediates of the address
-- `T` of the table in each callee.
set_option hygiene false in
local notation "P256" => udivrem_256_progAt hi0 lo0 hi1 lo1 hi2 lo2 hi3 lo3 hi4 lo4

theorem words_ret8_quot (m : Mem) (r q a0 a1 a2 a3 z : BitVec 64) (hz : z = 0#64)
    (hr : r.toNat + 64 ≤ 2 ^ 64) :
    words (memStore (memStore (memStore (memStore (memStore (memStore (memStore
      (memStore m r.toNat q) (r + 8#64).toNat z) (r + 16#64).toNat z)
      (r + 24#64).toNat z) (r + 32#64).toNat a0) (r + 40#64).toNat a1) (r + 48#64).toNat a2)
      (r + 56#64).toNat a3) r 4 = q.toNat :=
  (words_ret8 m r q a0 a1 a2 a3 z hz hr _ rfl).1

theorem words_ret8_rem (m : Mem) (r q a0 a1 a2 a3 z : BitVec 64) (hz : z = 0#64)
    (hr : r.toNat + 64 ≤ 2 ^ 64) :
    words (memStore (memStore (memStore (memStore (memStore (memStore (memStore
      (memStore m r.toNat q) (r + 8#64).toNat z) (r + 16#64).toNat z)
      (r + 24#64).toNat z) (r + 32#64).toNat a0) (r + 40#64).toNat a1) (r + 48#64).toNat a2)
      (r + 56#64).toNat a3) (r + 32#64) 4 =
      a0.toNat + 2 ^ 64 * (a1.toNat + 2 ^ 64 * (a2.toNat + 2 ^ 64 * a3.toNat)) :=
  (words_ret8 m r q a0 a1 a2 a3 z hz hr _ rfl).2.1

/-- A store outside the data keeps it. -/
theorem holdsData_memStore_iff {b : Nat} {w : BitVec 64} :
    ∀ {m : Mem} {a : BitVec 64} (ds : List (BitVec 64)),
    (b + 8 ≤ a.toNat ∨ a.toNat + 8 * ds.length ≤ b) → a.toNat + 8 * ds.length ≤ 2 ^ 64 →
    (HoldsData (memStore m b w) a ds ↔ HoldsData m a ds)
  | _, _, [], _, _ => Iff.rfl
  | m, a, d :: ds, h1, h2 => by
    simp only [List.length_cons] at h1 h2
    simp only [HoldsData]
    rw [memWord_memStore_of_ne _ _ _ _ (by omega)]
    cases ds with
    | nil => exact Iff.rfl
    | cons d' ds' =>
      simp only [List.length_cons] at h1 h2
      have h8 : (a + 8).toNat = a.toNat + 8 := by bv_omega
      rw [holdsData_memStore_iff (d' :: ds') (by simp only [List.length_cons]; omega)
        (by simp only [List.length_cons]; omega)]

/-- A store outside the table of the reciprocal keeps it. -/
theorem holdsData_table_memStore {m : Mem} {T : BitVec 64} {b : Nat} {w : BitVec 64}
    (h : b + 8 ≤ T.toNat ∨ T.toNat + 2048 ≤ b) (hT : T.toNat + 2048 ≤ 2 ^ 64) :
    HoldsData (memStore m b w) T reciprocal_2by1_image_data ↔
      HoldsData m T reciprocal_2by1_image_data :=
  holdsData_memStore_iff _ (by rw [show reciprocal_2by1_image_data.length = 256 from rfl]; omega)
    (by rw [show reciprocal_2by1_image_data.length = 256 from rfl]; omega)

/-- The words of a buffer are in a longer one at the same address. -/
theorem mem_bufWords_of_le {a b : BitVec 64} {n n' : Nat} (h : n ≤ n') (hb : b ∈ bufWords a n) :
    b ∈ bufWords a n' := by
  obtain ⟨i, hi, rfl⟩ := exists_of_mem_bufWords hb
  exact mem_bufWords (by omega)

/-- The memory after a call that changes only parts of the bytes at `a` and `b`. -/
theorem UnchangedExcept2.trans2 {m m1 m2 : Mem} {a b b' : BitVec 64} {la lb la' lb' : Nat}
    (h1 : UnchangedExcept2 m m1 a la b lb) (h2 : UnchangedExcept2 m1 m2 a la' b' lb')
    (ha : la' ≤ la) (hb : b.toNat ≤ b'.toNat ∧ b'.toNat + lb' ≤ b.toNat + lb) :
    UnchangedExcept2 m m2 a la b lb := by
  intro k hka hkb
  rw [h2 k (by omega) (by omega), h1 k hka hkb]

/-- A buffer of `n` words with its first and last words outside `o1 + o2` bytes at `base` is
outside them. -/
theorem buf_outside (a base : BitVec 64) (n o1 o2 : Nat) (hn : 0 < n)
    (h0 : a.toNat + 8 ≤ base.toNat ∨ base.toNat + o1 + o2 ≤ a.toNat)
    (h1 : (a + BitVec.ofNat 64 (8 * (n - 1))).toNat + 8 ≤ base.toNat ∨
      base.toNat + o1 + o2 ≤ (a + BitVec.ofNat 64 (8 * (n - 1))).toNat)
    (ha : a.toNat + 8 * n ≤ 2 ^ 64) (ho : 8 * n ≤ o1 + o2) :
    a.toNat + 8 * n ≤ base.toNat ∨ base.toNat + o1 + o2 ≤ a.toNat := by
  have : (a + BitVec.ofNat 64 (8 * (n - 1))).toNat = a.toNat + 8 * (n - 1) := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : 8 * (n - 1) < 2 ^ 64)]
    exact Nat.mod_eq_of_lt (by omega)
  omega

/-- The end of `udivrem<256, 256>()` from 0x1c: the restore of ra and s0 from the frame of 16
bytes and the return, with the result stored. -/
theorem u256_epi {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hr : x.get 1#5 &&& 3 = 0) (x' : Regs) (m' : Mem)
    (h2 : x'.get 2#5 = x.get 2#5 + 18446744073709551600#64)
    (hra : memWord m' (x.get 2#5 + 18446744073709551608#64).toNat = x.get 1#5)
    (hs0 : memWord m' (x.get 2#5 + 18446744073709551600#64).toNat = x.get 8#5)
    (hcs : ∀ i ∈ calleeSaved, i ≠ 2#5 → i ≠ 8#5 → x' i = x i)
    (hm : UnchangedExcept2 m m' (x.get 10#5) 64 (x.get 2#5 - 48#64) 48)
    (hq : words m' (x.get 10#5) 4 = words m (x.get 11#5) 4 / words m (x.get 12#5) 4)
    (hrem : words m' (x.get 10#5 + 32#64) 4 = if words m (x.get 12#5) 4 = 0 then 0
      else words m (x.get 11#5) 4 % words m (x.get 12#5) 4) :
    Reach (bufWords (x.get 11#5) 4 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 8 ++
        bufWords (x.get 2#5 - 48#64) 6 ++ D) P256 base (pcAt base 7) x' m'
      (x.get 1#5) (udivrem_256.post x m) := by
  have hm8 : x.get 2#5 + 18446744073709551600#64 + 8#64 = x.get 2#5 + 18446744073709551608#64 := by
    rw [BitVec.add_assoc]; rfl
  -- ra and s0.
  refine Reach.step (by decide) rfl ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  rw [h2, hm8]
  refine ⟨by rw [show x.get 2#5 + 18446744073709551608#64 = x.get 2#5 - 48#64 +
      BitVec.ofNat 64 (8 * 5) by bv_omega]
             exact List.mem_append_left _ (List.mem_append_right _ (mem_bufWords (by norm_num))),
    fun w1 hw1 => ?_⟩
  rw [hra] at hw1
  refine Reach.step (by decide) rfl ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  rw [h2]
  refine ⟨by rw [show x.get 2#5 + 18446744073709551600#64 = x.get 2#5 - 48#64 +
      BitVec.ofNat 64 (8 * 4) by bv_omega]
             exact List.mem_append_left _ (List.mem_append_right _ (mem_bufWords (by norm_num))),
    fun w2 hw2 => ?_⟩
  rw [hs0] at hw2
  simp only [Defn] at hw1 hw2
  subst hw1 hw2
  rv_step
  rv_step
  rv_val
  simp only [update_aligned hr, h2, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero]
  refine Reach.refl ?_
  simp only [udivrem_256.post]
  simp (disch := decide) only [Regs.eq_get x]
  refine ⟨hq, hrem, hm, ?_⟩
  intro i hi
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] <;>
    first
      | exact (Regs.eq_get x (by decide)).symm
      | (rw [h2]; bv_omega)
      | exact hcs _ (by decide) (by decide) (by decide)

/-- The frame of 16 bytes of `udivrem<256, 256>()` keeps the memory outside it. -/
theorem u256_frame_unchanged (m : Mem) (r sp a b : BitVec 64)
    (hs : (sp - 48#64).toNat + 48 ≤ 2 ^ 64) :
    UnchangedExcept2 m (memStore (memStore m (sp + 18446744073709551608#64).toNat a)
      (sp + 18446744073709551600#64).toNat b) r 64 (sp - 48#64) 48 := by
  simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
  exact unchangedExcept2_refl _ _ _ _ _

/-- The end of `udivrem<256, 256>()` for u < v from 0x108: the quotient 0 and the remainder u. -/
theorem u256_ult {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hr : x.get 1#5 &&& 3 = 0)
    (hrn : (x.get 10#5).toNat + 64 ≤ 2 ^ 64) (hun : (x.get 11#5).toNat + 32 ≤ 2 ^ 64)
    (hsn : (x.get 2#5 - 48#64).toNat + 48 ≤ 2 ^ 64)
    (hdru : (x.get 10#5).toNat + 64 ≤ (x.get 11#5).toNat ∨
      (x.get 11#5).toNat + 32 ≤ (x.get 10#5).toNat)
    (hdsu : (x.get 2#5 - 48#64).toNat + 48 ≤ (x.get 11#5).toNat ∨
      (x.get 11#5).toNat + 32 ≤ (x.get 2#5 - 48#64).toNat)
    (hdsr : (x.get 2#5 - 48#64).toNat + 48 ≤ (x.get 10#5).toNat ∨
      (x.get 10#5).toNat + 64 ≤ (x.get 2#5 - 48#64).toNat)
    (x' : Regs) (h10 : x'.get 10#5 = x.get 10#5)
    (h2 : x'.get 2#5 = x.get 2#5 + 18446744073709551600#64)
    (hcs : ∀ i ∈ calleeSaved, i ≠ 2#5 → i ≠ 8#5 → x' i = x i)
    (h11 : x'.get 11#5 = x.get 11#5)
    (hlt : words m (x.get 11#5) 4 < words m (x.get 12#5) 4) :
    Reach (bufWords (x.get 11#5) 4 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 8 ++
        bufWords (x.get 2#5 - 48#64) 6 ++ D) P256 base (pcAt base 66) x'
      (memStore (memStore m (x.get 2#5 + 18446744073709551608#64).toNat (x.get 1#5))
        (x.get 2#5 + 18446744073709551600#64).toNat (x.get 8#5))
      (x.get 1#5) (udivrem_256.post x m) := by
  have hz : x'.get 0#5 = 0#64 := by rw [show (0#5 : BitVec 5) = 0 from rfl, Regs.get_zero]; rfl
  rw [← h10, ← h11]
  rv_exec_cut 7
  simp only [BitVec.reduceSignExtend, BitVec.add_zero, hz, h10, h11]
  refine u256_epi base x m hr _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · exact h2
  · simp (disch := first | bv_omega | fail) only [memWord_memStore_of_ne, memWord_memStore_self]
  · simp (disch := first | bv_omega | fail) only [memWord_memStore_of_ne, memWord_memStore_self]
  · intro i hi h2i h8i
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] <;>
      first
        | exact hcs _ (by decide) (by decide) (by decide)
        | exact absurd rfl h2i
        | exact absurd rfl h8i
  · simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
    exact unchangedExcept2_refl _ _ _ _ _
  · simp only [h10]
    rw [words_ret8_quot _ _ _ _ _ _ _ _ rfl hrn, Nat.div_eq_of_lt hlt]; rfl
  · have hV : words m (x.get 12#5) 4 ≠ 0 := by omega
    simp only [h10]
    rw [words_ret8_rem _ _ _ _ _ _ _ _ rfl hrn, if_neg hV, Nat.mod_eq_of_lt hlt]
    simp only [Defn] at *
    subst_vars
    simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
      Nat.add_zero, h11]

/-- The end of `udivrem<256, 256>()` for v = 0 from 0x18c: the quotient and the remainder 0. -/
theorem u256_vzero {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hr : x.get 1#5 &&& 3 = 0)
    (hrn : (x.get 10#5).toNat + 64 ≤ 2 ^ 64)
    (hsn : (x.get 2#5 - 48#64).toNat + 48 ≤ 2 ^ 64)
    (hdsr : (x.get 2#5 - 48#64).toNat + 48 ≤ (x.get 10#5).toNat ∨
      (x.get 10#5).toNat + 64 ≤ (x.get 2#5 - 48#64).toNat)
    (x' : Regs) (h10 : x'.get 10#5 = x.get 10#5)
    (h2 : x'.get 2#5 = x.get 2#5 + 18446744073709551600#64)
    (hcs : ∀ i ∈ calleeSaved, i ≠ 2#5 → i ≠ 8#5 → x' i = x i)
    (hv : words m (x.get 12#5) 4 = 0) :
    Reach (bufWords (x.get 11#5) 4 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 8 ++
        bufWords (x.get 2#5 - 48#64) 6 ++ D) P256 base (pcAt base 99) x'
      (memStore (memStore m (x.get 2#5 + 18446744073709551608#64).toNat (x.get 1#5))
        (x.get 2#5 + 18446744073709551600#64).toNat (x.get 8#5))
      (x.get 1#5) (udivrem_256.post x m) := by
  have hz : x'.get 0#5 = 0#64 := by rw [show (0#5 : BitVec 5) = 0 from rfl, Regs.get_zero]; rfl
  rw [← h10]
  rv_exec_cut 7
  simp only [BitVec.reduceSignExtend, BitVec.add_zero, hz, h10]
  refine u256_epi base x m hr _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · exact h2
  · simp (disch := first | bv_omega | fail) only [memWord_memStore_of_ne, memWord_memStore_self]
  · simp (disch := first | bv_omega | fail) only [memWord_memStore_of_ne, memWord_memStore_self]
  · intro i hi h2i h8i
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] <;>
      first
        | exact hcs _ (by decide) (by decide) (by decide)
        | exact absurd rfl h2i
        | exact absurd rfl h8i
  · simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
    exact unchangedExcept2_refl _ _ _ _ _
  · rw [hv, Nat.div_zero]
    simp (disch := first | bv_omega | fail) only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd, memWord_memStore_self, memWord_memStore_of_ne, BitVec.toNat_ofNat,
      Nat.zero_mod, Nat.mul_zero, Nat.add_zero]
  · simp only [hv, if_pos]
    simp (disch := first | bv_omega | fail) only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd, memWord_memStore_self, memWord_memStore_of_ne, BitVec.toNat_ofNat,
      Nat.zero_mod, Nat.mul_zero, Nat.add_zero]

/-- The end of the path of `udivrem_by2()` in `udivrem<256, 256>()` from 0xfc: the store of the
remainder in a0:a1 above the quotient. -/
theorem u256_by2_ret {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hr : x.get 1#5 &&& 3 = 0) (hrn : (x.get 10#5).toNat + 64 ≤ 2 ^ 64)
    (hsn : (x.get 2#5 - 48#64).toNat + 48 ≤ 2 ^ 64)
    (hdsr : (x.get 2#5 - 48#64).toNat + 48 ≤ (x.get 10#5).toNat ∨
      (x.get 10#5).toNat + 64 ≤ (x.get 2#5 - 48#64).toNat)
    (x3 : Regs) (m3 : Mem) (h8 : x3.get 8#5 = x.get 10#5)
    (h2 : x3.get 2#5 = x.get 2#5 + 18446744073709551600#64)
    (hcs : ∀ i ∈ calleeSaved, i ≠ 2#5 → i ≠ 8#5 → x3 i = x i)
    (hra : memWord m3 (x.get 2#5 + 18446744073709551608#64).toNat = x.get 1#5)
    (hs0 : memWord m3 (x.get 2#5 + 18446744073709551600#64).toNat = x.get 8#5)
    (hm : UnchangedExcept2 m m3 (x.get 10#5) 64 (x.get 2#5 - 48#64) 48)
    (hz6 : memWord m3 (x.get 10#5 + 48#64).toNat = 0#64)
    (hz7 : memWord m3 (x.get 10#5 + 56#64).toNat = 0#64)
    (hq : words m3 (x.get 10#5) 4 = words m (x.get 11#5) 4 / words m (x.get 12#5) 4)
    (hv : words m (x.get 12#5) 4 ≠ 0)
    (hrem : (x3.get 10#5).toNat + 2 ^ 64 * (x3.get 11#5).toNat =
      words m (x.get 11#5) 4 % words m (x.get 12#5) 4) :
    Reach (bufWords (x.get 11#5) 4 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 8 ++
        bufWords (x.get 2#5 - 48#64) 6 ++ D) P256 base (pcAt base 63) x3 m3
      (x.get 1#5)
      (udivrem_256.post x m) := by
  rw [← h8]
  rv_exec_cut 7
  simp only [BitVec.reduceSignExtend, h8]
  refine u256_epi base x m hr _ _ h2 ?_ ?_ hcs ?_ ?_ ?_
  · rw [memWord_memStore_of_ne _ _ _ _ (by bv_omega), memWord_memStore_of_ne _ _ _ _ (by bv_omega)]
    exact hra
  · rw [memWord_memStore_of_ne _ _ _ _ (by bv_omega), memWord_memStore_of_ne _ _ _ _ (by bv_omega)]
    exact hs0
  · simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
    exact hm
  · rw [← hq]
    simp (disch := first | bv_omega | fail) only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd, memWord_memStore_of_ne]
  · rw [if_neg hv, ← hrem]
    simp (disch := first | bv_omega | fail) only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd, memWord_memStore_of_ne, memWord_memStore_self, hz6, hz7,
      BitVec.toNat_zero, Nat.mul_zero, Nat.add_zero]

/-- The memory after the call of `udivrem_by2()` in `udivrem<256, 256>()`, which writes `Q` words of
the quotient over the zeros of the result and uses its frame of 32 bytes below the frame of the
caller. -/
theorem u256_by2_mem (m m3 : Mem) (r sp ra s0 : BitVec 64) (Q : Nat) (hQ : Q = 2 ∨ Q = 3)
    (hrn : r.toNat + 64 ≤ 2 ^ 64) (hsn : (sp - 48#64).toNat + 48 ≤ 2 ^ 64)
    (hdsr : (sp - 48#64).toNat + 48 ≤ r.toNat ∨ r.toNat + 64 ≤ (sp - 48#64).toNat)
    (hunc : UnchangedExcept2 (memStore (memStore (memStore (memStore (memStore (memStore
        (memStore (memStore
        (memStore (memStore m (sp + 18446744073709551608#64).toNat ra)
          (sp + 18446744073709551600#64).toNat s0)
        r.toNat 0#64) (r + 8#64).toNat 0#64) (r + 16#64).toNat 0#64)
        (r + 24#64).toNat 0#64) (r + 32#64).toNat 0#64)
        (r + 40#64).toNat 0#64) (r + 48#64).toNat 0#64)
        (r + 56#64).toNat 0#64) m3 r (8 * Q) (sp - 48#64) 32) :
    memWord m3 (sp + 18446744073709551608#64).toNat = ra ∧
      memWord m3 (sp + 18446744073709551600#64).toNat = s0 ∧
      UnchangedExcept2 m m3 r 64 (sp - 48#64) 48 ∧
      memWord m3 (r + 48#64).toNat = 0#64 ∧ memWord m3 (r + 56#64).toNat = 0#64 ∧
      words m3 r 4 = words m3 r Q := by
  have hz : ∀ k, Q ≤ k → k < 8 → memWord m3 (r + BitVec.ofNat 64 (8 * k)).toNat = 0#64 := by
    intro k hk hk8
    have hrk : (r + BitVec.ofNat 64 (8 * k)).toNat = r.toNat + 8 * k := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8 * k < 2 ^ 64)]
      exact Nat.mod_eq_of_lt (by omega)
    rw [memWord_of_unchangedExcept2 hunc _ (by omega) (by omega)]
    interval_cases k <;> rcases hQ with rfl | rfl <;> first | omega |
      simp (disch := first | bv_omega | fail) only [Nat.reduceMul,
        memWord_memStore_of_ne, memWord_memStore_self]
  refine ⟨?_, ?_, ?_, hz 6 (by omega) (by omega), hz 7 (by omega) (by omega), ?_⟩
  · rw [memWord_of_unchangedExcept2 hunc _ (by bv_omega) (by bv_omega)]
    simp (disch := first | bv_omega | fail) only [memWord_memStore_of_ne, memWord_memStore_self]
  · rw [memWord_of_unchangedExcept2 hunc _ (by bv_omega) (by bv_omega)]
    simp (disch := first | bv_omega | fail) only [memWord_memStore_of_ne, memWord_memStore_self]
  · refine UnchangedExcept2.trans2 ?_ hunc (by omega) (by omega)
    simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
    exact unchangedExcept2_refl _ _ _ _ _
  · have z2 := hz 2
    have z3 := hz 3
    simp only [Nat.reduceMul] at z2 z3
    rcases hQ with rfl | rfl
    · simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
        z2 (by omega) (by omega), z3 (by omega) (by omega), BitVec.toNat_zero, Nat.mul_zero,
        Nat.add_zero]
    · simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
        z3 (by omega) (by omega), BitVec.toNat_zero, Nat.mul_zero, Nat.add_zero]

/-- The words of u at the call of `udivrem_by2()` in `udivrem<256, 256>()`: u is outside the
stores of the frame and of the zeros of the result. -/
theorem u256_by2_u (m : Mem) (r sp ra s0 u : BitVec 64) (n : Nat) (hn : n ≤ 4)
    (hrn : r.toNat + 64 ≤ 2 ^ 64) (hun : u.toNat + 32 ≤ 2 ^ 64)
    (hdru : r.toNat + 64 ≤ u.toNat ∨ u.toNat + 32 ≤ r.toNat)
    (hdsu : (sp - 48#64).toNat + 48 ≤ u.toNat ∨ u.toNat + 32 ≤ (sp - 48#64).toNat)
    (hsn : (sp - 48#64).toNat + 48 ≤ 2 ^ 64) :
    words (memStore (memStore (memStore (memStore (memStore (memStore (memStore (memStore
        (memStore (memStore m (sp + 18446744073709551608#64).toNat ra)
          (sp + 18446744073709551600#64).toNat s0)
        r.toNat 0#64) (r + 8#64).toNat 0#64) (r + 16#64).toNat 0#64)
        (r + 24#64).toNat 0#64) (r + 32#64).toNat 0#64)
        (r + 40#64).toNat 0#64) (r + 48#64).toNat 0#64)
        (r + 56#64).toNat 0#64) u n = words m u n := by
  interval_cases n <;>
    simp (disch := first | bv_omega | fail) only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd, memWord_memStore_of_ne]

/-- The end of the path of `udivrem_by1()` in `udivrem<256, 256>()` from 0x184: the store of the
remainder in a0 above the quotient. -/
theorem u256_by1_ret {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hr : x.get 1#5 &&& 3 = 0) (hrn : (x.get 10#5).toNat + 64 ≤ 2 ^ 64)
    (hsn : (x.get 2#5 - 48#64).toNat + 48 ≤ 2 ^ 64)
    (hdsr : (x.get 2#5 - 48#64).toNat + 48 ≤ (x.get 10#5).toNat ∨
      (x.get 10#5).toNat + 64 ≤ (x.get 2#5 - 48#64).toNat)
    (x3 : Regs) (m3 : Mem) (h8 : x3.get 8#5 = x.get 10#5)
    (h2 : x3.get 2#5 = x.get 2#5 + 18446744073709551600#64)
    (hcs : ∀ i ∈ calleeSaved, i ≠ 2#5 → i ≠ 8#5 → x3 i = x i)
    (hra : memWord m3 (x.get 2#5 + 18446744073709551608#64).toNat = x.get 1#5)
    (hs0 : memWord m3 (x.get 2#5 + 18446744073709551600#64).toNat = x.get 8#5)
    (hm : UnchangedExcept2 m m3 (x.get 10#5) 64 (x.get 2#5 - 48#64) 48)
    (hz5 : memWord m3 (x.get 10#5 + 40#64).toNat = 0#64)
    (hz6 : memWord m3 (x.get 10#5 + 48#64).toNat = 0#64)
    (hz7 : memWord m3 (x.get 10#5 + 56#64).toNat = 0#64)
    (hq : words m3 (x.get 10#5) 4 = words m (x.get 11#5) 4 / words m (x.get 12#5) 4)
    (hv : words m (x.get 12#5) 4 ≠ 0)
    (hrem : (x3.get 10#5).toNat = words m (x.get 11#5) 4 % words m (x.get 12#5) 4) :
    Reach (bufWords (x.get 11#5) 4 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 8 ++
        bufWords (x.get 2#5 - 48#64) 6 ++ D) P256 base (pcAt base 97) x3 m3
      (x.get 1#5)
      (udivrem_256.post x m) := by
  rw [← h8]
  rv_exec_cut 7
  simp only [BitVec.reduceSignExtend, h8]
  refine u256_epi base x m hr _ _ h2 ?_ ?_ hcs ?_ ?_ ?_
  · rw [memWord_memStore_of_ne _ _ _ _ (by bv_omega)]
    exact hra
  · rw [memWord_memStore_of_ne _ _ _ _ (by bv_omega)]
    exact hs0
  · simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
    exact hm
  · rw [← hq]
    simp (disch := first | bv_omega | fail) only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd, memWord_memStore_of_ne]
  · rw [if_neg hv, ← hrem]
    simp (disch := first | bv_omega | fail) only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd, memWord_memStore_of_ne, memWord_memStore_self, hz5, hz6, hz7,
      BitVec.toNat_zero, Nat.mul_zero, Nat.add_zero]

/-- The memory after the call of `udivrem_by1()` in `udivrem<256, 256>()`, which writes `Q` words of
the quotient over the zeros of the result. -/
theorem u256_by1_mem (m m3 : Mem) (r sp ra s0 : BitVec 64) (Q : Nat) (hQ : 2 ≤ Q ∧ Q ≤ 4)
    (hrn : r.toNat + 64 ≤ 2 ^ 64) (hsn : (sp - 48#64).toNat + 48 ≤ 2 ^ 64)
    (hdsr : (sp - 48#64).toNat + 48 ≤ r.toNat ∨ r.toNat + 64 ≤ (sp - 48#64).toNat)
    (hunc : UnchangedExcept (memStore (memStore (memStore (memStore (memStore (memStore
        (memStore (memStore
        (memStore (memStore m (sp + 18446744073709551608#64).toNat ra)
          (sp + 18446744073709551600#64).toNat s0)
        (r + 32#64).toNat 0#64) (r + 40#64).toNat 0#64) (r + 48#64).toNat 0#64)
        (r + 56#64).toNat 0#64) r.toNat 0#64)
        (r + 8#64).toNat 0#64) (r + 16#64).toNat 0#64)
        (r + 24#64).toNat 0#64) m3 r (8 * Q)) :
    memWord m3 (sp + 18446744073709551608#64).toNat = ra ∧
      memWord m3 (sp + 18446744073709551600#64).toNat = s0 ∧
      UnchangedExcept2 m m3 r 64 (sp - 48#64) 48 ∧
      memWord m3 (r + 40#64).toNat = 0#64 ∧ memWord m3 (r + 48#64).toNat = 0#64 ∧
      memWord m3 (r + 56#64).toNat = 0#64 ∧ words m3 r 4 = words m3 r Q := by
  have hz : ∀ k, Q ≤ k → k < 8 → memWord m3 (r + BitVec.ofNat 64 (8 * k)).toNat = 0#64 := by
    intro k hk hk8
    have hrk : (r + BitVec.ofNat 64 (8 * k)).toNat = r.toNat + 8 * k := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8 * k < 2 ^ 64)]
      exact Nat.mod_eq_of_lt (by omega)
    rw [memWord_of_unchangedExcept hunc _ (by omega)]
    obtain ⟨hQ2, hQ4⟩ := hQ
    interval_cases k <;> interval_cases Q <;> first | omega |
      simp (disch := first | bv_omega | fail) only [Nat.reduceMul,
        memWord_memStore_of_ne, memWord_memStore_self]
  refine ⟨?_, ?_, ?_, hz 5 (by omega) (by omega), hz 6 (by omega) (by omega),
    hz 7 (by omega) (by omega), ?_⟩
  · rw [memWord_of_unchangedExcept hunc _ (by bv_omega)]
    simp (disch := first | bv_omega | fail) only [memWord_memStore_of_ne, memWord_memStore_self]
  · rw [memWord_of_unchangedExcept hunc _ (by bv_omega)]
    simp (disch := first | bv_omega | fail) only [memWord_memStore_of_ne, memWord_memStore_self]
  · refine UnchangedExcept2.trans2 ?_ (unchangedExcept2_of (sp - 48#64) 0 hunc) (by omega)
      (by omega)
    simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
    exact unchangedExcept2_refl _ _ _ _ _
  · have z2 := hz 2
    have z3 := hz 3
    simp only [Nat.reduceMul] at z2 z3
    obtain ⟨hQ2, hQ4⟩ := hQ
    interval_cases Q
    · simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
        z2 (by omega) (by omega), z3 (by omega) (by omega), BitVec.toNat_zero, Nat.mul_zero,
        Nat.add_zero]
    · simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
        z3 (by omega) (by omega), BitVec.toNat_zero, Nat.mul_zero, Nat.add_zero]
    · rfl

/-- The words of u at the call of `udivrem_by1()` in `udivrem<256, 256>()`. -/
theorem u256_by1_u (m : Mem) (r sp ra s0 u : BitVec 64) (n : Nat) (hn : n ≤ 4)
    (hrn : r.toNat + 64 ≤ 2 ^ 64) (hun : u.toNat + 32 ≤ 2 ^ 64)
    (hdru : r.toNat + 64 ≤ u.toNat ∨ u.toNat + 32 ≤ r.toNat)
    (hdsu : (sp - 48#64).toNat + 48 ≤ u.toNat ∨ u.toNat + 32 ≤ (sp - 48#64).toNat)
    (hsn : (sp - 48#64).toNat + 48 ≤ 2 ^ 64) :
    words (memStore (memStore (memStore (memStore (memStore (memStore (memStore (memStore
        (memStore (memStore m (sp + 18446744073709551608#64).toNat ra)
          (sp + 18446744073709551600#64).toNat s0)
        (r + 32#64).toNat 0#64) (r + 40#64).toNat 0#64) (r + 48#64).toNat 0#64)
        (r + 56#64).toNat 0#64) r.toNat 0#64)
        (r + 8#64).toNat 0#64) (r + 16#64).toNat 0#64)
        (r + 24#64).toNat 0#64) u n = words m u n := by
  interval_cases n <;>
    simp (disch := first | bv_omega | fail) only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd, memWord_memStore_of_ne]

/-- The words of a buffer at an offset of `k` words are in a buffer at the address. -/
theorem mem_bufWords_of_offset {a b : BitVec 64} {k n n' : Nat} (h : k + n ≤ n')
    (hb : b ∈ bufWords (a + BitVec.ofNat 64 (8 * k)) n) : b ∈ bufWords a n' := by
  obtain ⟨i, hi, rfl⟩ := exists_of_mem_bufWords hb
  rw [BitVec.add_assoc, show BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 (8 * i) =
    BitVec.ofNat 64 (8 * (k + i)) by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega]
  exact mem_bufWords (by omega)

/-- The words of an argument of `udivrem<256, 256>()` are outside its frame of 16 bytes. -/
theorem u256_frame_words (m : Mem) (sp ra s0 u : BitVec 64) (hun : u.toNat + 32 ≤ 2 ^ 64)
    (hdsu : (sp - 48#64).toNat + 48 ≤ u.toNat ∨ u.toNat + 32 ≤ (sp - 48#64).toNat)
    (hsn : (sp - 48#64).toNat + 48 ≤ 2 ^ 64) :
    words (memStore (memStore m (sp + 18446744073709551608#64).toNat ra)
      (sp + 18446744073709551600#64).toNat s0) u 4 = words m u 4 := by
  simp (disch := first | bv_omega | fail) only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
    BitVec.reduceAdd, memWord_memStore_of_ne]

/-- The frame of `udivrem<256, 256>()` after a call that changes the result and `fl` bytes of the
stack at `fb` below the frame. -/
theorem u256_top_mem (m m3 : Mem) (r sp ra s0 fb : BitVec 64) (fl : Nat)
    (hrn : r.toNat + 64 ≤ 2 ^ 64) (hsn : (sp - 48#64).toNat + 48 ≤ 2 ^ 64)
    (hdsr : (sp - 48#64).toNat + 48 ≤ r.toNat ∨ r.toNat + 64 ≤ (sp - 48#64).toNat)
    (hfb : (sp - 48#64).toNat ≤ fb.toNat ∧ fb.toNat + fl ≤ (sp - 48#64).toNat + 32)
    (hunc : UnchangedExcept2 (memStore (memStore m (sp + 18446744073709551608#64).toNat ra)
      (sp + 18446744073709551600#64).toNat s0) m3 r 64 fb fl) :
    memWord m3 (sp + 18446744073709551608#64).toNat = ra ∧
      memWord m3 (sp + 18446744073709551600#64).toNat = s0 ∧
      UnchangedExcept2 m m3 r 64 (sp - 48#64) 48 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [memWord_of_unchangedExcept2 hunc _ (by bv_omega) (by bv_omega)]
    simp (disch := first | bv_omega | fail) only [memWord_memStore_of_ne, memWord_memStore_self]
  · rw [memWord_of_unchangedExcept2 hunc _ (by bv_omega) (by bv_omega)]
    simp only [memWord_memStore_self]
  · refine UnchangedExcept2.trans2 ?_ hunc (by omega) (by omega)
    simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
    exact unchangedExcept2_refl _ _ _ _ _

theorem words4_unfold (m : Mem) (a : BitVec 64) :
    words m a 4 = (memWord m a.toNat).toNat + 2 ^ 64 * ((memWord m (a + 8#64).toNat).toNat +
      2 ^ 64 * ((memWord m (a + 16#64).toNat).toNat +
      2 ^ 64 * (memWord m (a + 24#64).toNat).toNat)) := by
  simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
    Nat.add_zero]

/-- The values of the arguments of `udivrem_top1<3>()` in `udivrem<256, 256>()`. -/
theorem u256_top13_vals (m : Mem) (u v : BitVec 64) (hv3 : memWord m (v + 24#64).toNat ≠ 0#64) :
    2 ^ (64 * 3) ≤ words m v 4 ∧ words m v 4 < 2 ^ (64 * (3 + 1)) ∧
      words m u 4 / 2 ^ (64 * (3 + 1)) < words m v 4 / 2 ^ (64 * 3) := by
  have h3 : 0 < (memWord m (v + 24#64).toNat).toNat := by
    rcases Nat.eq_zero_or_pos (memWord m (v + 24#64).toNat).toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hv3
    · exact h
  rw [words4_unfold, words4_unfold]
  have := (memWord m u.toNat).isLt
  have := (memWord m (u + 8#64).toNat).isLt
  have := (memWord m (u + 16#64).toNat).isLt
  have := (memWord m (u + 24#64).toNat).isLt
  have := (memWord m v.toNat).isLt
  have := (memWord m (v + 8#64).toNat).isLt
  have := (memWord m (v + 16#64).toNat).isLt
  have := (memWord m (v + 24#64).toNat).isLt
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd] at *
  omega

/-- The values of the arguments of `udivrem_top1<2>()` in `udivrem<256, 256>()`. -/
theorem u256_top12_vals (m : Mem) (u v : BitVec 64) (hv3 : memWord m (v + 24#64).toNat = 0#64)
    (hv2 : memWord m (v + 16#64).toNat ≠ 0#64)
    (hu3 : memWord m (u + 24#64).toNat < memWord m (v + 16#64).toNat) :
    2 ^ (64 * 2) ≤ words m v 4 ∧ words m v 4 < 2 ^ (64 * (2 + 1)) ∧
      words m u 4 / 2 ^ (64 * (2 + 1)) < words m v 4 / 2 ^ (64 * 2) := by
  have h2 : 0 < (memWord m (v + 16#64).toNat).toNat := by
    rcases Nat.eq_zero_or_pos (memWord m (v + 16#64).toNat).toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hv2
    · exact h
  rw [BitVec.lt_def] at hu3
  rw [words4_unfold, words4_unfold, hv3]
  have := (memWord m u.toNat).isLt
  have := (memWord m (u + 8#64).toNat).isLt
  have := (memWord m (u + 16#64).toNat).isLt
  have := (memWord m (u + 24#64).toNat).isLt
  have := (memWord m v.toNat).isLt
  have := (memWord m (v + 8#64).toNat).isLt
  have := (memWord m (v + 16#64).toNat).isLt
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, BitVec.toNat_zero] at *
  omega

/-- The values of the arguments of `udivrem_top2<3>()` in `udivrem<256, 256>()`. -/
theorem u256_top23_vals (m : Mem) (u v : BitVec 64) (hv3 : memWord m (v + 24#64).toNat = 0#64)
    (hv2 : memWord m (v + 16#64).toNat ≠ 0#64) :
    2 ^ (64 * (3 - 1)) ≤ words m v 4 ∧ words m v 4 < 2 ^ (64 * 3) ∧
      words m u 4 / 2 ^ (64 * (3 + 1)) < words m v 4 / 2 ^ (64 * (3 - 1)) + 0 := by
  have h2 : 0 < (memWord m (v + 16#64).toNat).toNat := by
    rcases Nat.eq_zero_or_pos (memWord m (v + 16#64).toNat).toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hv2
    · exact h
  rw [words4_unfold, words4_unfold, hv3]
  have := (memWord m u.toNat).isLt
  have := (memWord m (u + 8#64).toNat).isLt
  have := (memWord m (u + 16#64).toNat).isLt
  have := (memWord m (u + 24#64).toNat).isLt
  have := (memWord m v.toNat).isLt
  have := (memWord m (v + 8#64).toNat).isLt
  have := (memWord m (v + 16#64).toNat).isLt
  simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, BitVec.toNat_zero] at *
  omega

/-- The path of `udivrem<256, 256>()` for v ≥ 2^192 from 0x14: the call of `udivrem_top1<3>()`. -/
theorem u256_top13 {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hb3 : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0) (hpre : udivrem_256.pre x m)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64)
    (hTs : (x.get 2#5 - 48#64).toNat + 48 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 48#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data)
    (hD : ∀ a ∈ bufWords T 256, a ∈ D)
    (hT3 : pcAt (pcAt base 824) 75 + ((hi3 ++ 0x000#12).signExtend 64 +
      lo3.signExtend 64) = T)
    (x' : Regs) (h10 : x'.get 10#5 = x.get 10#5) (h11 : x'.get 11#5 = x.get 11#5)
    (h12 : x'.get 12#5 = x.get 12#5) (h2 : x'.get 2#5 = x.get 2#5 + 18446744073709551600#64)
    (hcs : ∀ i ∈ calleeSaved, i ≠ 2#5 → i ≠ 8#5 → x' i = x i)
    (hv3 : memWord m (x.get 12#5 + 24#64).toNat ≠ 0#64) :
    Reach (bufWords (x.get 11#5) 4 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 8 ++
        bufWords (x.get 2#5 - 48#64) 6 ++ D) P256 base (pcAt base 5) x'
      (memStore (memStore m (x.get 2#5 + 18446744073709551608#64).toNat (x.get 1#5))
        (x.get 2#5 + 18446744073709551600#64).toNat (x.get 8#5))
      (x.get 1#5) (udivrem_256.post x m) := by
  -- `omega` and `subst_vars` do not see the address of the table.
  replace hT3 := PLift.up hT3
  simp only [udivrem_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr⟩ := hpre
  have hv := u256_top13_vals m (x.get 11#5) (x.get 12#5) hv3
  have hvne : words m (x.get 12#5) 4 ≠ 0 := by
    have h := hv.1; intro h0; rw [h0] at h; exact absurd h (by norm_num)
  have eu := u256_frame_words m (x.get 2#5) (x.get 1#5) (x.get 8#5) (x.get 11#5) hun hdsu hsn
  have ev := u256_frame_words m (x.get 2#5) (x.get 1#5) (x.get 8#5) (x.get 12#5) hvn hdsv hsn
  have hsub : x.get 2#5 + 18446744073709551600#64 - 16#64 = x.get 2#5 - 32#64 := by bv_omega
  rv_exec_cut 824
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  rw [show pcAt base 5 + 4096#64 + BitVec.signExtend 64 3276#12 = pcAt base 824 by
      simp only [pcAt, BitVec.reduceSignExtend]; bv_omega,
    update_aligned (by simp only [pcAt]; exact aligned_add hb3 (by decide))]
  refine Reach.call_sub (r := 7) udivrem_256_progAt_udivrem_top1_3_in
    (by rw [udivrem_256_progAt_length]; decide)
    (udivrem_top1_3.reach hi3 lo3 (pcAt base 824) T _ _ hT3.down ?_ ?_ ?_ ?_ ?_)
    ?_ ?_ ?_
  · omega
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    simp only [pcAt]; exact aligned_add hb3 (by decide)
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    rw [h2, hsub]
    bv_omega
  · simp (disch := first | bv_omega | fail) only [holdsData_table_memStore]
    exact hhold
  · simp only [udivrem_top1_3.pre, Buf, Disjoint]
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    simp (disch := decide) only [Regs.eq_get x']
    simp only [h10, h11, h12, h2, hsub, eu, ev]
    repeat' apply And.intro
    all_goals first | exact hv.1 | exact hv.2.1 | exact hv.2.2 | omega | bv_omega
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · intro a ha
    simp only [udivrem_top1_3.bufs] at ha
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at ha
    simp (disch := decide) only [Regs.eq_get x'] at ha
    simp only [h10, h11, h12, h2, hsub, List.mem_append] at ha
    simp only [List.mem_append]
    rcases ha with ((((h | h) | h) | h) | h)
    · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    · exact Or.inl (Or.inl (Or.inr h))
    · rw [show x.get 2#5 - 32#64 = x.get 2#5 - 48#64 + BitVec.ofNat 64 (8 * 2) by bv_omega] at h
      exact Or.inl (Or.inr (mem_bufWords_of_offset (by decide) h))
    · exact Or.inr (hD _ h)
  · intro x3 m3 hpost
    obtain ⟨hq, hrem, hunc, hsaved⟩ := hpost
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at hq hrem hunc
    simp (disch := decide) only [Regs.eq_get x'] at hq hrem hunc
    simp only [h10, h11, h12, h2, hsub, eu, ev] at hq hrem hunc
    obtain ⟨hra3, hs03, hm3⟩ := u256_top_mem m m3 (x.get 10#5) (x.get 2#5) (x.get 1#5) (x.get 8#5)
      (x.get 2#5 - 32#64) 16 hrn hsn hdsr (by bv_omega) hunc
    have h23 : x3.get 2#5 = x.get 2#5 + 18446744073709551600#64 := by
      rw [← Regs.eq_get x3 (by decide), hsaved 2#5 (by decide)]
      simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
      rw [Regs.eq_get x' (by decide)]; exact h2
    have hcs3 : ∀ i ∈ calleeSaved, i ≠ 2#5 → i ≠ 8#5 → x3 i = x i := by
      intro i hi h2i h8i
      rw [hsaved i hi]
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] <;>
        first
          | exact hcs _ (by decide) (by decide) (by decide)
          | exact absurd rfl h2i
          | exact absurd rfl h8i
    exact u256_epi base x m hr x3 m3 h23 hra3 hs03 hcs3 hm3 hq (by rw [if_neg hvne]; exact hrem)

/-- The path of `udivrem<256, 256>()` for 2^128 ≤ v < 2^192 and u[3] < v[2] from 0x3c: the call of
`udivrem_top1<2>()`. -/
theorem u256_top12 {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hb3 : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0) (hpre : udivrem_256.pre x m)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64)
    (hTs : (x.get 2#5 - 48#64).toNat + 48 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 48#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data)
    (hD : ∀ a ∈ bufWords T 256, a ∈ D)
    (hT2 : pcAt (pcAt base 615) 89 + ((hi2 ++ 0x000#12).signExtend 64 +
      lo2.signExtend 64) = T)
    (x' : Regs) (h10 : x'.get 10#5 = x.get 10#5) (h11 : x'.get 11#5 = x.get 11#5)
    (h12 : x'.get 12#5 = x.get 12#5) (h2 : x'.get 2#5 = x.get 2#5 + 18446744073709551600#64)
    (hcs : ∀ i ∈ calleeSaved, i ≠ 2#5 → i ≠ 8#5 → x' i = x i)
    (hv3 : memWord m (x.get 12#5 + 24#64).toNat = 0#64)
    (hv2 : memWord m (x.get 12#5 + 16#64).toNat ≠ 0#64)
    (hu3 : memWord m (x.get 11#5 + 24#64).toNat < memWord m (x.get 12#5 + 16#64).toNat) :
    Reach (bufWords (x.get 11#5) 4 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 8 ++
        bufWords (x.get 2#5 - 48#64) 6 ++ D) P256 base (pcAt base 15) x'
      (memStore (memStore m (x.get 2#5 + 18446744073709551608#64).toNat (x.get 1#5))
        (x.get 2#5 + 18446744073709551600#64).toNat (x.get 8#5))
      (x.get 1#5) (udivrem_256.post x m) := by
  -- `omega` and `subst_vars` do not see the address of the table.
  replace hT2 := PLift.up hT2
  simp only [udivrem_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr⟩ := hpre
  have hv := u256_top12_vals m (x.get 11#5) (x.get 12#5) hv3 hv2 hu3
  have hvne : words m (x.get 12#5) 4 ≠ 0 := by
    have h := hv.1; intro h0; rw [h0] at h; exact absurd h (by norm_num)
  have eu := u256_frame_words m (x.get 2#5) (x.get 1#5) (x.get 8#5) (x.get 11#5) hun hdsu hsn
  have ev := u256_frame_words m (x.get 2#5) (x.get 1#5) (x.get 8#5) (x.get 12#5) hvn hdsv hsn
  have hsub : x.get 2#5 + 18446744073709551600#64 - 16#64 = x.get 2#5 - 32#64 := by bv_omega
  rv_exec_cut 615
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  rw [show pcAt base 15 + 4096#64 + BitVec.signExtend 64 2400#12 = pcAt base 615 by
      simp only [pcAt, BitVec.reduceSignExtend]; bv_omega,
    update_aligned (by simp only [pcAt]; exact aligned_add hb3 (by decide))]
  refine Reach.call_sub (r := 17) udivrem_256_progAt_udivrem_top1_2_in
    (by rw [udivrem_256_progAt_length]; decide)
    (udivrem_top1_2.reach hi2 lo2 (pcAt base 615) T _ _ hT2.down ?_ ?_ ?_ ?_ ?_)
    ?_ ?_ ?_
  · omega
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    simp only [pcAt]; exact aligned_add hb3 (by decide)
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    rw [h2, hsub]
    bv_omega
  · simp (disch := first | bv_omega | fail) only [holdsData_table_memStore]
    exact hhold
  · simp only [udivrem_top1_2.pre, Buf, Disjoint]
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    simp (disch := decide) only [Regs.eq_get x']
    simp only [h10, h11, h12, h2, hsub, eu, ev]
    repeat' apply And.intro
    all_goals first | exact hv.1 | exact hv.2.1 | exact hv.2.2 | omega | bv_omega
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · intro a ha
    simp only [udivrem_top1_2.bufs] at ha
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at ha
    simp (disch := decide) only [Regs.eq_get x'] at ha
    simp only [h10, h11, h12, h2, hsub, List.mem_append] at ha
    simp only [List.mem_append]
    rcases ha with ((((h | h) | h) | h) | h)
    · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    · exact Or.inl (Or.inl (Or.inr h))
    · rw [show x.get 2#5 - 32#64 = x.get 2#5 - 48#64 + BitVec.ofNat 64 (8 * 2) by bv_omega] at h
      exact Or.inl (Or.inr (mem_bufWords_of_offset (by decide) h))
    · exact Or.inr (hD _ h)
  · intro x3 m3 hpost
    obtain ⟨hq, hrem, hunc, hsaved⟩ := hpost
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at hq hrem hunc
    simp (disch := decide) only [Regs.eq_get x'] at hq hrem hunc
    simp only [h10, h11, h12, h2, hsub, eu, ev] at hq hrem hunc
    obtain ⟨hra3, hs03, hm3⟩ := u256_top_mem m m3 (x.get 10#5) (x.get 2#5) (x.get 1#5) (x.get 8#5)
      (x.get 2#5 - 32#64) 16 hrn hsn hdsr (by bv_omega) hunc
    have h23 : x3.get 2#5 = x.get 2#5 + 18446744073709551600#64 := by
      rw [← Regs.eq_get x3 (by decide), hsaved 2#5 (by decide)]
      simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
      rw [Regs.eq_get x' (by decide)]; exact h2
    have hcs3 : ∀ i ∈ calleeSaved, i ≠ 2#5 → i ≠ 8#5 → x3 i = x i := by
      intro i hi h2i h8i
      rw [hsaved i hi]
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] <;>
        first
          | exact hcs _ (by decide) (by decide) (by decide)
          | exact absurd rfl h2i
          | exact absurd rfl h8i
    rv_exec_cut 7
    exact u256_epi base x m hr x3 m3 h23 hra3 hs03 hcs3 hm3 hq (by rw [if_neg hvne]; exact hrem)

/-- The path of `udivrem<256, 256>()` for 2^128 ≤ v < 2^192 and u[3] ≥ v[2] from 0x64: the call of
`udivrem_top2<3>()`. -/
theorem u256_top23 {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hb3 : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0) (hpre : udivrem_256.pre x m)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64)
    (hTs : (x.get 2#5 - 48#64).toNat + 48 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 48#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data)
    (hD : ∀ a ∈ bufWords T 256, a ∈ D)
    (hT4 : pcAt (pcAt base 1033) 85 + ((hi4 ++ 0x000#12).signExtend 64 +
      lo4.signExtend 64) = T)
    (x' : Regs) (h10 : x'.get 10#5 = x.get 10#5) (h11 : x'.get 11#5 = x.get 11#5)
    (h12 : x'.get 12#5 = x.get 12#5) (h2 : x'.get 2#5 = x.get 2#5 + 18446744073709551600#64)
    (hcs : ∀ i ∈ calleeSaved, i ≠ 2#5 → i ≠ 8#5 → x' i = x i)
    (hv3 : memWord m (x.get 12#5 + 24#64).toNat = 0#64)
    (hv2 : memWord m (x.get 12#5 + 16#64).toNat ≠ 0#64) :
    Reach (bufWords (x.get 11#5) 4 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 8 ++
        bufWords (x.get 2#5 - 48#64) 6 ++ D) P256 base (pcAt base 25) x'
      (memStore (memStore m (x.get 2#5 + 18446744073709551608#64).toNat (x.get 1#5))
        (x.get 2#5 + 18446744073709551600#64).toNat (x.get 8#5))
      (x.get 1#5) (udivrem_256.post x m) := by
  -- `omega` and `subst_vars` do not see the address of the table.
  replace hT4 := PLift.up hT4
  simp only [udivrem_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr⟩ := hpre
  have hv := u256_top23_vals m (x.get 11#5) (x.get 12#5) hv3 hv2
  have hvne : words m (x.get 12#5) 4 ≠ 0 := by
    have h := hv.1; intro h0; rw [h0] at h; exact absurd h (by norm_num)
  have eu := u256_frame_words m (x.get 2#5) (x.get 1#5) (x.get 8#5) (x.get 11#5) hun hdsu hsn
  have ev := u256_frame_words m (x.get 2#5) (x.get 1#5) (x.get 8#5) (x.get 12#5) hvn hdsv hsn
  have hsub : x.get 2#5 + 18446744073709551600#64 - 32#64 = x.get 2#5 - 48#64 := by bv_omega
  rv_exec_cut 1033
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  rw [show pcAt base 25 + 4096#64 + BitVec.signExtend 64 4032#12 = pcAt base 1033 by
      simp only [pcAt, BitVec.reduceSignExtend]; bv_omega,
    update_aligned (by simp only [pcAt]; exact aligned_add hb3 (by decide))]
  refine Reach.call_sub (r := 27) udivrem_256_progAt_udivrem_top2_3_in
    (by rw [udivrem_256_progAt_length]; decide)
    (udivrem_top2_3.reach hi4 lo4 (pcAt base 1033) T _ _ hT4.down ?_ ?_ ?_ ?_ ?_)
    ?_ ?_ ?_
  · omega
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    simp only [pcAt]; exact aligned_add hb3 (by decide)
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    rw [h2, hsub]
    bv_omega
  · simp (disch := first | bv_omega | fail) only [holdsData_table_memStore]
    exact hhold
  · simp only [udivrem_top2_3.pre, Buf, Disjoint]
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    simp (disch := decide) only [Regs.eq_get x']
    simp only [h10, h11, h12, h2, hsub, eu, ev]
    repeat' apply And.intro
    all_goals first | exact hv.1 | exact hv.2.1 | exact hv.2.2 | omega | bv_omega
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · intro a ha
    simp only [udivrem_top2_3.bufs] at ha
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at ha
    simp (disch := decide) only [Regs.eq_get x'] at ha
    simp only [h10, h11, h12, h2, hsub, List.mem_append] at ha
    simp only [List.mem_append]
    rcases ha with ((((h | h) | h) | h) | h)
    · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr (mem_bufWords_of_le (by decide) h))
    · exact Or.inr (hD _ h)
  · intro x3 m3 hpost
    obtain ⟨hq, hrem, hunc, hsaved⟩ := hpost
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at hq hrem hunc
    simp (disch := decide) only [Regs.eq_get x'] at hq hrem hunc
    simp only [h10, h11, h12, h2, hsub, eu, ev] at hq hrem hunc
    obtain ⟨hra3, hs03, hm3⟩ := u256_top_mem m m3 (x.get 10#5) (x.get 2#5) (x.get 1#5) (x.get 8#5)
      (x.get 2#5 - 48#64) 32 hrn hsn hdsr (by bv_omega) hunc
    have h23 : x3.get 2#5 = x.get 2#5 + 18446744073709551600#64 := by
      rw [← Regs.eq_get x3 (by decide), hsaved 2#5 (by decide)]
      simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
      rw [Regs.eq_get x' (by decide)]; exact h2
    have hcs3 : ∀ i ∈ calleeSaved, i ≠ 2#5 → i ≠ 8#5 → x3 i = x i := by
      intro i hi h2i h8i
      rw [hsaved i hi]
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] <;>
        first
          | exact hcs _ (by decide) (by decide) (by decide)
          | exact absurd rfl h2i
          | exact absurd rfl h8i
    rv_exec_cut 7
    exact u256_epi base x m hr x3 m3 h23 hra3 hs03 hcs3 hm3 hq (by rw [if_neg hvne]; exact hrem)

/-- The branch of `udivrem<256, 256>()` on `bgeu`. -/
theorem zopz0zKzJ_u_eq (a b : BitVec 64) :
    LeanRV64D.Functions.zopz0zKzJ_u a b = decide (b ≤ a) := by
  simp [LeanRV64D.Functions.zopz0zKzJ_u, Sail.BitVec.toNatInt, BitVec.le_def]

/-- `snez` of a word that a branch has tested. -/
theorem ite_zero_lt_of_ne {w a b : BitVec 64} (h : ¬w = 0#64) :
    (if 0#64 < w then a else b) = a := if_pos (by bv_omega)

theorem ite_zero_lt_of_eq {w a b : BitVec 64} (h : w = 0#64) :
    (if 0#64 < w then a else b) = b := if_neg (by subst h; decide)

theorem words4_zero (m : Mem) (a : BitVec 64) (h0 : memWord m a.toNat = 0#64)
    (h1 : memWord m (a + 8#64).toNat = 0#64) (h2 : memWord m (a + 16#64).toNat = 0#64)
    (h3 : memWord m (a + 24#64).toNat = 0#64) : words m a 4 = 0 := by
  rw [words4_unfold, h0, h1, h2, h3]; rfl

set_option hygiene false in
/-- The registers at a call in `udivrem<256, 256>()` from the registers `x'` of the path: the
ones that the path sets, the others by `hcs`. -/
macro "u256_regs" : tactic => `(tactic| (
  all_goals first
    | (intro i hi h2i h8i
       simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
       rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
         rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] <;>
         first
           | exact hcs _ (by decide) (by decide) (by decide)
           | exact absurd rfl h2i
           | exact absurd rfl h8i)
    | (simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, Nat.reduceAdd,
          true_implies, false_implies] <;>
         first | with_reducible rfl | with_reducible assumption)
    | with_reducible assumption))

end IntxRV.Api
