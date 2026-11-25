import IntxRV.Gen.Api.udivrem_by2
import IntxRV.DivShared
import IntxRV.Arith
import IntxRV.Div3by2
import IntxRV.Loop
import IntxRV.Recip3
import IntxRV.DivBy1
/-!
# The division of a span by two words

The lemmas of the proof of `internal::udivrem_by2()` (`IntxRV/Api/udivrem_by2.lean`). The code
inlines `udivrem_3by2()` three times: for the top digits, in the loop and for the last digit, with
the products in other orders than `udivrem_3by2()` itself (`div3by2BVo`). Each copy branches to
select the remainder and for the rare correction; `by2_div_top`, `by2_div_loop` and `by2_div_last`
run its paths to its end (`by2_div3_paths`), so that the proof of the function runs each copy as
one step (`Reach.trans`).
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
-- The guards that select the paths do not change the goals.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- The inlined `udivrem_3by2()` of the top digits of `udivrem_by2()`, from 0x2a4 to 0x318:
`a5:t5:t2` by `t1:t0` with the reciprocal in a1, to the quotient in a5 and the remainder in
`t4:t2`. -/
theorem by2_div_top {A : List (BitVec 64)} {hi : BitVec 20} {lo : BitVec 12} (base : BitVec 64)
    (x : Regs) (m : Mem)
    (hd : 2 ^ 127 ≤ (x.get 5#5).toNat + 2 ^ 64 * (x.get 6#5).toNat)
    (hu : (x.get 15#5).toNat * 2 ^ 64 + (x.get 30#5).toNat <
      (x.get 5#5).toNat + 2 ^ 64 * (x.get 6#5).toNat)
    (hv : (x.get 11#5).toNat =
      (2 ^ 192 - 1) / ((x.get 5#5).toNat + 2 ^ 64 * (x.get 6#5).toNat) - 2 ^ 64) :
    Reach A (udivrem_by2_progAt hi lo) base (pcAt base 169) x m (pcAt base 198) (fun x' m' =>
      m' = m ∧ Div3Out x x' ((x.get 15#5).toNat * 2 ^ 128 + (x.get 30#5).toNat * 2 ^ 64 +
        (x.get 7#5).toNat) ((x.get 5#5).toNat + 2 ^ 64 * (x.get 6#5).toNat) 15#5 7#5 29#5
        [7#5, 8#5, 9#5, 15#5, 29#5, 30#5, 31#5]) := by
  by2_div3_paths div3by2BVo_spec false (x.get 15#5) (x.get 30#5) (x.get 7#5) (x.get 5#5)
    (x.get 6#5) (x.get 11#5) hd hu hv

/-- The inlined `udivrem_3by2()` of the loop of `udivrem_by2()`, from 0x358 to 0x3cc: `t4:t2:t6`
by `t1:t0` with the reciprocal in a1, to the quotient in t5 and the remainder in `t4:t2`. -/
theorem by2_div_loop {A : List (BitVec 64)} {hi : BitVec 20} {lo : BitVec 12} (base : BitVec 64)
    (x : Regs) (m : Mem)
    (hd : 2 ^ 127 ≤ (x.get 5#5).toNat + 2 ^ 64 * (x.get 6#5).toNat)
    (hu : (x.get 29#5).toNat * 2 ^ 64 + (x.get 7#5).toNat <
      (x.get 5#5).toNat + 2 ^ 64 * (x.get 6#5).toNat)
    (hv : (x.get 11#5).toNat =
      (2 ^ 192 - 1) / ((x.get 5#5).toNat + 2 ^ 64 * (x.get 6#5).toNat) - 2 ^ 64) :
    Reach A (udivrem_by2_progAt hi lo) base (pcAt base 214) x m (pcAt base 243) (fun x' m' =>
      m' = m ∧ Div3Out x x' ((x.get 29#5).toNat * 2 ^ 128 + (x.get 7#5).toNat * 2 ^ 64 +
        (x.get 31#5).toNat) ((x.get 5#5).toNat + 2 ^ 64 * (x.get 6#5).toNat) 30#5 7#5 29#5
        [7#5, 8#5, 9#5, 28#5, 29#5, 30#5, 31#5]) := by
  by2_div3_paths div3by2BVo_spec true (x.get 29#5) (x.get 7#5) (x.get 31#5) (x.get 5#5)
    (x.get 6#5) (x.get 11#5) hd hu hv

/-- The inlined `udivrem_3by2()` of the last digit of `udivrem_by2()`, from 0x404 (after the load
of `u[0]` to a2) to 0x47c: `t4:t2:(a2 << s)` by `t1:t0` with the reciprocal in a1, to the
quotient in a3 and the remainder in `a1:a2`. -/
theorem by2_div_last {A : List (BitVec 64)} {hi : BitVec 20} {lo : BitVec 12} (base : BitVec 64)
    (x : Regs) (m : Mem)
    (hd : 2 ^ 127 ≤ (x.get 5#5).toNat + 2 ^ 64 * (x.get 6#5).toNat)
    (hu : (x.get 29#5).toNat * 2 ^ 64 + (x.get 7#5).toNat <
      (x.get 5#5).toNat + 2 ^ 64 * (x.get 6#5).toNat)
    (hv : (x.get 11#5).toNat =
      (2 ^ 192 - 1) / ((x.get 5#5).toNat + 2 ^ 64 * (x.get 6#5).toNat) - 2 ^ 64)
    -- The numerator, not written with the shift that the run computes and names.
    (U : Nat) (hU : (x.get 29#5).toNat * 2 ^ 128 + (x.get 7#5).toNat * 2 ^ 64 +
      (x.get 12#5 <<< ((x.get 16#5).toNat % 64)).toNat = U) :
    Reach A (udivrem_by2_progAt hi lo) base (pcAt base 257) x m (pcAt base 287) (fun x' m' =>
      m' = m ∧ Div3Out x x' U ((x.get 5#5).toNat + 2 ^ 64 * (x.get 6#5).toNat) 13#5 12#5 11#5
        [7#5, 11#5, 12#5, 13#5, 14#5, 15#5, 28#5]) := by
  by2_div3_paths hU ▸ div3by2BV_spec (x.get 29#5) (x.get 7#5)
    (x.get 12#5 <<< ((x.get 16#5).toNat % 64)) (x.get 5#5) (x.get 6#5) (x.get 11#5) hd hu hv

/-- The byte offset of the word `i` of a buffer, `i << 3`. -/
theorem shl3_ofNat (a : BitVec 64) (_h : 8 * a.toNat < 2 ^ 64) :
    a <<< 3 = BitVec.ofNat 64 (8 * a.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

/-- The offset of the word `n - 2` of a buffer of `n` words from its end. -/
theorem off16 (n : BitVec 64) (h : 2 ≤ n.toNat) (hn : 8 * n.toNat ≤ 2 ^ 64) :
    n <<< 3 + 18446744073709551600#64 = BitVec.ofNat 64 (8 * (n.toNat - 2)) := by
  bv_omega

/-- The offset of the word `n - 3` of a buffer of `n` words from its end. -/
theorem off24 (n : BitVec 64) (h : 3 ≤ n.toNat) (hn : 8 * n.toNat ≤ 2 ^ 64) :
    n <<< 3 + 18446744073709551592#64 = BitVec.ofNat 64 (8 * (n.toNat - 3)) := by
  bv_omega

/-- A number below twice the divisor: the quotient is 0 or 1. -/
theorem div_lt_two {T D : Nat} (h : T < 2 * D) :
    T / D = (if T < D then 0 else 1) ∧ T % D = (if T < D then T else T - D) := by
  split_ifs with hl
  · exact ⟨Nat.div_eq_of_lt hl, Nat.mod_eq_of_lt hl⟩
  · have hD : 0 < D := by omega
    refine ⟨Nat.div_eq_of_lt_le (by omega) (by omega), ?_⟩
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The subtraction of the top words of `udivrem_by2()` when the top word of u is at most d1, from
0x218 to 0x258: `t5:s0` minus `a5:a4` if it is not below, the quotient word 0 or 1 in a4 and the
remainder in `t4:t2`. -/
theorem by2_sub_top {A : List (BitVec 64)} {hi : BitVec 20} {lo : BitVec 12} (base : BitVec 64)
    (x : Regs) (m : Mem) (hd : 0 < (x.get 15#5).toNat)
    (hu : (x.get 30#5).toNat ≤ (x.get 15#5).toNat) :
    Reach A (udivrem_by2_progAt hi lo) base (pcAt base 134) x m (pcAt base 150) (fun x' m' =>
      m' = m ∧ Div3Out x x' ((x.get 8#5).toNat + 2 ^ 64 * (x.get 30#5).toNat)
        ((x.get 14#5).toNat + 2 ^ 64 * (x.get 15#5).toNat) 14#5 7#5 29#5
        [7#5, 9#5, 14#5, 29#5]) := by
  have hT : (x.get 8#5).toNat + 2 ^ 64 * (x.get 30#5).toNat <
      2 * ((x.get 14#5).toNat + 2 ^ 64 * (x.get 15#5).toNat) := by
    have := (x.get 8#5).isLt; omega
  obtain ⟨hq, hr⟩ := div_lt_two hT
  rv_exec
  all_goals
    simp only [Div3Out]
    try simp only [beq_eq_false_iff_ne, bne_eq_false_iff_eq, ne_eq] at *
  -- The two tests of t5 = a5 agree.
  all_goals first
    | (rv_get he : x.get 30#5 = x.get 15#5
       rv_get hne : ¬x.get 30#5 = x.get 15#5
       exact absurd he hne)
    | skip
  all_goals
    refine ⟨by first | rfl | trivial, ?_, ?_, ?_, ?_⟩
    rotate_left 2
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp (config := { decide := true }) only [Regs.set_apply, hr, ↓reduceIte]
    all_goals
      simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      first | rw [hq] | rw [hr]
      simp only [Defn] at *
      subst_vars
      split_ifs at * <;> (try simp only [BitVec.reduceXOr] at *) <;> first | bv_omega | simp_all

/-- A word of u in the memory of the body of `udivrem_by2()`: u is outside q and the frame. -/
theorem memWord_u {m m' : Mem} {q u sp : BitVec 64} {qs n : Nat}
    (hun : UnchangedExcept2 m m' q (8 * qs) sp 32)
    (hdqu : q.toNat + 8 * qs ≤ u.toNat ∨ u.toNat + 8 * n ≤ q.toNat)
    (hdsu : sp.toNat + 32 ≤ u.toNat ∨ u.toNat + 8 * n ≤ sp.toNat)
    (hun8 : u.toNat + 8 * n ≤ 2 ^ 64) (k : Nat) (hk : k < n) :
    memWord m' (u + BitVec.ofNat 64 (8 * k)).toNat =
      memWord m (u + BitVec.ofNat 64 (8 * k)).toNat := by
  have hu8 : (u + BitVec.ofNat 64 (8 * k)).toNat = u.toNat + 8 * k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  exact memWord_of_unchangedExcept2 hun _ (by rw [hu8]; omega) (by rw [hu8]; omega)

/-- A store to q leaves the words that `udivrem_by2()` saves below its sp. -/
theorem memStore_q_stack (mm : Mem) {q sp : BitVec 64} {qs : Nat} (k : Nat) (hk : k < qs)
    (v : BitVec 64) (hq : q.toNat + 8 * qs ≤ 2 ^ 64) (hs : (sp - 32#64).toNat + 32 ≤ 2 ^ 64)
    (hd : (sp - 32#64).toNat + 32 ≤ q.toNat ∨ q.toNat + 8 * qs ≤ (sp - 32#64).toNat)
    (c : BitVec 64) (hc : c = sp + 18446744073709551608#64 ∨ c = sp + 18446744073709551600#64 ∨
      c = sp + 18446744073709551592#64) :
    memWord (memStore mm (q + BitVec.ofNat 64 (8 * k)).toNat v) c.toNat = memWord mm c.toNat := by
  apply memWord_memStore_of_ne
  rcases hc with rfl | rfl | rfl <;> bv_omega

/-- The store of q[0] leaves the words that `udivrem_by2()` saves below its sp. -/
theorem memStore_q0_stack (mm : Mem) {q sp : BitVec 64} {qs : Nat} (hk : 0 < qs)
    (v : BitVec 64) (hq : q.toNat + 8 * qs ≤ 2 ^ 64) (hs : (sp - 32#64).toNat + 32 ≤ 2 ^ 64)
    (hd : (sp - 32#64).toNat + 32 ≤ q.toNat ∨ q.toNat + 8 * qs ≤ (sp - 32#64).toNat)
    (c : BitVec 64) (hc : c = sp + 18446744073709551608#64 ∨ c = sp + 18446744073709551600#64 ∨
      c = sp + 18446744073709551592#64) :
    memWord (memStore mm q.toNat v) c.toNat = memWord mm c.toNat := by
  apply memWord_memStore_of_ne
  rcases hc with rfl | rfl | rfl <;> bv_omega

/-- The words that `udivrem_by2()` saves, at sp + 24, 16 and 8 below the sp of the call, as words of
its frame. -/
theorem frame_w3 (sp : BitVec 64) :
    sp + 18446744073709551584#64 + 24#64 = sp - 32#64 + BitVec.ofNat 64 (8 * 3) := by
  bv_omega

theorem frame_w2 (sp : BitVec 64) :
    sp + 18446744073709551584#64 + 16#64 = sp - 32#64 + BitVec.ofNat 64 (8 * 2) := by
  bv_omega

theorem frame_w1 (sp : BitVec 64) :
    sp + 18446744073709551584#64 + 8#64 = sp - 32#64 + BitVec.ofNat 64 (8 * 1) := by
  bv_omega

/-- The offset of the word `i` from the word `i - 1`. -/
theorem ofNat_sub1_add8 (i : Nat) (h : 1 ≤ i) :
    BitVec.ofNat 64 (8 * (i - 1)) + 8#64 = BitVec.ofNat 64 (8 * i) := by
  bv_omega

/-- The divisor normalized by the count of the leading zeros of its top word: at least `2^127`. -/
theorem by2_D127 (d0 d1 : BitVec 64) (hd1 : d1.toNat ≠ 0) :
    2 ^ 127 ≤ (d0.toNat + 2 ^ 64 * d1.toNat) * 2 ^ (63 - Nat.log2 d1.toNat) := by
  have hL := (Nat.log2_lt hd1).mpr d1.isLt
  have := Nat.log2_self_le hd1
  have h63 : 2 ^ 63 ≤ d1.toNat * 2 ^ (63 - Nat.log2 d1.toNat) := by
    calc 2 ^ 63 = 2 ^ Nat.log2 d1.toNat * 2 ^ (63 - Nat.log2 d1.toNat) := by
          rw [← pow_add]; congr 1; omega
      _ ≤ _ := Nat.mul_le_mul_right _ this
  calc 2 ^ 127 = 2 ^ 64 * 2 ^ 63 := by norm_num
    _ ≤ 2 ^ 64 * (d1.toNat * 2 ^ (63 - Nat.log2 d1.toNat)) := Nat.mul_le_mul_left _ h63
    _ ≤ _ := by rw [Nat.add_mul, ← Nat.mul_assoc]; omega

/-- The frame of `udivrem_by2()` in its body: sp 32 bytes lower, s0, s1 and s2 saved below the sp
of the call, the memory unchanged except for q and the frame, and the return address and the
other callee-saved registers unchanged. -/
def By2Frame (x : Regs) (m : Mem) (x' : Regs) (m' : Mem) : Prop :=
  x'.get 2#5 = x.get 2#5 + 18446744073709551584#64 ∧ x'.get 1#5 = x.get 1#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551608#64).toNat = x.get 8#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551600#64).toNat = x.get 9#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551592#64).toNat = x.get 18#5 ∧
  UnchangedExcept2 m m' (x.get 10#5) (8 * (x.get 11#5).toNat) (x.get 2#5 - 32#64) 32 ∧
  ∀ r ∈ calleeSaved, r ≠ 2#5 → r ≠ 8#5 → r ≠ 9#5 → r ≠ 18#5 → x'.get r = x.get r

/-- The state at the head of the loop of `udivrem_by2()` before the digit `i` of the numerator
normalized by `S`: the quotient words above `i` stored, and the normalized remainder in `t4:t2` of
the digits above `i`, `Qhi * D + rem = (u * 2^S) / 2^(64 * (i + 1))`. -/
def by2Head (x : Regs) (m : Mem) (i : Nat) (x' : Regs) (m' : Mem) : Prop :=
  let n := (x.get 13#5).toNat
  let S := 63 - Nat.log2 (x.get 15#5).toNat
  let D := ((x.get 14#5).toNat + 2 ^ 64 * (x.get 15#5).toNat) * 2 ^ S
  1 ≤ i ∧ i + 3 ≤ n ∧
  x'.get 10#5 = x.get 10#5 ∧ x'.get 12#5 = x.get 12#5 ∧ (x'.get 16#5).toNat = S ∧
  x'.get 17#5 = x'.get 16#5 ^^^ 18446744073709551615#64 ∧
  (x'.get 5#5).toNat + 2 ^ 64 * (x'.get 6#5).toNat = D ∧
  (x'.get 11#5).toNat = (2 ^ 192 - 1) / D - 2 ^ 64 ∧
  x'.get 13#5 = BitVec.ofNat 64 i ∧
  x'.get 14#5 = x.get 12#5 + BitVec.ofNat 64 (8 * (i - 1)) ∧
  x'.get 15#5 = x.get 10#5 + BitVec.ofNat 64 (8 * i) ∧
  (x'.get 7#5).toNat + 2 ^ 64 * (x'.get 29#5).toNat < D ∧
  words m' (x.get 10#5 + BitVec.ofNat 64 (8 * (i + 1))) (n - 2 - i) * D +
      ((x'.get 7#5).toNat + 2 ^ 64 * (x'.get 29#5).toNat) =
    words m (x.get 12#5) n * 2 ^ S / 2 ^ (64 * (i + 1)) ∧
  By2Frame x m x' m'

/-- The state at the exit of the loop, before the last digit. -/
def by2Exit (x : Regs) (m : Mem) (x' : Regs) (m' : Mem) : Prop :=
  let n := (x.get 13#5).toNat
  let S := 63 - Nat.log2 (x.get 15#5).toNat
  let D := ((x.get 14#5).toNat + 2 ^ 64 * (x.get 15#5).toNat) * 2 ^ S
  x'.get 10#5 = x.get 10#5 ∧ x'.get 12#5 = x.get 12#5 ∧ (x'.get 16#5).toNat = S ∧
  x'.get 17#5 = x'.get 16#5 ^^^ 18446744073709551615#64 ∧
  (x'.get 5#5).toNat + 2 ^ 64 * (x'.get 6#5).toNat = D ∧
  (x'.get 11#5).toNat = (2 ^ 192 - 1) / D - 2 ^ 64 ∧
  (x'.get 7#5).toNat + 2 ^ 64 * (x'.get 29#5).toNat < D ∧
  words m' (x.get 10#5 + 8#64) (n - 2) * D + ((x'.get 7#5).toNat + 2 ^ 64 * (x'.get 29#5).toNat) =
    words m (x.get 12#5) n * 2 ^ S / 2 ^ 64 ∧
  By2Frame x m x' m'

theorem by2_exit {hi : BitVec 20} {lo : BitVec 12} {D : List (BitVec 64)} (base : BitVec 64)
    (x : Regs) (m : Mem) (hpre : udivrem_by2.pre x m) (hr : x.get 1#5 &&& 3 = 0) (x' : Regs)
    (m' : Mem) (h : by2Exit x m x' m') :
    Reach (bufWords (x.get 12#5) (x.get 13#5).toNat ++ bufWords (x.get 10#5) (x.get 11#5).toNat ++
        bufWords (x.get 2#5 - 32#64) 4 ++ D) (udivrem_by2_progAt hi lo) base (pcAt base 256) x' m'
      (x.get 1#5) (udivrem_by2.post x m) := by
  obtain ⟨h10, h12, h16, h17, hdn, hv, hrem, hq, hfr⟩ := h
  have hfr0 := hfr
  obtain ⟨h2, h1, hs8, hs9, hs18, hun, hcs⟩ := hfr0
  have hpre' := hpre
  simp only [udivrem_by2.pre, Buf, Disjoint] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hqa, hqn⟩, ⟨hua, hun8⟩, hdqu, ⟨hsa, hsn⟩, hdsu, hdsq, hn3, hqs, hd⟩ := hpre'
  have hd1 : (x.get 15#5).toNat ≠ 0 := by
    intro h; have := (x.get 14#5).isLt; omega
  have hD := by2_D127 (x.get 14#5) (x.get 15#5) hd1
  have hum := memWord_u hun hdqu hdsu hun8
  have hS64 : 63 - Nat.log2 (x.get 15#5).toNat < 64 := by
    have := (Nat.log2_lt hd1).mpr (x.get 15#5).isLt; omega
  -- The word u[0].
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  rw [h12]
  refine ⟨List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (mem_bufWords_zero (by omega)))), fun w0 hw0 => ?_⟩
  -- The inlined udivrem_3by2() of the last digit.
  refine Reach.trans (by2_div_last base _ _ ?_ ?_ ?_ _ rfl) ?_
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    rw [hdn]; exact hD
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    rw [hdn]; linarith
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    rw [hv, hdn]
  intro x'' m'' ⟨hm, hq0, hr0, h00, hfr'⟩
  subst hm
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte] at hq0 hr0
  rw [regs_eq_sets _ x'' _ h00 hfr']
  simp only [setRegs]
  -- The word q[0].
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  rw [h10]
  refine ⟨List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (mem_bufWords_zero (by omega)))), ?_⟩
  rv_exec_cut
  -- The saved s0, s1 and s2.
  have hq0n : 0 < (x.get 11#5).toNat := by omega
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  rw [h2]
  refine ⟨by rw [frame_w3]; exact List.mem_append_left _ (List.mem_append_right _
    (mem_bufWords (by norm_num))), fun ws0 hws0 => ?_⟩
  rw [show x.get 2#5 + 18446744073709551584#64 + 24#64 = x.get 2#5 + 18446744073709551608#64 by
    rw [BitVec.add_assoc]; rfl] at hws0
  try rw [memStore_q0_stack _ hq0n _ hqn hsn hdsq _ (Or.inl rfl)] at hws0
  rw [hs8] at hws0
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  rw [h2]
  refine ⟨by rw [frame_w2]; exact List.mem_append_left _ (List.mem_append_right _
    (mem_bufWords (by norm_num))), fun ws1 hws1 => ?_⟩
  rw [show x.get 2#5 + 18446744073709551584#64 + 16#64 = x.get 2#5 + 18446744073709551600#64 by
    rw [BitVec.add_assoc]; rfl] at hws1
  try rw [memStore_q0_stack _ hq0n _ hqn hsn hdsq _ (Or.inr (Or.inl rfl))] at hws1
  rw [hs9] at hws1
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  rw [h2]
  refine ⟨by rw [frame_w1]; exact List.mem_append_left _ (List.mem_append_right _
    (mem_bufWords (by norm_num))), fun ws2 hws2 => ?_⟩
  rw [show x.get 2#5 + 18446744073709551584#64 + 8#64 = x.get 2#5 + 18446744073709551592#64 by
    rw [BitVec.add_assoc]; rfl] at hws2
  try rw [memStore_q0_stack _ hq0n _ hqn hsn hdsq _ (Or.inr (Or.inr rfl))] at hws2
  rw [hs18] at hws2
  rv_exec_cut
  all_goals
    rv_val
    rw [h1, update_aligned hr]
    refine Reach.refl ?_
    simp only [udivrem_by2.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    simp (disch := decide) only [Regs.eq_get x]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    -- The quotient and the remainder of the numerator normalized by S.
    have hu0 := hum 0 (by omega)
    simp only [Nat.mul_zero, BitVec.add_zero] at hu0
    have hdig : (w0 <<< ((x'.get 16#5).toNat % 64)).toNat = words m (x.get 12#5)
        (x.get 13#5).toNat * 2 ^ (63 - Nat.log2 (x.get 15#5).toNat) % 2 ^ 64 := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, h16, Nat.mod_eq_of_lt hS64, hw0.eq, hu0,
        words_mul_mod m _ _ _ (by omega)]
    rw [hdig, show ∀ a b c : Nat, a * 2 ^ 128 + b * 2 ^ 64 + c = 2 ^ 64 * (b + 2 ^ 64 * a) + c
      from fun a b c => by ring, hdn] at hq0 hr0
    obtain ⟨hfq, hfr⟩ := by1_final
      (by omega : 0 < (x.get 14#5).toNat + 2 ^ 64 * (x.get 15#5).toNat) hq rfl hq0 hr0
    have hres := defn_shr_toNat ‹Defn _ (x'' 11#5 >>> ((x'.get 16#5).toNat % 64))›
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [words_memStore_first _ _ _ _ hq0n hqn,
        show (x.get 11#5).toNat - 1 = (x.get 13#5).toNat - 2 by omega,
        Regs.eq_get x'' (show (13#5 : BitVec 5) ≠ 0 by decide)]
      exact hfq
    · rw [← hfr, hres, ← Regs.eq_get x'' (show (12#5 : BitVec 5) ≠ 0 by decide),
        ← Regs.eq_get x'' (show (11#5 : BitVec 5) ≠ 0 by decide), h16]
      first
        | (rv_get hz : x'.get 16#5 = 0#64
           have hS0 : 63 - Nat.log2 (x.get 15#5).toNat = 0 := by rw [← h16, hz]; rfl
           rw [hS0]
           simp)
        | (rv_get hnz : ¬x'.get 16#5 = 0#64
           have ht0 : 0 < (x'.get 16#5).toNat := by
             rcases Nat.eq_zero_or_pos (x'.get 16#5).toNat with h | h
             · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hnz
             · exact h
           have hf := toNat_fshr_code (x'' 12#5) (x'' 11#5) (x'.get 16#5) (by omega) ht0
           rw [← h17] at hf
           rv_fold hf
           rv_fold hf
           rw [hf, h16, Nat.mod_eq_of_lt hS64]
           exact fshr_words _ _ _ hS64)
    · exact (unchangedExcept2_memStore _ _ (Or.inl ⟨le_refl _, by omega⟩)).mpr hun
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
      simp (disch := decide) only [Regs.eq_get x']
      rw [h2, hws0.eq, hws1.eq, hws2.eq]
      refine ⟨by rw [BitVec.add_assoc]; simp, ?_⟩
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hcs
      obtain ⟨-, h3, h4, -, -, -, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩ := hcs
      exact ⟨h3 (by decide) (by decide) (by decide) (by decide),
        h4 (by decide) (by decide) (by decide) (by decide), rfl, rfl, rfl,
        h19 (by decide) (by decide) (by decide) (by decide),
        h20 (by decide) (by decide) (by decide) (by decide),
        h21 (by decide) (by decide) (by decide) (by decide),
        h22 (by decide) (by decide) (by decide) (by decide),
        h23 (by decide) (by decide) (by decide) (by decide),
        h24 (by decide) (by decide) (by decide) (by decide),
        h25 (by decide) (by decide) (by decide) (by decide),
        h26 (by decide) (by decide) (by decide) (by decide),
        h27 (by decide) (by decide) (by decide) (by decide)⟩

theorem by2_loop {hi : BitVec 20} {lo : BitVec 12} {D : List (BitVec 64)} (base : BitVec 64)
    (x : Regs) (m : Mem) (hpre : udivrem_by2.pre x m) (hr : x.get 1#5 &&& 3 = 0) :
    ∀ i x' m', by2Head x m i x' m' →
    Reach (bufWords (x.get 12#5) (x.get 13#5).toNat ++ bufWords (x.get 10#5) (x.get 11#5).toNat ++
        bufWords (x.get 2#5 - 32#64) 4 ++ D) (udivrem_by2_progAt hi lo) base (pcAt base 207) x' m'
      (x.get 1#5) (udivrem_by2.post x m) := by
  apply Reach.loop (by2Head x m)
  intro i x' m' h ih
  obtain ⟨hi1, hin, h10, h12, h16, h17, hdn, hv, h13, h14, h15, hrem, hq, hfr⟩ := h
  have hfr0 := hfr
  obtain ⟨h2, h1, hs8, hs9, hs18, hun, hcs⟩ := hfr0
  have hpre' := hpre
  simp only [udivrem_by2.pre, Buf, Disjoint] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hqa, hqn⟩, ⟨hua, hun8⟩, hdqu, ⟨hsa, hsn⟩, hdsu, hdsq, hn3, hqs, hd⟩ := hpre'
  have hd1 : (x.get 15#5).toNat ≠ 0 := by
    intro h; have := (x.get 14#5).isLt; omega
  have hD := by2_D127 (x.get 14#5) (x.get 15#5) hd1
  have hS64 : 63 - Nat.log2 (x.get 15#5).toNat < 64 := by
    have := (Nat.log2_lt hd1).mpr (x.get 15#5).isLt; omega
  have hum := memWord_u hun hdqu hdsu hun8
  have hq8 : (x.get 10#5 + BitVec.ofNat 64 (8 * i)).toNat = (x.get 10#5).toNat + 8 * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hq8' : x.get 10#5 + BitVec.ofNat 64 (8 * i) + 8 =
      x.get 10#5 + BitVec.ofNat 64 (8 * (i + 1)) := by
    rw [BitVec.add_assoc, ofNat_add8]
  have hDp : 0 < ((x.get 14#5).toNat + 2 ^ 64 * (x.get 15#5).toNat) *
      2 ^ (63 - Nat.log2 (x.get 15#5).toNat) := by omega
  -- The word u[i].
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  rw [h14, BitVec.add_assoc, ofNat_sub1_add8 i hi1]
  refine ⟨List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (mem_bufWords (by omega)))), fun wH hwH => ?_⟩
  rv_exec_cut 207 214 256
  -- s ≠ 0: the word u[i - 1] for the funnel shift.
  all_goals first
    | (rv_not_at 209; skip)
    | (refine Reach.step (by decide) (by rv_fetch) ?_
       simp only [StepGoal, Nat.reduceAdd]
       rv_val
       rw [h14]
       refine ⟨List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
         (mem_bufWords (by omega)))), fun wL hwL => ?_⟩
       rv_exec_cut 207 214 256)
  -- The inlined udivrem_3by2() of the digit i.
  all_goals
    refine Reach.trans (by2_div_loop base _ _ ?_ ?_ ?_) ?_
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      rw [hdn]; exact hD
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      rw [hdn]; linarith
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      rw [hv, hdn]
    intro x'' m'' ⟨hm, hq0, hr0, h00, hfr'⟩
    subst hm
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte] at hq0 hr0
    rw [regs_eq_sets _ x'' _ h00 hfr']
    simp only [setRegs]
    rv_exec_cut 207 214 256
  -- The digit i of the numerator normalized by S, from the words of u in the memory at the start.
  all_goals first
    | (rv_lacks x'.get 16#5 = 0#64; skip)
    | (rv_get hz : x'.get 16#5 = 0#64
       have hS0 : 63 - Nat.log2 (x.get 15#5).toNat = 0 := by rw [← h16, hz]; rfl
       have hdig : wH.toNat = words m (x.get 12#5) (x.get 13#5).toNat *
           2 ^ (63 - Nat.log2 (x.get 15#5).toNat) / 2 ^ (64 * i) % 2 ^ 64 := by
         rw [norm_digit m (x.get 12#5) (x.get 13#5).toNat (63 - Nat.log2 (x.get 15#5).toNat) i
           hS64 hi1 (by omega), hS0]
         simp only [pow_zero, Nat.mul_one, Nat.sub_zero, wordAt]
         rw [Nat.div_eq_of_lt (BitVec.isLt _), Nat.add_zero, Nat.mod_eq_of_lt (BitVec.isLt _),
           hwH.eq, hum i (by omega)]
       rw [hdig] at hq0 hr0)
  all_goals first
    | (rv_lacks ¬x'.get 16#5 = 0#64; skip)
    | (have hf := toNat_fshl_code wH wL (x'.get 16#5) (by omega)
       rw [← h17] at hf
       rv_fold hf
       rv_fold hf
       rw [h16, hwH.eq, hwL.eq, hum i (by omega), hum (i - 1) (by omega),
         ← norm_digit m (x.get 12#5) (x.get 13#5).toNat _ i hS64 hi1 (by omega)] at hf
       rw [hf] at hq0 hr0)
  all_goals
    rw [show ∀ a b c : Nat, a * 2 ^ 128 + b * 2 ^ 64 + c = 2 ^ 64 * (b + 2 ^ 64 * a) + c from
      fun a b c => by ring, hdn] at hq0 hr0
    have hstep := div_step i hq hq0 hr0
    -- The quotient word q[i].
    refine Reach.step (by decide) (by rv_fetch) ?_
    simp only [StepGoal, Nat.reduceAdd]
    rv_val
    rw [h15]
    refine ⟨List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (mem_bufWords (by omega)))), ?_⟩
    rv_exec_cut 207 214 256
  -- The memory after the store of q[i].
  all_goals
    have hri' := hr0 ▸ Nat.mod_lt _ hDp
    have hwq : ∀ (mm : Mem) (v : BitVec 64), words (memStore mm (x.get 10#5 +
        BitVec.ofNat 64 (8 * i)).toNat v) (x.get 10#5 + BitVec.ofNat 64 (8 * i))
          ((x.get 13#5).toNat - 2 - (i - 1)) = v.toNat + 2 ^ 64 *
          words mm (x.get 10#5 + BitVec.ofNat 64 (8 * (i + 1))) ((x.get 13#5).toNat - 2 - i) := by
      intro mm v
      rw [words_memStore_first mm _ v _ (by omega) (by rw [hq8]; omega), hq8',
        show (x.get 13#5).toNat - 2 - (i - 1) - 1 = (x.get 13#5).toNat - 2 - i by omega]
  -- The exit after the digit 1.
  all_goals first
    | (rv_not_at 256; skip)
    | (rv_get heq : x'.get 13#5 + 18446744073709551615#64 = 0#64
       have hi : i = 1 := ofNat_sub1_eq_zero i (by omega) (h13 ▸ heq)
       subst hi
       refine by2_exit base x m hpre hr _ _ ?_
       simp only [by2Exit, By2Frame]
       simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
       rw [Regs.eq_get x'' (show (7#5 : BitVec 5) ≠ 0 by decide),
         Regs.eq_get x'' (show (29#5 : BitVec 5) ≠ 0 by decide),
         Regs.eq_get x'' (show (30#5 : BitVec 5) ≠ 0 by decide)]
       refine ⟨h10, h12, h16, h17, hdn, hv, hri', ?_, h2, h1, ?_, ?_, ?_, ?_, ?_⟩
       · rw [show x.get 10#5 + 8#64 = x.get 10#5 + BitVec.ofNat 64 (8 * 1) from rfl,
           show (x.get 13#5).toNat - 2 = (x.get 13#5).toNat - 2 - (1 - 1) by omega, hwq]
         rw [Nat.mul_one] at hstep
         exact hstep
       · rw [memStore_q_stack _ 1 (by omega) _ hqn hsn hdsq _ (Or.inl rfl)]; exact hs8
       · rw [memStore_q_stack _ 1 (by omega) _ hqn hsn hdsq _ (Or.inr (Or.inl rfl))]; exact hs9
       · rw [memStore_q_stack _ 1 (by omega) _ hqn hsn hdsq _ (Or.inr (Or.inr rfl))]; exact hs18
       · exact (unchangedExcept2_memStore _ _
           (Or.inl ⟨by rw [hq8]; omega, by rw [hq8]; omega⟩)).mpr hun
       · intro r hr h2' h8' h9' h18'
         simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
         rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
           rfl | rfl <;>
         first
           | exact absurd rfl h2' | exact absurd rfl h8' | exact absurd rfl h9'
           | exact absurd rfl h18'
           | (simp (config := { decide := true }) only [↓reduceIte]
              exact hcs _ (by decide) (by decide) (by decide) (by decide) (by decide)))
  -- The head before the digit i - 1.
  all_goals first
    | (rv_not_at 207; skip)
    | (rv_get hne : ¬x'.get 13#5 + 18446744073709551615#64 = 0#64
       have hi : i ≠ 1 := by rintro rfl; rw [h13] at hne; exact hne (by decide)
       refine ih (i - 1) (by omega) _ _ ?_
       simp only [by2Head, By2Frame]
       simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
       rw [show i - 1 + 1 = i by omega, Regs.eq_get x'' (show (7#5 : BitVec 5) ≠ 0 by decide),
         Regs.eq_get x'' (show (29#5 : BitVec 5) ≠ 0 by decide),
         Regs.eq_get x'' (show (30#5 : BitVec 5) ≠ 0 by decide)]
       refine ⟨by omega, by omega, h10, h12, h16, h17, hdn, hv, ?_, ?_, ?_, hri', ?_, h2, h1, ?_,
         ?_, ?_, ?_, ?_⟩
       · rw [h13]; exact ofNat_sub1 i (by omega) (by omega)
       · rw [h14]; exact ptr_sub8 _ (i - 1) (by omega) (by omega)
       · rw [h15]; exact ptr_sub8 _ i (by omega) (by omega)
       · rw [hwq]; exact hstep
       · rw [memStore_q_stack _ i (by omega) _ hqn hsn hdsq _ (Or.inl rfl)]; exact hs8
       · rw [memStore_q_stack _ i (by omega) _ hqn hsn hdsq _ (Or.inr (Or.inl rfl))]; exact hs9
       · rw [memStore_q_stack _ i (by omega) _ hqn hsn hdsq _ (Or.inr (Or.inr rfl))]; exact hs18
       · exact (unchangedExcept2_memStore _ _
           (Or.inl ⟨by rw [hq8]; omega, by rw [hq8]; omega⟩)).mpr hun
       · intro r hr h2' h8' h9' h18'
         simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
         rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
           rfl | rfl <;>
         first
           | exact absurd rfl h2' | exact absurd rfl h8' | exact absurd rfl h9'
           | exact absurd rfl h18'
           | (simp (config := { decide := true }) only [↓reduceIte]
              exact hcs _ (by decide) (by decide) (by decide) (by decide) (by decide)))

/-- The top two digits of the normalized numerator are below the normalized divisor. -/
theorem top2_lt {u2 u1 D S : Nat} (hS : S ≤ 63) (h2 : u2 < 2 ^ S) (h1 : u1 < 2 ^ 64)
    (hD : 2 ^ 127 ≤ D) : u2 * 2 ^ 64 + u1 < D := by
  have : 2 ^ S ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) hS
  have : u2 * 2 ^ 64 + u1 < (u2 + 1) * 2 ^ 64 := by omega
  have : (u2 + 1) * 2 ^ 64 ≤ 2 ^ 63 * 2 ^ 64 := Nat.mul_le_mul_right _ (by omega)
  omega

/-- The bits of a word shifted right by `64 - S`: below `2^S`. -/
theorem shr_lt_pow (a : BitVec 64) (S : Nat) (hS : S < 64) : a.toNat / 2 ^ (64 - S) < 2 ^ S := by
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add,
    show S + (64 - S) = 64 by omega]
  exact a.isLt

/-- A number divided by `2^(64k)`: its digits `k + 2` and above, `k + 1` and `k`. -/
theorem top3_digits (X k : Nat) : X / 2 ^ (64 * k) = X / 2 ^ (64 * (k + 2)) * 2 ^ 128 +
    X / 2 ^ (64 * (k + 1)) % 2 ^ 64 * 2 ^ 64 + X / 2 ^ (64 * k) % 2 ^ 64 := by
  have h1 : X / 2 ^ (64 * (k + 1)) = X / 2 ^ (64 * k) / 2 ^ 64 := by
    rw [Nat.div_div_eq_div_mul, ← pow_add]; congr 2
  have h2 : X / 2 ^ (64 * (k + 2)) = X / 2 ^ (64 * (k + 1)) / 2 ^ 64 := by
    rw [Nat.div_div_eq_div_mul, ← pow_add]; congr 2
  have e1 := Nat.div_add_mod (X / 2 ^ (64 * k)) (2 ^ 64)
  have e2 := Nat.div_add_mod (X / 2 ^ (64 * (k + 1))) (2 ^ 64)
  rw [← h1] at e1; rw [← h2] at e2
  calc X / 2 ^ (64 * k) = 2 ^ 64 * (2 ^ 64 * (X / 2 ^ (64 * (k + 2))) +
        X / 2 ^ (64 * (k + 1)) % 2 ^ 64) + X / 2 ^ (64 * k) % 2 ^ 64 := by rw [e2, e1]
    _ = _ := by ring

/-- The top three digits of the words of `a` shifted left by `S`. -/
theorem by2_top3 (m : Mem) (a : BitVec 64) (n S : Nat) (hS : S < 64) (hn : 3 ≤ n) :
    words m a n * 2 ^ S / 2 ^ (64 * (n - 2)) =
      wordAt m a (n - 1) / 2 ^ (64 - S) * 2 ^ 128 +
      (wordAt m a (n - 1) * 2 ^ S + wordAt m a (n - 2) / 2 ^ (64 - S)) % 2 ^ 64 * 2 ^ 64 +
      (wordAt m a (n - 2) * 2 ^ S + wordAt m a (n - 3) / 2 ^ (64 - S)) % 2 ^ 64 := by
  rw [top3_digits _ (n - 2), show n - 2 + 2 = n by omega, show n - 2 + 1 = n - 1 by omega,
    norm_top m a n S hS (by omega), norm_digit m a n S (n - 1) hS (by omega) (by omega),
    norm_digit m a n S (n - 2) hS (by omega) (by omega),
    show n - 1 - 1 = n - 2 by omega, show n - 2 - 1 = n - 3 by omega]

/-- The division by a divisor normalized by `S` of a numerator normalized by `S` with low bits. -/
theorem div_norm_low {T d S r : Nat} (hd : 0 < d) (hr : r < 2 ^ S) :
    (T * 2 ^ S + r) / (d * 2 ^ S) = T / d ∧ (T * 2 ^ S + r) % (d * 2 ^ S) = T % d * 2 ^ S + r := by
  have hP : 0 < 2 ^ S := by positivity
  have hT := Nat.div_add_mod T d
  have hlt : T % d * 2 ^ S + r < d * 2 ^ S := by
    have : (T % d + 1) * 2 ^ S ≤ d * 2 ^ S := Nat.mul_le_mul_right _ (Nat.mod_lt _ hd)
    nlinarith
  have heq : T * 2 ^ S + r = d * 2 ^ S * (T / d) + (T % d * 2 ^ S + r) := by
    calc T * 2 ^ S + r = (d * (T / d) + T % d) * 2 ^ S + r := by rw [hT]
      _ = _ := by ring
  rw [heq, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hlt, Nat.add_zero,
    Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
  exact ⟨rfl, rfl⟩

theorem cnt_sub3_eq_zero (n : BitVec 64) (h : 3 ≤ n.toNat)
    (he : n + 18446744073709551613#64 = 0#64) : n.toNat = 3 := by
  bv_omega

/-- The pointers of the loop of `udivrem_by2()` from the end of a buffer of n words: to its words
n - 4 and n - 3. -/
theorem ptr_end_sub32 (p n : BitVec 64) (h : 4 ≤ n.toNat) (hn : 8 * n.toNat ≤ 2 ^ 64) :
    n <<< 3 + p + 18446744073709551584#64 = p + BitVec.ofNat 64 (8 * (n.toNat - 3 - 1)) := by
  bv_omega

theorem ptr_end_sub24 (p n : BitVec 64) (h : 3 ≤ n.toNat) (hn : 8 * n.toNat ≤ 2 ^ 64) :
    n <<< 3 + p + 18446744073709551592#64 = p + BitVec.ofNat 64 (8 * (n.toNat - 3)) := by
  bv_omega

/-- The frame of `udivrem_by2()` stays when a register other than ra and the callee-saved ones
changes. -/
theorem By2Frame.set {x x' : Regs} {m m' : Mem} {r : BitVec 5} (v : BitVec 64)
    (hr : r ∉ calleeSaved) (hr1 : r ≠ 1#5) (h : By2Frame x m x' m') :
    By2Frame x m (x'.set r v) m' := by
  obtain ⟨h2, h1, h8, h9, h18, hu, hcs⟩ := h
  have hr2 : r ≠ 2#5 := fun e => hr (by rw [e]; decide)
  refine ⟨?_, ?_, h8, h9, h18, hu, fun r' hr' a b c d => ?_⟩
  · rw [Regs.get_set, if_neg (by decide), if_neg (fun e => hr2 e.symm)]; exact h2
  · rw [Regs.get_set, if_neg (by decide), if_neg (fun e => hr1 e.symm)]; exact h1
  · have hne : r' ≠ r := fun e => hr (e ▸ hr')
    rw [Regs.get_set, if_neg hne]
    by_cases h0 : r' = 0
    · subst h0; exact absurd hr' (by decide)
    · rw [if_neg h0]; exact hcs r' hr' a b c d

theorem words_one (mm : Mem) (a : BitVec 64) : words mm a 1 = (memWord mm a.toNat).toNat := by
  simp [words]

/-- The state of `udivrem_by2()` after the division of its top digits (the instruction 201): the
quotient word q[n - 2] stored and the remainder in `t4:t2` of the digits above n - 3 of the
numerator normalized by `S`. -/
def by2Top (x : Regs) (m : Mem) (x' : Regs) (m' : Mem) : Prop :=
  let n := (x.get 13#5).toNat
  let S := 63 - Nat.log2 (x.get 15#5).toNat
  let D := ((x.get 14#5).toNat + 2 ^ 64 * (x.get 15#5).toNat) * 2 ^ S
  x'.get 10#5 = x.get 10#5 ∧ x'.get 12#5 = x.get 12#5 ∧ x'.get 13#5 = x.get 13#5 ∧
  (x'.get 28#5).toNat = 8 * (x.get 13#5).toNat % 2 ^ 64 ∧ (x'.get 16#5).toNat = S ∧
  x'.get 17#5 = x'.get 16#5 ^^^ 18446744073709551615#64 ∧
  (x'.get 5#5).toNat + 2 ^ 64 * (x'.get 6#5).toNat = D ∧
  (x'.get 11#5).toNat = (2 ^ 192 - 1) / D - 2 ^ 64 ∧
  (x'.get 7#5).toNat + 2 ^ 64 * (x'.get 29#5).toNat < D ∧
  (memWord m' (x.get 10#5 + BitVec.ofNat 64 (8 * (n - 2))).toNat).toNat * D +
      ((x'.get 7#5).toNat + 2 ^ 64 * (x'.get 29#5).toNat) =
    words m (x.get 12#5) n * 2 ^ S / 2 ^ (64 * (n - 2)) ∧
  By2Frame x m x' m'

theorem by2_top_exit {hi : BitVec 20} {lo : BitVec 12} {D : List (BitVec 64)} (base : BitVec 64)
    (x : Regs) (m : Mem) (hpre : udivrem_by2.pre x m) (hr : x.get 1#5 &&& 3 = 0) (x' : Regs)
    (m' : Mem) (h : by2Top x m x' m') :
    Reach (bufWords (x.get 12#5) (x.get 13#5).toNat ++ bufWords (x.get 10#5) (x.get 11#5).toNat ++
        bufWords (x.get 2#5 - 32#64) 4 ++ D) (udivrem_by2_progAt hi lo) base (pcAt base 201) x' m'
      (x.get 1#5) (udivrem_by2.post x m) := by
  obtain ⟨h10, h12, h13, h28, h16, h17, hdn, hv, hrem, hq, hfr⟩ := h
  replace h28 : x'.get 28#5 = x.get 13#5 <<< 3 := BitVec.eq_of_toNat_eq (by
    rw [h28, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm])
  have hpre' := hpre
  simp only [udivrem_by2.pre, Buf, Disjoint] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hqa, hqn⟩, ⟨hua, hun8⟩, hdqu, ⟨hsa, hsn⟩, hdsu, hdsq, hn3, hqs, hd⟩ := hpre'
  have hn8 : 8 * (x.get 13#5).toNat ≤ 2 ^ 64 := by omega
  rv_exec_cut 207 256
  -- n = 3: the last digit.
  all_goals first
    | (rv_not_at 256; skip)
    | (rv_get heq : x'.get 13#5 + 18446744073709551613#64 = 0#64
       rw [h13] at heq
       have hn := cnt_sub3_eq_zero _ (by omega) heq
       refine by2_exit base x m hpre hr _ _ ?_
       simp only [by2Exit]
       simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
       refine ⟨h10, h12, h16, h17, hdn, hv, hrem, ?_, ?_⟩
       rotate_left
       · repeat (first | exact hfr | apply By2Frame.set _ (by decide) (by decide))
       rw [hn, show 3 - 2 = 1 from rfl, words_one]
       rw [hn] at hq
       simpa using hq)
  -- n > 3: the head of the loop before the digit n - 3.
  all_goals first
    | (rv_not_at 207; skip)
    | (rv_get hne : ¬x'.get 13#5 + 18446744073709551613#64 = 0#64
       rw [h13] at hne
       have hn4 : 4 ≤ (x.get 13#5).toNat := by
         by_contra hc
         exact hne (by rw [cnt_sub3 _ (by omega), show (x.get 13#5).toNat - 3 = 0 by omega])
       have hp4 : x'.get 28#5 + x'.get 12#5 + 18446744073709551584#64 =
           x.get 12#5 + BitVec.ofNat 64 (8 * ((x.get 13#5).toNat - 3 - 1)) := by
         rw [h28, h12, ptr_end_sub32 _ _ hn4 hn8]
       have hp5 : x'.get 28#5 + x'.get 10#5 + 18446744073709551592#64 =
           x.get 10#5 + BitVec.ofNat 64 (8 * ((x.get 13#5).toNat - 3)) := by
         rw [h28, h10, ptr_end_sub24 _ _ (by omega) hn8]
       rv_fold hp4
       rv_fold hp5
       refine by2_loop base x m hpre hr ((x.get 13#5).toNat - 3) _ _ ?_
       simp only [by2Head]
       simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
       refine ⟨by omega, by omega, h10, h12, h16, h17, hdn, hv, ?_, hp4, hp5, hrem, ?_, ?_⟩
       rotate_right
       · repeat (first | exact hfr | apply By2Frame.set _ (by decide) (by decide))
       · rw [h13]; exact cnt_sub3 _ (by omega)
       · rw [show (x.get 13#5).toNat - 3 + 1 = (x.get 13#5).toNat - 2 by omega,
           show (x.get 13#5).toNat - 2 - ((x.get 13#5).toNat - 3) = 1 by omega, words_one]
         exact hq)

/-- The memory of `udivrem_by2()` after the division of its top digits: s0, s1 and s2 saved below
the sp of the call and the quotient word stored in q. -/
theorem by2_frame_top (m m' : Mem) (q sp : BitVec 64) (qs k : Nat) (s0 s1 s2 v : BitVec 64)
    (hk : k < qs) (hq : q.toNat + 8 * qs ≤ 2 ^ 64) (hs : (sp - 32#64).toNat + 32 ≤ 2 ^ 64)
    (hd : (sp - 32#64).toNat + 32 ≤ q.toNat ∨ q.toNat + 8 * qs ≤ (sp - 32#64).toNat)
    (hm : m' = memStore (memStore (memStore (memStore m (sp + 18446744073709551608#64).toNat s0)
      (sp + 18446744073709551600#64).toNat s1) (sp + 18446744073709551592#64).toNat s2)
      (q + BitVec.ofNat 64 (8 * k)).toNat v) :
    memWord m' (sp + 18446744073709551608#64).toNat = s0 ∧
      memWord m' (sp + 18446744073709551600#64).toNat = s1 ∧
      memWord m' (sp + 18446744073709551592#64).toNat = s2 ∧
      UnchangedExcept2 m m' q (8 * qs) (sp - 32#64) 32 := by
  subst hm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [memWord_memStore_of_ne _ _ _ _ (by bv_omega), memWord_memStore_of_ne _ _ _ _ (by bv_omega),
      memWord_memStore_of_ne _ _ _ _ (by bv_omega), memWord_memStore_self]
  · rw [memWord_memStore_of_ne _ _ _ _ (by bv_omega), memWord_memStore_of_ne _ _ _ _ (by bv_omega),
      memWord_memStore_self]
  · rw [memWord_memStore_of_ne _ _ _ _ (by bv_omega), memWord_memStore_self]
  · rw [unchangedExcept2_memStore _ _ (Or.inl ⟨by bv_omega, by bv_omega⟩),
      unchangedExcept2_memStore _ _ (Or.inr ⟨by bv_omega, by bv_omega⟩),
      unchangedExcept2_memStore _ _ (Or.inr ⟨by bv_omega, by bv_omega⟩),
      unchangedExcept2_memStore _ _ (Or.inr ⟨by bv_omega, by bv_omega⟩)]
    exact unchangedExcept2_refl _ _ _ _ _

/-- A word of u through the three stores of the frame of `udivrem_by2()`: u is outside the frame. -/
theorem memWord_stack_u (m : Mem) (sp u : BitVec 64) (n k : Nat) (s0 s1 s2 : BitVec 64)
    (hk : k < n) (hun8 : u.toNat + 8 * n ≤ 2 ^ 64) (hs : (sp - 32#64).toNat + 32 ≤ 2 ^ 64)
    (hd : (sp - 32#64).toNat + 32 ≤ u.toNat ∨ u.toNat + 8 * n ≤ (sp - 32#64).toNat) :
    memWord (memStore (memStore (memStore m (sp + 18446744073709551608#64).toNat s0)
      (sp + 18446744073709551600#64).toNat s1) (sp + 18446744073709551592#64).toNat s2)
      (u + BitVec.ofNat 64 (8 * k)).toNat = memWord m (u + BitVec.ofNat 64 (8 * k)).toNat := by
  rw [memWord_memStore_of_ne _ _ _ _ (by bv_omega), memWord_memStore_of_ne _ _ _ _ (by bv_omega),
    memWord_memStore_of_ne _ _ _ _ (by bv_omega)]

/-- The top two words of the words of `a`, `n ≥ 3`, not shifted. -/
theorem by2_top3_s0 (m : Mem) (a : BitVec 64) (n : Nat) (hn : 3 ≤ n) :
    words m a n / 2 ^ (64 * (n - 2)) = wordAt m a (n - 1) * 2 ^ 64 + wordAt m a (n - 2) := by
  have h := by2_top3 m a n 0 (by norm_num) hn
  simp only [pow_zero, Nat.mul_one, Nat.sub_zero] at h
  have h0 : ∀ k, wordAt m a k / 2 ^ 64 = 0 := fun k => Nat.div_eq_of_lt (BitVec.isLt _)
  have h1 : ∀ k, wordAt m a k % 2 ^ 64 = wordAt m a k := fun k => Nat.mod_eq_of_lt (BitVec.isLt _)
  rw [h, h0, h0, h0, Nat.add_zero, Nat.add_zero, h1, h1]
  ring

end IntxRV.Api
