import IntxRV.Gen.Api
import IntxRV.DivBy2
import IntxRV.DivTop2
import IntxRV.Knuth
import IntxRV.Api.submul
import IntxRV.DivWords
/-!
# The blocks of `internal::udivrem_knuth_normalized<3>()`

The code divides a digit in a block from the test of the overflow at 0x130 to the store of the
quotient digit at 0x1e8: the inlined `udivrem_3by2()` of the top 3 words of the partial remainder
by the top 2 words of d (`k3_div`, the paths of `div3by2BVo` by `by2_div3_paths`), then the
subtraction of the multiple of d with the add-back (`k3_sub`, by `knuth3_noborrow` and
`knuth3_addback`), or, if the top 2 words of the remainder are the top 2 words of d, the digit
`2^64 - 1` by the call of `submul()` (`k3_over`).

The loop runs from its head at 0x130 by `Reach.loop` with the invariant `k3Head`: the pointers to
u[j] and q[j], the words j + 2 and j + 3 of u in a2 and a4, the words of u below j + 1 unchanged,
and the quotient and the remainder of the digits above j (`knuth_digit`). `k3_tail` runs a digit
from the store of the quotient digit to the next head, or for the last digit to the epilogue
(`k3_exit`), and `k3_loop` routes the overflow and the paths of the division to it. The frame is
`K3Frame`: ra and s0 to s7 saved, and the memory outside q, u and the frame unchanged.
-/

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
-- The guards that select the paths do not change the goals.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace IntxRV.Api
open IntxRV IntxRV.Gen

/-- The inlined `udivrem_3by2()` of `udivrem_knuth_normalized<3>()`, from 0x13c to 0x1b0 (the
correction at 0x230): `a4:a2:a0` by `s3:s2` with the reciprocal in s6, to the quotient in s7 and
the remainder in `a0:a1`. -/
theorem k3_div {A : List (BitVec 64)} {hi : BitVec 20} {lo : BitVec 12} (base : BitVec 64)
    (x : Regs) (m : Mem)
    (hd : 2 ^ 127 ≤ (x.get 18#5).toNat + 2 ^ 64 * (x.get 19#5).toNat)
    (hu : (x.get 14#5).toNat * 2 ^ 64 + (x.get 12#5).toNat <
      (x.get 18#5).toNat + 2 ^ 64 * (x.get 19#5).toNat)
    (hv : (x.get 22#5).toNat =
      (2 ^ 192 - 1) / ((x.get 18#5).toNat + 2 ^ 64 * (x.get 19#5).toNat) - 2 ^ 64) :
    Reach A (udivrem_knuth_normalized_3_progAt hi lo) base (pcAt base 79) x m (pcAt base 108)
      (fun x' m' => m' = m ∧ Div3Out x x' ((x.get 14#5).toNat * 2 ^ 128 +
        (x.get 12#5).toNat * 2 ^ 64 + (x.get 10#5).toNat)
        ((x.get 18#5).toNat + 2 ^ 64 * (x.get 19#5).toNat) 23#5 11#5 10#5
        [10#5, 11#5, 12#5, 14#5, 15#5, 16#5, 23#5]) := by
  by2_div3_paths div3by2BVo_spec true (x.get 14#5) (x.get 12#5) (x.get 10#5) (x.get 18#5)
    (x.get 19#5) (x.get 22#5) hd hu hv

/-- `u - c` and whether it borrows, `u < u - c`. -/
theorem sub_borrow_cases {h u c : BitVec 64} (hh : Defn h (u - c)) :
    (¬u < h → h.toNat + c.toNat = u.toNat) ∧ (u < h → h.toNat + c.toNat = u.toNat + 2 ^ 64) := by
  rw [hh.eq]
  have hu := u.isLt; have hc := c.isLt
  have e : (u - c).toNat = (u.toNat + (2 ^ 64 - c.toNat)) % 2 ^ 64 := by
    rw [BitVec.toNat_sub]; omega
  constructor <;> intro hlt <;> simp only [BitVec.lt_def] at hlt <;> omega

theorem toNat_add8 (a : BitVec 64) (k : Nat) (hk : k < 2 ^ 64) (ha : a.toNat + k < 2 ^ 64) :
    (a + BitVec.ofNat 64 k).toNat = a.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt ha]

/-- The 3 words at `a`. -/
theorem words3_eq (m : Mem) (a : BitVec 64) :
    words m a 3 = (memWord m a.toNat).toNat + 2 ^ 64 * ((memWord m (a + 8#64).toNat).toNat +
      2 ^ 64 * (memWord m (a + 16#64).toNat).toNat) := by
  simp only [words, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero, Nat.add_zero]
  rfl

/-- The memory with the 3 words at `a` stored. -/
abbrev memStore3 (m : Mem) (a w0 w1 w2 : BitVec 64) : Mem :=
  memStore (memStore (memStore m a.toNat w0) (a + 8#64).toNat w1) (a + 16#64).toNat w2

theorem memStore3_words (m : Mem) (a w0 w1 w2 : BitVec 64) (ha : a.toNat + 24 ≤ 2 ^ 64) :
    words (memStore3 m a w0 w1 w2) a 3 = w0.toNat + 2 ^ 64 * (w1.toNat + 2 ^ 64 * w2.toNat) ∧
      memWord (memStore3 m a w0 w1 w2) (a + 8#64).toNat = w1 ∧
      memWord (memStore3 m a w0 w1 w2) (a + 16#64).toNat = w2 := by
  have h8 : (a + 8#64).toNat = a.toNat + 8 := by bv_omega
  have h16 : (a + 16#64).toNat = a.toNat + 16 := by bv_omega
  rw [words3_eq]
  refine ⟨?_, ?_, ?_⟩
  · rw [memWord_memStore_of_ne _ _ _ _ (by omega), memWord_memStore_of_ne _ _ _ _ (by omega),
      memWord_memStore_self, memWord_memStore_of_ne _ _ _ _ (by omega), memWord_memStore_self,
      memWord_memStore_self]
  · rw [memWord_memStore_of_ne _ _ _ _ (by omega), memWord_memStore_self]
  · rw [memWord_memStore_self]

theorem memStore3_unchanged {m m' : Mem} (a w0 w1 w2 : BitVec 64) (ha : a.toNat + 24 ≤ 2 ^ 64) :
    UnchangedExcept m (memStore3 m' a w0 w1 w2) a 24 ↔ UnchangedExcept m m' a 24 := by
  have h8 : (a + 8#64).toNat = a.toNat + 8 := by bv_omega
  have h16 : (a + 16#64).toNat = a.toNat + 16 := by bv_omega
  rw [unchangedExcept_memStore _ _ (by omega), unchangedExcept_memStore _ _ (by omega),
    unchangedExcept_memStore _ _ (by omega)]

/-- The bound of the high word of a product and a borrow. -/
theorem hi_bit_lt {ph b1 a c : BitVec 64} (hph : Defn ph (mulhu a c)) {s t : BitVec 64}
    (hb1 : Defn b1 (if s < t then 1#64 else 0#64)) : ph.toNat + b1.toNat < 2 ^ 64 := by
  have h1 := defn_mulhu_le hph; have h2 := defn_bit hb1; omega

theorem toNat_add_neg1 (a : BitVec 64) (ha : 1 ≤ a.toNat) :
    (a + 18446744073709551615#64).toNat = a.toNat - 1 := by
  rw [BitVec.toNat_add]; have := a.isLt; simp only [BitVec.toNat_ofNat]; omega

/-- The registers and the memory after the subtraction of the multiple of the divisor of a digit of
`udivrem_knuth_normalized<3>()` at 0x1e8: the quotient digit of `N` by `D` in s7, the remainder in
the 3 words at `s`, and its words 1 and 2 in a2 and a4, the top words of the next remainder. -/
def K3Sub (x x' : Regs) (m m' : Mem) (s : BitVec 64) (N D : Nat) : Prop :=
  (x'.get 23#5).toNat * D + words m' s 3 = N ∧ words m' s 3 < D ∧ UnchangedExcept m m' s 24 ∧
    x'.get 12#5 = memWord m' (s + 8#64).toNat ∧ x'.get 14#5 = memWord m' (s + 16#64).toNat ∧
    x' 0 = x 0 ∧ ∀ r, r ∉ [10#5, 11#5, 12#5, 14#5, 15#5, 23#5] → x' r = x r

/-- The subtraction of `qh * d` from the 4 words `N` at s0 of `udivrem_knuth_normalized<3>()`, from
0x1b0 to 0x1e8, with the estimate `qh` in s7 and the remainder `rh` of the 3/2 division of the
top words `Nt` of `N` by the top words `Dhi` of `d` in `a0:a1`: the inlined `submul()` of the word
`d[0]`, the subtraction of its high word from `rh`, and `d` added back if it borrows. -/
theorem k3_sub {hi : BitVec 20} {lo : BitVec 12} (base : BitVec 64) (x : Regs) (m : Mem)
    (Nt : Nat)
    (hs : (x.get 8#5).toNat + 24 ≤ 2 ^ 64) (hdn : (x.get 13#5).toNat + 24 ≤ 2 ^ 64)
    (hds : Disjoint (x.get 8#5) 24 (x.get 13#5) 24)
    (h18 : x.get 18#5 = memWord m (x.get 13#5 + 8#64).toNat)
    (h19 : x.get 19#5 = memWord m (x.get 13#5 + 16#64).toNat)
    (hD : 2 ^ 127 ≤ (x.get 18#5).toNat + 2 ^ 64 * (x.get 19#5).toNat)
    (hq : (x.get 23#5).toNat * ((x.get 18#5).toNat + 2 ^ 64 * (x.get 19#5).toNat) +
      ((x.get 11#5).toNat + 2 ^ 64 * (x.get 10#5).toNat) = Nt)
    (hr : (x.get 11#5).toNat + 2 ^ 64 * (x.get 10#5).toNat <
      (x.get 18#5).toNat + 2 ^ 64 * (x.get 19#5).toNat) :
    Reach (bufWords (x.get 13#5) 3 ++ bufWords (x.get 8#5) 3) (udivrem_knuth_normalized_3_progAt hi lo)
      base (pcAt base 108) x m (pcAt base 122) (fun x' m' => K3Sub x x' m m' (x.get 8#5)
        (Nt * 2 ^ 64 + (memWord m (x.get 8#5).toNat).toNat) (words m (x.get 13#5) 3)) := by
  simp only [Disjoint] at hds
  have hdw := words3_eq m (x.get 13#5)
  rw [← h18, ← h19] at hdw
  rv_exec
  all_goals simp (config := { decide := true }) only [K3Sub, Regs.get_set, ↓reduceIte,
    BitVec.reduceSignExtend, BitVec.add_zero]
  · -- The borrow: d added back.
    rename_i wd0 hwd0 wuj hwuj p hp ph hph s hs' t ht b1 hb1 t' ht' c1 hc1 h hh hb wd0' hwd0' e0 he0
      wd1 hwd1 k0 hk0 e1 he1 k1a hk1a n1 hn1 wd2 hwd2 k1b hk1b k1 hk1 e2 he2 n2 hn2
    simp only [zopz0zI_u_eq, decide_eq_true_eq] at hb
    have hL := defn_sub_borrow0 hs' hb1
    have hm := defn_mul_mulhu hp hph
    have hT1 := defn_sub2_borrow ht ht' hc1 (hi_bit_lt hph hb1)
    have hT2 := (sub_borrow_cases hh).2 hb
    have hadd := add3c_words he0 hn1 he1 hk0 hk1a hk1b hn2 he2 hk1
    rw [hwd0'.eq, hwd1.eq, hwd2.eq, ← h18, ← h19, ← hdw] at hadd
    rw [hwd0.eq] at hm
    rw [hwuj.eq] at hL
    obtain ⟨hw3, h8, h16⟩ := memStore3_words (memStore3 m (x.get 8#5) s t' h) (x.get 8#5) e0 n1 n2 hs
    have hw3' : e0.toNat + 2 ^ 64 * (n1.toNat + 2 ^ 64 * n2.toNat) < 2 ^ 192 :=
      hw3 ▸ words_lt _ 3 _
    obtain ⟨hq1, hres, hlt⟩ := knuth3_addback hdw (memWord m (x.get 13#5).toNat).isLt hD hq
      hr (x.get 23#5).isLt (memWord m (x.get 8#5).toNat).isLt s.isLt t'.isLt h.isLt hL hm hT1 hT2
      (lt_2_128_of_words rfl) hw3' hadd
    have hq' := toNat_add_neg1 _ hq1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hq', hw3, hres]
    · rw [hw3]; exact hlt
    · exact (memStore3_unchanged _ _ _ _ hs).mpr
        ((memStore3_unchanged _ _ _ _ hs).mpr (unchangedExcept_refl _ _ _))
    · exact h8.symm
    · exact h16.symm
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp (config := { decide := true }) only [Regs.set_apply, hr, ↓reduceIte]
  · -- No borrow.
    rename_i wd0 hwd0 wuj hwuj p hp ph hph s hs' t ht b1 hb1 t' ht' c1 hc1 h hh hb
    simp only [zopz0zI_u_eq, decide_eq_false_iff_not] at hb
    have hL := defn_sub_borrow0 hs' hb1
    have hm := defn_mul_mulhu hp hph
    have hT1 := defn_sub2_borrow ht ht' hc1 (hi_bit_lt hph hb1)
    have hT2 := (sub_borrow_cases hh).1 hb
    obtain ⟨hw3, h8, h16⟩ := memStore3_words m (x.get 8#5) s t' h hs
    rw [hwd0.eq] at hm
    rw [hwuj.eq] at hL
    obtain ⟨hres, hlt⟩ := knuth3_noborrow hdw (memWord m (x.get 13#5).toNat).isLt hD hq
      hr (x.get 23#5).isLt (memWord m (x.get 8#5).toNat).isLt hL hm hT1 hT2
    refine ⟨?_, ?_, (memStore3_unchanged _ _ _ _ hs).mpr (unchangedExcept_refl _ _ _), ?_, ?_, ?_, ?_⟩
    · rw [hw3]; exact hres
    · rw [hw3]; exact hlt
    · exact h8.symm
    · exact h16.symm
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp (config := { decide := true }) only [Regs.set_apply, hr, ↓reduceIte]

/-- The registers that the division of the overflow at 0x200 may change: the call of `submul()`
changes the registers that are not callee-saved. -/
def k3OverCl : List (BitVec 5) :=
  [0#5, 1#5, 5#5, 6#5, 7#5, 9#5, 10#5, 11#5, 12#5, 14#5, 15#5, 16#5, 17#5, 23#5, 28#5, 29#5, 30#5,
    31#5]

theorem k3OverCl_saved : ∀ r : BitVec 5, r ∉ k3OverCl → r ≠ 13#5 → r ≠ 8#5 →
    r ∈ calleeSaved ∧ r ≠ 9#5 ∧ r ≠ 23#5 := by decide

/-- The division overflows, from 0x200 to 0x1e8: the 3 words at s0 less `2^64 - 1` times d by the
call of `submul()` (at 0x2bc), the digit `2^64 - 1` in s7, and the words 1 and 2 of the remainder
in a2 and a4. -/
theorem k3_over {hi : BitVec 20} {lo : BitVec 12} (base : BitVec 64) (x : Regs) (m : Mem)
    (hb : base &&& 3 = 0)
    (hs : (x.get 8#5).toNat + 24 ≤ 2 ^ 64) (hsa : (x.get 8#5).toNat % 8 = 0)
    (hdn : (x.get 13#5).toNat + 24 ≤ 2 ^ 64) (hda : (x.get 13#5).toNat % 8 = 0)
    (hds : Disjoint (x.get 8#5) 24 (x.get 13#5) 24) :
    Reach (bufWords (x.get 13#5) 3 ++ bufWords (x.get 8#5) 3) (udivrem_knuth_normalized_3_progAt hi lo)
      base (pcAt base 128) x m (pcAt base 122) (fun x' m' =>
        (∃ k, words m' (x.get 8#5) 3 + (2 ^ 64 - 1) * words m (x.get 13#5) 3 =
          words m (x.get 8#5) 3 + k * 2 ^ 192) ∧
        UnchangedExcept m m' (x.get 8#5) 24 ∧ x'.get 23#5 = 18446744073709551615#64 ∧
        x'.get 12#5 = memWord m' (x.get 8#5 + 8#64).toNat ∧
        x'.get 14#5 = memWord m' (x.get 8#5 + 16#64).toNat ∧
        ∀ r, r ∉ k3OverCl → x' r = x r) := by
  simp only [Disjoint] at hds
  rv_exec_cut 175
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  rw [show (0#5 : BitVec 5) = 0 from rfl, Regs.get_zero, zero_add,
    show pcAt base 134 + BitVec.signExtend 64 164#12 = pcAt base 175 by
      simp only [pcAt, BitVec.reduceSignExtend]; bv_omega,
    update_aligned (by simp only [pcAt]; exact aligned_add hb (by decide))]
  refine Reach.call_sub (r := 136) udivrem_knuth_normalized_3_progAt_submul_in
    (by rw [udivrem_knuth_normalized_3_progAt_length]; decide)
    (submul.reach (pcAt base 175) _ m ?_ ?_) ?_ ?_ ?_
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    simp only [pcAt]; exact aligned_add hb (by decide)
  · simp only [submul.pre, Buf, Disjoint]
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    try simp (disch := decide) only [Regs.eq_get x]
    simp only [show (3#64).toNat = 3 from rfl, and_true]
    omega
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · intro a ha
    simp only [submul.bufs] at ha
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at ha
    try simp (disch := decide) only [Regs.eq_get x] at ha
    rwa [show (3#64).toNat = 3 from rfl] at ha
  · intro x3 m3 hpost
    simp only [submul.post] at hpost
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at hpost
    obtain ⟨hres, hun, hcs⟩ := hpost
    rw [show (3#64).toNat = 3 from rfl] at hres hun
    have hx3 : ∀ r ∈ calleeSaved, r ≠ 9#5 → r ≠ 23#5 → x3 r = x r := by
      intro r hr h9 h23
      rw [hcs r hr]
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> simp (config := { decide := true }) only [↓reduceIte] <;>
        first | exact absurd rfl h9 | exact absurd rfl h23
    have h83 : x3.get 8#5 = x.get 8#5 := by
      rw [← Regs.eq_get x3 (by decide), ← Regs.eq_get x (by decide)]
      exact hx3 _ (by decide) (by decide) (by decide)
    have h93 : x3.get 9#5 = x.get 13#5 := by
      rw [← Regs.eq_get x3 (by decide), hcs _ (by decide)]
      simp (config := { decide := true }) only [↓reduceIte]
    have h233 : x3.get 23#5 = 18446744073709551615#64 := by
      rw [← Regs.eq_get x3 (by decide), hcs _ (by decide)]
      simp (config := { decide := true }) only [↓reduceIte]
    rw [← regs_set_of_get' (by decide) h83, ← regs_set_of_get' (by decide) h93]
    rv_exec
    rename_i w12 hw12 w14 hw14
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    rw [show (18446744073709551615#64).toNat = 2 ^ 64 - 1 from rfl,
      show 64 * 3 = 192 from rfl] at hres
    refine ⟨⟨(x3.get 10#5).toNat, hres⟩, hun, h233, ?_, ?_, ?_⟩
    · rw [hw12.eq]
    · rw [hw14.eq]
    · intro r hr
      have hcl := k3OverCl_saved r hr
      simp only [k3OverCl, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨h0, h1, h5, h6, h7, h9, h10, h11, h12, h14, h15, h16, h17, h23, h28, h29, h30, h31⟩ := hr
      simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte, h9, h12, h14]
      split_ifs with h13 h8
      · subst h13; exact (Regs.eq_get x (by decide)).symm
      · subst h8; exact (Regs.eq_get x (by decide)).symm
      · obtain ⟨hs', h9', h23'⟩ := hcl h13 h8
        exact hx3 r hs' h9' h23'


/-- The top 2 words of the remainder are less than the top 2 words of `d` unless they are equal. -/
theorem top2_lt_of_lt {r0 r1 r2 d0 d1 d2 : Nat} (h0 : r0 < 2 ^ 64) (hd0 : d0 < 2 ^ 64)
    (hR : r0 + 2 ^ 64 * (r1 + 2 ^ 64 * r2) < d0 + 2 ^ 64 * (d1 + 2 ^ 64 * d2))
    (hne : ¬(r1 = d1 ∧ r2 = d2)) (h1 : r1 < 2 ^ 64) (hd1 : d1 < 2 ^ 64) :
    r2 * 2 ^ 64 + r1 < d1 + 2 ^ 64 * d2 := by
  omega

/-- The words of `submul()` of the overflow: `S + X` is `N` with `N - X` below `D`. -/
theorem over_words {S X L N D k t : Nat} (hS : S < 2 ^ 192) (h : S + X = L + k * 2 ^ 192)
    (hN : N = L + 2 ^ 192 * t) (hX : X ≤ N) (hNX : N < X + D) (hDK : D ≤ 2 ^ 192) :
    S + X = N := by
  omega

/-- The word `j` of a buffer of `n` words is the digit `j` of its value. -/
theorem words_digit (m : Mem) (a : BitVec 64) {n j : Nat} (hj : j < n) :
    (memWord m (a + BitVec.ofNat 64 (8 * j)).toNat).toNat = words m a n / 2 ^ (64 * j) % 2 ^ 64 := by
  have hs := words_split m j (n - j) a
  rw [show j + (n - j) = n by omega] at hs
  obtain ⟨k, hk⟩ : ∃ k, n - j = k + 1 := ⟨n - j - 1, by omega⟩
  rw [hk, words] at hs
  have hlt := words_lt m j a
  rw [hs, show words m a j + 2 ^ (64 * j) * ((memWord m (a + BitVec.ofNat 64 (8 * j)).toNat).toNat +
      2 ^ 64 * words m (a + BitVec.ofNat 64 (8 * j) + 8) k) =
      words m a j + ((memWord m (a + BitVec.ofNat 64 (8 * j)).toNat).toNat +
      2 ^ 64 * words m (a + BitVec.ofNat 64 (8 * j) + 8) k) * 2 ^ (64 * j) by ring,
    Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlt, Nat.zero_add]
  have := (memWord m (a + BitVec.ofNat 64 (8 * j)).toNat).isLt
  omega

/-- The words outside the bytes that may change. -/
theorem words_of_unchangedExcept {m m' : Mem} {a : BitVec 64} {len : Nat}
    (h : UnchangedExcept m m' a len) : ∀ (n : Nat) (b : BitVec 64), b.toNat + 8 * n ≤ 2 ^ 64 →
      (b.toNat + 8 * n ≤ a.toNat ∨ a.toNat + len ≤ b.toNat) → words m' b n = words m b n
  | 0, _, _, _ => rfl
  | n + 1, b, hb, hd => by
    rw [words, words, memWord_of_unchangedExcept h _ (by omega)]
    cases n with
    | zero => rfl
    | succ k =>
      have h8 : (b + 8).toNat = b.toNat + 8 := by
        rw [BitVec.toNat_add]; simp; omega
      rw [words_of_unchangedExcept h (k + 1) (b + 8) (by omega) (by omega)]

/-- The frame of `udivrem_knuth_normalized<3>()` after its prologue: sp 80 bytes lower, ra and
s0 to s7 saved, and the memory outside q, u and the frame unchanged. -/
def K3Frame (x : Regs) (m : Mem) (x' : Regs) (m' : Mem) : Prop :=
  x'.get 2#5 = x.get 2#5 + 18446744073709551536#64 ∧
  memWord m' (x.get 2#5 + 18446744073709551608#64).toNat = x.get 1#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551600#64).toNat = x.get 8#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551592#64).toNat = x.get 9#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551584#64).toNat = x.get 18#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551576#64).toNat = x.get 19#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551568#64).toNat = x.get 20#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551560#64).toNat = x.get 21#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551552#64).toNat = x.get 22#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551544#64).toNat = x.get 23#5 ∧
  UnchangedExcept3 m m' (x.get 10#5) (8 * ((x.get 12#5).toNat - 3)) (x.get 11#5)
    (8 * (x.get 12#5).toNat) (x.get 2#5 - 80#64) 80 ∧
  ∀ r ∈ calleeSaved, r ∉ [2#5, 8#5, 9#5, 18#5, 19#5, 20#5, 21#5, 22#5, 23#5] → x'.get r = x.get r

/-- The registers and the memory at the head of the loop of `udivrem_knuth_normalized<3>()` at
0x130 for the digit `j` of u: the pointers to u[j] in s0 and q[j] in s5, `j + 1` in s4, the top
words of the divisor and the reciprocal, the words j + 2 and j + 3 of u (the top of the partial
remainder) in a2 and a4, the words of u up to j unchanged, and the quotient and the remainder of
the digits of u above j by d. -/
def k3Head (x : Regs) (m : Mem) (j : Nat) (x' : Regs) (m' : Mem) : Prop :=
  j + 4 ≤ (x.get 12#5).toNat ∧ K3Frame x m x' m' ∧
  x'.get 8#5 = x.get 11#5 + BitVec.ofNat 64 (8 * j) ∧
  x'.get 21#5 = x.get 10#5 + BitVec.ofNat 64 (8 * j) ∧
  x'.get 20#5 = BitVec.ofNat 64 (j + 1) ∧ x'.get 13#5 = x.get 13#5 ∧
  x'.get 18#5 = memWord m (x.get 13#5 + 8#64).toNat ∧
  x'.get 19#5 = memWord m (x.get 13#5 + 16#64).toNat ∧
  (x'.get 22#5).toNat =
    (2 ^ 192 - 1) / ((x'.get 18#5).toNat + 2 ^ 64 * (x'.get 19#5).toNat) - 2 ^ 64 ∧
  x'.get 12#5 = memWord m' (x.get 11#5 + BitVec.ofNat 64 (8 * (j + 2))).toNat ∧
  x'.get 14#5 = memWord m' (x.get 11#5 + BitVec.ofNat 64 (8 * (j + 3))).toNat ∧
  (∀ k, k ≤ j → memWord m' (x.get 11#5 + BitVec.ofNat 64 (8 * k)).toNat =
    memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * k)).toNat) ∧
  words m' (x.get 10#5 + BitVec.ofNat 64 (8 * (j + 1))) ((x.get 12#5).toNat - 4 - j) *
      words m (x.get 13#5) 3 + words m' (x.get 11#5 + BitVec.ofNat 64 (8 * (j + 1))) 3 =
    words m (x.get 11#5) (x.get 12#5).toNat / 2 ^ (64 * (j + 1)) ∧
  words m' (x.get 11#5 + BitVec.ofNat 64 (8 * (j + 1))) 3 < words m (x.get 13#5) 3

/-- The memory after a digit: u[j..j+3) and q[j] changed. -/
theorem k3_step_unchanged {m' m3 : Mem} {s q u : BitVec 64} {lq lu : Nat} (v : BitVec 64)
    (qj : Nat) (hm3 : UnchangedExcept m' m3 s 24) (hs : u.toNat ≤ s.toNat ∧ s.toNat + 24 ≤ u.toNat + lu)
    (hq : q.toNat ≤ qj ∧ qj + 8 ≤ q.toNat + lq) :
    UnchangedExcept2 m' (memStore m3 qj v) q lq u lu := by
  intro k hkq hku
  rw [getElem?_memStore_of_ne _ _ _ _ (by omega)]
  exact hm3 k (by omega)

/-- The frame of `udivrem_knuth_normalized<3>()` after a change of words of q and u. -/
theorem K3Frame.step {x : Regs} {m : Mem} {x' x'' : Regs} {m' m'' : Mem}
    (hpre : udivrem_knuth_normalized_3.pre x m) (hF : K3Frame x m x' m')
    (h2 : UnchangedExcept2 m' m'' (x.get 10#5) (8 * ((x.get 12#5).toNat - 3)) (x.get 11#5)
      (8 * (x.get 12#5).toNat))
    (hsp : x''.get 2#5 = x'.get 2#5)
    (hcs : ∀ r ∈ calleeSaved, r ∉ [2#5, 8#5, 9#5, 18#5, 19#5, 20#5, 21#5, 22#5, 23#5] →
      x''.get r = x'.get r) :
    K3Frame x m x'' m'' := by
  simp only [udivrem_knuth_normalized_3.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨-, -, -, -, -, -, ⟨-, hsn⟩, -, hdsq, hdsu, -⟩ := hpre
  obtain ⟨hsp', h1, h8, h9, h18, h19, h20, h21, h22, h23, hun, hcs'⟩ := hF
  have hf : ∀ c : Nat, c < 80 → c % 8 = 0 →
      memWord m'' (x.get 2#5 - 80#64 + BitVec.ofNat 64 c).toNat =
        memWord m' (x.get 2#5 - 80#64 + BitVec.ofNat 64 c).toNat := by
    intro c hc _
    have : (x.get 2#5 - 80#64 + BitVec.ofNat 64 c).toNat = (x.get 2#5 - 80#64).toNat + c :=
      toNat_add8 _ _ (by omega) (by omega)
    exact memWord_of_unchangedExcept2 h2 _ (by rw [this]; omega) (by rw [this]; omega)
  have e : ∀ c : BitVec 64, x.get 2#5 + c = x.get 2#5 - 80#64 + BitVec.ofNat 64 (c + 80#64).toNat := by
    intro c; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub,
      BitVec.toNat_ofNat]; omega
  refine ⟨hsp.trans hsp', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e, hf _ (by decide) (by decide), ← e]; exact h1
  · rw [e, hf _ (by decide) (by decide), ← e]; exact h8
  · rw [e, hf _ (by decide) (by decide), ← e]; exact h9
  · rw [e, hf _ (by decide) (by decide), ← e]; exact h18
  · rw [e, hf _ (by decide) (by decide), ← e]; exact h19
  · rw [e, hf _ (by decide) (by decide), ← e]; exact h20
  · rw [e, hf _ (by decide) (by decide), ← e]; exact h21
  · rw [e, hf _ (by decide) (by decide), ← e]; exact h22
  · rw [e, hf _ (by decide) (by decide), ← e]; exact h23
  · intro k hq hu hs
    rw [h2 k hq hu]; exact hun k hq hu hs
  · intro r hr hnr
    rw [hcs r hr hnr]; exact hcs' r hr hnr

/-- The addresses of the words of the frame of 80 bytes below sp. -/
theorem k3_frame_toNat (sp : BitVec 64) (hs : (sp - 80#64).toNat + 80 ≤ 2 ^ 64) :
    (sp + 18446744073709551608#64).toNat = (sp - 80#64).toNat + 72 ∧
    (sp + 18446744073709551600#64).toNat = (sp - 80#64).toNat + 64 ∧
    (sp + 18446744073709551592#64).toNat = (sp - 80#64).toNat + 56 ∧
    (sp + 18446744073709551584#64).toNat = (sp - 80#64).toNat + 48 ∧
    (sp + 18446744073709551576#64).toNat = (sp - 80#64).toNat + 40 ∧
    (sp + 18446744073709551568#64).toNat = (sp - 80#64).toNat + 32 ∧
    (sp + 18446744073709551560#64).toNat = (sp - 80#64).toNat + 24 ∧
    (sp + 18446744073709551552#64).toNat = (sp - 80#64).toNat + 16 ∧
    (sp + 18446744073709551544#64).toNat = (sp - 80#64).toNat + 8 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_omega

theorem ptr_add_8 (p : BitVec 64) (k : Nat) :
    p + BitVec.ofNat 64 (8 * k) + 8#64 = p + BitVec.ofNat 64 (8 * (k + 1)) := by
  rw [BitVec.add_assoc]; congr 1; bv_omega

theorem ptr_add_16 (p : BitVec 64) (k : Nat) :
    p + BitVec.ofNat 64 (8 * k) + 16#64 = p + BitVec.ofNat 64 (8 * (k + 2)) := by
  rw [BitVec.add_assoc]; congr 1; bv_omega

/-- The epilogue of `udivrem_knuth_normalized<3>()` at 0x290: the registers restored from the frame
and the return. -/
theorem k3_exit {hi : BitVec 20} {lo : BitVec 12} {Dt : List (BitVec 64)} (base : BitVec 64)
    (x : Regs) (m : Mem) (hr : x.get 1#5 &&& 3 = 0) (x4 : Regs) (m4 : Mem)
    (hF : K3Frame x m x4 m4)
    (hq : words m4 (x.get 10#5) ((x.get 12#5).toNat - 3) =
      words m (x.get 11#5) (x.get 12#5).toNat / words m (x.get 13#5) 3)
    (hu : words m4 (x.get 11#5) (x.get 12#5).toNat % 2 ^ (64 * 3) =
      words m (x.get 11#5) (x.get 12#5).toNat % words m (x.get 13#5) 3) :
    Reach (bufWords (x.get 13#5) 3 ++ bufWords (x.get 10#5) ((x.get 12#5).toNat - 3) ++
        bufWords (x.get 11#5) (x.get 12#5).toNat ++ bufWords (x.get 2#5 - 80#64) 10 ++ Dt)
      (udivrem_knuth_normalized_3_progAt hi lo) base (pcAt base 164) x4 m4 (x.get 1#5)
      (udivrem_knuth_normalized_3.post x m) := by
  obtain ⟨hsp, hfra, hfs0, hfs1, hfs2, hfs3, hfs4, hfs5, hfs6, hfs7, hunF, hcsF⟩ := hF
  rw [← regs_set_of_get' (by decide) hsp]
  rv_exec
  rename_i wra hwra ws0 hws0 ws1 hws1 ws2 hws2 ws3 hws3 ws4 hws4 ws5 hws5 ws6 hws6 ws7 hws7
  rw [hfra] at hwra
  rw [hfs0] at hws0
  rw [hfs1] at hws1
  rw [hfs2] at hws2
  rw [hfs3] at hws3
  rw [hfs4] at hws4
  rw [hfs5] at hws5
  rw [hfs6] at hws6
  rw [hfs7] at hws7
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.reduceSignExtend,
    BitVec.add_zero]
  rw [hwra.eq, update_aligned hr]
  refine Reach.refl ?_
  simp only [udivrem_knuth_normalized_3.post]
  simp (disch := decide) only [Regs.eq_get x]
  refine ⟨hq, hu, hunF, ?_⟩
  intro r hr'
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
  all_goals first
    | exact (Regs.eq_get x (by decide)).symm
    | (rw [Regs.eq_get x4 (by decide), Regs.eq_get x (by decide)]
       exact hcsF _ (by decide) (by decide))
    | (rw [Regs.eq_get x (by decide)]
       first
         | exact hws0 | exact hws1 | exact hws2 | exact hws3 | exact hws4 | exact hws5
         | exact hws6 | exact hws7)

/-- The registers that the step of a digit keeps for the tail. -/
def k3Kept : List (BitVec 5) :=
  [2#5, 3#5, 4#5, 8#5, 13#5, 18#5, 19#5, 20#5, 21#5, 22#5, 24#5, 25#5, 26#5, 27#5]

/-- From the store of the quotient digit at 0x1e8 to the head of the loop for the digit `j - 1`, or
for `j = 0` to the return. -/
theorem k3_tail {hi : BitVec 20} {lo : BitVec 12} {Dt : List (BitVec 64)} (base : BitVec 64)
    (x : Regs) (m : Mem) (hr : x.get 1#5 &&& 3 = 0) (hpre : udivrem_knuth_normalized_3.pre x m)
    (j : Nat) (x' : Regs) (m' : Mem) (hh : k3Head x m j x' m') (x3 : Regs) (m3 : Mem)
    (h3 : ∀ r ∈ k3Kept, x3.get r = x'.get r)
    (hm3 : UnchangedExcept m' m3 (x'.get 8#5) 24)
    (hdig : (x3.get 23#5).toNat * words m (x.get 13#5) 3 + words m3 (x'.get 8#5) 3 =
      words m' (x'.get 8#5) 4)
    (hlt : words m3 (x'.get 8#5) 3 < words m (x.get 13#5) 3)
    (h12 : x3.get 12#5 = memWord m3 (x'.get 8#5 + 8#64).toNat)
    (h14 : x3.get 14#5 = memWord m3 (x'.get 8#5 + 16#64).toNat)
    (ih : ∀ k < j, ∀ x' m', k3Head x m k x' m' →
      Reach (udivrem_knuth_normalized_3.bufs x ++ Dt) (udivrem_knuth_normalized_3_progAt hi lo)
        base (pcAt base 76) x' m' (x.get 1#5) (udivrem_knuth_normalized_3.post x m)) :
    Reach (udivrem_knuth_normalized_3.bufs x ++ Dt) (udivrem_knuth_normalized_3_progAt hi lo)
      base (pcAt base 122) x3 m3 (x.get 1#5) (udivrem_knuth_normalized_3.post x m) := by
  obtain ⟨hj4, hF, h8, h21, h20, h13, h18, h19, h22, h12', h14', hlow, hQR, hRD⟩ := hh
  have hpre' := hpre
  simp only [udivrem_knuth_normalized_3.pre, Buf, Disjoint] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hqa, hqn⟩, ⟨hua, hun⟩, ⟨hda, hdn⟩, hdqd, hdqu, hdud, ⟨hsa, hsn⟩, hdsd, hdsq, hdsu, -,
    hn3, hD, hU⟩ := hpre'
  have hF0 := hF
  obtain ⟨hsp, hfra, hfs0, hfs1, hfs2, hfs3, hfs4, hfs5, hfs6, hfs7, hunF, hcsF⟩ := hF
  have k2 := h3 2#5 (by decide)
  have k8 := h3 8#5 (by decide)
  have k20 := h3 20#5 (by decide)
  have k21 := h3 21#5 (by decide)
  rw [hsp] at k2
  rw [h8] at k8
  rw [h20] at k20
  rw [h21] at k21
  -- The addresses of the words j and j + 1 of q and u.
  have hn := (x.get 12#5).toNat
  have hqj : (x.get 10#5 + BitVec.ofNat 64 (8 * j)).toNat = (x.get 10#5).toNat + 8 * j :=
    toNat_add8 _ _ (by omega) (by omega)
  have huj : (x.get 11#5 + BitVec.ofNat 64 (8 * j)).toNat = (x.get 11#5).toNat + 8 * j :=
    toNat_add8 _ _ (by omega) (by omega)
  have hq1 : x.get 10#5 + BitVec.ofNat 64 (8 * j) + 8 = x.get 10#5 + BitVec.ofNat 64 (8 * (j + 1)) := by
    rw [BitVec.add_assoc, ofNat_add8]
  have hu1 : x.get 11#5 + BitVec.ofNat 64 (8 * j) + 8 = x.get 11#5 + BitVec.ofNat 64 (8 * (j + 1)) := by
    rw [BitVec.add_assoc, ofNat_add8]
  rw [h8] at hm3 hdig hlt h12 h14
  -- The memory after the store of the digit.
  set m4 := memStore m3 (x.get 10#5 + BitVec.ofNat 64 (8 * j)).toNat (x3.get 23#5) with hm4
  have hQ3 : words m3 (x.get 10#5 + BitVec.ofNat 64 (8 * (j + 1))) ((x.get 12#5).toNat - 4 - j) =
      words m' (x.get 10#5 + BitVec.ofNat 64 (8 * (j + 1))) ((x.get 12#5).toNat - 4 - j) := by
    rcases Nat.eq_zero_or_pos ((x.get 12#5).toNat - 4 - j) with h0 | h0
    · rw [h0]; rfl
    · have := toNat_add8 (x.get 10#5) (8 * (j + 1)) (by omega) (by omega)
      exact words_of_unchangedExcept hm3 _ _ (by omega) (by rw [huj]; omega)
  have hQ4 : words m4 (x.get 10#5 + BitVec.ofNat 64 (8 * j)) ((x.get 12#5).toNat - 3 - j) =
      (x3.get 23#5).toNat + 2 ^ 64 *
        words m' (x.get 10#5 + BitVec.ofNat 64 (8 * (j + 1))) ((x.get 12#5).toNat - 4 - j) := by
    rw [hm4, words_memStore_first _ _ _ _ (by omega) (by rw [hqj]; omega), hq1, ← hQ3,
      show (x.get 12#5).toNat - 3 - j - 1 = (x.get 12#5).toNat - 4 - j by omega]
  have hR4 : words m4 (x.get 11#5 + BitVec.ofNat 64 (8 * j)) 3 =
      words m3 (x.get 11#5 + BitVec.ofNat 64 (8 * j)) 3 :=
    words_memStore_of_disjoint _ _ _ _ _ (by rw [huj]; omega) (by rw [huj, hqj]; omega)
  have hmem4 : ∀ b, b + 8 ≤ (x.get 10#5).toNat + 8 * j ∨ (x.get 10#5).toNat + 8 * j + 8 ≤ b →
      memWord m4 b = memWord m3 b := fun b hb =>
    memWord_memStore_of_ne _ _ _ _ (by rw [hqj]; omega)
  -- The digit: the quotient and the remainder of the digits from j.
  have hN : words m' (x.get 11#5 + BitVec.ofNat 64 (8 * j)) 4 =
      (memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * j)).toNat).toNat + 2 ^ 64 *
        words m' (x.get 11#5 + BitVec.ofNat 64 (8 * (j + 1))) 3 := by
    rw [words, hu1, hlow j le_rfl]
  have hdigit := knuth_digit hQR (q := (x3.get 23#5).toNat)
    (R' := words m3 (x.get 11#5 + BitVec.ofNat 64 (8 * j)) 3)
    (by rw [hdig, hN, ← words_digit m (x.get 11#5) (by omega)]; ring)
  simp only [udivrem_knuth_normalized_3.bufs]
  simp (disch := decide) only [Regs.eq_get x]
  rw [← regs_set_of_get' (by decide) k2, ← regs_set_of_get' (by decide) k8,
    ← regs_set_of_get' (by decide) k20, ← regs_set_of_get' (by decide) k21]
  -- The store of the quotient digit q[j].
  refine Reach.step (by decide) rfl ?_
  simp only [StepGoal, Nat.reduceAdd, BitVec.reduceSignExtend, BitVec.add_zero]
  rv_val
  refine ⟨List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (mem_bufWords (by omega))))), ?_⟩
  have h2 := k3_step_unchanged (q := x.get 10#5) (u := x.get 11#5)
    (lq := 8 * ((x.get 12#5).toNat - 3)) (lu := 8 * (x.get 12#5).toNat) (x3.get 23#5)
    (x.get 10#5 + BitVec.ofNat 64 (8 * j)).toNat hm3 ⟨by rw [huj]; omega, by rw [huj]; omega⟩
    ⟨by rw [hqj]; omega, by rw [hqj]; omega⟩
  rw [← hm4] at h2
  have hF4 : ∀ x4 : Regs, x4.get 2#5 = x'.get 2#5 → (∀ r ∈ [3#5, 4#5, 24#5, 25#5, 26#5, 27#5],
      x4.get r = x3.get r) → K3Frame x m x4 m4 := by
    intro x4 h42 h4c
    refine K3Frame.step hpre hF0 h2 h42 (fun r hr hnr => ?_)
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr hnr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;>
      first | (simp at hnr; done) | (rw [h4c _ (by decide)]; exact h3 _ (by decide))
  rv_exec_cut 76 164
  · -- The next digit.
    rename_i hb
    have hj0 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · subst h0; exact absurd (by decide) hb
      · exact h0
    refine ih (j - 1) (by omega) _ _ ?_
    have ej : j - 1 + 1 = j := Nat.sub_add_cancel hj0
    refine ⟨by omega, hF4 _ ?_ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · exact hsp.symm
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp (config := { decide := true }) only [↓reduceIte]
    · rw [← BitVec.add_assoc, ptr_sub8 _ _ hj0 (by omega)]
    · rw [← BitVec.add_assoc, ptr_sub8 _ _ hj0 (by omega)]
    · rw [ofNat_sub1 _ (by omega) (by omega), Nat.add_sub_cancel, ej]
    · rw [h3 _ (by decide), h13]
    · rw [h3 _ (by decide), h18]
    · rw [h3 _ (by decide), h19]
    · rw [h3 _ (by decide), h3 _ (by decide), h3 _ (by decide), h22]
    · have := toNat_add8 (x.get 11#5) (8 * (j + 1)) (by omega) (by omega)
      rw [h12, show j - 1 + 2 = j + 1 by omega, ptr_add_8, hmem4 _ (by rw [this]; omega)]
    · have := toNat_add8 (x.get 11#5) (8 * (j + 2)) (by omega) (by omega)
      rw [h14, show j - 1 + 3 = j + 2 by omega, ptr_add_16, hmem4 _ (by rw [this]; omega)]
    · intro k hk
      have := toNat_add8 (x.get 11#5) (8 * k) (by omega) (by omega)
      rw [hmem4 _ (by rw [this]; omega), memWord_of_unchangedExcept hm3 _ (by rw [this, huj]; omega),
        hlow k (by omega)]
    · rw [ej, show (x.get 12#5).toNat - 4 - (j - 1) = (x.get 12#5).toNat - 3 - j by omega, hQ4,
        hR4]
      exact hdigit
    · rw [ej, hR4]; exact hlt
  · -- The last digit: the epilogue.
    rename_i hb
    have hj1 : j + 1 < 2 ^ 64 := by
      have := (x.get 12#5).isLt
      clear * - hj4 this
      omega
    have hj0 : j = 0 := Nat.succ.inj (ofNat_sub1_eq_zero (j + 1) hj1 hb)
    have hq0 : x.get 10#5 + BitVec.ofNat 64 (8 * j) = x.get 10#5 := by
      rw [hj0]; exact BitVec.add_zero _
    have hu0 : x.get 11#5 + BitVec.ofNat 64 (8 * j) = x.get 11#5 := by
      rw [hj0]; exact BitVec.add_zero _
    rw [hq0, hj0, Nat.sub_zero] at hQ4
    rw [hu0] at hR4 hdigit hlt
    rw [hj0, Nat.mul_zero, pow_zero, Nat.div_one] at hdigit
    obtain ⟨hq, hr'⟩ := knuth_noborrow ((Nat.add_comm _ _).trans hdigit)
      (hdigit ▸ Nat.add_lt_add_left hlt _)
    refine k3_exit base x m hr _ _ (hF4 _ ?_ ?_) ?_ ?_
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact hsp.symm
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · rw [hQ4]; exact hq
    · have hs := words_split m4 3 ((x.get 12#5).toNat - 3) (x.get 11#5)
      rw [show 3 + ((x.get 12#5).toNat - 3) = (x.get 12#5).toNat by omega] at hs
      rw [hs, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (words_lt _ _ _), hR4, ← hr']

theorem ptr_add_24 (p : BitVec 64) (k : Nat) :
    p + BitVec.ofNat 64 (8 * k) + 24#64 = p + BitVec.ofNat 64 (8 * (k + 3)) := by
  rw [BitVec.add_assoc]; congr 1; bv_omega

/-- The 4 words at `a`. -/
theorem words4_eq (m : Mem) (a : BitVec 64) :
    words m a 4 = (memWord m a.toNat).toNat + 2 ^ 64 * ((memWord m (a + 8#64).toNat).toNat +
      2 ^ 64 * ((memWord m (a + 16#64).toNat).toNat + 2 ^ 64 * (memWord m (a + 24#64).toNat).toNat)) := by
  simp only [words, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero, Nat.add_zero]
  rfl

/-- The top 2 words of a normalized 3-word divisor. -/
theorem k3_dhi {D d0 X : Nat} (hD : 2 ^ (64 * 3 - 1) ≤ D) (he : D = d0 + 2 ^ 64 * X)
    (h0 : d0 < 2 ^ 64) : 2 ^ 127 ≤ X := by
  omega

/-- The digit of the overflow: `submul()` gives `N - (2^64 - 1) * D` for the 4 words `N` whose top 3
words `R` are below `D` and start with the top 2 words of `D`. -/
theorem k3_over_nat {S D d0 d1 d2 r0 uj N L k : Nat} (hS : S < 2 ^ 192)
    (hk : S + (2 ^ 64 - 1) * D = L + k * 2 ^ 192) (hL : L < 2 ^ 192)
    (hD : D = d0 + 2 ^ 64 * (d1 + 2 ^ 64 * d2)) (hd0 : d0 < 2 ^ 64) (hd2 : 2 ^ 63 ≤ d2)
    (hd2' : d2 < 2 ^ 64) (hR : r0 + 2 ^ 64 * (d1 + 2 ^ 64 * d2) < D) (huj : uj < 2 ^ 64)
    (hN : N = uj + 2 ^ 64 * (r0 + 2 ^ 64 * (d1 + 2 ^ 64 * d2)))
    (hNL : N = L + 2 ^ 192 * d2) :
    (2 ^ 64 - 1) * D + S = N ∧ S < D := by
  have ho := knuth_overflow (N := N) (R := r0 + 2 ^ 64 * (d1 + 2 ^ 64 * d2)) (u := uj) (P := 2 ^ 64)
    (dhi := d1 + 2 ^ 64 * d2) (dlo := d0) (hD.trans (by ring)) hd0 (by omega) hR (by omega) huj
    (hN.trans (by ring))
  have hDK : D ≤ 2 ^ 192 := by omega
  have := over_words (t := d2) hS hk hNL ho.1 ho.2 hDK
  omega

theorem k3_d2 {D d0 d1 d2 : Nat} (hD : 2 ^ (64 * 3 - 1) ≤ D)
    (he : D = d0 + 2 ^ 64 * (d1 + 2 ^ 64 * d2)) (h0 : d0 < 2 ^ 64) (h1 : d1 < 2 ^ 64) :
    2 ^ 63 ≤ d2 := by
  omega

theorem k3Kept_not_overCl : ∀ r ∈ k3Kept, r ∉ k3OverCl ∧ r ≠ 0 := by decide

/-- A word of a buffer within another buffer. -/
theorem mem_bufWords_within {a b : BitVec 64} {n n' k : Nat} (hb : b = a + BitVec.ofNat 64 (8 * k))
    (h : k + n ≤ n') : ∀ c ∈ bufWords b n, c ∈ bufWords a n' := by
  intro c hc
  subst hb
  induction n generalizing k c with
  | zero => simp [bufWords] at hc
  | succ n ih =>
    simp only [bufWords, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact mem_bufWords (by omega)
    · exact ih (k := k + 1) (by omega) c (by rwa [BitVec.add_assoc, ofNat_add8] at hc)

/-- The words of d in the memory of the loop: d is outside q, u and the frame. -/
theorem k3_d_words {x : Regs} {m m' : Mem} (hpre : udivrem_knuth_normalized_3.pre x m)
    (hun : UnchangedExcept3 m m' (x.get 10#5) (8 * ((x.get 12#5).toNat - 3)) (x.get 11#5)
      (8 * (x.get 12#5).toNat) (x.get 2#5 - 80#64) 80) :
    words m' (x.get 13#5) 3 = words m (x.get 13#5) 3 := by
  simp only [udivrem_knuth_normalized_3.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨-, -, ⟨-, hdn⟩, hdqd, -, hdud, -, hdsd, -, -, -⟩ := hpre
  have h8 : (x.get 13#5 + 8#64).toNat = (x.get 13#5).toNat + 8 := by bv_omega
  have h16 : (x.get 13#5 + 16#64).toNat = (x.get 13#5).toNat + 16 := by bv_omega
  rw [words3_eq, words3_eq]
  have e : ∀ c, (x.get 13#5).toNat ≤ c → c + 8 ≤ (x.get 13#5).toNat + 24 → memWord m' c = memWord m c := by
    intro c h1 h2
    simp only [memWord, Std.ExtHashMap.getD_eq_getD_getElem?]
    rw [hun c (by omega) (by omega) (by omega), hun (c + 1) (by omega) (by omega) (by omega),
      hun (c + 2) (by omega) (by omega) (by omega), hun (c + 3) (by omega) (by omega) (by omega),
      hun (c + 4) (by omega) (by omega) (by omega), hun (c + 5) (by omega) (by omega) (by omega),
      hun (c + 6) (by omega) (by omega) (by omega), hun (c + 7) (by omega) (by omega) (by omega)]
  rw [e _ (by omega) (by omega), e _ (by omega) (by omega), e _ (by omega) (by omega)]

theorem k3Kept_not_cl : ∀ r ∈ k3Kept, r ∉ [10#5, 11#5, 12#5, 14#5, 15#5, 23#5] ∧
    r ∉ [10#5, 11#5, 12#5, 14#5, 15#5, 16#5, 23#5] ∧ r ≠ 10#5 ∧ r ≠ 0 := by decide

/-- The word at `b` outside the three regions that may change. -/
theorem memWord_of_unchangedExcept3 {m m' : Mem} {a b c : BitVec 64} {la lb lc : Nat}
    (h : UnchangedExcept3 m m' a la b lb c lc) (e : Nat) (ha : e + 8 ≤ a.toNat ∨ a.toNat + la ≤ e)
    (hb : e + 8 ≤ b.toNat ∨ b.toNat + lb ≤ e) (hc : e + 8 ≤ c.toNat ∨ c.toNat + lc ≤ e) :
    memWord m' e = memWord m e := by
  simp only [memWord, Std.ExtHashMap.getD_eq_getD_getElem?]
  rw [h e (by omega) (by omega) (by omega), h (e + 1) (by omega) (by omega) (by omega),
    h (e + 2) (by omega) (by omega) (by omega), h (e + 3) (by omega) (by omega) (by omega),
    h (e + 4) (by omega) (by omega) (by omega), h (e + 5) (by omega) (by omega) (by omega),
    h (e + 6) (by omega) (by omega) (by omega), h (e + 7) (by omega) (by omega) (by omega)]

/-- A word of d in the memory of the loop. -/
theorem k3_d_mem {x : Regs} {m m' : Mem} (hpre : udivrem_knuth_normalized_3.pre x m)
    (hun : UnchangedExcept3 m m' (x.get 10#5) (8 * ((x.get 12#5).toNat - 3)) (x.get 11#5)
      (8 * (x.get 12#5).toNat) (x.get 2#5 - 80#64) 80) (k : BitVec 64) (hk : k = 8#64 ∨ k = 16#64) :
    memWord m' (x.get 13#5 + k).toNat = memWord m (x.get 13#5 + k).toNat := by
  simp only [udivrem_knuth_normalized_3.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨-, -, ⟨-, hdn⟩, hdqd, -, hdud, -, hdsd, -, -, -⟩ := hpre
  have hc : (x.get 13#5).toNat + 8 ≤ (x.get 13#5 + k).toNat ∧
      (x.get 13#5 + k).toNat + 8 ≤ (x.get 13#5).toNat + 24 := by
    rcases hk with rfl | rfl <;> constructor <;> bv_omega
  exact memWord_of_unchangedExcept3 hun _ (by omega) (by omega) (by omega)

/-- The loop of `udivrem_knuth_normalized<3>()` from its head at 0x130. -/
theorem k3_loop {hi : BitVec 20} {lo : BitVec 12} {Dt : List (BitVec 64)} (base : BitVec 64)
    (x : Regs) (m : Mem) (hb : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0)
    (hpre : udivrem_knuth_normalized_3.pre x m) :
    ∀ j x' m', k3Head x m j x' m' →
    Reach (udivrem_knuth_normalized_3.bufs x ++ Dt) (udivrem_knuth_normalized_3_progAt hi lo)
      base (pcAt base 76) x' m' (x.get 1#5) (udivrem_knuth_normalized_3.post x m) := by
  apply Reach.loop (k3Head x m)
  intro j x' m' hh ih
  have hh0 := hh
  obtain ⟨hj4, hF, h8, h21, h20, h13, h18, h19, h22, h12, h14, hlow, hQR, hRD⟩ := hh
  have hpre' := hpre
  simp only [udivrem_knuth_normalized_3.pre, Buf, Disjoint] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hqa, hqn⟩, ⟨hua, hun⟩, ⟨hda, hdn⟩, hdqd, hdqu, hdud, ⟨hsa, hsn⟩, hdsd, hdsq, hdsu, -,
    hn3, hD, hU⟩ := hpre'
  -- The pointer to u[j] and the words of d.
  have hj1 : 8 * j < 2 ^ 64 ∧ (x.get 11#5).toNat + 8 * j < 2 ^ 64 ∧
      (x.get 11#5).toNat + 8 * j + 32 ≤ (x.get 11#5).toNat + 8 * (x.get 12#5).toNat := by
    clear * - hj4 hun; omega
  have hs0 : (x'.get 8#5).toNat = (x.get 11#5).toNat + 8 * j := by
    rw [h8]; exact toNat_add8 _ _ hj1.1 hj1.2.1
  have hDm := k3_d_words hpre hF.2.2.2.2.2.2.2.2.2.2.1
  have hDw := words3_eq m (x.get 13#5)
  rw [← h18, ← h19] at hDw
  have hd2 := k3_d2 hD hDw (memWord m (x.get 13#5).toNat).isLt (x'.get 18#5).isLt
  have hbufs : ∀ a ∈ bufWords (x'.get 13#5) 3 ++ bufWords (x'.get 8#5) 3,
      a ∈ udivrem_knuth_normalized_3.bufs x ++ Dt := by
    intro a ha
    simp only [udivrem_knuth_normalized_3.bufs]
    simp (disch := decide) only [Regs.eq_get x]
    rw [h13] at ha
    rcases List.mem_append.mp ha with ha | ha
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ ha)))
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        (mem_bufWords_within h8 (by clear * - hj4; omega) a ha)))
  -- The words of the partial remainder.
  have hRw := words3_eq m' (x.get 11#5 + BitVec.ofNat 64 (8 * (j + 1)))
  rw [ptr_add_8, ptr_add_16, ← h12, ← h14] at hRw
  have a8 : x'.get 8#5 + 8#64 = x.get 11#5 + BitVec.ofNat 64 (8 * (j + 1)) := by
    rw [h8, ptr_add_8]
  have a16 : x'.get 8#5 + 16#64 = x.get 11#5 + BitVec.ofNat 64 (8 * (j + 2)) := by
    rw [h8, ptr_add_16]
  have a24 : x'.get 8#5 + 24#64 = x.get 11#5 + BitVec.ofNat 64 (8 * (j + 3)) := by
    rw [h8, ptr_add_24]
  have hNw := words4_eq m' (x'.get 8#5)
  rw [a8, a16, a24, ← h12, ← h14] at hNw
  have hLw := words3_eq m' (x'.get 8#5)
  rw [a8, a16, ← h12] at hLw
  -- The overflow: the top 2 words of the remainder are the top 2 words of d.
  have hover : x'.get 12#5 = x'.get 18#5 → x'.get 14#5 = x'.get 19#5 →
      Reach (udivrem_knuth_normalized_3.bufs x ++ Dt) (udivrem_knuth_normalized_3_progAt hi lo)
        base (pcAt base 128) x' m' (x.get 1#5) (udivrem_knuth_normalized_3.post x m) := by
    intro e12 e14
    have hds : Disjoint (x'.get 8#5) 24 (x'.get 13#5) 24 := by
      simp only [Disjoint]; rw [hs0, h13]; clear * - hj1 hdud; omega
    refine Reach.trans (Reach.mono_bufs hbufs (k3_over base x' m' hb (by rw [hs0]; omega)
      (by rw [hs0]; clear * - hua; omega) (by rw [h13]; exact hdn) (by rw [h13]; exact hda) hds)) ?_
    intro x3 m3 ⟨⟨k, hk⟩, hun3, h23, h12', h14', hcl⟩
    rw [h13, hDm] at hk
    have hS := words_lt m3 3 (x'.get 8#5)
    have hL := words_lt m' 3 (x'.get 8#5)
    rw [e12, e14] at hRw hNw
    rw [e12] at hLw
    have hov := k3_over_nat hS hk hL hDw (memWord m (x.get 13#5).toNat).isLt hd2
      (x'.get 19#5).isLt (hRw ▸ hRD) (memWord m' (x'.get 8#5).toNat).isLt hNw
      (by rw [hNw, hLw]; ring)
    refine k3_tail base x m hr hpre j x' m' hh0 x3 m3 ?_ hun3 ?_ hov.2 h12' h14' ih
    · intro r hr'
      obtain ⟨hr1, hr0⟩ := k3Kept_not_overCl r hr'
      rw [← Regs.eq_get x3 hr0, ← Regs.eq_get x' hr0]; exact hcl r hr1
    · rw [h23, show (18446744073709551615#64).toNat = 2 ^ 64 - 1 from rfl, ← hov.1]
  -- The division of the top 3 words by the top 2 words of d.
  have hnorm : ¬(x'.get 12#5 = x'.get 18#5 ∧ x'.get 14#5 = x'.get 19#5) →
      Reach (udivrem_knuth_normalized_3.bufs x ++ Dt) (udivrem_knuth_normalized_3_progAt hi lo)
        base (pcAt base 78) x' m' (x.get 1#5) (udivrem_knuth_normalized_3.post x m) := by
    intro hne
    -- The word u[j + 1] at 0x138.
    refine Reach.step (by decide) rfl ?_
    simp only [StepGoal, Nat.reduceAdd, BitVec.reduceSignExtend]
    refine ⟨hbufs _ (List.mem_append_right _
      (mem_bufWords (n := 3) (i := 1) (a := x'.get 8#5) (by norm_num) : _)), fun w hw => ?_⟩
    have g : ∀ r, r ≠ 10#5 → (x'.set 10#5 w).get r = x'.get r := by
      intro r hr; rw [Regs.get_set, if_neg hr]; split_ifs with h0 <;> simp [Regs.get, h0]
    have g10 : (x'.set 10#5 w).get 10#5 = w := by
      simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    have hne' : ¬((x'.get 12#5).toNat = (x'.get 18#5).toNat ∧
        (x'.get 14#5).toNat = (x'.get 19#5).toNat) :=
      fun ⟨e1, e2⟩ => hne ⟨BitVec.eq_of_toNat_eq e1, BitVec.eq_of_toNat_eq e2⟩
    have hR' := hRD
    rw [hRw, hDw] at hR'
    have hu := top2_lt_of_lt (memWord m' (x.get 11#5 + BitVec.ofNat 64 (8 * (j + 1))).toNat).isLt
      (memWord m (x.get 13#5).toNat).isLt hR' hne' (x'.get 12#5).isLt (x'.get 18#5).isLt
    have hDhi := k3_dhi hD hDw (memWord m (x.get 13#5).toNat).isLt
    refine Reach.trans (k3_div base (x'.set 10#5 w) m' ?_ ?_ ?_) ?_
    · rw [g 18#5 (by decide), g 19#5 (by decide)]; exact hDhi
    · rw [g 14#5 (by decide), g 12#5 (by decide), g 18#5 (by decide), g 19#5 (by decide)]
      exact hu
    · rw [g 22#5 (by decide), g 18#5 (by decide), g 19#5 (by decide)]; exact h22
    intro x2 m2 ⟨hm2, hq2, hr2, h02, hcl2⟩
    subst m2
    have e2 : ∀ r, r ∉ [10#5, 11#5, 12#5, 14#5, 15#5, 16#5, 23#5] → r ≠ 0 → x2.get r = x'.get r := by
      intro r hr hr0
      rw [← Regs.eq_get x2 hr0, hcl2 r hr, Regs.eq_get (x'.set 10#5 w) hr0, g r (by
        intro h; subst h; exact hr (by decide))]
    have e8 := e2 8#5 (by decide) (by decide)
    have e13 := e2 13#5 (by decide) (by decide)
    have e18 := e2 18#5 (by decide) (by decide)
    have e19 := e2 19#5 (by decide) (by decide)
    rw [g 14#5 (by decide), g 12#5 (by decide), g 18#5 (by decide), g 19#5 (by decide), g10]
      at hq2 hr2
    have hDpos : 0 < (x'.get 18#5).toNat + 2 ^ 64 * (x'.get 19#5).toNat := by
      clear * - hDhi; omega
    have hds : Disjoint (x'.get 8#5) 24 (x'.get 13#5) 24 := by
      simp only [Disjoint]; rw [hs0, h13]; clear * - hj1 hdud; omega
    refine Reach.trans (Reach.mono_bufs (A := bufWords (x2.get 13#5) 3 ++ bufWords (x2.get 8#5) 3)
      (by rw [e13, e8]; exact hbufs)
      (k3_sub (hi := hi) (lo := lo) base x2 m'
        ((x'.get 14#5).toNat * 2 ^ 128 + (x'.get 12#5).toNat * 2 ^ 64 + w.toNat)
        (by rw [e8, hs0]; clear * - hj1 hun; omega) (by rw [e13, h13]; exact hdn)
        (by rw [e8, e13]; exact hds)
        (by rw [e18, e13, h13, h18, k3_d_mem hpre hF.2.2.2.2.2.2.2.2.2.2.1 _ (Or.inl rfl)])
        (by rw [e19, e13, h13, h19, k3_d_mem hpre hF.2.2.2.2.2.2.2.2.2.2.1 _ (Or.inr rfl)])
        (by rw [e18, e19]; exact hDhi)
        (by rw [hq2, hr2, e18, e19]; exact Nat.div_add_mod' _ _)
        (by rw [hr2, e18, e19]; exact Nat.mod_lt _ hDpos))) ?_
    intro x3 m3 ⟨hdig, hlt, hun3, h12', h14', h03, hcl3⟩
    rw [e8, e13, h13, hDm] at hdig hlt
    rw [e8] at hun3 h12' h14'
    refine k3_tail base x m hr hpre j x' m' hh0 x3 m3 ?_ hun3 ?_ hlt h12' h14' ih
    · intro r hr'
      obtain ⟨h1, h2, h3, h0⟩ := k3Kept_not_cl r hr'
      rw [← Regs.eq_get x3 h0, hcl3 r h1, Regs.eq_get x2 h0]
      exact e2 r h2 h0
    · rw [hdig, hNw, hw.eq, a8]; ring
  rv_step
  all_goals try rv_step
  · rename_i hb
    exact hnorm (fun h => hb h.1)
  · rename_i hb1 hb
    exact hover (by simpa using hb1) hb
  · rename_i hb1 hb
    exact hnorm (fun h => by simp only [beq_eq_false_iff_ne] at hb; exact hb h.2)

theorem k3_addr_u2 (u n : BitVec 64) (h : 4 ≤ n.toNat) :
    u + n <<< 3 + 18446744073709551600#64 = u + BitVec.ofNat 64 (8 * (n.toNat - 4 + 2)) := by
  bv_omega

theorem k3_addr_u3 (u n : BitVec 64) (h : 4 ≤ n.toNat) :
    u + (n <<< 3 + 18446744073709551608#64) = u + BitVec.ofNat 64 (8 * (n.toNat - 4 + 3)) := by
  bv_omega

/-- The memory after the prologue of `udivrem_knuth_normalized<3>()`: ra and s0 to s7 stored in the
frame. -/
abbrev k3FrameMem (x : Regs) (m : Mem) : Mem :=
  memStore (memStore (memStore (memStore (memStore (memStore (memStore (memStore (memStore m
    (x.get 2#5 + 18446744073709551608#64).toNat (x.get 1#5))
    (x.get 2#5 + 18446744073709551600#64).toNat (x.get 8#5))
    (x.get 2#5 + 18446744073709551592#64).toNat (x.get 9#5))
    (x.get 2#5 + 18446744073709551584#64).toNat (x.get 18#5))
    (x.get 2#5 + 18446744073709551576#64).toNat (x.get 19#5))
    (x.get 2#5 + 18446744073709551568#64).toNat (x.get 20#5))
    (x.get 2#5 + 18446744073709551560#64).toNat (x.get 21#5))
    (x.get 2#5 + 18446744073709551552#64).toNat (x.get 22#5))
    (x.get 2#5 + 18446744073709551544#64).toNat (x.get 23#5)

theorem k3FrameMem_unchanged (x : Regs) (m : Mem)
    (hs : (x.get 2#5 - 80#64).toNat + 80 ≤ 2 ^ 64) :
    UnchangedExcept m (k3FrameMem x m) (x.get 2#5 - 80#64) 80 := by
  obtain ⟨f1, f8, f9, f18, f19, f20, f21, f22, f23⟩ := k3_frame_toNat (x.get 2#5) hs
  simp only [k3FrameMem]
  rw [unchangedExcept_memStore _ _ (by omega), unchangedExcept_memStore _ _ (by omega),
    unchangedExcept_memStore _ _ (by omega), unchangedExcept_memStore _ _ (by omega),
    unchangedExcept_memStore _ _ (by omega), unchangedExcept_memStore _ _ (by omega),
    unchangedExcept_memStore _ _ (by omega), unchangedExcept_memStore _ _ (by omega),
    unchangedExcept_memStore _ _ (by omega)]
  exact unchangedExcept_refl _ _ _

theorem k3FrameMem_words (x : Regs) (m : Mem) (hs : (x.get 2#5 - 80#64).toNat + 80 ≤ 2 ^ 64) :
    memWord (k3FrameMem x m) (x.get 2#5 + 18446744073709551608#64).toNat = x.get 1#5 ∧
    memWord (k3FrameMem x m) (x.get 2#5 + 18446744073709551600#64).toNat = x.get 8#5 ∧
    memWord (k3FrameMem x m) (x.get 2#5 + 18446744073709551592#64).toNat = x.get 9#5 ∧
    memWord (k3FrameMem x m) (x.get 2#5 + 18446744073709551584#64).toNat = x.get 18#5 ∧
    memWord (k3FrameMem x m) (x.get 2#5 + 18446744073709551576#64).toNat = x.get 19#5 ∧
    memWord (k3FrameMem x m) (x.get 2#5 + 18446744073709551568#64).toNat = x.get 20#5 ∧
    memWord (k3FrameMem x m) (x.get 2#5 + 18446744073709551560#64).toNat = x.get 21#5 ∧
    memWord (k3FrameMem x m) (x.get 2#5 + 18446744073709551552#64).toNat = x.get 22#5 ∧
    memWord (k3FrameMem x m) (x.get 2#5 + 18446744073709551544#64).toNat = x.get 23#5 := by
  obtain ⟨f1, f8, f9, f18, f19, f20, f21, f22, f23⟩ := k3_frame_toNat (x.get 2#5) hs
  simp only [k3FrameMem]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := omega) only [memWord_memStore_self, memWord_memStore_of_ne]

theorem k3_addr_end (p n : BitVec 64) (h : 4 ≤ n.toNat) :
    p + (n <<< 3 + 18446744073709551584#64) = p + BitVec.ofNat 64 (8 * (n.toNat - 4)) := by
  bv_omega

/-- The top 3 words of u: the remainder of the digits above the digit `n - 4`. -/
theorem k3_top3 (m : Mem) (u : BitVec 64) (n : Nat) (hn : 4 ≤ n) :
    words m u n / 2 ^ (64 * (n - 4 + 1)) = words m (u + BitVec.ofNat 64 (8 * (n - 4 + 1))) 3 := by
  have hs := words_split m (n - 4 + 1) 3 u
  rw [show n - 4 + 1 + 3 = n by omega] at hs
  rw [hs, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (words_lt _ _ _),
    Nat.zero_add]

/-- The frame of 80 bytes below sp is outside the image: its first and last words are. -/
theorem k3_frame_outside (sp base : BitVec 64) (o : Nat)
    (h0 : (sp - 80#64).toNat + 8 ≤ base.toNat ∨ base.toNat + o ≤ (sp - 80#64).toNat)
    (h9 : (sp - 80#64 + BitVec.ofNat 64 (8 * 9)).toNat + 8 ≤ base.toNat ∨
      base.toNat + o ≤ (sp - 80#64 + BitVec.ofNat 64 (8 * 9)).toNat)
    (hs : (sp - 80#64).toNat + 80 ≤ 2 ^ 64) (ho : 80 ≤ o) :
    (sp - 80#64).toNat + 80 ≤ base.toNat ∨ base.toNat + o ≤ (sp - 80#64).toNat := by
  have : (sp - 80#64 + BitVec.ofNat 64 (8 * 9)).toNat = (sp - 80#64).toNat + 72 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  omega

end IntxRV.Api
