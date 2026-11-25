import IntxRV.Knuth3
import IntxRV.Gen.Api.udivrem_knuth_normalized_4

/-!
# The blocks and the loop of `internal::udivrem_knuth_normalized<4>()`

The code of the 4-word instance has the structure of the 3-word one (`IntxRV/Knuth3.lean`), in its
image after `submul()`, 22 instructions from the start: the inlined `udivrem_3by2()` of the top 3
words of the partial remainder by the top 2 words d[2] and d[3] of d (`k4_div`), the subtraction
of the multiple of the low words d[0] and d[1] with the add-back of the 4 words of d (`k4_sub`, by
`knuth4_noborrow` and `knuth4_addback`), and the digit `2^64 - 1` by the call of `submul()` at the
start of the image (`k4_over`). The loop (`k4Head`, `k4_tail`, `k4_loop`) is the loop of the
3-word instance with the 4-word remainder.
-/

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace IntxRV.Api
open IntxRV IntxRV.Gen

/-- The inlined `udivrem_3by2()` of `udivrem_knuth_normalized<4>()`, from 0x13c to 0x1b0 of its code
(22 instructions after `submul()` in its image; the correction at 0x264): `a4:a2:a0` by `s3:s2`
with the reciprocal in s6, to the quotient in s7 and the remainder in `a0:a1`. -/
theorem k4_div {A : List (BitVec 64)} {hi : BitVec 20} {lo : BitVec 12} (base : BitVec 64)
    (x : Regs) (m : Mem)
    (hd : 2 ^ 127 ≤ (x.get 18#5).toNat + 2 ^ 64 * (x.get 19#5).toNat)
    (hu : (x.get 14#5).toNat * 2 ^ 64 + (x.get 12#5).toNat <
      (x.get 18#5).toNat + 2 ^ 64 * (x.get 19#5).toNat)
    (hv : (x.get 22#5).toNat =
      (2 ^ 192 - 1) / ((x.get 18#5).toNat + 2 ^ 64 * (x.get 19#5).toNat) - 2 ^ 64) :
    Reach A (udivrem_knuth_normalized_4_progAt hi lo) base (pcAt base 101) x m (pcAt base 130)
      (fun x' m' => m' = m ∧ Div3Out x x' ((x.get 14#5).toNat * 2 ^ 128 +
        (x.get 12#5).toNat * 2 ^ 64 + (x.get 10#5).toNat)
        ((x.get 18#5).toNat + 2 ^ 64 * (x.get 19#5).toNat) 23#5 11#5 10#5
        [10#5, 11#5, 12#5, 14#5, 15#5, 16#5, 23#5]) := by
  by2_div3_paths div3by2BVo_spec true (x.get 14#5) (x.get 12#5) (x.get 10#5) (x.get 18#5)
    (x.get 19#5) (x.get 22#5) hd hu hv

/-- The 4-word addition of the add-back of `udivrem_knuth_normalized<4>()`, without the carry out. -/
theorem add4_words_nc {r0 r1 r2 r3 v0 v1 v2 v3 a0 c0 a1 e1 n1 f1 c1 a2 e2 n2 f2 c2 a3 n3 : BitVec 64}
    (ha0 : Defn a0 (r0 + v0)) (hc0 : Defn c0 (if a0 < r0 then 1#64 else 0#64))
    (ha1 : Defn a1 (r1 + v1)) (he1 : Defn e1 (if a1 < r1 then 1#64 else 0#64))
    (hn1 : Defn n1 (a1 + c0)) (hf1 : Defn f1 (if n1 < a1 then 1#64 else 0#64))
    (hc1 : Defn c1 (e1 ||| f1))
    (ha2 : Defn a2 (r2 + v2)) (he2 : Defn e2 (if a2 < r2 then 1#64 else 0#64))
    (hn2 : Defn n2 (a2 + c1)) (hf2 : Defn f2 (if n2 < a2 then 1#64 else 0#64))
    (hc2 : Defn c2 (e2 ||| f2)) (ha3 : Defn a3 (r3 + v3)) (hn3 : Defn n3 (a3 + c2)) :
    ∃ co, a0.toNat + 2 ^ 64 * (n1.toNat + 2 ^ 64 * (n2.toNat + 2 ^ 64 * n3.toNat)) + 2 ^ 256 * co =
      r0.toNat + 2 ^ 64 * (r1.toNat + 2 ^ 64 * (r2.toNat + 2 ^ 64 * r3.toNat)) +
        (v0.toNat + 2 ^ 64 * (v1.toNat + 2 ^ 64 * (v2.toNat + 2 ^ 64 * v3.toNat))) := by
  have e0 := defn_carry_left ha0 hc0
  have l0 := defn_bit_le hc0
  obtain ⟨e1', l1⟩ := defn_add_carry ha1 he1 hn1 hf1 hc1 l0
  obtain ⟨e2', l2⟩ := defn_add_carry ha2 he2 hn2 hf2 hc2 l1
  have h3 := defn_add ha3
  have h3' := defn_add hn3
  refine ⟨(r3.toNat + v3.toNat + c2.toNat) / 2 ^ 64, ?_⟩
  have := r3.isLt; have := v3.isLt
  omega

/-- The memory with the 4 words at `a` stored. -/
abbrev memStore4 (m : Mem) (a w0 w1 w2 w3 : BitVec 64) : Mem :=
  memStore (memStore (memStore (memStore m a.toNat w0) (a + 8#64).toNat w1) (a + 16#64).toNat w2)
    (a + 24#64).toNat w3

theorem memStore4_words (m : Mem) (a w0 w1 w2 w3 : BitVec 64) (ha : a.toNat + 32 ≤ 2 ^ 64) :
    words (memStore4 m a w0 w1 w2 w3) a 4 =
        w0.toNat + 2 ^ 64 * (w1.toNat + 2 ^ 64 * (w2.toNat + 2 ^ 64 * w3.toNat)) ∧
      memWord (memStore4 m a w0 w1 w2 w3) (a + 16#64).toNat = w2 ∧
      memWord (memStore4 m a w0 w1 w2 w3) (a + 24#64).toNat = w3 := by
  have h8 : (a + 8#64).toNat = a.toNat + 8 := by bv_omega
  have h16 : (a + 16#64).toNat = a.toNat + 16 := by bv_omega
  have h24 : (a + 24#64).toNat = a.toNat + 24 := by bv_omega
  rw [words4_eq]
  refine ⟨?_, ?_, ?_⟩
  · simp (disch := omega) only [memWord_memStore_self, memWord_memStore_of_ne]
  · simp (disch := omega) only [memWord_memStore_self, memWord_memStore_of_ne]
  · simp only [memWord_memStore_self]

theorem memStore4_unchanged {m m' : Mem} (a w0 w1 w2 w3 : BitVec 64) (ha : a.toNat + 32 ≤ 2 ^ 64) :
    UnchangedExcept m (memStore4 m' a w0 w1 w2 w3) a 32 ↔ UnchangedExcept m m' a 32 := by
  have h8 : (a + 8#64).toNat = a.toNat + 8 := by bv_omega
  have h16 : (a + 16#64).toNat = a.toNat + 16 := by bv_omega
  have h24 : (a + 24#64).toNat = a.toNat + 24 := by bv_omega
  simp only [memStore4]
  rw [unchangedExcept_memStore _ _ (by omega), unchangedExcept_memStore _ _ (by omega),
    unchangedExcept_memStore _ _ (by omega), unchangedExcept_memStore _ _ (by omega)]

/-- The 4-word `submul()` of the high word: at most `2^64 - 1` with the borrow. -/
theorem k4_kb_lt {k1 b1 : BitVec 64} (hk : k1.toNat ≤ 2 ^ 64 - 2) (hb : b1.toNat ≤ 1) :
    k1.toNat + b1.toNat < 2 ^ 64 := by omega

/-- The registers and the memory after the subtraction of the multiple of the divisor of a digit of
`udivrem_knuth_normalized<4>()`: the quotient digit of `N` by `D` in s7, the remainder in the 4
words at `s`, and its words 2 and 3 in a2 and a4, the top words of the next remainder. -/
def K4Sub (x x' : Regs) (m m' : Mem) (s : BitVec 64) (N D : Nat) : Prop :=
  (x'.get 23#5).toNat * D + words m' s 4 = N ∧ words m' s 4 < D ∧ UnchangedExcept m m' s 32 ∧
    x'.get 12#5 = memWord m' (s + 16#64).toNat ∧ x'.get 14#5 = memWord m' (s + 24#64).toNat ∧
    x' 0 = x 0 ∧ ∀ r, r ∉ [5#5, 10#5, 11#5, 12#5, 14#5, 15#5, 16#5, 17#5, 23#5] → x' r = x r

theorem k4_sub {hi : BitVec 20} {lo : BitVec 12} (base : BitVec 64) (x : Regs) (m : Mem)
    (Nt : Nat)
    (hs : (x.get 8#5).toNat + 32 ≤ 2 ^ 64) (hdn : (x.get 13#5).toNat + 32 ≤ 2 ^ 64)
    (hds : Disjoint (x.get 8#5) 32 (x.get 13#5) 32)
    (h18 : x.get 18#5 = memWord m (x.get 13#5 + 16#64).toNat)
    (h19 : x.get 19#5 = memWord m (x.get 13#5 + 24#64).toNat)
    (hD : 2 ^ 127 ≤ (x.get 18#5).toNat + 2 ^ 64 * (x.get 19#5).toNat)
    (hq : (x.get 23#5).toNat * ((x.get 18#5).toNat + 2 ^ 64 * (x.get 19#5).toNat) +
      ((x.get 11#5).toNat + 2 ^ 64 * (x.get 10#5).toNat) = Nt)
    (hr : (x.get 11#5).toNat + 2 ^ 64 * (x.get 10#5).toNat <
      (x.get 18#5).toNat + 2 ^ 64 * (x.get 19#5).toNat) :
    Reach (bufWords (x.get 13#5) 4 ++ bufWords (x.get 8#5) 4) (udivrem_knuth_normalized_4_progAt hi lo)
      base (pcAt base 130) x m (pcAt base 157) (fun x' m' => K4Sub x x' m m' (x.get 8#5)
        (Nt * 2 ^ 128 + ((memWord m (x.get 8#5).toNat).toNat +
          2 ^ 64 * (memWord m (x.get 8#5 + 8#64).toNat).toNat)) (words m (x.get 13#5) 4)) := by
  simp only [Disjoint] at hds
  have hdw := words4_eq m (x.get 13#5)
  rw [← h18, ← h19] at hdw
  have hdw' : words m (x.get 13#5) 4 = (memWord m (x.get 13#5).toNat).toNat +
      2 ^ 64 * (memWord m (x.get 13#5 + 8#64).toNat).toNat +
      2 ^ 128 * ((x.get 18#5).toNat + 2 ^ 64 * (x.get 19#5).toNat) := by rw [hdw]; ring
  rv_exec
  all_goals simp (config := { decide := true }) only [K4Sub, Regs.get_set, ↓reduceIte,
    BitVec.reduceSignExtend, BitVec.add_zero]
  · -- The borrow: d added back.
    rename_i wd0 hwd0 wuj hwuj wuj1 hwuj1 lo0 hlo0 s0w hs0w wd1 hwd1 hi0 hhi0 lo1 hlo1 hi1 hhi1
      p1 hp1 c hc k1 hk1 b0 hb0 dd hdd e he s1w hs1w f hf t ht b1 hb1 t' ht' c1 hc1 h hh hb
      wd0' hwd0' n0 hn0 wd1' hwd1' k0 hk0 e1 he1 n1 hn1 wd2 hwd2 k1a hk1a k1b hk1b kc1 hkc1
      e2 he2 k2a hk2a n2 hn2 wd3 hwd3 k2b hk2b kc2 hkc2 e3 he3 n3 hn3
    simp only [zopz0zI_u_eq, decide_eq_true_eq] at hb
    have hm0 := defn_mul_mulhu hlo0 hhi0
    have hm1 := defn_mul_mulhu hlo1 hhi1
    rw [hwd0.eq] at hm0
    rw [hwd1.eq] at hm1
    have hp := (defn_carry_left hp1 hc).trans (Nat.add_comm _ _)
    have hk := defn_add_exact hk1 (by have := defn_mulhu_le hhi1; have := defn_bit hc; omega)
    rw [Nat.add_comm] at hk
    have hkl := knuth4_hi_le (memWord m (x.get 13#5).toNat).isLt
      (memWord m (x.get 13#5 + 8#64).toNat).isLt (x.get 23#5).isLt hm0 hm1 hp hk
    have hs0 := defn_sub_borrow0 hs0w hb0
    obtain ⟨hs1, hb1'⟩ := defn_sub_borrow hdd he hs1w hf hb1 (defn_bit hb0)
    have hT1 := defn_sub2_borrow ht ht' hc1 (k4_kb_lt hkl hb1')
    have hT2 := (sub_borrow_cases hh).2 hb
    obtain ⟨co, hadd⟩ := add4_words_nc hn0 hk0 he1 hk1a hn1 hk1b hkc1 he2 hk2a hn2 hk2b hkc2 he3 hn3
    rw [hwd0'.eq, hwd1'.eq, hwd2.eq, hwd3.eq, ← h18, ← h19] at hadd
    rw [hwuj.eq] at hs0
    rw [hwuj1.eq] at hs1
    obtain ⟨hw4, h16, h24⟩ := memStore4_words (memStore4 m (x.get 8#5) s0w s1w t' h) (x.get 8#5)
      n0 n1 n2 n3 hs
    have hw4' : n0.toNat + 2 ^ 64 * (n1.toNat + 2 ^ 64 * (n2.toNat + 2 ^ 64 * n3.toNat)) < 2 ^ 256 :=
      hw4 ▸ words_lt _ 4 _
    rw [← hdw] at hadd
    obtain ⟨hq1, hres, hlt⟩ := knuth4_addback hdw' (memWord m (x.get 13#5).toNat).isLt
      (memWord m (x.get 13#5 + 8#64).toNat).isLt hD (lt_2_128_of_words rfl) hq hr
      (x.get 23#5).isLt (memWord m (x.get 8#5).toNat).isLt
      (memWord m (x.get 8#5 + 8#64).toNat).isLt s0w.isLt s1w.isLt t'.isLt h.isLt hm0 hm1 hp hk
      hs0 hs1 hT1 hT2 hw4' hadd
    have hq' := toNat_add_neg1 _ hq1
    refine ⟨?_, ?_, ?_, h16.symm, h24.symm, ?_, ?_⟩
    · rw [hq', hw4, hres]
    · rw [hw4]; exact hlt
    · exact (memStore4_unchanged _ _ _ _ _ hs).mpr
        ((memStore4_unchanged _ _ _ _ _ hs).mpr (unchangedExcept_refl _ _ _))
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp (config := { decide := true }) only [Regs.set_apply, hr, ↓reduceIte]
  · -- No borrow.
    rename_i wd0 hwd0 wuj hwuj wuj1 hwuj1 lo0 hlo0 s0w hs0w wd1 hwd1 hi0 hhi0 lo1 hlo1 hi1 hhi1
      p1 hp1 c hc k1 hk1 b0 hb0 dd hdd e he s1w hs1w f hf t ht b1 hb1 t' ht' c1 hc1 h hh hb
    simp only [zopz0zI_u_eq, decide_eq_false_iff_not] at hb
    have hm0 := defn_mul_mulhu hlo0 hhi0
    have hm1 := defn_mul_mulhu hlo1 hhi1
    rw [hwd0.eq] at hm0
    rw [hwd1.eq] at hm1
    have hp := (defn_carry_left hp1 hc).trans (Nat.add_comm _ _)
    have hk := defn_add_exact hk1 (by have := defn_mulhu_le hhi1; have := defn_bit hc; omega)
    rw [Nat.add_comm] at hk
    have hkl := knuth4_hi_le (memWord m (x.get 13#5).toNat).isLt
      (memWord m (x.get 13#5 + 8#64).toNat).isLt (x.get 23#5).isLt hm0 hm1 hp hk
    have hs0 := defn_sub_borrow0 hs0w hb0
    obtain ⟨hs1, hb1'⟩ := defn_sub_borrow hdd he hs1w hf hb1 (defn_bit hb0)
    have hT1 := defn_sub2_borrow ht ht' hc1 (k4_kb_lt hkl hb1')
    have hT2 := (sub_borrow_cases hh).1 hb
    rw [hwuj.eq] at hs0
    rw [hwuj1.eq] at hs1
    obtain ⟨hw4, h16, h24⟩ := memStore4_words m (x.get 8#5) s0w s1w t' h hs
    obtain ⟨hres, hlt⟩ := knuth4_noborrow hdw' (memWord m (x.get 13#5).toNat).isLt
      (memWord m (x.get 13#5 + 8#64).toNat).isLt hD hq hr (x.get 23#5).isLt
      (memWord m (x.get 8#5).toNat).isLt (memWord m (x.get 8#5 + 8#64).toNat).isLt hm0 hm1 hp hk
      hs0 hs1 hT1 hT2
    refine ⟨?_, ?_, (memStore4_unchanged _ _ _ _ _ hs).mpr (unchangedExcept_refl _ _ _), h16.symm,
      h24.symm, ?_, ?_⟩
    · rw [hw4]; exact hres
    · rw [hw4]; exact hlt
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp (config := { decide := true }) only [Regs.set_apply, hr, ↓reduceIte]

/-- The division overflows, from 0x234 to 0x21c of the code of `udivrem_knuth_normalized<4>()`: the
4 words at s0 less `2^64 - 1` times d by the call of `submul()` (at the start of its image), the digit `2^64 - 1` in s7, and the words 1 and 2 of the remainder
in a2 and a4. -/
theorem k4_over {hi : BitVec 20} {lo : BitVec 12} (base : BitVec 64) (x : Regs) (m : Mem)
    (hb : base &&& 3 = 0)
    (hs : (x.get 8#5).toNat + 32 ≤ 2 ^ 64) (hsa : (x.get 8#5).toNat % 8 = 0)
    (hdn : (x.get 13#5).toNat + 32 ≤ 2 ^ 64) (hda : (x.get 13#5).toNat % 8 = 0)
    (hds : Disjoint (x.get 8#5) 32 (x.get 13#5) 32) :
    Reach (bufWords (x.get 13#5) 4 ++ bufWords (x.get 8#5) 4) (udivrem_knuth_normalized_4_progAt hi lo)
      base (pcAt base 163) x m (pcAt base 157) (fun x' m' =>
        (∃ k, words m' (x.get 8#5) 4 + (2 ^ 64 - 1) * words m (x.get 13#5) 4 =
          words m (x.get 8#5) 4 + k * 2 ^ 256) ∧
        UnchangedExcept m m' (x.get 8#5) 32 ∧ x'.get 23#5 = 18446744073709551615#64 ∧
        x'.get 12#5 = memWord m' (x.get 8#5 + 16#64).toNat ∧
        x'.get 14#5 = memWord m' (x.get 8#5 + 24#64).toNat ∧
        ∀ r, r ∉ k3OverCl → x' r = x r) := by
  simp only [Disjoint] at hds
  rv_exec_cut 0
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  rw [show (0#5 : BitVec 5) = 0 from rfl, Regs.get_zero, zero_add,
    show pcAt base 169 + BitVec.signExtend 64 3420#12 = pcAt base 0 by
      simp only [pcAt, BitVec.reduceSignExtend]; bv_omega,
    update_aligned (by simp only [pcAt]; exact aligned_add hb (by decide))]
  refine Reach.call_sub (r := 171) udivrem_knuth_normalized_4_progAt_submul_in
    (by rw [udivrem_knuth_normalized_4_progAt_length]; decide)
    (submul.reach (pcAt base 0) _ m ?_ ?_) ?_ ?_ ?_
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    simp only [pcAt]; exact aligned_add hb (by decide)
  · simp only [submul.pre, Buf, Disjoint]
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    try simp (disch := decide) only [Regs.eq_get x]
    simp only [show (4#64).toNat = 4 from rfl, and_true]
    omega
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · intro a ha
    simp only [submul.bufs] at ha
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at ha
    try simp (disch := decide) only [Regs.eq_get x] at ha
    rwa [show (4#64).toNat = 4 from rfl] at ha
  · intro x3 m3 hpost
    simp only [submul.post] at hpost
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at hpost
    obtain ⟨hres, hun, hcs⟩ := hpost
    rw [show (4#64).toNat = 4 from rfl] at hres hun
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
      show 64 * 4 = 256 from rfl] at hres
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


/-- The top 2 words of the 4-word remainder are less than the top 2 words of `d` unless they are
equal. -/
theorem top2_lt_of_lt4 {r0 r1 r2 r3 d0 d1 d2 d3 : Nat} (h0 : r0 < 2 ^ 64) (h1 : r1 < 2 ^ 64)
    (hd0 : d0 < 2 ^ 64) (hd1 : d1 < 2 ^ 64)
    (hR : r0 + 2 ^ 64 * (r1 + 2 ^ 64 * (r2 + 2 ^ 64 * r3)) <
      d0 + 2 ^ 64 * (d1 + 2 ^ 64 * (d2 + 2 ^ 64 * d3)))
    (hne : ¬(r2 = d2 ∧ r3 = d3)) (h2 : r2 < 2 ^ 64) (hd2 : d2 < 2 ^ 64) :
    r3 * 2 ^ 64 + r2 < d2 + 2 ^ 64 * d3 := by
  omega

/-- The words of `submul()` of the overflow of 4 words: `S + X` is `N` with `N - X` below `D`. -/
theorem over_words4 {S X L N D k t : Nat} (hS : S < 2 ^ 256) (h : S + X = L + k * 2 ^ 256)
    (hN : N = L + 2 ^ 256 * t) (hX : X ≤ N) (hNX : N < X + D) (hDK : D ≤ 2 ^ 256) :
    S + X = N := by
  omega

/-- The 5 words at `a`. -/
theorem words5_eq (m : Mem) (a : BitVec 64) :
    words m a 5 = (memWord m a.toNat).toNat + 2 ^ 64 * ((memWord m (a + 8#64).toNat).toNat +
      2 ^ 64 * ((memWord m (a + 16#64).toNat).toNat + 2 ^ 64 * ((memWord m (a + 24#64).toNat).toNat +
        2 ^ 64 * (memWord m (a + 32#64).toNat).toNat))) := by
  simp only [words, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero, Nat.add_zero]
  rfl

theorem ptr_add_32 (p : BitVec 64) (k : Nat) :
    p + BitVec.ofNat 64 (8 * k) + 32#64 = p + BitVec.ofNat 64 (8 * (k + 4)) := by
  rw [BitVec.add_assoc]; congr 1; bv_omega

/-- The frame of `udivrem_knuth_normalized<4>()` after its prologue: sp 80 bytes lower, ra and
s0 to s7 saved, and the memory outside q, u and the frame unchanged. -/
def K4Frame (x : Regs) (m : Mem) (x' : Regs) (m' : Mem) : Prop :=
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
  UnchangedExcept3 m m' (x.get 10#5) (8 * ((x.get 12#5).toNat - 4)) (x.get 11#5)
    (8 * (x.get 12#5).toNat) (x.get 2#5 - 80#64) 80 ∧
  ∀ r ∈ calleeSaved, r ∉ [2#5, 8#5, 9#5, 18#5, 19#5, 20#5, 21#5, 22#5, 23#5] → x'.get r = x.get r

/-- The registers and the memory at the head of the loop of `udivrem_knuth_normalized<4>()` at
0x1b8 of its image for the digit `j` of u: the pointers to u[j] in s0 and q[j] in s5, `j + 1` in s4, the top
words of the divisor and the reciprocal, the words j + 3 and j + 4 of u (the top of the partial
remainder) in a2 and a4, the words of u up to j unchanged, and the quotient and the remainder of
the digits of u above j by d. -/
def k4Head (x : Regs) (m : Mem) (j : Nat) (x' : Regs) (m' : Mem) : Prop :=
  j + 5 ≤ (x.get 12#5).toNat ∧ K4Frame x m x' m' ∧
  x'.get 8#5 = x.get 11#5 + BitVec.ofNat 64 (8 * j) ∧
  x'.get 21#5 = x.get 10#5 + BitVec.ofNat 64 (8 * j) ∧
  x'.get 20#5 = BitVec.ofNat 64 (j + 1) ∧ x'.get 13#5 = x.get 13#5 ∧
  x'.get 18#5 = memWord m (x.get 13#5 + 16#64).toNat ∧
  x'.get 19#5 = memWord m (x.get 13#5 + 24#64).toNat ∧
  (x'.get 22#5).toNat =
    (2 ^ 192 - 1) / ((x'.get 18#5).toNat + 2 ^ 64 * (x'.get 19#5).toNat) - 2 ^ 64 ∧
  x'.get 12#5 = memWord m' (x.get 11#5 + BitVec.ofNat 64 (8 * (j + 3))).toNat ∧
  x'.get 14#5 = memWord m' (x.get 11#5 + BitVec.ofNat 64 (8 * (j + 4))).toNat ∧
  (∀ k, k ≤ j → memWord m' (x.get 11#5 + BitVec.ofNat 64 (8 * k)).toNat =
    memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * k)).toNat) ∧
  words m' (x.get 10#5 + BitVec.ofNat 64 (8 * (j + 1))) ((x.get 12#5).toNat - 5 - j) *
      words m (x.get 13#5) 4 + words m' (x.get 11#5 + BitVec.ofNat 64 (8 * (j + 1))) 4 =
    words m (x.get 11#5) (x.get 12#5).toNat / 2 ^ (64 * (j + 1)) ∧
  words m' (x.get 11#5 + BitVec.ofNat 64 (8 * (j + 1))) 4 < words m (x.get 13#5) 4

/-- The memory after a digit of `udivrem_knuth_normalized<4>()`: u[j..j+4) and q[j] changed. -/
theorem k4_step_unchanged {m' m3 : Mem} {s q u : BitVec 64} {lq lu : Nat} (v : BitVec 64)
    (qj : Nat) (hm3 : UnchangedExcept m' m3 s 32) (hs : u.toNat ≤ s.toNat ∧ s.toNat + 32 ≤ u.toNat + lu)
    (hq : q.toNat ≤ qj ∧ qj + 8 ≤ q.toNat + lq) :
    UnchangedExcept2 m' (memStore m3 qj v) q lq u lu := by
  intro k hkq hku
  rw [getElem?_memStore_of_ne _ _ _ _ (by omega)]
  exact hm3 k (by omega)

/-- The frame of `udivrem_knuth_normalized<4>()` after a change of words of q and u. -/
theorem K4Frame.step {x : Regs} {m : Mem} {x' x'' : Regs} {m' m'' : Mem}
    (hpre : udivrem_knuth_normalized_4.pre x m) (hF : K4Frame x m x' m')
    (h2 : UnchangedExcept2 m' m'' (x.get 10#5) (8 * ((x.get 12#5).toNat - 4)) (x.get 11#5)
      (8 * (x.get 12#5).toNat))
    (hsp : x''.get 2#5 = x'.get 2#5)
    (hcs : ∀ r ∈ calleeSaved, r ∉ [2#5, 8#5, 9#5, 18#5, 19#5, 20#5, 21#5, 22#5, 23#5] →
      x''.get r = x'.get r) :
    K4Frame x m x'' m'' := by
  simp only [udivrem_knuth_normalized_4.pre, Buf, Disjoint] at hpre
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

/-- The epilogue of `udivrem_knuth_normalized<4>()` at 0x338 of its image: the registers restored from the frame
and the return. -/
theorem k4_exit {hi : BitVec 20} {lo : BitVec 12} {Dt : List (BitVec 64)} (base : BitVec 64)
    (x : Regs) (m : Mem) (hr : x.get 1#5 &&& 3 = 0) (x4 : Regs) (m4 : Mem)
    (hF : K4Frame x m x4 m4)
    (hq : words m4 (x.get 10#5) ((x.get 12#5).toNat - 4) =
      words m (x.get 11#5) (x.get 12#5).toNat / words m (x.get 13#5) 4)
    (hu : words m4 (x.get 11#5) (x.get 12#5).toNat % 2 ^ (64 * 4) =
      words m (x.get 11#5) (x.get 12#5).toNat % words m (x.get 13#5) 4) :
    Reach (bufWords (x.get 13#5) 4 ++ bufWords (x.get 10#5) ((x.get 12#5).toNat - 4) ++
        bufWords (x.get 11#5) (x.get 12#5).toNat ++ bufWords (x.get 2#5 - 80#64) 10 ++ Dt)
      (udivrem_knuth_normalized_4_progAt hi lo) base (pcAt base 206) x4 m4 (x.get 1#5)
      (udivrem_knuth_normalized_4.post x m) := by
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
  simp only [udivrem_knuth_normalized_4.post]
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

/-- From the store of the quotient digit at 0x274 of the image of `udivrem_knuth_normalized<4>()` to the head of the loop for the digit `j - 1`, or
for `j = 0` to the return. -/
theorem k4_tail {hi : BitVec 20} {lo : BitVec 12} {Dt : List (BitVec 64)} (base : BitVec 64)
    (x : Regs) (m : Mem) (hr : x.get 1#5 &&& 3 = 0) (hpre : udivrem_knuth_normalized_4.pre x m)
    (j : Nat) (x' : Regs) (m' : Mem) (hh : k4Head x m j x' m') (x3 : Regs) (m3 : Mem)
    (h3 : ∀ r ∈ k3Kept, x3.get r = x'.get r)
    (hm3 : UnchangedExcept m' m3 (x'.get 8#5) 32)
    (hdig : (x3.get 23#5).toNat * words m (x.get 13#5) 4 + words m3 (x'.get 8#5) 4 =
      words m' (x'.get 8#5) 5)
    (hlt : words m3 (x'.get 8#5) 4 < words m (x.get 13#5) 4)
    (h12 : x3.get 12#5 = memWord m3 (x'.get 8#5 + 16#64).toNat)
    (h14 : x3.get 14#5 = memWord m3 (x'.get 8#5 + 24#64).toNat)
    (ih : ∀ k < j, ∀ x' m', k4Head x m k x' m' →
      Reach (udivrem_knuth_normalized_4.bufs x ++ Dt) (udivrem_knuth_normalized_4_progAt hi lo)
        base (pcAt base 98) x' m' (x.get 1#5) (udivrem_knuth_normalized_4.post x m)) :
    Reach (udivrem_knuth_normalized_4.bufs x ++ Dt) (udivrem_knuth_normalized_4_progAt hi lo)
      base (pcAt base 157) x3 m3 (x.get 1#5) (udivrem_knuth_normalized_4.post x m) := by
  obtain ⟨hj4, hF, h8, h21, h20, h13, h18, h19, h22, h12', h14', hlow, hQR, hRD⟩ := hh
  have hpre' := hpre
  simp only [udivrem_knuth_normalized_4.pre, Buf, Disjoint] at hpre'
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
  have hQ3 : words m3 (x.get 10#5 + BitVec.ofNat 64 (8 * (j + 1))) ((x.get 12#5).toNat - 5 - j) =
      words m' (x.get 10#5 + BitVec.ofNat 64 (8 * (j + 1))) ((x.get 12#5).toNat - 5 - j) := by
    rcases Nat.eq_zero_or_pos ((x.get 12#5).toNat - 5 - j) with h0 | h0
    · rw [h0]; rfl
    · have := toNat_add8 (x.get 10#5) (8 * (j + 1)) (by omega) (by omega)
      exact words_of_unchangedExcept hm3 _ _ (by omega) (by rw [huj]; omega)
  have hQ4 : words m4 (x.get 10#5 + BitVec.ofNat 64 (8 * j)) ((x.get 12#5).toNat - 4 - j) =
      (x3.get 23#5).toNat + 2 ^ 64 *
        words m' (x.get 10#5 + BitVec.ofNat 64 (8 * (j + 1))) ((x.get 12#5).toNat - 5 - j) := by
    rw [hm4, words_memStore_first _ _ _ _ (by omega) (by rw [hqj]; omega), hq1, ← hQ3,
      show (x.get 12#5).toNat - 4 - j - 1 = (x.get 12#5).toNat - 5 - j by omega]
  have hR4 : words m4 (x.get 11#5 + BitVec.ofNat 64 (8 * j)) 4 =
      words m3 (x.get 11#5 + BitVec.ofNat 64 (8 * j)) 4 :=
    words_memStore_of_disjoint _ _ _ _ _ (by rw [huj]; omega) (by rw [huj, hqj]; omega)
  have hmem4 : ∀ b, b + 8 ≤ (x.get 10#5).toNat + 8 * j ∨ (x.get 10#5).toNat + 8 * j + 8 ≤ b →
      memWord m4 b = memWord m3 b := fun b hb =>
    memWord_memStore_of_ne _ _ _ _ (by rw [hqj]; omega)
  -- The digit: the quotient and the remainder of the digits from j.
  have hN : words m' (x.get 11#5 + BitVec.ofNat 64 (8 * j)) 5 =
      (memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * j)).toNat).toNat + 2 ^ 64 *
        words m' (x.get 11#5 + BitVec.ofNat 64 (8 * (j + 1))) 4 := by
    rw [words, hu1, hlow j le_rfl]
  have hdigit := knuth_digit hQR (q := (x3.get 23#5).toNat)
    (R' := words m3 (x.get 11#5 + BitVec.ofNat 64 (8 * j)) 4)
    (by rw [hdig, hN, ← words_digit m (x.get 11#5) (by omega)]; ring)
  simp only [udivrem_knuth_normalized_4.bufs]
  simp (disch := decide) only [Regs.eq_get x]
  rw [← regs_set_of_get' (by decide) k2, ← regs_set_of_get' (by decide) k8,
    ← regs_set_of_get' (by decide) k20, ← regs_set_of_get' (by decide) k21]
  -- The store of the quotient digit q[j].
  refine Reach.step (by decide) (by rv_fetch) ?_
  simp only [StepGoal, Nat.reduceAdd, BitVec.reduceSignExtend, BitVec.add_zero]
  rv_val
  refine ⟨List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (mem_bufWords (by omega))))), ?_⟩
  have h2 := k4_step_unchanged (q := x.get 10#5) (u := x.get 11#5)
    (lq := 8 * ((x.get 12#5).toNat - 4)) (lu := 8 * (x.get 12#5).toNat) (x3.get 23#5)
    (x.get 10#5 + BitVec.ofNat 64 (8 * j)).toNat hm3 ⟨by rw [huj]; omega, by rw [huj]; omega⟩
    ⟨by rw [hqj]; omega, by rw [hqj]; omega⟩
  rw [← hm4] at h2
  have hF4 : ∀ x4 : Regs, x4.get 2#5 = x'.get 2#5 → (∀ r ∈ [3#5, 4#5, 24#5, 25#5, 26#5, 27#5],
      x4.get r = x3.get r) → K4Frame x m x4 m4 := by
    intro x4 h42 h4c
    refine K4Frame.step hpre hF0 h2 h42 (fun r hr hnr => ?_)
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr hnr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;>
      first | (simp at hnr; done) | (rw [h4c _ (by decide)]; exact h3 _ (by decide))
  rv_exec_cut 98 206
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
    · have := toNat_add8 (x.get 11#5) (8 * (j + 2)) (by omega) (by omega)
      rw [h12, show j - 1 + 3 = j + 2 by omega, ptr_add_16, hmem4 _ (by rw [this]; omega)]
    · have := toNat_add8 (x.get 11#5) (8 * (j + 3)) (by omega) (by omega)
      rw [h14, show j - 1 + 4 = j + 3 by omega, ptr_add_24, hmem4 _ (by rw [this]; omega)]
    · intro k hk
      have := toNat_add8 (x.get 11#5) (8 * k) (by omega) (by omega)
      rw [hmem4 _ (by rw [this]; omega), memWord_of_unchangedExcept hm3 _ (by rw [this, huj]; omega),
        hlow k (by omega)]
    · rw [ej, show (x.get 12#5).toNat - 5 - (j - 1) = (x.get 12#5).toNat - 4 - j by omega, hQ4,
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
    refine k4_exit base x m hr _ _ (hF4 _ ?_ ?_) ?_ ?_
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]; exact hsp.symm
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · rw [hQ4]; exact hq
    · have hs := words_split m4 4 ((x.get 12#5).toNat - 4) (x.get 11#5)
      rw [show 4 + ((x.get 12#5).toNat - 4) = (x.get 12#5).toNat by omega] at hs
      rw [hs, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (words_lt _ _ _), hR4, ← hr']

theorem k4_dhi {D d0 d1 X : Nat} (hD : 2 ^ (64 * 4 - 1) ≤ D)
    (he : D = d0 + 2 ^ 64 * (d1 + 2 ^ 64 * X)) (h0 : d0 < 2 ^ 64) (h1 : d1 < 2 ^ 64) :
    2 ^ 127 ≤ X := by
  omega

theorem k4_d3 {D d0 d1 d2 d3 : Nat} (hD : 2 ^ (64 * 4 - 1) ≤ D)
    (he : D = d0 + 2 ^ 64 * (d1 + 2 ^ 64 * (d2 + 2 ^ 64 * d3))) (h0 : d0 < 2 ^ 64)
    (h1 : d1 < 2 ^ 64) (h2 : d2 < 2 ^ 64) : 2 ^ 63 ≤ d3 := by
  omega

/-- The digit of the overflow of `udivrem_knuth_normalized<4>()`: `submul()` gives
`N - (2^64 - 1) * D` for the 5 words `N` whose top 4 words `R` are below `D` and start with the top 2
words of `D`. -/
theorem k4_over_nat {S D d0 d1 d2 d3 r0 r1 uj N L k : Nat} (hS : S < 2 ^ 256)
    (hk : S + (2 ^ 64 - 1) * D = L + k * 2 ^ 256) (hL : L < 2 ^ 256)
    (hD : D = d0 + 2 ^ 64 * (d1 + 2 ^ 64 * (d2 + 2 ^ 64 * d3))) (hd0 : d0 < 2 ^ 64)
    (hd1 : d1 < 2 ^ 64) (hd3 : 2 ^ 63 ≤ d3) (hd3' : d3 < 2 ^ 64)
    (hR : r0 + 2 ^ 64 * (r1 + 2 ^ 64 * (d2 + 2 ^ 64 * d3)) < D) (h0 : r0 < 2 ^ 64)
    (h1 : r1 < 2 ^ 64) (huj : uj < 2 ^ 64)
    (hN : N = uj + 2 ^ 64 * (r0 + 2 ^ 64 * (r1 + 2 ^ 64 * (d2 + 2 ^ 64 * d3))))
    (hNL : N = L + 2 ^ 256 * d3) :
    (2 ^ 64 - 1) * D + S = N ∧ S < D := by
  have ho := knuth_overflow (N := N) (R := r0 + 2 ^ 64 * (r1 + 2 ^ 64 * (d2 + 2 ^ 64 * d3)))
    (u := uj) (P := 2 ^ 128) (dhi := d2 + 2 ^ 64 * d3) (dlo := d0 + 2 ^ 64 * d1)
    (hD.trans (by ring)) (by omega) (by omega) hR (by omega) huj (hN.trans (by ring))
  have hDK : D ≤ 2 ^ 256 := by omega
  have := over_words4 (t := d3) hS hk hNL ho.1 ho.2 hDK
  omega

theorem k4Kept_not_cl : ∀ r ∈ k3Kept, r ∉ [5#5, 10#5, 11#5, 12#5, 14#5, 15#5, 16#5, 17#5, 23#5] ∧
    r ∉ [10#5, 11#5, 12#5, 14#5, 15#5, 16#5, 23#5] ∧ r ≠ 10#5 ∧ r ≠ 0 := by decide

/-- The words of d in the memory of the loop: d is outside q, u and the frame. -/
theorem k4_d_words {x : Regs} {m m' : Mem} (hpre : udivrem_knuth_normalized_4.pre x m)
    (hun : UnchangedExcept3 m m' (x.get 10#5) (8 * ((x.get 12#5).toNat - 4)) (x.get 11#5)
      (8 * (x.get 12#5).toNat) (x.get 2#5 - 80#64) 80) :
    words m' (x.get 13#5) 4 = words m (x.get 13#5) 4 := by
  simp only [udivrem_knuth_normalized_4.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨-, -, ⟨-, hdn⟩, hdqd, -, hdud, -, hdsd, -, -, -⟩ := hpre
  have h8 : (x.get 13#5 + 8#64).toNat = (x.get 13#5).toNat + 8 := by bv_omega
  have h16 : (x.get 13#5 + 16#64).toNat = (x.get 13#5).toNat + 16 := by bv_omega
  have h24 : (x.get 13#5 + 24#64).toNat = (x.get 13#5).toNat + 24 := by bv_omega
  rw [words4_eq, words4_eq]
  have e : ∀ c, (x.get 13#5).toNat ≤ c → c + 8 ≤ (x.get 13#5).toNat + 32 → memWord m' c = memWord m c := by
    intro c h1 h2
    simp only [memWord, Std.ExtHashMap.getD_eq_getD_getElem?]
    rw [hun c (by omega) (by omega) (by omega), hun (c + 1) (by omega) (by omega) (by omega),
      hun (c + 2) (by omega) (by omega) (by omega), hun (c + 3) (by omega) (by omega) (by omega),
      hun (c + 4) (by omega) (by omega) (by omega), hun (c + 5) (by omega) (by omega) (by omega),
      hun (c + 6) (by omega) (by omega) (by omega), hun (c + 7) (by omega) (by omega) (by omega)]
  rw [e _ (by omega) (by omega), e _ (by omega) (by omega), e _ (by omega) (by omega),
    e _ (by omega) (by omega)]

/-- A word of d in the memory of the loop. -/
theorem k4_d_mem {x : Regs} {m m' : Mem} (hpre : udivrem_knuth_normalized_4.pre x m)
    (hun : UnchangedExcept3 m m' (x.get 10#5) (8 * ((x.get 12#5).toNat - 4)) (x.get 11#5)
      (8 * (x.get 12#5).toNat) (x.get 2#5 - 80#64) 80) (k : BitVec 64) (hk : k = 16#64 ∨ k = 24#64) :
    memWord m' (x.get 13#5 + k).toNat = memWord m (x.get 13#5 + k).toNat := by
  simp only [udivrem_knuth_normalized_4.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨-, -, ⟨-, hdn⟩, hdqd, -, hdud, -, hdsd, -, -, -⟩ := hpre
  have hc : (x.get 13#5).toNat + 8 ≤ (x.get 13#5 + k).toNat ∧
      (x.get 13#5 + k).toNat + 8 ≤ (x.get 13#5).toNat + 32 := by
    rcases hk with rfl | rfl <;> constructor <;> bv_omega
  exact memWord_of_unchangedExcept3 hun _ (by omega) (by omega) (by omega)

/-- The loop of `udivrem_knuth_normalized<4>()` from its head at 0x1b8 of its image. -/
theorem k4_loop {hi : BitVec 20} {lo : BitVec 12} {Dt : List (BitVec 64)} (base : BitVec 64)
    (x : Regs) (m : Mem) (hb : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0)
    (hpre : udivrem_knuth_normalized_4.pre x m) :
    ∀ j x' m', k4Head x m j x' m' →
    Reach (udivrem_knuth_normalized_4.bufs x ++ Dt) (udivrem_knuth_normalized_4_progAt hi lo)
      base (pcAt base 98) x' m' (x.get 1#5) (udivrem_knuth_normalized_4.post x m) := by
  apply Reach.loop (k4Head x m)
  intro j x' m' hh ih
  have hh0 := hh
  obtain ⟨hj4, hF, h8, h21, h20, h13, h18, h19, h22, h12, h14, hlow, hQR, hRD⟩ := hh
  have hpre' := hpre
  simp only [udivrem_knuth_normalized_4.pre, Buf, Disjoint] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hqa, hqn⟩, ⟨hua, hun⟩, ⟨hda, hdn⟩, hdqd, hdqu, hdud, ⟨hsa, hsn⟩, hdsd, hdsq, hdsu, -,
    hn3, hD, hU⟩ := hpre'
  -- The pointer to u[j] and the words of d.
  have hj1 : 8 * j < 2 ^ 64 ∧ (x.get 11#5).toNat + 8 * j < 2 ^ 64 ∧
      (x.get 11#5).toNat + 8 * j + 40 ≤ (x.get 11#5).toNat + 8 * (x.get 12#5).toNat := by
    clear * - hj4 hun; omega
  have hs0 : (x'.get 8#5).toNat = (x.get 11#5).toNat + 8 * j := by
    rw [h8]; exact toNat_add8 _ _ hj1.1 hj1.2.1
  have hDm := k4_d_words hpre hF.2.2.2.2.2.2.2.2.2.2.1
  have hDw := words4_eq m (x.get 13#5)
  rw [← h18, ← h19] at hDw
  have hd3 := k4_d3 hD hDw (memWord m (x.get 13#5).toNat).isLt
    (memWord m (x.get 13#5 + 8#64).toNat).isLt (x'.get 18#5).isLt
  have hbufs : ∀ a ∈ bufWords (x'.get 13#5) 4 ++ bufWords (x'.get 8#5) 4,
      a ∈ udivrem_knuth_normalized_4.bufs x ++ Dt := by
    intro a ha
    simp only [udivrem_knuth_normalized_4.bufs]
    simp (disch := decide) only [Regs.eq_get x]
    rw [h13] at ha
    rcases List.mem_append.mp ha with ha | ha
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ ha)))
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        (mem_bufWords_within h8 (by clear * - hj4; omega) a ha)))
  -- The words of the partial remainder.
  have hRw := words4_eq m' (x.get 11#5 + BitVec.ofNat 64 (8 * (j + 1)))
  rw [ptr_add_8, ptr_add_16, ptr_add_24, ← h12, ← h14] at hRw
  have a8 : x'.get 8#5 + 8#64 = x.get 11#5 + BitVec.ofNat 64 (8 * (j + 1)) := by
    rw [h8, ptr_add_8]
  have a16 : x'.get 8#5 + 16#64 = x.get 11#5 + BitVec.ofNat 64 (8 * (j + 2)) := by
    rw [h8, ptr_add_16]
  have a24 : x'.get 8#5 + 24#64 = x.get 11#5 + BitVec.ofNat 64 (8 * (j + 3)) := by
    rw [h8, ptr_add_24]
  have a32 : x'.get 8#5 + 32#64 = x.get 11#5 + BitVec.ofNat 64 (8 * (j + 4)) := by
    rw [h8, ptr_add_32]
  have hNw := words5_eq m' (x'.get 8#5)
  rw [a8, a16, a24, a32, ← h12, ← h14] at hNw
  have hLw := words4_eq m' (x'.get 8#5)
  rw [a8, a16, a24, ← h12] at hLw
  -- The overflow: the top 2 words of the remainder are the top 2 words of d.
  have hover : x'.get 12#5 = x'.get 18#5 → x'.get 14#5 = x'.get 19#5 →
      Reach (udivrem_knuth_normalized_4.bufs x ++ Dt) (udivrem_knuth_normalized_4_progAt hi lo)
        base (pcAt base 163) x' m' (x.get 1#5) (udivrem_knuth_normalized_4.post x m) := by
    intro e12 e14
    have hds : Disjoint (x'.get 8#5) 32 (x'.get 13#5) 32 := by
      simp only [Disjoint]; rw [hs0, h13]; clear * - hj1 hdud; omega
    refine Reach.trans (Reach.mono_bufs hbufs (k4_over base x' m' hb (by rw [hs0]; omega)
      (by rw [hs0]; clear * - hua; omega) (by rw [h13]; exact hdn) (by rw [h13]; exact hda) hds)) ?_
    intro x3 m3 ⟨⟨k, hk⟩, hun3, h23, h12', h14', hcl⟩
    rw [h13, hDm] at hk
    have hS := words_lt m3 4 (x'.get 8#5)
    have hL := words_lt m' 4 (x'.get 8#5)
    rw [e12, e14] at hRw hNw
    rw [e12] at hLw
    have hov := k4_over_nat hS hk hL hDw (memWord m (x.get 13#5).toNat).isLt
      (memWord m (x.get 13#5 + 8#64).toNat).isLt hd3 (x'.get 19#5).isLt (hRw ▸ hRD)
      (memWord m' (x.get 11#5 + BitVec.ofNat 64 (8 * (j + 1))).toNat).isLt
      (memWord m' (x.get 11#5 + BitVec.ofNat 64 (8 * (j + 2))).toNat).isLt
      (memWord m' (x'.get 8#5).toNat).isLt hNw (by rw [hNw, hLw]; ring)
    refine k4_tail base x m hr hpre j x' m' hh0 x3 m3 ?_ hun3 ?_ hov.2 h12' h14' ih
    · intro r hr'
      obtain ⟨hr1, hr0⟩ := k3Kept_not_overCl r hr'
      rw [← Regs.eq_get x3 hr0, ← Regs.eq_get x' hr0]; exact hcl r hr1
    · rw [h23, show (18446744073709551615#64).toNat = 2 ^ 64 - 1 from rfl, ← hov.1]
  -- The division of the top 3 words by the top 2 words of d.
  have hnorm : ¬(x'.get 12#5 = x'.get 18#5 ∧ x'.get 14#5 = x'.get 19#5) →
      Reach (udivrem_knuth_normalized_4.bufs x ++ Dt) (udivrem_knuth_normalized_4_progAt hi lo)
        base (pcAt base 100) x' m' (x.get 1#5) (udivrem_knuth_normalized_4.post x m) := by
    intro hne
    -- The word u[j + 2] at 0x138 of its code.
    refine Reach.step (by decide) (by rv_fetch) ?_
    simp only [StepGoal, Nat.reduceAdd, BitVec.reduceSignExtend]
    refine ⟨hbufs _ (List.mem_append_right _
      (mem_bufWords (n := 4) (i := 2) (a := x'.get 8#5) (by norm_num) : _)), fun w hw => ?_⟩
    have g : ∀ r, r ≠ 10#5 → (x'.set 10#5 w).get r = x'.get r := by
      intro r hr; rw [Regs.get_set, if_neg hr]; split_ifs with h0 <;> simp [Regs.get, h0]
    have g10 : (x'.set 10#5 w).get 10#5 = w := by
      simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    have hne' : ¬((x'.get 12#5).toNat = (x'.get 18#5).toNat ∧
        (x'.get 14#5).toNat = (x'.get 19#5).toNat) :=
      fun ⟨e1, e2⟩ => hne ⟨BitVec.eq_of_toNat_eq e1, BitVec.eq_of_toNat_eq e2⟩
    have hR' := hRD
    rw [hRw, hDw] at hR'
    have hu := top2_lt_of_lt4 (memWord m' (x.get 11#5 + BitVec.ofNat 64 (8 * (j + 1))).toNat).isLt
      (memWord m' (x.get 11#5 + BitVec.ofNat 64 (8 * (j + 2))).toNat).isLt
      (memWord m (x.get 13#5).toNat).isLt (memWord m (x.get 13#5 + 8#64).toNat).isLt hR' hne'
      (x'.get 12#5).isLt (x'.get 18#5).isLt
    have hDhi := k4_dhi hD hDw (memWord m (x.get 13#5).toNat).isLt
      (memWord m (x.get 13#5 + 8#64).toNat).isLt
    refine Reach.trans (k4_div base (x'.set 10#5 w) m' ?_ ?_ ?_) ?_
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
    have hds : Disjoint (x'.get 8#5) 32 (x'.get 13#5) 32 := by
      simp only [Disjoint]; rw [hs0, h13]; clear * - hj1 hdud; omega
    refine Reach.trans (Reach.mono_bufs (A := bufWords (x2.get 13#5) 4 ++ bufWords (x2.get 8#5) 4)
      (by rw [e13, e8]; exact hbufs)
      (k4_sub (hi := hi) (lo := lo) base x2 m'
        ((x'.get 14#5).toNat * 2 ^ 128 + (x'.get 12#5).toNat * 2 ^ 64 + w.toNat)
        (by rw [e8, hs0]; clear * - hj1 hun; omega) (by rw [e13, h13]; exact hdn)
        (by rw [e8, e13]; exact hds)
        (by rw [e18, e13, h13, h18, k4_d_mem hpre hF.2.2.2.2.2.2.2.2.2.2.1 _ (Or.inl rfl)])
        (by rw [e19, e13, h13, h19, k4_d_mem hpre hF.2.2.2.2.2.2.2.2.2.2.1 _ (Or.inr rfl)])
        (by rw [e18, e19]; exact hDhi)
        (by rw [hq2, hr2, e18, e19]; exact Nat.div_add_mod' _ _)
        (by rw [hr2, e18, e19]; exact Nat.mod_lt _ hDpos))) ?_
    intro x3 m3 ⟨hdig, hlt, hun3, h12', h14', h03, hcl3⟩
    rw [e8, e13, h13, hDm] at hdig hlt
    rw [e8] at hun3 h12' h14'
    refine k4_tail base x m hr hpre j x' m' hh0 x3 m3 ?_ hun3 ?_ hlt h12' h14' ih
    · intro r hr'
      obtain ⟨h1, h2, h3, h0⟩ := k4Kept_not_cl r hr'
      rw [← Regs.eq_get x3 h0, hcl3 r h1, Regs.eq_get x2 h0]
      exact e2 r h2 h0
    · rw [hdig, hNw, hw.eq, a16, a8]; ring
  rv_step
  all_goals try rv_step
  · rename_i hb
    exact hnorm (fun h => hb h.1)
  · rename_i hb1 hb
    exact hover (by simpa using hb1) hb
  · rename_i hb1 hb
    exact hnorm (fun h => by simp only [beq_eq_false_iff_ne] at hb; exact hb h.2)

theorem k4_addr_u2 (u n : BitVec 64) (h : 5 ≤ n.toNat) :
    u + n <<< 3 + 18446744073709551600#64 = u + BitVec.ofNat 64 (8 * (n.toNat - 5 + 3)) := by
  bv_omega

theorem k4_addr_u3 (u n : BitVec 64) (h : 5 ≤ n.toNat) :
    u + (n <<< 3 + 18446744073709551608#64) = u + BitVec.ofNat 64 (8 * (n.toNat - 5 + 4)) := by
  bv_omega

theorem k4_addr_end (p n : BitVec 64) (h : 5 ≤ n.toNat) :
    p + (n <<< 3 + 18446744073709551576#64) = p + BitVec.ofNat 64 (8 * (n.toNat - 5)) := by
  bv_omega

theorem k4_cnt (n : BitVec 64) (h : 5 ≤ n.toNat) :
    n + 18446744073709551612#64 = BitVec.ofNat 64 (n.toNat - 5 + 1) := by
  bv_omega

/-- The top 4 words of u: the remainder of the digits above the digit `n - 5`. -/
theorem k4_top4 (m : Mem) (u : BitVec 64) (n : Nat) (hn : 5 ≤ n) :
    words m u n / 2 ^ (64 * (n - 5 + 1)) = words m (u + BitVec.ofNat 64 (8 * (n - 5 + 1))) 4 := by
  have hs := words_split m (n - 5 + 1) 4 u
  rw [show n - 5 + 1 + 4 = n by omega] at hs
  rw [hs, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (words_lt _ _ _),
    Nat.zero_add]

end IntxRV.Api
