import IntxRV.Div256
/-!
# The path of `udivrem<256, 256>()` that calls `udivrem_by2()`

The path of `udivrem_by2()` for v < 2^128 and v[1] ≠ 0 (`u256_by2`): the result is zeroed, and
the call passes max(m, 3) words of u. The call lemma `u256_by2_call` takes the registers of the
path as hypotheses, so the two sizes of u share its proof. See `IntxRV/Div256.lean`.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
-- The guards that select the paths do not change the goals.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- The call of `udivrem_by2()` in `udivrem<256, 256>()` at 0x4b4 with Q + 1 words of u, from the
registers that the path sets. -/
theorem u256_by2_call {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hb3 : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0) (hpre : udivrem_256.pre x m)
    (hw : base.toNat + 5272 + 8 * 256 ≤ 2 ^ 64)
    (hTr : (x.get 10#5).toNat + 64 ≤ base.toNat ∨ base.toNat + 5272 + 8 * 256 ≤ (x.get 10#5).toNat)
    (hTs : (x.get 2#5 - 48#64).toNat + 48 ≤ base.toNat ∨
      base.toNat + 5272 + 8 * 256 ≤ (x.get 2#5 - 48#64).toNat)
    (hhold : HoldsData m (base + BitVec.ofNat 64 5272) reciprocal_2by1_image_data)
    (hD : ∀ a ∈ bufWords (base + BitVec.ofNat 64 5272) 256, a ∈ D)
    (Q : Nat) (hQ : Q = 2 ∨ Q = 3)
    (hu : words m (x.get 11#5) (Q + 1) = words m (x.get 11#5) 4)
    (x'' : Regs) (h1 : x''.get 1#5 = pcAt base 63)
    (h2 : x''.get 2#5 = x.get 2#5 + 18446744073709551600#64) (h8 : x''.get 8#5 = x.get 10#5)
    (h10 : x''.get 10#5 = x.get 10#5) (h11 : x''.get 11#5 = BitVec.ofNat 64 Q)
    (h12 : x''.get 12#5 = x.get 11#5) (h13 : x''.get 13#5 = BitVec.ofNat 64 (Q + 1))
    (h14 : x''.get 14#5 = memWord m (x.get 12#5).toNat)
    (h15 : x''.get 15#5 = memWord m (x.get 12#5 + 8#64).toNat)
    (hcs : ∀ i ∈ calleeSaved, i ≠ 2#5 → i ≠ 8#5 → x'' i = x i)
    (hv1 : memWord m (x.get 12#5 + 8#64).toNat ≠ 0#64)
    (hv2 : memWord m (x.get 12#5 + 16#64).toNat = 0#64)
    (hv3 : memWord m (x.get 12#5 + 24#64).toNat = 0#64) :
    Reach (bufWords (x.get 11#5) 4 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 8 ++
        bufWords (x.get 2#5 - 48#64) 6 ++ D) udivrem_256_image_prog base (pcAt base 301) x''
      (memStore (memStore (memStore (memStore (memStore (memStore (memStore (memStore
        (memStore (memStore m (x.get 2#5 + 18446744073709551608#64).toNat (x.get 1#5))
          (x.get 2#5 + 18446744073709551600#64).toNat (x.get 8#5))
        (x.get 10#5).toNat 0#64)
        (x.get 10#5 + 8#64).toNat 0#64)
        (x.get 10#5 + 16#64).toNat 0#64)
        (x.get 10#5 + 24#64).toNat 0#64)
        (x.get 10#5 + 32#64).toNat 0#64)
        (x.get 10#5 + 40#64).toNat 0#64)
        (x.get 10#5 + 48#64).toNat 0#64)
        (x.get 10#5 + 56#64).toNat 0#64)
      (x.get 1#5) (udivrem_256.post x m) := by
  simp only [udivrem_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr⟩ := hpre
  have hT' : (base + 5272#64).toNat = base.toNat + 5272 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hQn : (BitVec.ofNat 64 Q).toNat = Q := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hUn : (BitVec.ofNat 64 (Q + 1)).toNat = Q + 1 := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have ev : words m (x.get 12#5) 4 = (memWord m (x.get 12#5).toNat).toNat +
      2 ^ 64 * (memWord m (x.get 12#5 + 8#64).toNat).toNat := by
    simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, hv2, hv3,
      BitVec.toNat_zero, Nat.mul_zero, Nat.add_zero]
  have hv1n : 0 < (memWord m (x.get 12#5 + 8#64).toNat).toNat := by
    rcases Nat.eq_zero_or_pos (memWord m (x.get 12#5 + 8#64).toNat).toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hv1
    · exact h
  have hsub : x.get 2#5 + 18446744073709551600#64 - 32#64 = x.get 2#5 - 48#64 := by bv_omega
  refine Reach.call_sub (r := 63) udivrem_256_image_udivrem_by2_in (by decide)
    (udivrem_by2.reach 0x1#20 0xf0c#12 (pcAt base 301) (base + 5272#64) _ _ ?_ ?_ ?_ ?_ ?_ ?_)
    ?_ ?_ ?_
  · simp only [pcAt, BitVec.reduceAppend, BitVec.reduceSignExtend]; bv_omega
  · rw [hT']; omega
  · rw [h1]; simp only [pcAt]; exact aligned_add hb3 (by decide)
  · rw [h2, hsub, hT']; omega
  · simp (disch := first | (rw [hT']; bv_omega) | fail) only [holdsData_table_memStore]
    exact hhold
  · simp only [udivrem_by2.pre, Buf, Disjoint]
    simp (disch := decide) only [Regs.eq_get x'']
    rw [h10, h11, h12, h13, h14, h15, h2, hsub, hQn, hUn]
    refine ⟨⟨hra, by omega⟩, ⟨hua, by omega⟩, by omega, ⟨by omega, by omega⟩, by omega, by omega,
      by omega, rfl, by omega⟩
  · exact h1
  · intro a ha
    simp only [udivrem_by2.bufs] at ha
    simp (disch := decide) only [Regs.eq_get x''] at ha
    rw [h10, h11, h12, h13, h2, hsub, hQn, hUn] at ha
    simp only [List.mem_append] at ha ⊢
    rcases ha with ((h | h) | h) | h
    · exact Or.inl (Or.inl (Or.inl (Or.inl (mem_bufWords_of_le (by omega) h))))
    · exact Or.inl (Or.inl (Or.inr (mem_bufWords_of_le (by omega) h)))
    · exact Or.inl (Or.inr (mem_bufWords_of_le (by decide) h))
    · exact Or.inr (hD _ h)
  · intro x3 m3 hpost
    obtain ⟨hq, hrem, hunc, hsaved⟩ := hpost
    simp (disch := decide) only [Regs.eq_get x''] at hq hrem hunc
    simp only [h10, h11, h12, h13, h14, h15, h2, hsub, hQn, hUn] at hq hrem hunc
    obtain ⟨hra3, hs03, hm3, z6, z7, hw4⟩ := u256_by2_mem m m3 (x.get 10#5) (x.get 2#5)
      (x.get 1#5) (x.get 8#5) Q hQ hrn hsn hdsr hunc
    rw [u256_by2_u m (x.get 10#5) (x.get 2#5) (x.get 1#5) (x.get 8#5) (x.get 11#5) (Q + 1)
      (by omega) hrn hun hdru hdsu hsn, hu, ← ev] at hq hrem
    have h8' : x3.get 8#5 = x.get 10#5 := by
      rw [← Regs.eq_get x3 (by decide), hsaved 8#5 (by decide), Regs.eq_get x'' (by decide), h8]
    have h23 : x3.get 2#5 = x.get 2#5 + 18446744073709551600#64 := by
      rw [← Regs.eq_get x3 (by decide), hsaved 2#5 (by decide), Regs.eq_get x'' (by decide), h2]
    have hcs3 : ∀ i ∈ calleeSaved, i ≠ 2#5 → i ≠ 8#5 → x3 i = x i := fun i hi h2i h8i => by
      rw [hsaved i hi]; exact hcs i hi h2i h8i
    exact u256_by2_ret base x m hr hrn hsn hdsr x3 m3 h8' h23 hcs3 hra3 hs03 hm3 z6 z7
      (hw4 ▸ hq) (by rw [ev]; omega) hrem

/-- The path of `udivrem<256, 256>()` for v < 2^128 and v[1] ≠ 0 from 0xb4: the call of
`udivrem_by2()` with max(m, 3) words of u, and the store of the remainder. -/
theorem u256_by2 {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hb3 : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0) (hpre : udivrem_256.pre x m)
    (hw : base.toNat + 5272 + 8 * 256 ≤ 2 ^ 64)
    (hTr : (x.get 10#5).toNat + 64 ≤ base.toNat ∨ base.toNat + 5272 + 8 * 256 ≤ (x.get 10#5).toNat)
    (hTs : (x.get 2#5 - 48#64).toNat + 48 ≤ base.toNat ∨
      base.toNat + 5272 + 8 * 256 ≤ (x.get 2#5 - 48#64).toNat)
    (hhold : HoldsData m (base + BitVec.ofNat 64 5272) reciprocal_2by1_image_data)
    (hD : ∀ a ∈ bufWords (base + BitVec.ofNat 64 5272) 256, a ∈ D)
    (x' : Regs) (h10 : x'.get 10#5 = x.get 10#5) (h11 : x'.get 11#5 = x.get 11#5)
    (h12 : x'.get 12#5 = x.get 12#5) (h2 : x'.get 2#5 = x.get 2#5 + 18446744073709551600#64)
    (hcs : ∀ i ∈ calleeSaved, i ≠ 2#5 → i ≠ 8#5 → x' i = x i)
    (h13 : (x'.get 13#5).toNat ≤ 4)
    (hu3 : (x'.get 13#5).toNat ≤ 3 → memWord m (x.get 11#5 + 24#64).toNat = 0#64)
    (h15 : x'.get 15#5 = memWord m (x.get 12#5 + 8#64).toNat) (hv1 : x'.get 15#5 ≠ 0#64)
    (hv2 : memWord m (x.get 12#5 + 16#64).toNat = 0#64)
    (hv3 : memWord m (x.get 12#5 + 24#64).toNat = 0#64) :
    Reach (bufWords (x.get 11#5) 4 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 8 ++
        bufWords (x.get 2#5 - 48#64) 6 ++ D) udivrem_256_image_prog base (pcAt base 45) x'
      (memStore (memStore m (x.get 2#5 + 18446744073709551608#64).toNat (x.get 1#5))
        (x.get 2#5 + 18446744073709551600#64).toNat (x.get 8#5))
      (x.get 1#5) (udivrem_256.post x m) := by
  have hpre0 := hpre
  simp only [udivrem_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr⟩ := hpre
  have hz : x'.get 0#5 = 0#64 := by rw [show (0#5 : BitVec 5) = 0 from rfl, Regs.get_zero]; rfl
  have hT' : (base + 5272#64).toNat = base.toNat + 5272 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [← h10, ← h11, ← h12]
  rv_exec_cut 301
  all_goals
    simp only [Defn] at *
    subst_vars
    simp only [zopz0zI_u_eq, decide_eq_true_eq, decide_eq_false_iff_not] at *
    simp only [h10, h11, h12]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    rw [show pcAt base 61 + BitVec.signExtend 64 960#12 = pcAt base 301 by
        simp only [pcAt, BitVec.reduceSignExtend]; bv_omega,
      update_aligned (by simp only [pcAt]; exact aligned_add hb3 (by decide))]
  -- The paths for u_size = 4 and 3.
  · have h4 : x'.get 13#5 = 4#64 := by bv_omega
    simp only [h4, BitVec.reduceAdd]
    refine u256_by2_call base x m hb3 hr hpre0 hw hTr hTs hhold hD 3 (Or.inr rfl) rfl _ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ (h15 ▸ hv1) hv2 hv3
    u256_regs
  · have h4 : (x'.get 13#5).toNat ≤ 3 := by bv_omega
    have hu3' := hu3 h4
    refine u256_by2_call base x m hb3 hr hpre0 hw hTr hTs hhold hD 2 (Or.inl rfl)
      (by simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, hu3',
        BitVec.toNat_zero, Nat.mul_zero, Nat.add_zero]) _ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ (h15 ▸ hv1) hv2 hv3
    u256_regs

end IntxRV.Api
