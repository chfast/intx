import IntxRV.Div256
/-!
# The path of `udivrem<256, 256>()` that calls `udivrem_by1()`

The path of `udivrem_by1()` for v < 2^64 and v ≠ 0 (`u256_by1`): the result is zeroed, and the
call passes max(m, 2) words of u. The call lemma `u256_by1_call` takes the registers of the path
as hypotheses, so the three sizes of u share its proof. See `IntxRV/Div256.lean`.
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

/-- The call of `udivrem_by1()` in `udivrem<256, 256>()` at 0x1b0 with U words of u, from the
registers that the path sets. -/
theorem u256_by1_call {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hb3 : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0) (hpre : udivrem_256.pre x m)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64)
    (hTr : (x.get 10#5).toNat + 64 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hTs : (x.get 2#5 - 48#64).toNat + 48 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 48#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data)
    (hD : ∀ a ∈ bufWords T 256, a ∈ D)
    (hT0 : pcAt (pcAt base 108) 5 + ((hi0 ++ 0x000#12).signExtend 64 +
      lo0.signExtend 64) = T)
    (U : Nat) (hU2 : 2 ≤ U) (hU4 : U ≤ 4) (hu : words m (x.get 11#5) U = words m (x.get 11#5) 4)
    (x'' : Regs) (h1 : x''.get 1#5 = pcAt base 97)
    (h2 : x''.get 2#5 = x.get 2#5 + 18446744073709551600#64) (h8 : x''.get 8#5 = x.get 10#5)
    (h10 : x''.get 10#5 = x.get 10#5) (h11 : x''.get 11#5 = BitVec.ofNat 64 U)
    (h12 : x''.get 12#5 = x.get 11#5) (h13 : x''.get 13#5 = BitVec.ofNat 64 U)
    (h14 : x''.get 14#5 = memWord m (x.get 12#5).toNat)
    (hcs : ∀ i ∈ calleeSaved, i ≠ 2#5 → i ≠ 8#5 → x'' i = x i)
    (hv0 : memWord m (x.get 12#5).toNat ≠ 0#64) (hv1 : memWord m (x.get 12#5 + 8#64).toNat = 0#64)
    (hv2 : memWord m (x.get 12#5 + 16#64).toNat = 0#64)
    (hv3 : memWord m (x.get 12#5 + 24#64).toNat = 0#64) :
    Reach (bufWords (x.get 11#5) 4 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 8 ++
        bufWords (x.get 2#5 - 48#64) 6 ++ D) P256 base (pcAt base 108) x''
      (memStore (memStore (memStore (memStore (memStore (memStore (memStore (memStore
        (memStore (memStore m (x.get 2#5 + 18446744073709551608#64).toNat (x.get 1#5))
          (x.get 2#5 + 18446744073709551600#64).toNat (x.get 8#5))
        (x.get 10#5 + 32#64).toNat 0#64)
        (x.get 10#5 + 40#64).toNat 0#64)
        (x.get 10#5 + 48#64).toNat 0#64)
        (x.get 10#5 + 56#64).toNat 0#64)
        (x.get 10#5).toNat 0#64)
        (x.get 10#5 + 8#64).toNat 0#64)
        (x.get 10#5 + 16#64).toNat 0#64)
        (x.get 10#5 + 24#64).toNat 0#64)
      (x.get 1#5) (udivrem_256.post x m) := by
  -- `omega` and `subst_vars` do not see the address of the table.
  replace hT0 := PLift.up hT0
  simp only [udivrem_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr⟩ := hpre
  have hUn : (BitVec.ofNat 64 U).toNat = U := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have ev : words m (x.get 12#5) 4 = (memWord m (x.get 12#5).toNat).toNat := by
    simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, hv1, hv2, hv3,
      BitVec.toNat_zero, Nat.mul_zero, Nat.add_zero]
  have hv0n : 0 < (memWord m (x.get 12#5).toNat).toNat := by
    rcases Nat.eq_zero_or_pos (memWord m (x.get 12#5).toNat).toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hv0
    · exact h
  refine Reach.call_sub (r := 97) udivrem_256_progAt_udivrem_by1_in
    (by rw [udivrem_256_progAt_length]; decide)
    (udivrem_by1.reach hi0 lo0 (pcAt base 108) T _ _ hT0.down ?_ ?_ ?_ ?_)
    ?_ ?_ ?_
  · omega
  · rw [h1]; simp only [pcAt]; exact aligned_add hb3 (by decide)
  · simp (disch := first | bv_omega | fail) only [holdsData_table_memStore]
    exact hhold
  · simp only [udivrem_by1.pre, Buf, Disjoint]
    simp (disch := decide) only [Regs.eq_get x'']
    rw [h10, h11, h12, h13, h14, hUn]
    refine ⟨⟨hra, by omega⟩, ⟨hua, by omega⟩, by omega, hU2, rfl, hv0n⟩
  · exact h1
  · intro a ha
    simp only [udivrem_by1.bufs] at ha
    simp (disch := decide) only [Regs.eq_get x''] at ha
    rw [h10, h11, h12, h13, hUn] at ha
    simp only [List.mem_append] at ha ⊢
    rcases ha with (h | h) | h
    · exact Or.inl (Or.inl (Or.inl (Or.inl (mem_bufWords_of_le hU4 h))))
    · exact Or.inl (Or.inl (Or.inr (mem_bufWords_of_le (by omega) h)))
    · exact Or.inr (hD _ h)
  · intro x3 m3 hpost
    obtain ⟨hq, hrem, hunc, hsaved⟩ := hpost
    simp (disch := decide) only [Regs.eq_get x''] at hq hrem hunc
    simp only [h10, h11, h12, h13, h14, hUn] at hq hrem hunc
    obtain ⟨hra3, hs03, hm3, z5, z6, z7, hw4⟩ := u256_by1_mem m m3 (x.get 10#5) (x.get 2#5)
      (x.get 1#5) (x.get 8#5) U ⟨hU2, hU4⟩ hrn hsn hdsr hunc
    rw [u256_by1_u m (x.get 10#5) (x.get 2#5) (x.get 1#5) (x.get 8#5) (x.get 11#5) U hU4
      hrn hun hdru hdsu hsn, hu, ← ev] at hq hrem
    have h8' : x3.get 8#5 = x.get 10#5 := by
      rw [← Regs.eq_get x3 (by decide), hsaved 8#5 (by decide), Regs.eq_get x'' (by decide), h8]
    have h23 : x3.get 2#5 = x.get 2#5 + 18446744073709551600#64 := by
      rw [← Regs.eq_get x3 (by decide), hsaved 2#5 (by decide), Regs.eq_get x'' (by decide), h2]
    have hcs3 : ∀ i ∈ calleeSaved, i ≠ 2#5 → i ≠ 8#5 → x3 i = x i := fun i hi h2i h8i => by
      rw [hsaved i hi]; exact hcs i hi h2i h8i
    exact u256_by1_ret base x m hr hrn hsn hdsr x3 m3 h8' h23 hcs3 hra3 hs03 hm3 z5 z6 z7
      (hw4 ▸ hq) (by rw [ev]; omega) hrem

/-- The path of `udivrem<256, 256>()` for v < 2^64 and v[0] ≠ 0 from 0x144: the call of
`udivrem_by1()` with max(m, 2) words of u, and the store of the remainder. -/
theorem u256_by1 {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hb3 : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0) (hpre : udivrem_256.pre x m)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64)
    (hTr : (x.get 10#5).toNat + 64 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data)
    (hTs : (x.get 2#5 - 48#64).toNat + 48 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 48#64).toNat)
    (hD : ∀ a ∈ bufWords T 256, a ∈ D)
    (hT0 : pcAt (pcAt base 108) 5 + ((hi0 ++ 0x000#12).signExtend 64 +
      lo0.signExtend 64) = T)
    (x' : Regs) (h10 : x'.get 10#5 = x.get 10#5) (h11 : x'.get 11#5 = x.get 11#5)
    (h2 : x'.get 2#5 = x.get 2#5 + 18446744073709551600#64)
    (hcs : ∀ i ∈ calleeSaved, i ≠ 2#5 → i ≠ 8#5 → x' i = x i)
    (h13 : (x'.get 13#5).toNat ≤ 4)
    (hu3 : (x'.get 13#5).toNat ≤ 3 → memWord m (x.get 11#5 + 24#64).toNat = 0#64)
    (hu2 : (x'.get 13#5).toNat ≤ 2 → memWord m (x.get 11#5 + 16#64).toNat = 0#64)
    (h14 : x'.get 14#5 = memWord m (x.get 12#5).toNat) (hv0 : x'.get 14#5 ≠ 0#64)
    (hv1 : memWord m (x.get 12#5 + 8#64).toNat = 0#64)
    (hv2 : memWord m (x.get 12#5 + 16#64).toNat = 0#64)
    (hv3 : memWord m (x.get 12#5 + 24#64).toNat = 0#64) :
    Reach (bufWords (x.get 11#5) 4 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 8 ++
        bufWords (x.get 2#5 - 48#64) 6 ++ D) P256 base (pcAt base 81) x'
      (memStore (memStore m (x.get 2#5 + 18446744073709551608#64).toNat (x.get 1#5))
        (x.get 2#5 + 18446744073709551600#64).toNat (x.get 8#5))
      (x.get 1#5) (udivrem_256.post x m) := by
  -- `omega` and `subst_vars` do not see the address of the table.
  replace hT0 := PLift.up hT0
  have hpre0 := hpre
  simp only [udivrem_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr⟩ := hpre
  have hz : x'.get 0#5 = 0#64 := by rw [show (0#5 : BitVec 5) = 0 from rfl, Regs.get_zero]; rfl
  rw [← h10, ← h11]
  rv_exec_cut 108
  all_goals
    simp only [zopz0zI_u_eq, decide_eq_true_eq, decide_eq_false_iff_not] at *
    try simp only [h10, h11]
    try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  all_goals
    rw [show pcAt base 95 + BitVec.signExtend 64 52#12 = pcAt base 108 by
        simp only [pcAt, BitVec.reduceSignExtend]; bv_omega,
      update_aligned (by simp only [pcAt]; exact aligned_add hb3 (by decide))]
  -- The paths for u_size = 3 or 4, and 2.
  · rcases (show x'.get 13#5 = 3#64 ∨ x'.get 13#5 = 4#64 by bv_omega) with h4 | h4
    · have hu3' := hu3 (by rw [h4]; decide)
      refine u256_by1_call base x m hb3 hr hpre0 hw hTr hTs hhold hD hT0.down 3 (by norm_num)
        (by norm_num) (by simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, hu3',
          BitVec.toNat_zero, Nat.mul_zero, Nat.add_zero]) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        (h14 ▸ hv0) hv1 hv2 hv3
      u256_regs
    · refine u256_by1_call base x m hb3 hr hpre0 hw hTr hTs hhold hD hT0.down 4 (by norm_num)
        (by norm_num) (rfl) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        (h14 ▸ hv0) hv1 hv2 hv3
      u256_regs
  · have h4 : (x'.get 13#5).toNat ≤ 2 := by bv_omega
    have hu3' := hu3 (by omega)
    have hu2' := hu2 h4
    refine u256_by1_call base x m hb3 hr hpre0 hw hTr hTs hhold hD hT0.down 2 (by norm_num)
      (by norm_num) (by simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, hu2', hu3',
        BitVec.toNat_zero, Nat.mul_zero, Nat.add_zero]) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        (h14 ▸ hv0) hv1 hv2 hv3
    u256_regs

end IntxRV.Api
