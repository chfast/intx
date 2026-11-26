import IntxRV.Div512
import IntxRV.Gen.Api.udivrem_320_256
/-!
# The paths of `udivrem<320, 256>()`

The frame of 48 bytes with ra and s0 to s4 (`U320Frame`), the epilogue (`u320_epi`), the call of
`memset()` that zeroes the result (`u320_memset`), and the paths for u < v (`u320_ult`) and v = 0
(`u320_vzero`). See `IntxRV/Api/udivrem_320_256.lean`.
-/

namespace IntxRV

open IntxRV.Gen IntxRV.Api

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {hi0 hi1 hi2 hi3 hi4 hi5 hi6 hi7 hi8 hi9 : BitVec 20}
  {lo0 lo1 lo2 lo3 lo4 lo5 lo6 lo7 lo8 lo9 : BitVec 12}

-- The instructions of the callees of `udivrem<320, 256>()` with the immediates of the address of
-- the table in each callee, nested to the right.
set_option hygiene false in
local notation "R320" => udivrem_by1_progAt hi0 lo0 ++ (udivrem_by1_5_progAt hi1 lo1 ++
  (udivrem_by2_progAt hi2 lo2 ++ (udivrem_by2_4_progAt hi3 lo3 ++
  (udivrem_top1_2_320_progAt hi4 lo4 ++ (udivrem_top1_3_320_progAt hi5 lo5 ++
  (udivrem_top2_3_320_progAt hi6 lo6 ++ (udivrem_top2_3_equal_320_progAt hi7 lo7 ++
  (udivrem_top2_4_320_progAt hi8 lo8 ++ (udivrem_knuth_320_progOwn ++
  (udivrem_knuth_normalized_progOwn hi9 lo9 ++ (submul_prog ++ memset_prog)))))))))))

-- The instructions of `udivrem<320, 256>()` and its callees: its own code first, so that the fetch
-- of an instruction of its code does not reduce the instructions of the callees.
set_option hygiene false in
local notation "P320" => udivrem_320_256_progOwn ++ R320

/-- The image of `udivrem<320, 256>()` with the instructions of the callees nested to the right. -/
theorem p320_eq : udivrem_320_256_progAt hi0 lo0 hi1 lo1 hi2 lo2 hi3 lo3 hi4 lo4 hi5 lo5 hi6 lo6
    hi7 lo7 hi8 lo8 hi9 lo9 = P320 := by
  simp only [udivrem_320_256_progAt, List.append_assoc]

theorem p320_length : 4 * (P320).length < 2 ^ 64 := by
  rw [← p320_eq, udivrem_320_256_progAt_length]; decide

/-- The addresses of the words of `udivrem<320, 256>()`: u, v, the result, the frame of 336 bytes
with the frames of the callees and `D`. -/
abbrev u320Bufs (x : Regs) (D : List (BitVec 64)) : List (BitVec 64) :=
  bufWords (x.get 11#5) 5 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 9 ++
    bufWords (x.get 2#5 - 336#64) 42 ++ D

/-- The frame of `udivrem<320, 256>()` after its prologue: sp 48 bytes lower, ra and s0 to s4
saved, and the memory outside the result and the frame of 336 bytes unchanged. -/
def U320Frame (x : Regs) (m : Mem) (x' : Regs) (m' : Mem) : Prop :=
  x'.get 2#5 = x.get 2#5 + 18446744073709551568#64 ∧
  memWord m' (x.get 2#5 + 18446744073709551608#64).toNat = x.get 1#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551600#64).toNat = x.get 8#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551592#64).toNat = x.get 9#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551584#64).toNat = x.get 18#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551576#64).toNat = x.get 19#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551568#64).toNat = x.get 20#5 ∧
  UnchangedExcept2 m m' (x.get 10#5) 72 (x.get 2#5 - 336#64) 336 ∧
  ∀ r ∈ calleeSaved, r ∉ [2#5, 8#5, 9#5, 18#5, 19#5, 20#5] → x'.get r = x.get r

set_option hygiene false in
/-- The callee-saved registers that the frame keeps, through the sets of the other registers. -/
macro "u320_cs" : tactic => `(tactic| (
  intro r hr' hn
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte,
      List.mem_cons, List.not_mem_nil, or_false, not_true_eq_false, not_false_eq_true] at hn ⊢))

/-- The end of `udivrem<320, 256>()` at 142: the restore of ra and s0 to s4 and the return, with
the result stored. -/
theorem u320_epi {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hr : x.get 1#5 &&& 3 = 0) (x4 : Regs) (m4 : Mem) (hF : U320Frame x m x4 m4)
    (hq : words m4 (x.get 10#5) 5 = words m (x.get 11#5) 5 / words m (x.get 12#5) 4)
    (hrem : words m4 (x.get 10#5 + 40#64) 4 = if words m (x.get 12#5) 4 = 0 then 0
      else words m (x.get 11#5) 5 % words m (x.get 12#5) 4) :
    Reach (u320Bufs x D) P320 base (pcAt base 142) x4 m4 (x.get 1#5)
      (udivrem_320_256.post x m) := by
  obtain ⟨hsp, hfra, hfs0, hfs1, hfs2, hfs3, hfs4, hunF, hcsF⟩ := hF
  rw [← regs_set_of_get' (by decide) hsp]
  rv_exec
  rename_i wra hwra ws0 hws0 ws1 hws1 ws2 hws2 ws3 hws3 ws4 hws4
  rw [hfra] at hwra
  rw [hfs0] at hws0
  rw [hfs1] at hws1
  rw [hfs2] at hws2
  rw [hfs3] at hws3
  rw [hfs4] at hws4
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.reduceSignExtend,
    BitVec.add_zero]
  rw [hwra.eq, update_aligned hr]
  refine Reach.refl ?_
  simp only [udivrem_320_256.post]
  simp (disch := decide) only [Regs.eq_get x]
  refine ⟨hq, hrem, hunF, ?_⟩
  intro r hr'
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
  all_goals first
    | (rw [Regs.eq_get x (by decide)]; bv_omega)
    | (rw [Regs.eq_get x4 (by decide), Regs.eq_get x (by decide)]
       exact hcsF _ (by decide) (by decide))
    | (rw [Regs.eq_get x (by decide)]
       first
         | exact hws0 | exact hws1 | exact hws2 | exact hws3 | exact hws4)

/-- The frame after a change of the memory only in the result and below the saved registers. -/
theorem U320Frame.mem {x : Regs} {m : Mem} {x' : Regs} {m1 m2 : Mem} (hF : U320Frame x m x' m1)
    (hpre : udivrem_320_256.pre x m)
    (h : UnchangedExcept2 m1 m2 (x.get 10#5) 72 (x.get 2#5 - 336#64) 288) :
    U320Frame x m x' m2 := by
  simp only [udivrem_320_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, -, -, -, -, ⟨hsa, hsn⟩, -, -, hdsr⟩ := hpre
  obtain ⟨hsp, hfra, hfs0, hfs1, hfs2, hfs3, hfs4, hunF, hcsF⟩ := hF
  have hw : ∀ c : BitVec 64, (x.get 2#5 - 336#64).toNat + 288 ≤ (x.get 2#5 + c).toNat →
      (x.get 2#5 + c).toNat + 8 ≤ (x.get 2#5 - 336#64).toNat + 336 →
      memWord m2 (x.get 2#5 + c).toNat = memWord m1 (x.get 2#5 + c).toNat := fun c h1 h2 =>
    memWord_of_unchangedExcept2 h _ (by omega) (by omega)
  refine ⟨hsp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hcsF⟩
  · rw [hw 18446744073709551608#64 (by bv_omega) (by bv_omega)]; exact hfra
  · rw [hw 18446744073709551600#64 (by bv_omega) (by bv_omega)]; exact hfs0
  · rw [hw 18446744073709551592#64 (by bv_omega) (by bv_omega)]; exact hfs1
  · rw [hw 18446744073709551584#64 (by bv_omega) (by bv_omega)]; exact hfs2
  · rw [hw 18446744073709551576#64 (by bv_omega) (by bv_omega)]; exact hfs3
  · rw [hw 18446744073709551568#64 (by bv_omega) (by bv_omega)]; exact hfs4
  intro k hka hkb
  rw [h k hka (by omega)]; exact hunF k hka hkb

/-- The frame after a change of the registers that keeps sp and the callee-saved registers that
the frame keeps. -/
theorem U320Frame.regs {x : Regs} {m : Mem} {x' x'' : Regs} {m' : Mem} (hF : U320Frame x m x' m')
    (h2 : x''.get 2#5 = x'.get 2#5)
    (hcs : ∀ r ∈ calleeSaved, r ∉ [2#5, 8#5, 9#5, 18#5, 19#5, 20#5] → x''.get r = x'.get r) :
    U320Frame x m x'' m' := by
  obtain ⟨hsp, hfra, hfs0, hfs1, hfs2, hfs3, hfs4, hunF, hcsF⟩ := hF
  exact ⟨h2.trans hsp, hfra, hfs0, hfs1, hfs2, hfs3, hfs4, hunF,
    fun r hr hn => (hcs r hr hn).trans (hcsF r hr hn)⟩

/-- The frame after a call, which keeps the callee-saved registers. -/
theorem U320Frame.callee {x : Regs} {m : Mem} {x' x3 : Regs} {m' : Mem} (hF : U320Frame x m x' m')
    (hcs : ∀ i ∈ calleeSaved, x3 i = x' i) : U320Frame x m x3 m' := by
  have h0 : ∀ i ∈ calleeSaved, i ≠ 0 := by decide
  refine U320Frame.regs hF ?_ fun r hr _ => ?_
  · rw [← Regs.eq_get x3 (by decide), hcs _ (by decide), Regs.eq_get x' (by decide)]
  · rw [← Regs.eq_get x3 (h0 r hr), hcs r hr, Regs.eq_get x' (h0 r hr)]

/-- A word of u in the memory of the frame. -/
theorem U320Frame.memWord_u {x : Regs} {m : Mem} {x' : Regs} {m' : Mem} (hF : U320Frame x m x' m')
    (hpre : udivrem_320_256.pre x m) (c : BitVec 64) (hc : c.toNat + 8 ≤ 40) :
    memWord m' (x.get 11#5 + c).toNat = memWord m (x.get 11#5 + c).toNat := by
  simp only [udivrem_320_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, -, hdru, -, ⟨hsa, hsn⟩, hdsu, -, -⟩ := hpre
  exact memWord_of_unchangedExcept2 hF.2.2.2.2.2.2.2.1 _ (by bv_omega) (by bv_omega)

/-- A word of v in the memory of the frame. -/
theorem U320Frame.memWord_v {x : Regs} {m : Mem} {x' : Regs} {m' : Mem} (hF : U320Frame x m x' m')
    (hpre : udivrem_320_256.pre x m) (c : BitVec 64) (hc : c.toNat + 8 ≤ 32) :
    memWord m' (x.get 12#5 + c).toNat = memWord m (x.get 12#5 + c).toNat := by
  simp only [udivrem_320_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, -, ⟨hva, hvn⟩, -, hdrv, ⟨hsa, hsn⟩, -, hdsv, -⟩ := hpre
  exact memWord_of_unchangedExcept2 hF.2.2.2.2.2.2.2.1 _ (by bv_omega) (by bv_omega)

/-- The words of u in the memory of the frame. -/
theorem U320Frame.words_u {x : Regs} {m : Mem} {x' : Regs} {m' : Mem} (hF : U320Frame x m x' m')
    (hpre : udivrem_320_256.pre x m) (k : Nat) (hk : k ≤ 5) :
    words m' (x.get 11#5) k = words m (x.get 11#5) k := by
  simp only [udivrem_320_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, -, hdru, -, ⟨hsa, hsn⟩, hdsu, -, -⟩ := hpre
  exact words_of_unchangedExcept2 hF.2.2.2.2.2.2.2.1 k _ (by omega) (by omega) (by omega)

/-- The words of v in the memory of the frame. -/
theorem U320Frame.words_v {x : Regs} {m : Mem} {x' : Regs} {m' : Mem} (hF : U320Frame x m x' m')
    (hpre : udivrem_320_256.pre x m) (k : Nat) (hk : k ≤ 4) :
    words m' (x.get 12#5) k = words m (x.get 12#5) k := by
  simp only [udivrem_320_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, -, ⟨hva, hvn⟩, -, hdrv, ⟨hsa, hsn⟩, -, hdsv, -⟩ := hpre
  exact words_of_unchangedExcept2 hF.2.2.2.2.2.2.2.1 k _ (by omega) (by omega) (by omega)

/-- The table of the reciprocal in the memory of the frame. -/
theorem U320Frame.holdsData {x : Regs} {m : Mem} {x' : Regs} {m' : Mem} {T : BitVec 64}
    (hF : U320Frame x m x' m') (hw : T.toNat + 8 * 256 ≤ 2 ^ 64)
    (hTr : (x.get 10#5).toNat + 72 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hTs : (x.get 2#5 - 336#64).toNat + 336 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 336#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) :
    HoldsData m' T reciprocal_2by1_image_data :=
  holdsData_of_unchangedExcept2 hF.2.2.2.2.2.2.2.1 _ T hw hTr hTs hhold

/-- The call of `memset()` that zeroes the 72 bytes of the result, with the return at `r`. -/
theorem u320_memset {D : List (BitVec 64)} {Q : Regs → Mem → Prop} (base : BitVec 64) (x : Regs)
    (m : Mem) (hb3 : base &&& 3 = 0) (hpre : udivrem_320_256.pre x m) (x' : Regs) (m' : Mem)
    (h10 : x'.get 10#5 = x.get 10#5) (h11 : x'.get 11#5 = 0#64) (h12 : x'.get 12#5 = 72#64)
    (r : Nat) (h1 : x'.get 1#5 = pcAt base r)
    (hcont : ∀ x'' m'', m'' = memFill m' (x.get 10#5).toNat 0#8 72 → x''.get 10#5 = x.get 10#5 →
      (∀ i ∈ calleeSaved, x'' i = x' i) →
      Reach (u320Bufs x D) P320 base (pcAt base r) x'' m'' (x.get 1#5) Q) :
    Reach (u320Bufs x D) P320 base (pcAt base 2996) x' m' (x.get 1#5) Q := by
  simp only [udivrem_320_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, -⟩ := hpre
  refine Reach.call_sub (r := r) (p320_eq ▸ udivrem_320_256_progAt_memset_in) p320_length
    (memset.reach (A := bufWords (x.get 10#5) 9) (pcAt base 2996) x' m' ?_ ?_ ?_) h1 ?_ ?_
  · rw [h1]; exact pcAt_aligned hb3 r
  · rw [h10, h12]; simp only [BitVec.toNat_ofNat]; omega
  · intro i hi
    rw [h10]
    rw [h12] at hi
    exact and_not7_mem_bufWords hra (by simpa using hi)
  · intro a ha
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inr ha))
  · intro x'' m'' ⟨hm, hx10, hcs⟩
    rw [h10, h11, h12] at hm
    rw [h10] at hx10
    exact hcont x'' m'' hm hx10 hcs

/-- The frame after `memset()` of the result. -/
theorem U320Frame.memFill {x : Regs} {m : Mem} {x' : Regs} {m' : Mem} (hF : U320Frame x m x' m')
    (hpre : udivrem_320_256.pre x m) :
    U320Frame x m x' (IntxRV.memFill m' (x.get 10#5).toNat 0#8 72) :=
  U320Frame.mem hF hpre (unchangedExcept2_of _ _ (unchangedExcept_memFill m' (x.get 10#5) 0#8 72))

/-- A word of the result after `memset()`. -/
theorem u320_memFill_zero {x : Regs} {m : Mem} (m' : Mem) (hpre : udivrem_320_256.pre x m)
    (c : BitVec 64) (hc : c.toNat + 8 ≤ 72) :
    memWord (IntxRV.memFill m' (x.get 10#5).toNat 0#8 72) (x.get 10#5 + c).toNat = 0#64 := by
  simp only [udivrem_320_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, -⟩ := hpre
  exact memWord_memFill_zero _ _ _ _ (by bv_omega)

/-- The words of the result after `memset()`. -/
theorem u320_memFill_words {x : Regs} {m : Mem} (m' : Mem) (hpre : udivrem_320_256.pre x m) :
    ∀ (j k : Nat), 8 * (k + j) ≤ 72 →
      words (IntxRV.memFill m' (x.get 10#5).toNat 0#8 72) (x.get 10#5 + BitVec.ofNat 64 (8 * k)) j
        = 0
  | 0, _, _ => rfl
  | j + 1, k, h => by
    rw [words, u320_memFill_zero m' hpre _ (by rw [BitVec.toNat_ofNat]; omega),
      show x.get 10#5 + BitVec.ofNat 64 (8 * k) + 8 = x.get 10#5 + BitVec.ofNat 64 (8 * (k + 1)) by
        rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega,
      u320_memFill_words m' hpre j (k + 1) (by omega)]
    rfl

/-- The path of `udivrem<320, 256>()` for u < v from 129: the quotient 0 and the remainder u. -/
theorem u320_ult {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hr : x.get 1#5 &&& 3 = 0) (hpre : udivrem_320_256.pre x m) (x' : Regs) (m' : Mem)
    (hF : U320Frame x m x' m') (h10 : x'.get 10#5 = x.get 10#5) (h11 : x'.get 11#5 = x.get 11#5)
    (hlt : words m (x.get 11#5) 5 < words m (x.get 12#5) 4) :
    Reach (u320Bufs x D) P320 base (pcAt base 129) x' m' (x.get 1#5)
      (udivrem_320_256.post x m) := by
  have hpre0 := hpre
  simp only [udivrem_320_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr⟩ := hpre
  rw [← regs_set_of_get' (by decide) h10, ← regs_set_of_get' (by decide) h11]
  rv_exec_cut 142
  rename_i w0 hw0 w1 hw1 w2 hw2 w3 hw3
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.reduceSignExtend,
    BitVec.add_zero] at hw0 hw1 hw2 hw3 ⊢
  simp only [Defn] at hw0 hw1 hw2 hw3
  have hu0 := hF.memWord_u hpre0 0#64 (by decide)
  rw [BitVec.add_zero] at hu0
  rw [hu0] at hw0
  rw [hF.memWord_u hpre0 8#64 (by decide)] at hw1
  rw [hF.memWord_u hpre0 16#64 (by decide)] at hw2
  rw [hF.memWord_u hpre0 24#64 (by decide)] at hw3
  subst hw0 hw1 hw2 hw3
  refine u320_epi base x m hr _ _ (U320Frame.regs (U320Frame.mem hF hpre0 ?_) ?_ ?_) ?_ ?_
  · simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
    exact unchangedExcept2_refl _ _ _ _ _
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · u320_cs
  · rw [Nat.div_eq_of_lt hlt]
    simp (disch := first | bv_omega | fail) only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd, memWord_memStore_self, memWord_memStore_of_ne, BitVec.toNat_zero,
      Nat.mul_zero, Nat.add_zero]
  · have hV : words m (x.get 12#5) 4 ≠ 0 := by omega
    rw [if_neg hV, Nat.mod_eq_of_lt hlt]
    have hs := words_split m 4 1 (x.get 11#5)
    rw [show 4 + 1 = 5 from rfl] at hs
    rw [← lo_of_lt hs (lt_trans hlt (words_lt m 4 _))]
    simp (disch := first | bv_omega | fail) only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd, memWord_memStore_self, memWord_memStore_of_ne, Nat.mul_zero, Nat.add_zero]

/-- The path of `udivrem<320, 256>()` for v = 0 from 177: `memset()` of the result. -/
theorem u320_vzero {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hb3 : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0) (hpre : udivrem_320_256.pre x m)
    (x' : Regs) (m' : Mem) (hF : U320Frame x m x' m') (h10 : x'.get 10#5 = x.get 10#5)
    (hv : words m (x.get 12#5) 4 = 0) :
    Reach (u320Bufs x D) P320 base (pcAt base 177) x' m' (x.get 1#5)
      (udivrem_320_256.post x m) := by
  rw [← regs_set_of_get' (by decide) h10]
  rv_exec_cut 2996
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  rw [show pcAt base 179 + 12288#64 + BitVec.signExtend 64 3076#12 = pcAt base 2996 by
      simp only [pcAt, BitVec.reduceSignExtend]; bv_omega,
    update_aligned (pcAt_aligned hb3 2996)]
  have hF1 : U320Frame x m ((((((x'.set (10#5) (x.get 10#5)).set 12#5 72#64).set 11#5 0#64).set
      (1#5) (pcAt base 179 + 12288#64)).set (1#5) (pcAt base 181))) m' :=
    U320Frame.regs hF (by simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte])
      (by u320_cs)
  refine u320_memset base x m hb3 hpre _ m' ?_ ?_ ?_ 181 ?_ ?_
  all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  intro x'' m'' hm hx10 hcs
  subst hm
  have hF2 := (hF1.memFill hpre).callee hcs
  rv_exec_cut 142
  have hz : ∀ c : BitVec 64, c.toNat + 8 ≤ 72 →
      memWord (IntxRV.memFill m' (x.get 10#5).toNat 0#8 72) (x.get 10#5 + c).toNat = 0#64 :=
    u320_memFill_zero m' hpre
  have hz0 := hz 0#64 (by decide)
  rw [BitVec.add_zero] at hz0
  refine u320_epi base x m hr _ _ hF2 ?_ ?_
  · rw [hv, Nat.div_zero]
    simp (disch := decide) only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
      hz, hz0, BitVec.toNat_zero, Nat.mul_zero, Nat.add_zero]
  · rw [if_pos hv]
    simp (disch := decide) only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
      hz, BitVec.toNat_zero, Nat.mul_zero, Nat.add_zero]

end IntxRV
