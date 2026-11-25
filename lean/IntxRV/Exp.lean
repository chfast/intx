import IntxRV.Gen.Api.exp_256
import IntxRV.Mul256
import IntxRV.Div512
import IntxRV.Bits
import IntxRV.Loop

/-!
# The paths of `exp()`

The frame of 112 bytes with ra and s0 to s3 (`EXFrame`), the epilogue at 105 (`ex_epi`) and the
copy of the result from the frame at 97 (`ex_ret`). See `IntxRV/Api/exp_256.lean`.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

/-- The addresses of the words of `exp()`: the base, the exponent, the result, the frame of 112
bytes and `D`. -/
abbrev exBufs (x : Regs) (D : List (BitVec 64)) : List (BitVec 64) :=
  bufWords (x.get 11#5) 4 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 4 ++
    bufWords (x.get 2#5 - 112#64) 14 ++ D

/-- The frame of `exp()` after its prologue: sp 112 bytes lower, ra and s0 to s3 saved, and the
memory outside the result and the frame of 112 bytes unchanged. -/
def EXFrame (x : Regs) (m : Mem) (x' : Regs) (m' : Mem) : Prop :=
  x'.get 2#5 = x.get 2#5 + 18446744073709551504#64 ∧
  memWord m' (x.get 2#5 + 18446744073709551608#64).toNat = x.get 1#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551600#64).toNat = x.get 8#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551592#64).toNat = x.get 9#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551584#64).toNat = x.get 18#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551576#64).toNat = x.get 19#5 ∧
  UnchangedExcept2 m m' (x.get 10#5) 32 (x.get 2#5 - 112#64) 112 ∧
  ∀ r ∈ calleeSaved, r ∉ [2#5, 8#5, 9#5, 18#5, 19#5] → x'.get r = x.get r

set_option hygiene false in
/-- The callee-saved registers that the frame keeps, through the sets of the other registers. -/
local macro "ex_cs" : tactic => `(tactic| (
  intro r hr' hn
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte] at hn ⊢))

/-- The frame after a change of the memory only in the result and below the saved registers. -/
theorem EXFrame.mem {x : Regs} {m : Mem} {x' : Regs} {m1 m2 : Mem} (hF : EXFrame x m x' m1)
    (hpre : exp_256.pre x m)
    (h : UnchangedExcept2 m1 m2 (x.get 10#5) 32 (x.get 2#5 - 112#64) 72) :
    EXFrame x m x' m2 := by
  simp only [exp_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, -, -, -, -, ⟨hsa, hsn⟩, -, -, hdsr⟩ := hpre
  obtain ⟨hsp, hfra, hfs0, hfs1, hfs2, hfs3, hunF, hcsF⟩ := hF
  have hw : ∀ c : BitVec 64, (x.get 2#5 - 112#64).toNat + 72 ≤ (x.get 2#5 + c).toNat →
      (x.get 2#5 + c).toNat + 8 ≤ (x.get 2#5 - 112#64).toNat + 112 →
      memWord m2 (x.get 2#5 + c).toNat = memWord m1 (x.get 2#5 + c).toNat := fun c h1 h2 =>
    memWord_of_unchangedExcept2 h _ (by omega) (by omega)
  refine ⟨hsp, ?_, ?_, ?_, ?_, ?_, ?_, hcsF⟩
  · rw [hw 18446744073709551608#64 (by bv_omega) (by bv_omega)]; exact hfra
  · rw [hw 18446744073709551600#64 (by bv_omega) (by bv_omega)]; exact hfs0
  · rw [hw 18446744073709551592#64 (by bv_omega) (by bv_omega)]; exact hfs1
  · rw [hw 18446744073709551584#64 (by bv_omega) (by bv_omega)]; exact hfs2
  · rw [hw 18446744073709551576#64 (by bv_omega) (by bv_omega)]; exact hfs3
  intro k hka hkb
  rw [h k hka (by omega)]; exact hunF k hka hkb

/-- The frame after a change of the registers that keeps sp and the callee-saved registers that
the frame keeps. -/
theorem EXFrame.regs {x : Regs} {m : Mem} {x' x'' : Regs} {m' : Mem} (hF : EXFrame x m x' m')
    (h2 : x''.get 2#5 = x'.get 2#5)
    (hcs : ∀ r ∈ calleeSaved, r ∉ [2#5, 8#5, 9#5, 18#5, 19#5] → x''.get r = x'.get r) :
    EXFrame x m x'' m' := by
  obtain ⟨hsp, hfra, hfs0, hfs1, hfs2, hfs3, hunF, hcsF⟩ := hF
  exact ⟨h2.trans hsp, hfra, hfs0, hfs1, hfs2, hfs3, hunF,
    fun r hr hn => (hcs r hr hn).trans (hcsF r hr hn)⟩

/-- The frame after a call, which keeps the callee-saved registers. -/
theorem EXFrame.callee {x : Regs} {m : Mem} {x' x3 : Regs} {m' : Mem} (hF : EXFrame x m x' m')
    (hcs : ∀ i ∈ calleeSaved, x3 i = x' i) : EXFrame x m x3 m' := by
  have h0 : ∀ i ∈ calleeSaved, i ≠ 0 := by decide
  refine EXFrame.regs hF ?_ fun r hr _ => ?_
  · rw [← Regs.eq_get x3 (by decide), hcs _ (by decide), Regs.eq_get x' (by decide)]
  · rw [← Regs.eq_get x3 (h0 r hr), hcs r hr, Regs.eq_get x' (h0 r hr)]

/-- A word of an argument in the memory of the frame. -/
theorem EXFrame.memWord_arg {x : Regs} {m : Mem} {x' : Regs} {m' : Mem} (hF : EXFrame x m x' m')
    (hpre : exp_256.pre x m) (r : BitVec 5) (hr : r = 11#5 ∨ r = 12#5)
    (c : BitVec 64) (hc : c.toNat + 8 ≤ 32) :
    memWord m' (x.get r + c).toNat = memWord m (x.get r + c).toNat := by
  simp only [exp_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr⟩ := hpre
  rcases hr with rfl | rfl <;>
    exact memWord_of_unchangedExcept2 hF.2.2.2.2.2.2.1 _ (by bv_omega) (by bv_omega)

set_option hygiene false in
/-- The destructured precondition of `exp()`. -/
local macro "ex_pre" : tactic => `(tactic| (
  have hpre0 := hpre
  simp only [exp_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hba, hbn⟩, ⟨hea, hen⟩, hdrb, hdre, ⟨hsa, hsn⟩, hdsb, hdse, hdsr⟩ := hpre))

/-- The end of `exp()` at 105: the restore of ra and s0 to s3 and the return, with the result
stored. -/
theorem ex_epi {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hr : x.get 1#5 &&& 3 = 0) (x4 : Regs) (m4 : Mem) (hF : EXFrame x m x4 m4)
    (hres : words m4 (x.get 10#5) 4 = words m (x.get 11#5) 4 ^ words m (x.get 12#5) 4 % 2 ^ 256) :
    Reach (exBufs x D) exp_256_image_prog base (pcAt base 105) x4 m4 (x.get 1#5)
      (exp_256.post x m) := by
  obtain ⟨hsp, hfra, hfs0, hfs1, hfs2, hfs3, hunF, hcsF⟩ := hF
  rw [← regs_set_of_get' (by decide) hsp]
  rv_exec
  rename_i wra hwra ws0 hws0 ws1 hws1 ws2 hws2 ws3 hws3
  rw [hfra] at hwra
  rw [hfs0] at hws0
  rw [hfs1] at hws1
  rw [hfs2] at hws2
  rw [hfs3] at hws3
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.reduceSignExtend,
    BitVec.add_zero]
  rw [hwra.eq, update_aligned hr]
  refine Reach.refl ?_
  simp only [exp_256.post]
  simp (disch := decide) only [Regs.eq_get x]
  refine ⟨hres, hunF, ?_⟩
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
         | exact hws0 | exact hws1 | exact hws2 | exact hws3)

/-- The copy of the result from sp + 8 in the frame to the result at 97, then the epilogue. -/
theorem ex_ret {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hr : x.get 1#5 &&& 3 = 0) (hpre : exp_256.pre x m) (x' : Regs) (m' : Mem)
    (hF : EXFrame x m x' m') (h10 : x'.get 10#5 = x.get 10#5)
    (hR : words m' (x.get 2#5 + 18446744073709551512#64) 4 =
      words m (x.get 11#5) 4 ^ words m (x.get 12#5) 4 % 2 ^ 256) :
    Reach (exBufs x D) exp_256_image_prog base (pcAt base 97) x' m' (x.get 1#5)
      (exp_256.post x m) := by
  ex_pre
  rw [← regs_set_of_get' (by decide) h10, ← regs_set_of_get' (by decide) hF.1]
  rv_exec_cut 105
  refine ex_epi base x m hr _ _ (EXFrame.regs (EXFrame.mem hF hpre0 ?_) ?_ ?_) ?_
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.reduceSignExtend]
    simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
    exact unchangedExcept2_refl _ _ _ _ _
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    exact hF.1.symm
  · ex_cs
  · rw [← hR]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.reduceSignExtend]
    simp (disch := first | bv_omega | fail) only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd, BitVec.add_zero, memWord_memStore_self, memWord_memStore_of_ne,
      Nat.mul_zero, Nat.add_zero]
    rv_loads
    rfl

/-- The words of an argument in the memory of the frame. -/
theorem EXFrame.words_arg {x : Regs} {m : Mem} {x' : Regs} {m' : Mem} (hF : EXFrame x m x' m')
    (hpre : exp_256.pre x m) (r : BitVec 5) (hr : r = 11#5 ∨ r = 12#5) :
    words m' (x.get r) 4 = words m (x.get r) 4 := by
  simp only [exp_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hba, hbn⟩, ⟨hea, hen⟩, hdrb, hdre, ⟨hsa, hsn⟩, hdsb, hdse, hdsr⟩ := hpre
  rcases hr with rfl | rfl <;>
    exact words_of_unchangedExcept2 hF.2.2.2.2.2.2.1 4 _ (by omega) (by omega) (by omega)

/-- The words of the memory after the stores of a run. -/
local macro "ex_words" : tactic => `(tactic| (
  try simp only [BitVec.reduceSignExtend, BitVec.add_assoc, BitVec.reduceAdd]
  simp (disch := first | bv_omega | fail) only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
    BitVec.reduceAdd, BitVec.add_zero, memWord_memStore_self, memWord_memStore_of_ne,
    Nat.mul_zero, Nat.add_zero]))

set_option hygiene false in
/-- The registers and the memory after a multiplication of `exp()`, for its continuation. -/
local macro "ex_mul_end" : tactic => `(tactic| (
  refine hk _ _ (EXFrame.regs (EXFrame.mem hF hpre0 ?_) ?_ ?_) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte,
      BitVec.reduceSignExtend]
    simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
    exact unchangedExcept2_refl _ _ _ _ _
  all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  all_goals try ex_cs
  all_goals try (simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte,
      BitVec.reduceSignExtend, BitVec.add_assoc, BitVec.reduceAdd] at *; done)
  all_goals try (exact hsp.symm)
  all_goals try (ex_words; done)
  all_goals
    ex_words
    rv_cse
    rv_loads
    apply mul256_words
    all_goals assumption))

/-- The square of `exp()` from 126: the result at sp + 8 times itself to the temporary at
sp + 40. -/
theorem ex_sq {D : List (BitVec 64)} (base ret : BitVec 64) (x : Regs) (m : Mem)
    (hpre : exp_256.pre x m) (x' : Regs) (m' : Mem) (Q : Regs → Mem → Prop)
    (hF : EXFrame x m x' m') (h10 : x'.get 10#5 = x.get 10#5) (h11 : x'.get 11#5 = x.get 11#5)
    (h12 : x'.get 12#5 = x.get 12#5)
    (h14 : x'.get 14#5 = x.get 2#5 + 18446744073709551512#64) (h15 : x'.get 15#5 = 3#64)
    (h16 : x'.get 16#5 = 4#64)
    (hk : ∀ x'' m'', EXFrame x m x'' m'' → x''.get 10#5 = x.get 10#5 → x''.get 11#5 = x.get 11#5 →
      x''.get 12#5 = x.get 12#5 → x''.get 13#5 = x'.get 13#5 →
      x''.get 14#5 = x.get 2#5 + 18446744073709551512#64 → x''.get 15#5 = 3#64 → x''.get 16#5 = 4#64 →
      words m'' (x.get 2#5 + 18446744073709551544#64) 4 =
        words m' (x.get 2#5 + 18446744073709551512#64) 4 * words m' (x.get 2#5 + 18446744073709551512#64) 4 % 2 ^ 256 →
      words m'' (x.get 2#5 + 18446744073709551512#64) 4 = words m' (x.get 2#5 + 18446744073709551512#64) 4 →
      Reach (exBufs x D) exp_256_image_prog base (pcAt base 176) x'' m'' ret Q) :
    Reach (exBufs x D) exp_256_image_prog base (pcAt base 126) x' m' ret Q := by
  ex_pre
  have hsp := hF.1
  rw [← regs_set_of_get' (by decide) h10, ← regs_set_of_get' (by decide) h11,
    ← regs_set_of_get' (by decide) h12, ← regs_set_of_get' (by decide) hsp,
    ← regs_set_of_get' (by decide) h14, ← regs_set_of_get' (by decide) h15,
    ← regs_set_of_get' (by decide) h16]
  rv_exec_cut 176
  rv_copies
  try rv_val
  ex_mul_end

/-- The product of `exp()` from 192: the base times the result at sp + 8 to the temporary at
sp + 40. -/
theorem ex_mb {D : List (BitVec 64)} (base ret : BitVec 64) (x : Regs) (m : Mem)
    (hpre : exp_256.pre x m) (x' : Regs) (m' : Mem) (Q : Regs → Mem → Prop)
    (hF : EXFrame x m x' m') (h10 : x'.get 10#5 = x.get 10#5) (h11 : x'.get 11#5 = x.get 11#5)
    (h12 : x'.get 12#5 = x.get 12#5)
    (h14 : x'.get 14#5 = x.get 2#5 + 18446744073709551512#64) (h15 : x'.get 15#5 = 3#64)
    (h16 : x'.get 16#5 = 4#64)
    (hk : ∀ x'' m'', EXFrame x m x'' m'' → x''.get 10#5 = x.get 10#5 → x''.get 11#5 = x.get 11#5 →
      x''.get 12#5 = x.get 12#5 → x''.get 13#5 = x'.get 13#5 →
      x''.get 14#5 = x.get 2#5 + 18446744073709551512#64 → x''.get 15#5 = 3#64 → x''.get 16#5 = 4#64 →
      words m'' (x.get 2#5 + 18446744073709551544#64) 4 =
        words m (x.get 11#5) 4 * words m' (x.get 2#5 + 18446744073709551512#64) 4 % 2 ^ 256 →
      words m'' (x.get 2#5 + 18446744073709551512#64) 4 = words m' (x.get 2#5 + 18446744073709551512#64) 4 →
      Reach (exBufs x D) exp_256_image_prog base (pcAt base 117) x'' m'' ret Q) :
    Reach (exBufs x D) exp_256_image_prog base (pcAt base 192) x' m' ret Q := by
  simp only [← hF.words_arg hpre 11#5 (by decide)] at hk
  ex_pre
  have hsp := hF.1
  rw [← regs_set_of_get' (by decide) h10, ← regs_set_of_get' (by decide) h11,
    ← regs_set_of_get' (by decide) h12, ← regs_set_of_get' (by decide) hsp,
    ← regs_set_of_get' (by decide) h14, ← regs_set_of_get' (by decide) h15,
    ← regs_set_of_get' (by decide) h16]
  rv_exec_cut 117
  rv_copies
  try rv_val
  ex_mul_end

end IntxRV.Api
