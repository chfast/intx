import IntxRV.Api.udivrem_256
import IntxRV.Neg
import IntxRV.Div512
import IntxRV.TacticM
import IntxRV.Gen.Api.sdivrem_256

/-!
# The paths of `sdivrem()`

The frame of 112 bytes with ra and s0 to s3 (`SDFrame`), the epilogue at 124 (`sd_epi`), and the
arithmetic of the signed division by the magnitudes (`sdivrem_quot`, `sdivrem_rem`). The image of
`sdivrem()` with its segments nested to the right (`ps_eq`). See `IntxRV/Api/sdivrem_256.lean`.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

set_option hygiene false in
-- The image of `sdivrem()` with its segments nested to the right: the fetch of an instruction of
-- `sdivrem()` reduces only the first segments.
local notation "PS" => sdivrem_256_image_prog_0 ++ (sdivrem_256_image_prog_1 ++ (
  sdivrem_256_image_prog_2 ++ (sdivrem_256_image_prog_3 ++ (sdivrem_256_image_prog_4 ++ (
  sdivrem_256_image_prog_5 ++ (sdivrem_256_image_prog_6 ++ (sdivrem_256_image_prog_7 ++ (
  sdivrem_256_image_prog_8 ++ (sdivrem_256_image_prog_9 ++ (sdivrem_256_image_prog_10 ++ (
  sdivrem_256_image_prog_11 ++ (sdivrem_256_image_prog_12 ++ (sdivrem_256_image_prog_13 ++ (
  sdivrem_256_image_prog_14 ++ (sdivrem_256_image_prog_15 ++ (sdivrem_256_image_prog_16 ++ (
  sdivrem_256_image_prog_17 ++ (sdivrem_256_image_prog_18 ++ (sdivrem_256_image_prog_19 ++ (
  sdivrem_256_image_prog_20 ++ (sdivrem_256_image_prog_21 ++ (
  sdivrem_256_image_prog_22))))))))))))))))))))))

theorem ps_eq : sdivrem_256_image_prog = PS := by
  simp only [sdivrem_256_image_prog, List.append_assoc]

theorem ps_length : 4 * (PS).length < 2 ^ 64 := by
  rw [← ps_eq]; decide

/-- `udivrem<256, 256>()` and its callees in the image of `sdivrem()` nested to the right. -/
theorem ps_udivrem_in : ((PS).drop 131).take (udivrem_256_progAt 0x1#20 0x2d0#12 0x1#20 0xf08#12 0x1#20 0x994#12 0x0#20 0x688#12 0x0#20 0x31c#12).length =
    udivrem_256_progAt 0x1#20 0x2d0#12 0x1#20 0xf08#12 0x1#20 0x994#12 0x0#20 0x688#12 0x0#20 0x31c#12 := by
  rw [← ps_eq]; exact sdivrem_256_image_udivrem_256_in

/-- The addresses of the words of `sdivrem()`: u, v, the result, the frame of 160 bytes with the
frame of `udivrem()` and `D`. -/
abbrev sdBufs (x : Regs) (D : List (BitVec 64)) : List (BitVec 64) :=
  bufWords (x.get 11#5) 4 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 8 ++
    bufWords (x.get 2#5 - 160#64) 20 ++ D

/-- The frame of `sdivrem()` after its prologue: sp 112 bytes lower, ra and s0 to s3 saved, and the
memory outside the result and the frame of 160 bytes unchanged. -/
def SDFrame (x : Regs) (m : Mem) (x' : Regs) (m' : Mem) : Prop :=
  x'.get 2#5 = x.get 2#5 + 18446744073709551504#64 ∧
  memWord m' (x.get 2#5 + 18446744073709551608#64).toNat = x.get 1#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551600#64).toNat = x.get 8#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551592#64).toNat = x.get 9#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551584#64).toNat = x.get 18#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551576#64).toNat = x.get 19#5 ∧
  UnchangedExcept2 m m' (x.get 10#5) 64 (x.get 2#5 - 160#64) 160 ∧
  ∀ r ∈ calleeSaved, r ∉ [2#5, 8#5, 9#5, 18#5, 19#5] → x'.get r = x.get r

set_option hygiene false in
/-- The callee-saved registers that the frame keeps, through the sets of the other registers. -/
local macro "sd_cs" : tactic => `(tactic| (
  intro r hr' hn
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte] at hn ⊢))

/-- The frame after a change of the memory only in the result and below the saved registers. -/
theorem SDFrame.mem {x : Regs} {m : Mem} {x' : Regs} {m1 m2 : Mem} (hF : SDFrame x m x' m1)
    (hpre : sdivrem_256.pre x m)
    (h : UnchangedExcept2 m1 m2 (x.get 10#5) 64 (x.get 2#5 - 160#64) 120) :
    SDFrame x m x' m2 := by
  simp only [sdivrem_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, -, -, -, -, ⟨hsa, hsn⟩, -, -, hdsr⟩ := hpre
  obtain ⟨hsp, hfra, hfs0, hfs1, hfs2, hfs3, hunF, hcsF⟩ := hF
  have hw : ∀ c : BitVec 64, (x.get 2#5 - 160#64).toNat + 120 ≤ (x.get 2#5 + c).toNat →
      (x.get 2#5 + c).toNat + 8 ≤ (x.get 2#5 - 160#64).toNat + 160 →
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
theorem SDFrame.regs {x : Regs} {m : Mem} {x' x'' : Regs} {m' : Mem} (hF : SDFrame x m x' m')
    (h2 : x''.get 2#5 = x'.get 2#5)
    (hcs : ∀ r ∈ calleeSaved, r ∉ [2#5, 8#5, 9#5, 18#5, 19#5] → x''.get r = x'.get r) :
    SDFrame x m x'' m' := by
  obtain ⟨hsp, hfra, hfs0, hfs1, hfs2, hfs3, hunF, hcsF⟩ := hF
  exact ⟨h2.trans hsp, hfra, hfs0, hfs1, hfs2, hfs3, hunF,
    fun r hr hn => (hcs r hr hn).trans (hcsF r hr hn)⟩

/-- The frame after a call, which keeps the callee-saved registers. -/
theorem SDFrame.callee {x : Regs} {m : Mem} {x' x3 : Regs} {m' : Mem} (hF : SDFrame x m x' m')
    (hcs : ∀ i ∈ calleeSaved, x3 i = x' i) : SDFrame x m x3 m' := by
  have h0 : ∀ i ∈ calleeSaved, i ≠ 0 := by decide
  refine SDFrame.regs hF ?_ fun r hr _ => ?_
  · rw [← Regs.eq_get x3 (by decide), hcs _ (by decide), Regs.eq_get x' (by decide)]
  · rw [← Regs.eq_get x3 (h0 r hr), hcs r hr, Regs.eq_get x' (h0 r hr)]

/-- A word of an argument in the memory of the frame. -/
theorem SDFrame.memWord_arg {x : Regs} {m : Mem} {x' : Regs} {m' : Mem} (hF : SDFrame x m x' m')
    (hpre : sdivrem_256.pre x m) (r : BitVec 5) (hr : r = 11#5 ∨ r = 12#5)
    (c : BitVec 64) (hc : c.toNat + 8 ≤ 32) :
    memWord m' (x.get r + c).toNat = memWord m (x.get r + c).toNat := by
  simp only [sdivrem_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr⟩ := hpre
  rcases hr with rfl | rfl <;>
    exact memWord_of_unchangedExcept2 hF.2.2.2.2.2.2.1 _ (by bv_omega) (by bv_omega)

/-- The table of the reciprocal in the memory of the frame. -/
theorem SDFrame.holdsData {x : Regs} {m : Mem} {x' : Regs} {m' : Mem} {T : BitVec 64}
    (hF : SDFrame x m x' m') (hw : T.toNat + 8 * 256 ≤ 2 ^ 64)
    (hTr : (x.get 10#5).toNat + 64 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hTs : (x.get 2#5 - 160#64).toNat + 160 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 160#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) :
    HoldsData m' T reciprocal_2by1_image_data :=
  holdsData_of_unchangedExcept2 hF.2.2.2.2.2.2.1 _ T hw hTr hTs hhold

/-- The sign of a number of 4 words: the sign bit of its top word. -/
theorem sd_sign (w0 w1 w2 w3 : BitVec 64) :
    (2 ^ 63 ≤ w3.toNat) ↔
      2 ^ 255 ≤ w0.toNat + 2 ^ 64 * (w1.toNat + 2 ^ 64 * (w2.toNat + 2 ^ 64 * w3.toNat)) := by
  have := w0.isLt; have := w1.isLt; have := w2.isLt; have := w3.isLt
  omega

open LeanRV64D.Functions in
/-- `bge` with 0: the sign bit is 0. -/
theorem zopz0zKzJ_s_zero (a : BitVec 64) : zopz0zKzJ_s a 0#64 = decide (a.toNat < 2 ^ 63) := by
  simp only [zopz0zKzJ_s, BitVec.toInt_zero]
  rw [BitVec.toInt_eq_toNat_cond]
  split <;> simp <;> omega

/-! ## The arithmetic of the signed division -/

theorem tdiv_natCast (a b : Nat) : (a : Int).tdiv b = ((a / b : Nat) : Int) := by simp [Int.tdiv]
theorem tmod_natCast (a b : Nat) : (a : Int).tmod b = ((a % b : Nat) : Int) := by simp [Int.tmod]

/-- `-k` modulo `M` as a natural number. -/
theorem toNat_neg_emod {M k : Nat} (hk : k < M) :
    Int.toNat (-(k : Int) % (M : Int)) = (M - k) % M := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  · have h1 : -(k : Int) % (M : Int) = ((M - k : Nat) : Int) := by
      rw [← Int.add_emod_right, Int.emod_eq_of_lt (by omega) (by omega)]
      omega
    rw [h1, Int.toNat_natCast, Nat.mod_eq_of_lt (by omega)]

theorem toNat_natCast_emod {M k : Nat} (hk : k < M) : Int.toNat ((k : Int) % (M : Int)) = k := by
  rw [Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast]

theorem two_pow_pred {N : Nat} (hN : 0 < N) : 2 ^ N = 2 * 2 ^ (N - 1) := by
  rw [← Nat.pow_succ']; congr 1; omega

/-- A negative number of N bits: minus its magnitude. -/
theorem signed_of_neg {N U : Nat} (hN : 0 < N) (h : 2 ^ (N - 1) ≤ U) (hU : U < 2 ^ N) :
    signed N U = -((((2 ^ N - U) % 2 ^ N : Nat)) : Int) := by
  have := two_pow_pred hN
  rw [signed, if_neg (by omega), Nat.mod_eq_of_lt (by omega)]
  push_cast [Nat.cast_sub hU.le]
  ring

theorem signed_of_pos {N U : Nat} (h : ¬2 ^ (N - 1) ≤ U) : signed N U = (U : Int) := by
  rw [signed, if_pos (by omega)]

/-- The quotient of `sdivrem()`: the quotient of the magnitudes, negated for different signs. -/
theorem sdivrem_quot {N U V : Nat} (hN : 0 < N) (hU : U < 2 ^ N) (hV : V < 2 ^ N) :
    (if (2 ^ (N - 1) ≤ U) ≠ (2 ^ (N - 1) ≤ V) then
        (2 ^ N - (if 2 ^ (N - 1) ≤ U then (2 ^ N - U) % 2 ^ N else U) /
          (if 2 ^ (N - 1) ≤ V then (2 ^ N - V) % 2 ^ N else V)) % 2 ^ N
      else (if 2 ^ (N - 1) ≤ U then (2 ^ N - U) % 2 ^ N else U) /
          (if 2 ^ (N - 1) ≤ V then (2 ^ N - V) % 2 ^ N else V)) =
      Int.toNat ((signed N U).tdiv (signed N V) % 2 ^ N) := by
  have hM : ((2 ^ N : Nat) : Int) = (2 : Int) ^ N := by push_cast; rfl
  have hq : ∀ a b : Nat, a < 2 ^ N → a / b < 2 ^ N := fun a b h =>
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h
  have hm : ∀ a : Nat, a % 2 ^ N < 2 ^ N := fun a => Nat.mod_lt _ (by positivity)
  by_cases su : 2 ^ (N - 1) ≤ U <;> by_cases sv : 2 ^ (N - 1) ≤ V
  · rw [if_neg (by simp [su, sv]), if_pos su, if_pos sv, signed_of_neg hN su hU,
      signed_of_neg hN sv hV, Int.neg_tdiv, Int.tdiv_neg, Int.neg_neg, tdiv_natCast, ← hM,
      toNat_natCast_emod (hq _ _ (hm _))]
  · rw [if_pos (by simp [su, sv]), if_pos su, if_neg sv, signed_of_neg hN su hU,
      signed_of_pos sv, Int.neg_tdiv, tdiv_natCast, ← hM, toNat_neg_emod (hq _ _ (hm _))]
  · rw [if_pos (by simp [su, sv]), if_neg su, if_pos sv, signed_of_pos su,
      signed_of_neg hN sv hV, Int.tdiv_neg, tdiv_natCast, ← hM, toNat_neg_emod (hq _ _ hU)]
  · rw [if_neg (by simp [su, sv]), if_neg su, if_neg sv, signed_of_pos su, signed_of_pos sv,
      tdiv_natCast, ← hM, toNat_natCast_emod (hq _ _ hU)]

/-- The remainder of `sdivrem()`: the remainder of the magnitudes, negated for a negative u, and 0
for v = 0. -/
theorem sdivrem_rem {N U V : Nat} (hN : 0 < N) (hU : U < 2 ^ N) (hV : V < 2 ^ N) :
    (if 2 ^ (N - 1) ≤ U then
        (2 ^ N - (if (if 2 ^ (N - 1) ≤ V then (2 ^ N - V) % 2 ^ N else V) = 0 then 0 else
          (if 2 ^ (N - 1) ≤ U then (2 ^ N - U) % 2 ^ N else U) %
            (if 2 ^ (N - 1) ≤ V then (2 ^ N - V) % 2 ^ N else V))) % 2 ^ N
      else (if (if 2 ^ (N - 1) ≤ V then (2 ^ N - V) % 2 ^ N else V) = 0 then 0 else
          (if 2 ^ (N - 1) ≤ U then (2 ^ N - U) % 2 ^ N else U) %
            (if 2 ^ (N - 1) ≤ V then (2 ^ N - V) % 2 ^ N else V))) =
      if V = 0 then 0 else Int.toNat ((signed N U).tmod (signed N V) % 2 ^ N) := by
  have hM : ((2 ^ N : Nat) : Int) = (2 : Int) ^ N := by push_cast; rfl
  have hm : ∀ a : Nat, a % 2 ^ N < 2 ^ N := fun a => Nat.mod_lt _ (by positivity)
  have hr : ∀ a b : Nat, a < 2 ^ N → a % b < 2 ^ N := fun a b h =>
    Nat.lt_of_le_of_lt (Nat.mod_le _ _) h
  have := two_pow_pred hN
  by_cases hV0 : V = 0
  · subst hV0
    have : ¬2 ^ (N - 1) ≤ 0 := by have := Nat.two_pow_pos (N - 1); omega
    simp [this]
  have hva : (if 2 ^ (N - 1) ≤ V then (2 ^ N - V) % 2 ^ N else V) ≠ 0 := by
    split_ifs <;> [rw [Nat.mod_eq_of_lt (by omega)]; skip] <;> omega
  rw [if_neg hva, if_neg hV0]
  by_cases su : 2 ^ (N - 1) ≤ U <;> by_cases sv : 2 ^ (N - 1) ≤ V
  · rw [if_pos su, if_pos su, if_pos sv, signed_of_neg hN su hU, signed_of_neg hN sv hV,
      Int.tmod_neg, Int.neg_tmod, tmod_natCast, ← hM, toNat_neg_emod (hr _ _ (hm _))]
  · rw [if_pos su, if_pos su, if_neg sv, signed_of_neg hN su hU, signed_of_pos sv, Int.neg_tmod,
      tmod_natCast, ← hM, toNat_neg_emod (hr _ _ (hm _))]
  · rw [if_neg su, if_neg su, if_pos sv, signed_of_pos su, signed_of_neg hN sv hV, Int.tmod_neg,
      tmod_natCast, ← hM, toNat_natCast_emod (hr _ _ hU)]
  · rw [if_neg su, if_neg su, if_neg sv, signed_of_pos su, signed_of_pos sv, tmod_natCast, ← hM,
      toNat_natCast_emod (hr _ _ hU)]

/-- The end of `sdivrem()` at 124: the restore of ra and s0 to s3 and the return, with the result
stored. -/
theorem sd_epi {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hr : x.get 1#5 &&& 3 = 0) (x4 : Regs) (m4 : Mem) (hF : SDFrame x m x4 m4)
    (hq : words m4 (x.get 10#5) 4 = Int.toNat ((signed 256 (words m (x.get 11#5) 4)).tdiv
      (signed 256 (words m (x.get 12#5) 4)) % 2 ^ 256))
    (hrem : words m4 (x.get 10#5 + 32#64) 4 = if words m (x.get 12#5) 4 = 0 then 0 else
      Int.toNat ((signed 256 (words m (x.get 11#5) 4)).tmod (signed 256 (words m (x.get 12#5) 4)) %
        2 ^ 256)) :
    Reach (sdBufs x D) PS base (pcAt base 124) x4 m4 (x.get 1#5) (sdivrem_256.post x m) := by
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
  simp only [sdivrem_256.post]
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
         | exact hws0 | exact hws1 | exact hws2 | exact hws3)

set_option hygiene false in
/-- The destructured precondition of `sdivrem()`. -/
local macro "sd_pre" : tactic => `(tactic| (
  have hpre0 := hpre
  simp only [sdivrem_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr⟩ := hpre))

/-- The sign of u from its top word. -/
theorem sd_sign_u (m : Mem) (a : BitVec 64) :
    (2 ^ 63 ≤ (memWord m (a + 24#64).toNat).toNat) ↔ 2 ^ 255 ≤ words m a 4 := by
  rw [words4_unfold]; exact sd_sign _ _ _ _

/-- The remainder from 101: negated for a negative u, then the epilogue. -/
theorem sd_rem {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hr : x.get 1#5 &&& 3 = 0) (hpre : sdivrem_256.pre x m) (x' : Regs) (m' : Mem)
    (hF : SDFrame x m x' m') (h8 : x'.get 8#5 = x.get 10#5)
    (h9 : x'.get 9#5 = memWord m (x.get 11#5 + 24#64).toNat) (R0 : Nat)
    (hR : words m' (x.get 10#5 + 32#64) 4 = R0)
    (hq : words m' (x.get 10#5) 4 = Int.toNat ((signed 256 (words m (x.get 11#5) 4)).tdiv
      (signed 256 (words m (x.get 12#5) 4)) % 2 ^ 256))
    (hRs : (if 2 ^ 255 ≤ words m (x.get 11#5) 4 then (2 ^ 256 - R0) % 2 ^ 256 else R0) =
      if words m (x.get 12#5) 4 = 0 then 0 else
      Int.toNat ((signed 256 (words m (x.get 11#5) 4)).tmod (signed 256 (words m (x.get 12#5) 4)) %
        2 ^ 256)) :
    Reach (sdBufs x D) PS base (pcAt base 101) x' m' (x.get 1#5) (sdivrem_256.post x m) := by
  sd_pre
  have hsg := sd_sign_u m (x.get 11#5)
  rw [← regs_set_of_get' (by decide) h8, ← regs_set_of_get' (by decide) h9]
  rv_exec_cut 124
  all_goals try simp only [zopz0zKzJ_s_zero, decide_eq_true_eq, decide_eq_false_iff_not] at *
  · refine sd_epi base x m hr _ m' (SDFrame.regs hF ?_ ?_) hq ?_
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · sd_cs
    · rw [hR, ← hRs, if_neg (by omega)]
  · refine sd_epi base x m hr _ _ (SDFrame.regs (SDFrame.mem hF hpre0 ?_) ?_ ?_) ?_ ?_
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte,
        BitVec.reduceSignExtend]
      simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
      exact unchangedExcept2_refl _ _ _ _ _
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · sd_cs
    · rw [← hq]
      simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte,
        BitVec.reduceSignExtend]
      simp (disch := first | bv_omega | fail) only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
        BitVec.reduceAdd, memWord_memStore_of_ne, Nat.mul_zero, Nat.add_zero]
    · rw [← hRs, if_pos (by omega), ← hR]
      simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte,
        BitVec.reduceSignExtend]
      simp (disch := first | bv_omega | fail) only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
        BitVec.reduceAdd, memWord_memStore_self, memWord_memStore_of_ne,
        Nat.mul_zero, Nat.add_zero]
      rv_loads
      apply neg4_words
      all_goals assumption

/-- Two bits of `slti` are equal for equal conditions. -/
theorem sd_bits_eq {p q : Prop} [Decidable p] [Decidable q] :
    ((if p then 1#64 else 0#64) = (if q then 1#64 else 0#64)) ↔ (p ↔ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- The signs of u and v are equal for equal bits. -/
theorem sd_not_ne {a b c d : Prop} (hb : a ↔ b) (ha : a ↔ c) (hd : b ↔ d) : ¬(c ≠ d) :=
  fun h => h (propext (ha.symm.trans (hb.trans hd)))

/-- The signs of u and v differ for different bits. -/
theorem sd_ne {a b c d : Prop} (hb : ¬(a ↔ b)) (ha : a ↔ c) (hd : b ↔ d) : c ≠ d :=
  fun h => hb (ha.trans (h ▸ hd.symm))

/-- The quotient from 78: negated for different signs of u and v, then the remainder. -/
theorem sd_quot {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hr : x.get 1#5 &&& 3 = 0) (hpre : sdivrem_256.pre x m) (x' : Regs) (m' : Mem)
    (hF : SDFrame x m x' m') (h8 : x'.get 8#5 = x.get 10#5)
    (h9 : x'.get 9#5 = memWord m (x.get 11#5 + 24#64).toNat)
    (h18 : x'.get 18#5 =
      if 2 ^ 63 ≤ (memWord m (x.get 12#5 + 24#64).toNat).toNat then 1#64 else 0#64)
    (h19 : x'.get 19#5 =
      if 2 ^ 63 ≤ (memWord m (x.get 11#5 + 24#64).toNat).toNat then 1#64 else 0#64)
    (Q0 R0 : Nat) (hQ : words m' (x.get 10#5) 4 = Q0) (hR : words m' (x.get 10#5 + 32#64) 4 = R0)
    (hQs : (if (2 ^ 255 ≤ words m (x.get 11#5) 4) ≠ (2 ^ 255 ≤ words m (x.get 12#5) 4) then
        (2 ^ 256 - Q0) % 2 ^ 256 else Q0) = Int.toNat ((signed 256 (words m (x.get 11#5) 4)).tdiv
      (signed 256 (words m (x.get 12#5) 4)) % 2 ^ 256))
    (hRs : (if 2 ^ 255 ≤ words m (x.get 11#5) 4 then (2 ^ 256 - R0) % 2 ^ 256 else R0) =
      if words m (x.get 12#5) 4 = 0 then 0 else
      Int.toNat ((signed 256 (words m (x.get 11#5) 4)).tmod (signed 256 (words m (x.get 12#5) 4)) %
        2 ^ 256)) :
    Reach (sdBufs x D) PS base (pcAt base 78) x' m' (x.get 1#5) (sdivrem_256.post x m) := by
  sd_pre
  have hsu := sd_sign_u m (x.get 11#5)
  have hsv := sd_sign_u m (x.get 12#5)
  rw [← regs_set_of_get' (by decide) h8, ← regs_set_of_get' (by decide) h9,
    ← regs_set_of_get' (by decide) h18, ← regs_set_of_get' (by decide) h19]
  rv_exec_cut 101
  all_goals try simp only [sd_bits_eq] at *
  · refine sd_rem base x m hr hpre0 _ m' (SDFrame.regs hF ?_ ?_) ?_ ?_ R0 hR ?_ hRs
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · sd_cs
    · rw [hQ, ← hQs, if_neg (sd_not_ne (by assumption) hsu hsv)]
  · refine sd_rem base x m hr hpre0 _ _ (SDFrame.regs (SDFrame.mem hF hpre0 ?_) ?_ ?_) ?_ ?_ R0
      ?_ ?_ hRs
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte,
        BitVec.reduceSignExtend]
      simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
      exact unchangedExcept2_refl _ _ _ _ _
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · sd_cs
    · rw [← hR]
      simp only [BitVec.reduceSignExtend]
      simp (disch := first | bv_omega | fail) only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
        BitVec.reduceAdd, BitVec.add_zero, memWord_memStore_of_ne, Nat.mul_zero, Nat.add_zero]
    · rw [← hQs, if_pos (sd_ne (by assumption) hsu hsv), ← hQ]
      simp only [BitVec.reduceSignExtend]
      simp (disch := first | bv_omega | fail) only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
        BitVec.reduceAdd, BitVec.add_zero, memWord_memStore_self, memWord_memStore_of_ne,
        Nat.mul_zero, Nat.add_zero]
      rv_loads
      apply neg4_words
      all_goals assumption

/-- The magnitude of a number of 256 bits, as `sdivrem()` computes it. -/
abbrev sdAbs (U : Nat) : Nat := if 2 ^ 255 ≤ U then (2 ^ 256 - U) % 2 ^ 256 else U

/-- The call of `udivrem<256, 256>()` from 71 with the magnitudes of u and v in the frame, then the
quotient and the remainder. -/
theorem sd_call {D : List (BitVec 64)} (base T : BitVec 64) (x : Regs) (m : Mem)
    (hb3 : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0) (hpre : sdivrem_256.pre x m)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64)
    (hTr : (x.get 10#5).toNat + 64 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hTs : (x.get 2#5 - 160#64).toNat + 160 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 160#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hD : ∀ a ∈ bufWords T 256, a ∈ D)
    (hT0 : pcAt (pcAt (pcAt base 131) 108) 5 + ((0x1#20 ++ 0x000#12).signExtend 64 +
      (0x2d0#12).signExtend 64) = T)
    (hT1 : pcAt (pcAt (pcAt base 131) 301) 54 + ((0x1#20 ++ 0x000#12).signExtend 64 +
      (0xf08#12).signExtend 64) = T)
    (hT2 : pcAt (pcAt (pcAt base 131) 615) 89 + ((0x1#20 ++ 0x000#12).signExtend 64 +
      (0x994#12).signExtend 64) = T)
    (hT3 : pcAt (pcAt (pcAt base 131) 824) 75 + ((0x0#20 ++ 0x000#12).signExtend 64 +
      (0x688#12).signExtend 64) = T)
    (hT4 : pcAt (pcAt (pcAt base 131) 1033) 85 + ((0x0#20 ++ 0x000#12).signExtend 64 +
      (0x31c#12).signExtend 64) = T)
    (x' : Regs) (m' : Mem) (hF : SDFrame x m x' m') (h8 : x'.get 8#5 = x.get 10#5)
    (h9 : x'.get 9#5 = memWord m (x.get 11#5 + 24#64).toNat)
    (h13 : x'.get 13#5 = memWord m (x.get 12#5 + 24#64).toNat)
    (hUA : words m' (x.get 2#5 + 18446744073709551544#64) 4 = sdAbs (words m (x.get 11#5) 4))
    (hVA : words m' (x.get 2#5 + 18446744073709551512#64) 4 = sdAbs (words m (x.get 12#5) 4)) :
    Reach (sdBufs x D) PS base (pcAt base 71) x' m' (x.get 1#5) (sdivrem_256.post x m) := by
  -- `omega` and `subst_vars` do not see the addresses of the table.
  replace hT0 := PLift.up hT0
  replace hT1 := PLift.up hT1
  replace hT2 := PLift.up hT2
  replace hT3 := PLift.up hT3
  replace hT4 := PLift.up hT4
  sd_pre
  have hsp := hF.1
  rw [← regs_set_of_get' (by decide) h8, ← regs_set_of_get' (by decide) h9,
    ← regs_set_of_get' (by decide) h13, ← regs_set_of_get' (by decide) hsp]
  rv_exec_cut 131
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.reduceSignExtend]
  rw [show pcAt base 76 + 220#64 = pcAt base 131 by simp only [pcAt]; bv_omega,
    update_aligned (pcAt_aligned hb3 131)]
  have hU := words_lt m 4 (x.get 11#5)
  have hV := words_lt m 4 (x.get 12#5)
  have hsu := sd_sign_u m (x.get 11#5)
  have hsv := sd_sign_u m (x.get 12#5)
  refine Reach.call_sub (r := 78) ps_udivrem_in ps_length
    (udivrem_256.reach 0x1#20 0x2d0#12 0x1#20 0xf08#12 0x1#20 0x994#12 0x0#20 0x688#12 0x0#20
      0x31c#12
      (pcAt base 131) T _ _ hT0.down hT1.down hT2.down hT3.down hT4.down (pcAt_aligned hb3 131)
      hw ?_ ?_ ?_ ?_ ?_) ?_ ?_ ?_
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    exact pcAt_aligned hb3 78
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    exact hTr
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    bv_omega
  · exact hF.holdsData hw hTr hTs hhold
  · simp only [udivrem_256.pre, Buf, Disjoint]
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    try simp (disch := decide) only [Regs.eq_get x']
    repeat' apply And.intro
    all_goals bv_omega
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · intro a ha
    simp only [udivrem_256.bufs] at ha
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at ha
    try simp (disch := decide) only [Regs.eq_get x'] at ha
    simp only [List.mem_append] at ha ⊢
    rcases ha with ((((h | h) | h) | h) | h)
    · rw [show x.get 2#5 + 18446744073709551544#64 = x.get 2#5 - 160#64 + BitVec.ofNat 64 (8 * 11)
        by bv_omega] at h
      exact Or.inl (Or.inr (mem_bufWords_of_offset (by decide) h))
    · rw [show x.get 2#5 + 18446744073709551512#64 = x.get 2#5 - 160#64 + BitVec.ofNat 64 (8 * 7)
        by bv_omega] at h
      exact Or.inl (Or.inr (mem_bufWords_of_offset (by decide) h))
    · exact Or.inl (Or.inl (Or.inr h))
    · rw [show x.get 2#5 + 18446744073709551504#64 - 48#64 = x.get 2#5 - 160#64 +
        BitVec.ofNat 64 (8 * 0) by bv_omega] at h
      exact Or.inl (Or.inr (mem_bufWords_of_offset (by decide) h))
    · exact Or.inr (hD _ h)
  · intro x3 m3 hpost
    obtain ⟨hq, hrem, hunc, hsaved⟩ := hpost
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at hq hrem hunc
    try simp (disch := decide) only [Regs.eq_get x'] at hq hrem hunc
    rw [hUA, hVA] at hq hrem
    rw [show x.get 2#5 + 18446744073709551504#64 - 48#64 = x.get 2#5 - 160#64 by bv_omega] at hunc
    -- s2 and s3 hold the signs: the frame keeps the other callee-saved registers.
    have hF3 : SDFrame x m x3 m3 := by
      refine SDFrame.regs (SDFrame.mem hF hpre0 (fun k hk1 hk2 => hunc k hk1 (by omega))) ?_ ?_
      · rw [get_of_calleeSaved hsaved (by decide)]
        simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
        exact hsp.symm
      · intro r hr' hn
        rw [get_of_calleeSaved hsaved hr']
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl <;> simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
            at hn ⊢
    have hq3 := sdivrem_quot (N := 256) (by decide) hU hV
    have hr3 := sdivrem_rem (N := 256) (by decide) hU hV
    simp only [Nat.reduceSub] at hq3 hr3
    refine sd_quot base x m hr hpre0 x3 m3 hF3 ?_ ?_ ?_ ?_ _ _ hq hrem hq3 hr3
    all_goals rw [get_of_calleeSaved hsaved (by decide)]
    all_goals simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte,
      itypeVal_slti_zero]
    all_goals rfl

/-- The paths of `sdivrem()` from 6, after the prologue: the magnitudes of u and v, copied or
negated by their signs, in the frame, then the call. -/
theorem sd_main {D : List (BitVec 64)} (base T : BitVec 64) (x : Regs) (m : Mem)
    (hb3 : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0) (hpre : sdivrem_256.pre x m)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64)
    (hTr : (x.get 10#5).toNat + 64 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hTs : (x.get 2#5 - 160#64).toNat + 160 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 160#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hD : ∀ a ∈ bufWords T 256, a ∈ D)
    (hT0 : pcAt (pcAt (pcAt base 131) 108) 5 + ((0x1#20 ++ 0x000#12).signExtend 64 +
      (0x2d0#12).signExtend 64) = T)
    (hT1 : pcAt (pcAt (pcAt base 131) 301) 54 + ((0x1#20 ++ 0x000#12).signExtend 64 +
      (0xf08#12).signExtend 64) = T)
    (hT2 : pcAt (pcAt (pcAt base 131) 615) 89 + ((0x1#20 ++ 0x000#12).signExtend 64 +
      (0x994#12).signExtend 64) = T)
    (hT3 : pcAt (pcAt (pcAt base 131) 824) 75 + ((0x0#20 ++ 0x000#12).signExtend 64 +
      (0x688#12).signExtend 64) = T)
    (hT4 : pcAt (pcAt (pcAt base 131) 1033) 85 + ((0x0#20 ++ 0x000#12).signExtend 64 +
      (0x31c#12).signExtend 64) = T)
    (x' : Regs) (m' : Mem) (hF : SDFrame x m x' m') (h10 : x'.get 10#5 = x.get 10#5)
    (h11 : x'.get 11#5 = x.get 11#5) (h12 : x'.get 12#5 = x.get 12#5) :
    Reach (sdBufs x D) PS base (pcAt base 6) x' m' (x.get 1#5) (sdivrem_256.post x m) := by
  replace hT0 := PLift.up hT0
  replace hT1 := PLift.up hT1
  replace hT2 := PLift.up hT2
  replace hT3 := PLift.up hT3
  replace hT4 := PLift.up hT4
  sd_pre
  have hxw := hF.memWord_arg hpre0 11#5 (by decide)
  have hyw := hF.memWord_arg hpre0 12#5 (by decide)
  have hx0 := hxw 0#64 (by decide)
  have hy0 := hyw 0#64 (by decide)
  rw [BitVec.add_zero] at hx0 hy0
  have hU := words4_unfold m (x.get 11#5)
  have hV := words4_unfold m (x.get 12#5)
  rw [← regs_set_of_get' (by decide) h10, ← regs_set_of_get' (by decide) h11,
    ← regs_set_of_get' (by decide) h12, ← regs_set_of_get' (by decide) hF.1]
  -- The top words of u and v, whose sign bits are the signs.
  rv_exec_cut 8
  rename_i u3 hu3 v3 hv3
  simp only [hxw 24#64 (by decide), hyw 24#64 (by decide)] at hu3 hv3
  have hsu : 2 ^ 63 ≤ u3.toNat ↔ 2 ^ 255 ≤ words m (x.get 11#5) 4 := by
    rw [hu3.eq]; exact sd_sign_u m (x.get 11#5)
  have hsv : 2 ^ 63 ≤ v3.toNat ↔ 2 ^ 255 ≤ words m (x.get 12#5) 4 := by
    rw [hv3.eq]; exact sd_sign_u m (x.get 12#5)
  rv_exec_cut 71
  all_goals simp only [hxw 8#64 (by decide), hxw 16#64 (by decide), hxw 24#64 (by decide),
    hyw 8#64 (by decide), hyw 16#64 (by decide), hyw 24#64 (by decide), hx0, hy0] at *
  all_goals try simp only [zopz0zI_s_zero, zopz0zKzJ_s_zero, decide_eq_true_eq,
    decide_eq_false_iff_not] at *
  all_goals
    refine sd_call base T x m hb3 hr hpre0 hw hTr hTs hhold hD hT0.down hT1.down hT2.down
      hT3.down hT4.down _ _
      (SDFrame.regs (SDFrame.mem hF hpre0 ?_) ?_ ?_) ?_ ?_ ?_ ?_ ?_
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte,
        BitVec.reduceSignExtend]
      simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
      exact unchangedExcept2_refl _ _ _ _ _
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    all_goals try sd_cs
    all_goals try with_reducible exact hu3.eq
    all_goals try with_reducible exact hv3.eq
    all_goals first
      | exact hF.1.symm
      | (simp only [sdAbs]
         split
         all_goals first | (exfalso; omega) | skip
         simp only [BitVec.reduceSignExtend, BitVec.add_assoc, BitVec.reduceAdd]
         simp (disch := first | bv_omega | fail) only [words, BitVec.ofNat_eq_ofNat,
           BitVec.add_assoc, BitVec.reduceAdd, memWord_memStore_self,
           memWord_memStore_of_ne, Nat.mul_zero, Nat.add_zero]
         rv_cse
         rv_loads
         first
           | rfl
           | (apply neg4_words
              all_goals assumption))

end IntxRV.Api
