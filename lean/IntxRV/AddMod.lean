import IntxRV.Api.udivrem_320_256


/-!
# The paths of `addmod()`

The frame of 160 bytes with ra and s0 to s3 (`AMFrame`), the epilogue at 55 (`am_epi`), and the
path for a modulus below 2^192 or the top words of x or y above its top word from 13 (`am_slow`):
the sum of 5 words in the frame and the call of `udivrem<320, 256>()` with the result in the frame
(`am_call`). The image of `addmod()` with its segments nested to the right (`pa_eq`), so that the
fetch of an instruction of `addmod()` does not reduce the instructions of its callees. See
`IntxRV/Api/addmod_256.lean`.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option hygiene false in
-- The image of `addmod()` with its segments nested to the right: the fetch of an instruction of
-- `addmod()` reduces only the first segments.
local notation "PA" => addmod_256_image_prog_0 ++ (addmod_256_image_prog_1 ++ (addmod_256_image_prog_2 ++
  (addmod_256_image_prog_3 ++ (addmod_256_image_prog_4 ++ (addmod_256_image_prog_5 ++
  (addmod_256_image_prog_6 ++ (addmod_256_image_prog_7 ++ (addmod_256_image_prog_8 ++
  (addmod_256_image_prog_9 ++ (addmod_256_image_prog_10 ++ (addmod_256_image_prog_11 ++
  (addmod_256_image_prog_12 ++ (addmod_256_image_prog_13 ++ (addmod_256_image_prog_14 ++
  (addmod_256_image_prog_15 ++ (addmod_256_image_prog_16 ++ (addmod_256_image_prog_17 ++
  (addmod_256_image_prog_18 ++ (addmod_256_image_prog_19 ++ (addmod_256_image_prog_20 ++
  (addmod_256_image_prog_21 ++ (addmod_256_image_prog_22 ++ (addmod_256_image_prog_23 ++
  (addmod_256_image_prog_24 ++ (addmod_256_image_prog_25 ++ (addmod_256_image_prog_26 ++
  (addmod_256_image_prog_27 ++ (addmod_256_image_prog_28 ++ (addmod_256_image_prog_29 ++
  (addmod_256_image_prog_30 ++ (addmod_256_image_prog_31 ++ (addmod_256_image_prog_32 ++
  (addmod_256_image_prog_33 ++ (addmod_256_image_prog_34 ++ (addmod_256_image_prog_35 ++
  (addmod_256_image_prog_36 ++ (addmod_256_image_prog_37 ++ (addmod_256_image_prog_38 ++
  (addmod_256_image_prog_39 ++ (addmod_256_image_prog_40 ++ (addmod_256_image_prog_41 ++
  (addmod_256_image_prog_42 ++ (addmod_256_image_prog_43 ++ (addmod_256_image_prog_44 ++
  (addmod_256_image_prog_45 ++ (addmod_256_image_prog_46 ++ (addmod_256_image_prog_47 ++
  (addmod_256_image_prog_48 ++
  (addmod_256_image_prog_49)))))))))))))))))))))))))))))))))))))))))))))))))

theorem pa_eq : addmod_256_image_prog = PA := by
  simp only [addmod_256_image_prog, List.append_assoc]

theorem pa_length : 4 * (PA).length < 2 ^ 64 := by
  rw [← pa_eq]; decide

/-- `udivrem<320, 256>()` and its callees in the image of `addmod()` nested to the right. -/
theorem pa_udivrem_in : ((PA).drop 158).take (udivrem_320_256_progAt 0x3#20 0xc04#12 0x3#20 0x900#12 0x2#20 0x470#12 0x2#20 0xf98#12 0x2#20 0xa00#12 0x1#20 0x72c#12 0x1#20 0x3a0#12 0x1#20 0xed4#12 0x1#20 0xa1c#12 0x0#20 0x3ac#12).length =
    udivrem_320_256_progAt 0x3#20 0xc04#12 0x3#20 0x900#12 0x2#20 0x470#12 0x2#20 0xf98#12 0x2#20 0xa00#12 0x1#20 0x72c#12 0x1#20 0x3a0#12 0x1#20 0xed4#12 0x1#20 0xa1c#12 0x0#20 0x3ac#12 := by
  rw [← pa_eq]; exact addmod_256_image_udivrem_320_256_in

/-- The addresses of the words of `addmod()`: x, y, mod, the result, the frame of 496 bytes with
the frames of the callees and `D`. -/
abbrev amBufs (x : Regs) (D : List (BitVec 64)) : List (BitVec 64) :=
  bufWords (x.get 11#5) 4 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 13#5) 4 ++
    bufWords (x.get 10#5) 4 ++ bufWords (x.get 2#5 - 496#64) 62 ++ D

/-- The frame of `addmod()` after its prologue: sp 160 bytes lower, ra and s0 to s3 saved, and the
memory outside the result and the frame of 496 bytes unchanged. -/
def AMFrame (x : Regs) (m : Mem) (x' : Regs) (m' : Mem) : Prop :=
  x'.get 2#5 = x.get 2#5 + 18446744073709551456#64 ∧
  memWord m' (x.get 2#5 + 18446744073709551608#64).toNat = x.get 1#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551600#64).toNat = x.get 8#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551592#64).toNat = x.get 9#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551584#64).toNat = x.get 18#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551576#64).toNat = x.get 19#5 ∧
  UnchangedExcept2 m m' (x.get 10#5) 32 (x.get 2#5 - 496#64) 496 ∧
  ∀ r ∈ calleeSaved, r ∉ [2#5, 8#5, 9#5, 18#5, 19#5] → x'.get r = x.get r

set_option hygiene false in
/-- The callee-saved registers that the frame keeps, through the sets of the other registers. -/
local macro "am_cs" : tactic => `(tactic| (
  intro r hr' hn
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte] at hn ⊢))

/-- The end of `addmod()` at 55: the restore of ra and s0 to s3 and the return, with the result
stored. -/
theorem am_epi {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hr : x.get 1#5 &&& 3 = 0) (x4 : Regs) (m4 : Mem) (hF : AMFrame x m x4 m4)
    (hres : words m4 (x.get 10#5) 4 = if words m (x.get 13#5) 4 = 0 then 0
      else (words m (x.get 11#5) 4 + words m (x.get 12#5) 4) % words m (x.get 13#5) 4) :
    Reach (amBufs x D) PA base (pcAt base 55) x4 m4 (x.get 1#5) (addmod_256.post x m) := by
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
  simp only [addmod_256.post]
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

/-- The frame after a change of the memory only in the result and below the saved registers. -/
theorem AMFrame.mem {x : Regs} {m : Mem} {x' : Regs} {m1 m2 : Mem} (hF : AMFrame x m x' m1)
    (hpre : addmod_256.pre x m)
    (h : UnchangedExcept2 m1 m2 (x.get 10#5) 32 (x.get 2#5 - 496#64) 456) :
    AMFrame x m x' m2 := by
  simp only [addmod_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, -, -, -, -, -, -, ⟨hsa, hsn⟩, -, -, -, hdsr⟩ := hpre
  obtain ⟨hsp, hfra, hfs0, hfs1, hfs2, hfs3, hunF, hcsF⟩ := hF
  have hw : ∀ c : BitVec 64, (x.get 2#5 - 496#64).toNat + 456 ≤ (x.get 2#5 + c).toNat →
      (x.get 2#5 + c).toNat + 8 ≤ (x.get 2#5 - 496#64).toNat + 496 →
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
theorem AMFrame.regs {x : Regs} {m : Mem} {x' x'' : Regs} {m' : Mem} (hF : AMFrame x m x' m')
    (h2 : x''.get 2#5 = x'.get 2#5)
    (hcs : ∀ r ∈ calleeSaved, r ∉ [2#5, 8#5, 9#5, 18#5, 19#5] → x''.get r = x'.get r) :
    AMFrame x m x'' m' := by
  obtain ⟨hsp, hfra, hfs0, hfs1, hfs2, hfs3, hunF, hcsF⟩ := hF
  exact ⟨h2.trans hsp, hfra, hfs0, hfs1, hfs2, hfs3, hunF,
    fun r hr hn => (hcs r hr hn).trans (hcsF r hr hn)⟩

/-- The frame after a call, which keeps the callee-saved registers. -/
theorem AMFrame.callee {x : Regs} {m : Mem} {x' x3 : Regs} {m' : Mem} (hF : AMFrame x m x' m')
    (hcs : ∀ i ∈ calleeSaved, x3 i = x' i) : AMFrame x m x3 m' := by
  have h0 : ∀ i ∈ calleeSaved, i ≠ 0 := by decide
  refine AMFrame.regs hF ?_ fun r hr _ => ?_
  · rw [← Regs.eq_get x3 (by decide), hcs _ (by decide), Regs.eq_get x' (by decide)]
  · rw [← Regs.eq_get x3 (h0 r hr), hcs r hr, Regs.eq_get x' (h0 r hr)]

/-- A word of an argument in the memory of the frame. -/
theorem AMFrame.memWord_arg {x : Regs} {m : Mem} {x' : Regs} {m' : Mem} (hF : AMFrame x m x' m')
    (hpre : addmod_256.pre x m) (r : BitVec 5) (hr : r = 11#5 ∨ r = 12#5 ∨ r = 13#5)
    (c : BitVec 64) (hc : c.toNat + 8 ≤ 32) :
    memWord m' (x.get r + c).toNat = memWord m (x.get r + c).toNat := by
  simp only [addmod_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hxa, hxn⟩, ⟨hya, hyn⟩, ⟨hma, hmn⟩, hdrx, hdry, hdrm, ⟨hsa, hsn⟩, hdsx,
    hdsy, hdsm, hdsr⟩ := hpre
  rcases hr with rfl | rfl | rfl <;>
    exact memWord_of_unchangedExcept2 hF.2.2.2.2.2.2.1 _ (by bv_omega) (by bv_omega)

/-- The words of an argument in the memory of the frame. -/
theorem AMFrame.words_arg {x : Regs} {m : Mem} {x' : Regs} {m' : Mem} (hF : AMFrame x m x' m')
    (hpre : addmod_256.pre x m) (r : BitVec 5) (hr : r = 11#5 ∨ r = 12#5 ∨ r = 13#5) :
    words m' (x.get r) 4 = words m (x.get r) 4 := by
  simp only [addmod_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hxa, hxn⟩, ⟨hya, hyn⟩, ⟨hma, hmn⟩, hdrx, hdry, hdrm, ⟨hsa, hsn⟩, hdsx,
    hdsy, hdsm, hdsr⟩ := hpre
  rcases hr with rfl | rfl | rfl <;>
    exact words_of_unchangedExcept2 hF.2.2.2.2.2.2.1 4 _ (by omega) (by omega) (by omega)

/-- The table of the reciprocal in the memory of the frame. -/
theorem AMFrame.holdsData {x : Regs} {m : Mem} {x' : Regs} {m' : Mem} {T : BitVec 64}
    (hF : AMFrame x m x' m') (hw : T.toNat + 8 * 256 ≤ 2 ^ 64)
    (hTr : (x.get 10#5).toNat + 32 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hTs : (x.get 2#5 - 496#64).toNat + 496 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 496#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) :
    HoldsData m' T reciprocal_2by1_image_data :=
  holdsData_of_unchangedExcept2 hF.2.2.2.2.2.2.1 _ T hw hTr hTs hhold

/-- A number of 4 words with the top word at most the top word of the modulus is less than twice
the modulus, for a top word of the modulus not 0. -/
theorem am_lt2 {X M x3 m3 : Nat} (hX : X < (x3 + 1) * 2 ^ 192) (hM : m3 * 2 ^ 192 ≤ M)
    (h3 : x3 ≤ m3) (hm3 : 1 ≤ m3) : X < 2 * M := by
  have : (x3 + 1) * 2 ^ 192 ≤ (m3 + 1) * 2 ^ 192 := Nat.mul_le_mul_right _ (by omega)
  have : 2 ^ 192 ≤ m3 * 2 ^ 192 := Nat.le_mul_of_pos_left _ hm3
  nlinarith

/-- The sum of two remainders and its one subtraction of the modulus with the carry `c` and the
borrow `br` of 4 words: the remainder of the sum. -/
theorem am_sum_nat {xn yn M a b c br : Nat} (hxn : xn < M) (hyn : yn < M) (hM : M < 2 ^ 256)
    (ha : a + 2 ^ 256 * c = xn + yn) (hb : b + M = a + 2 ^ 256 * br) (hc : c ≤ 1)
    (hbr : br ≤ 1) (ha256 : a < 2 ^ 256) (hb256 : b < 2 ^ 256) :
    (if c = 1 ∨ br = 0 then b else a) = (xn + yn) % M := by
  split_ifs with h
  · rcases h with h | h
    · subst h
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hbr with h0 | h0 <;> subst h0 <;> omega
    · subst h
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  · have hc0 : c = 0 := by omega
    have hbr1 : br = 1 := by omega
    subst hc0 hbr1
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- The call of `udivrem<320, 256>()` in `addmod()` from 37 with the sum of 5 words in the
registers: the stores of the sum in the frame, the call with the result in the frame, and the copy
of the remainder to the result. -/
theorem am_call {D : List (BitVec 64)} (base T : BitVec 64) (x : Regs) (m : Mem)
    (hb3 : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0) (hpre : addmod_256.pre x m)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64)
    (hTr : (x.get 10#5).toNat + 32 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hTs : (x.get 2#5 - 496#64).toNat + 496 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 496#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hD : ∀ a ∈ bufWords T 256, a ∈ D)
    (hT0 : pcAt (pcAt (pcAt base 158) 182) 5 + ((0x3#20 ++ 0x000#12).signExtend 64 +
      (0xc04#12).signExtend 64) = T)
    (hT1 : pcAt (pcAt (pcAt base 158) 375) 5 + ((0x3#20 ++ 0x000#12).signExtend 64 +
      (0x900#12).signExtend 64) = T)
    (hT2 : pcAt (pcAt (pcAt base 158) 618) 54 + ((0x2#20 ++ 0x000#12).signExtend 64 +
      (0x470#12).signExtend 64) = T)
    (hT3 : pcAt (pcAt (pcAt base 158) 932) 50 + ((0x2#20 ++ 0x000#12).signExtend 64 +
      (0xf98#12).signExtend 64) = T)
    (hT4 : pcAt (pcAt (pcAt base 158) 1275) 65 + ((0x2#20 ++ 0x000#12).signExtend 64 +
      (0xa00#12).signExtend 64) = T)
    (hT5 : pcAt (pcAt (pcAt base 158) 1457) 64 + ((0x1#20 ++ 0x000#12).signExtend 64 +
      (0x72c#12).signExtend 64) = T)
    (hT6 : pcAt (pcAt (pcAt base 158) 1661) 87 + ((0x1#20 ++ 0x000#12).signExtend 64 +
      (0x3a0#12).signExtend 64) = T)
    (hT7 : pcAt (pcAt (pcAt base 158) 1948) 107 + ((0x1#20 ++ 0x000#12).signExtend 64 +
      (0xed4#12).signExtend 64) = T)
    (hT8 : pcAt (pcAt (pcAt base 158) 2273) 84 + ((0x1#20 ++ 0x000#12).signExtend 64 +
      (0xa1c#12).signExtend 64) = T)
    (hT9 : pcAt (pcAt (pcAt base 158) 2585) 184 + ((0x0#20 ++ 0x000#12).signExtend 64 +
      (0x3ac#12).signExtend 64) = T)
    (x' : Regs) (m' : Mem) (hF : AMFrame x m x' m') (h8 : x'.get 8#5 = x.get 10#5)
    (h13 : x'.get 13#5 = x.get 13#5)
    (hn : (x'.get 16#5).toNat + 2 ^ 64 * ((x'.get 10#5).toNat + 2 ^ 64 * ((x'.get 15#5).toNat +
      2 ^ 64 * (x'.get 11#5).toNat)) + 2 ^ 256 * (x'.get 12#5).toNat =
      words m (x.get 11#5) 4 + words m (x.get 12#5) 4) :
    Reach (amBufs x D) PA base (pcAt base 37) x' m' (x.get 1#5) (addmod_256.post x m) := by
  -- `omega` and `subst_vars` do not see the addresses of the table.
  replace hT0 := PLift.up hT0
  replace hT1 := PLift.up hT1
  replace hT2 := PLift.up hT2
  replace hT3 := PLift.up hT3
  replace hT4 := PLift.up hT4
  replace hT5 := PLift.up hT5
  replace hT6 := PLift.up hT6
  replace hT7 := PLift.up hT7
  replace hT8 := PLift.up hT8
  replace hT9 := PLift.up hT9
  have hpre0 := hpre
  simp only [addmod_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hxa, hxn⟩, ⟨hya, hyn⟩, ⟨hma, hmn⟩, hdrx, hdry, hdrm, ⟨hsa, hsn⟩, hdsx,
    hdsy, hdsm, hdsr⟩ := hpre
  have hsp := hF.1
  rw [← regs_set_of_get' (by decide) h8, ← regs_set_of_get' (by decide) h13,
    ← regs_set_of_get' (by decide) hsp]
  rv_exec_cut 158
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.reduceSignExtend]
  rw [show pcAt base 45 + 452#64 = pcAt base 158 by simp only [pcAt]; bv_omega,
    update_aligned (pcAt_aligned hb3 158)]
  -- The sum in the frame.
  have hFM := AMFrame.mem hF hpre0 (m2 := memStore (memStore (memStore (memStore (memStore m'
    (x.get 2#5 + 18446744073709551536#64).toNat (x'.get 16#5))
    (x.get 2#5 + 18446744073709551544#64).toNat (x'.get 10#5))
    (x.get 2#5 + 18446744073709551552#64).toNat (x'.get 15#5))
    (x.get 2#5 + 18446744073709551560#64).toNat (x'.get 11#5))
    (x.get 2#5 + 18446744073709551568#64).toNat (x'.get 12#5)) (by
      simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
      exact unchangedExcept2_refl _ _ _ _ _)
  have hn5 : words (memStore (memStore (memStore (memStore (memStore m'
      (x.get 2#5 + 18446744073709551536#64).toNat (x'.get 16#5))
      (x.get 2#5 + 18446744073709551544#64).toNat (x'.get 10#5))
      (x.get 2#5 + 18446744073709551552#64).toNat (x'.get 15#5))
      (x.get 2#5 + 18446744073709551560#64).toNat (x'.get 11#5))
      (x.get 2#5 + 18446744073709551568#64).toNat (x'.get 12#5))
      (x.get 2#5 + 18446744073709551536#64) 5 =
      words m (x.get 11#5) 4 + words m (x.get 12#5) 4 := by
    rw [← hn]
    simp (disch := first | bv_omega | fail) only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd, memWord_memStore_self, memWord_memStore_of_ne, Nat.mul_zero, Nat.add_zero]
    ring
  have hMw := hFM.words_arg hpre0 13#5 (by decide)
  refine Reach.call_sub (r := 47) pa_udivrem_in pa_length
    (udivrem_320_256.reach 0x3#20 0xc04#12 0x3#20 0x900#12 0x2#20 0x470#12 0x2#20 0xf98#12
      0x2#20 0xa00#12 0x1#20 0x72c#12 0x1#20 0x3a0#12 0x1#20 0xed4#12 0x1#20 0xa1c#12 0x0#20
      0x3ac#12 (pcAt base 158) T _ _ hT0.down hT1.down hT2.down hT3.down hT4.down hT5.down
      hT6.down hT7.down hT8.down hT9.down (pcAt_aligned hb3 158)
      hw ?_ ?_ ?_ ?_ ?_) ?_ ?_ ?_
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    exact pcAt_aligned hb3 47
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    bv_omega
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    bv_omega
  · exact hFM.holdsData hw hTr hTs hhold
  · simp only [udivrem_320_256.pre, Buf, Disjoint]
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
    try simp (disch := decide) only [Regs.eq_get x']
    repeat' apply And.intro
    all_goals bv_omega
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · intro a ha
    simp only [udivrem_320_256.bufs] at ha
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at ha
    try simp (disch := decide) only [Regs.eq_get x'] at ha
    simp only [List.mem_append] at ha ⊢
    rcases ha with ((((h | h) | h) | h) | h)
    · rw [show x.get 2#5 + 18446744073709551536#64 = x.get 2#5 - 496#64 + BitVec.ofNat 64 (8 * 52)
        by bv_omega] at h
      exact Or.inl (Or.inr (mem_bufWords_of_offset (by decide) h))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    · rw [show x.get 2#5 + 18446744073709551464#64 = x.get 2#5 - 496#64 + BitVec.ofNat 64 (8 * 43)
        by bv_omega] at h
      exact Or.inl (Or.inr (mem_bufWords_of_offset (by decide) h))
    · rw [show x.get 2#5 + 18446744073709551456#64 - 336#64 = x.get 2#5 - 496#64 +
        BitVec.ofNat 64 (8 * 0) by bv_omega] at h
      exact Or.inl (Or.inr (mem_bufWords_of_offset (by decide) h))
    · exact Or.inr (hD _ h)
  · intro x3 m3 hpost
    obtain ⟨hq, hrem, hunc, hsaved⟩ := hpost
    simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] at hq hrem hunc
    try simp (disch := decide) only [Regs.eq_get x'] at hq hrem hunc
    rw [hn5, hMw] at hrem
    have e344 : (x.get 2#5 + 18446744073709551464#64).toNat = (x.get 2#5 - 496#64).toNat + 344 := by
      bv_omega
    rw [show x.get 2#5 + 18446744073709551456#64 - 336#64 = x.get 2#5 - 496#64 by bv_omega] at hunc
    have hF3 : AMFrame x m x3 m3 := by
      refine (AMFrame.mem hFM hpre0 (fun k hk1 hk2 => hunc k (by omega) (by omega))).callee ?_
      intro i hi
      rw [hsaved i hi]
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]
      · rw [Regs.eq_get x' (by decide)]; exact hsp.symm
      · rw [Regs.eq_get x' (by decide)]; exact h8.symm
    have h23 : x3.get 2#5 = x.get 2#5 + 18446744073709551456#64 := hF3.1
    have h83 : x3.get 8#5 = x.get 10#5 := by
      rw [get_of_calleeSaved hsaved (by decide)]
      simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    rw [← regs_set_of_get' (by decide) h23, ← regs_set_of_get' (by decide) h83]
    rv_exec_cut 55
    rename_i r0 hr0 r1 hr1 r2 hr2 r3 hr3
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.reduceSignExtend]
      at hr0 hr1 hr2 hr3 ⊢
    simp only [Defn] at hr0 hr1 hr2 hr3
    subst hr0 hr1 hr2 hr3
    refine am_epi base x m hr _ _ (AMFrame.regs (AMFrame.mem hF3 hpre0 ?_) ?_ ?_) ?_
    · simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
      exact unchangedExcept2_refl _ _ _ _ _
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      exact h23.symm
    · am_cs
    · rw [← hrem]
      simp (disch := first | bv_omega | fail) only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
        BitVec.reduceAdd, BitVec.add_zero, memWord_memStore_self, memWord_memStore_of_ne,
        Nat.mul_zero, Nat.add_zero]

/-- The path of `addmod()` that divides the 320-bit sum from 13: the sum of 5 words in the frame and
the call of `udivrem<320, 256>()` with the result in the frame. -/
theorem am_slow {D : List (BitVec 64)} (base T : BitVec 64) (x : Regs) (m : Mem)
    (hb3 : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0) (hpre : addmod_256.pre x m)
    (hw : T.toNat + 8 * 256 ≤ 2 ^ 64)
    (hTr : (x.get 10#5).toNat + 32 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hTs : (x.get 2#5 - 496#64).toNat + 496 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 496#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) (hD : ∀ a ∈ bufWords T 256, a ∈ D)
    (hT0 : pcAt (pcAt (pcAt base 158) 182) 5 + ((0x3#20 ++ 0x000#12).signExtend 64 +
      (0xc04#12).signExtend 64) = T)
    (hT1 : pcAt (pcAt (pcAt base 158) 375) 5 + ((0x3#20 ++ 0x000#12).signExtend 64 +
      (0x900#12).signExtend 64) = T)
    (hT2 : pcAt (pcAt (pcAt base 158) 618) 54 + ((0x2#20 ++ 0x000#12).signExtend 64 +
      (0x470#12).signExtend 64) = T)
    (hT3 : pcAt (pcAt (pcAt base 158) 932) 50 + ((0x2#20 ++ 0x000#12).signExtend 64 +
      (0xf98#12).signExtend 64) = T)
    (hT4 : pcAt (pcAt (pcAt base 158) 1275) 65 + ((0x2#20 ++ 0x000#12).signExtend 64 +
      (0xa00#12).signExtend 64) = T)
    (hT5 : pcAt (pcAt (pcAt base 158) 1457) 64 + ((0x1#20 ++ 0x000#12).signExtend 64 +
      (0x72c#12).signExtend 64) = T)
    (hT6 : pcAt (pcAt (pcAt base 158) 1661) 87 + ((0x1#20 ++ 0x000#12).signExtend 64 +
      (0x3a0#12).signExtend 64) = T)
    (hT7 : pcAt (pcAt (pcAt base 158) 1948) 107 + ((0x1#20 ++ 0x000#12).signExtend 64 +
      (0xed4#12).signExtend 64) = T)
    (hT8 : pcAt (pcAt (pcAt base 158) 2273) 84 + ((0x1#20 ++ 0x000#12).signExtend 64 +
      (0xa1c#12).signExtend 64) = T)
    (hT9 : pcAt (pcAt (pcAt base 158) 2585) 184 + ((0x0#20 ++ 0x000#12).signExtend 64 +
      (0x3ac#12).signExtend 64) = T)
    (x' : Regs) (m' : Mem) (hF : AMFrame x m x' m') (h8 : x'.get 8#5 = x.get 10#5)
    (h11 : x'.get 11#5 = x.get 11#5) (h12 : x'.get 12#5 = x.get 12#5)
    (h13 : x'.get 13#5 = x.get 13#5) (h14 : x'.get 14#5 = memWord m (x.get 11#5 + 24#64).toNat) :
    Reach (amBufs x D) PA base (pcAt base 13) x' m' (x.get 1#5) (addmod_256.post x m) := by
  replace hT0 := PLift.up hT0
  replace hT1 := PLift.up hT1
  replace hT2 := PLift.up hT2
  replace hT3 := PLift.up hT3
  replace hT4 := PLift.up hT4
  replace hT5 := PLift.up hT5
  replace hT6 := PLift.up hT6
  replace hT7 := PLift.up hT7
  replace hT8 := PLift.up hT8
  replace hT9 := PLift.up hT9
  have hpre0 := hpre
  simp only [addmod_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hxa, hxn⟩, ⟨hya, hyn⟩, ⟨hma, hmn⟩, hdrx, hdry, hdrm, ⟨hsa, hsn⟩, hdsx,
    hdsy, hdsm, hdsr⟩ := hpre
  have hsp := hF.1
  rw [← regs_set_of_get' (by decide) h8, ← regs_set_of_get' (by decide) h11,
    ← regs_set_of_get' (by decide) h12, ← regs_set_of_get' (by decide) h13,
    ← regs_set_of_get' (by decide) h14, ← regs_set_of_get' (by decide) hsp]
  rv_exec_cut 37
  rename_i x0 hx0 x1 hx1 x2 hx2 y0 hy0 y1 hy1 y2 hy2 y3 hy3 s0 hs0 a1 ha1 c0 hc0 e1 he1 s1 hs1
    f1 hf1 c1 hc1 a2 ha2 a3 ha3 e2 he2 e3 he3 s2 hs2 f2 hf2 c2 hc2 s3 hs3 f3 hf3 c3 hc3
  have hsum := add4_words hc3 hf3 hs3 he3 ha3 hc2 hf2 hs2 he2 ha2 hc1 hf1 hs1 he1 hc0 ha1 hs0
  have hX := hF.words_arg hpre0 11#5 (by decide)
  have hY := hF.words_arg hpre0 12#5 (by decide)
  have hXw := words4_unfold m' (x.get 11#5)
  have hYw := words4_unfold m' (x.get 12#5)
  have hx3 := hF.memWord_arg hpre0 11#5 (by decide) 24#64 (by decide)
  rw [hx0.eq, hx1.eq, hx2.eq, ← hx3] at hsum
  rw [hy0.eq, hy1.eq, hy2.eq, hy3.eq] at hsum
  rw [← hXw, ← hYw, hX, hY] at hsum
  refine am_call base T x m hb3 hr hpre0 hw hTr hTs hhold hD hT0.down hT1.down hT2.down hT3.down
    hT4.down hT5.down hT6.down hT7.down hT8.down hT9.down _ m' (AMFrame.regs hF ?_ ?_) ?_ ?_ ?_
  all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  all_goals first | exact hsp.symm | am_cs | exact hsum.1

end IntxRV.Api
