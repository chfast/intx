import IntxRV.Div256
import IntxRV.Memset
import IntxRV.Knuth3
import IntxRV.Bits
/-!
# The paths of `udivrem<512, 256>()`

The frame of 160 bytes with ra and s0 to s5 (`U512Frame`), the epilogue (`u512_epi`), the call of
`memset()` that zeroes the result (`u512_memset`), and the paths for u < v (`u512_ult`) and v = 0
(`u512_vzero`). See `IntxRV/Api/udivrem_512_256.lean`.
-/

namespace IntxRV

/-- u < v from the count `mm + [b ≤ a] ≤ n` of the words of u to divide, for the top word `a` of
the `mm` words of u and the top word `b` of the `n` words of v. -/
theorem ult_of_count {U V a b mm n : Nat} (hmm : 1 ≤ mm) (ha : a < 2 ^ 64)
    (hU : U < (a + 1) * 2 ^ (64 * (mm - 1))) (hV : b * 2 ^ (64 * (n - 1)) ≤ V)
    (hb : n = 1 ∨ 0 < b) (h : mm + (if b ≤ a then 1 else 0) ≤ n) : U < V := by
  split_ifs at h with hba
  · have hb0 : 0 < b := by rcases hb with hb | hb <;> omega
    calc U < (a + 1) * 2 ^ (64 * (mm - 1)) := hU
      _ ≤ 2 ^ 64 * 2 ^ (64 * (mm - 1)) := Nat.mul_le_mul_right _ ha
      _ = 2 ^ (64 * mm) := by rw [← pow_add]; congr 1; omega
      _ ≤ 2 ^ (64 * (n - 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ b * 2 ^ (64 * (n - 1)) := Nat.le_mul_of_pos_left _ hb0
      _ ≤ V := hV
  · calc U < (a + 1) * 2 ^ (64 * (mm - 1)) := hU
      _ ≤ b * 2 ^ (64 * (mm - 1)) := Nat.mul_le_mul_right _ (by omega)
      _ ≤ b * 2 ^ (64 * (n - 1)) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
      _ ≤ V := hV

/-- The normalized numerator `U * 2^s` of the Knuth division fits in the `ulen` words to divide,
and its top `n` of them are less than the normalized divisor. -/
theorem knuth_ulen {U V a b mm n s ulen : Nat} (hmm : 1 ≤ mm) (hn : 1 ≤ n) (ha : a < 2 ^ 64)
    (hU : U < (a + 1) * 2 ^ (64 * (mm - 1))) (hVb : b * 2 ^ (64 * (n - 1)) ≤ V)
    (hVs : V * 2 ^ s < 2 ^ (64 * n)) (hs : s < 64) (hb0 : 0 < b)
    (hl : ulen = mm + if b ≤ a then 1 else 0) (hlen : n < ulen) :
    U * 2 ^ s < 2 ^ (64 * ulen) ∧ U * 2 ^ s / 2 ^ (64 * (ulen - n)) < V * 2 ^ s := by
  have hbs : b * 2 ^ s < 2 ^ 64 := by
    have e : 2 ^ (64 * n) = 2 ^ 64 * 2 ^ (64 * (n - 1)) := by rw [← pow_add]; congr 1; omega
    have : b * 2 ^ s * 2 ^ (64 * (n - 1)) < 2 ^ 64 * 2 ^ (64 * (n - 1)) := by
      calc b * 2 ^ s * 2 ^ (64 * (n - 1)) = b * 2 ^ (64 * (n - 1)) * 2 ^ s := by ring
        _ ≤ V * 2 ^ s := Nat.mul_le_mul_right _ hVb
        _ < _ := by rw [← e]; exact hVs
    exact Nat.lt_of_mul_lt_mul_right this
  have hUV : U < V * 2 ^ (64 * (ulen - n)) := by
    split_ifs at hl with hba
    · calc U < (a + 1) * 2 ^ (64 * (mm - 1)) := hU
        _ ≤ 2 ^ 64 * 2 ^ (64 * (mm - 1)) := Nat.mul_le_mul_right _ ha
        _ = 2 ^ (64 * (n - 1)) * 2 ^ (64 * (ulen - n)) := by
          rw [← pow_add, ← pow_add]; congr 1; omega
        _ ≤ b * 2 ^ (64 * (n - 1)) * 2 ^ (64 * (ulen - n)) :=
          Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ hb0)
        _ ≤ V * 2 ^ (64 * (ulen - n)) := Nat.mul_le_mul_right _ hVb
    · calc U < (a + 1) * 2 ^ (64 * (mm - 1)) := hU
        _ ≤ b * 2 ^ (64 * (mm - 1)) := Nat.mul_le_mul_right _ (by omega)
        _ = b * 2 ^ (64 * (n - 1)) * 2 ^ (64 * (ulen - n)) := by
          rw [Nat.mul_assoc, ← pow_add]; congr 2; omega
        _ ≤ V * 2 ^ (64 * (ulen - n)) := Nat.mul_le_mul_right _ hVb
  constructor
  · split_ifs at hl with hba
    · calc U * 2 ^ s < (a + 1) * 2 ^ (64 * (mm - 1)) * 2 ^ 64 :=
            Nat.mul_lt_mul_of_lt_of_le hU (Nat.pow_le_pow_right (by norm_num) hs.le) (by positivity)
        _ ≤ 2 ^ 64 * 2 ^ (64 * (mm - 1)) * 2 ^ 64 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ha)
        _ = 2 ^ (64 * ulen) := by rw [← pow_add, ← pow_add]; congr 1; omega
    · calc U * 2 ^ s < (a + 1) * 2 ^ (64 * (mm - 1)) * 2 ^ s :=
            Nat.mul_lt_mul_of_pos_right hU (by positivity)
        _ ≤ b * 2 ^ (64 * (mm - 1)) * 2 ^ s :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
        _ = b * 2 ^ s * 2 ^ (64 * (mm - 1)) := by ring
        _ < 2 ^ 64 * 2 ^ (64 * (mm - 1)) := Nat.mul_lt_mul_of_pos_right hbs (by positivity)
        _ = 2 ^ (64 * ulen) := by rw [← pow_add]; congr 1; omega
  · rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc U * 2 ^ s < V * 2 ^ (64 * (ulen - n)) * 2 ^ s :=
          Nat.mul_lt_mul_of_pos_right hUV (by positivity)
      _ = V * 2 ^ s * 2 ^ (64 * (ulen - n)) := by ring

/-- The words of the divisor of 3 words shifted left by `s`, with the top bits of each word in the
next one, and no bits out of the top word. -/
theorem norm3_val (v0 v1 v2 s : Nat) (hs : s < 64) (h2 : v2 * 2 ^ s < 2 ^ 64) :
    v0 * 2 ^ s % 2 ^ 64 + 2 ^ 64 * ((v1 * 2 ^ s % 2 ^ 64 + v0 / 2 ^ (64 - s)) +
      2 ^ 64 * (v2 * 2 ^ s % 2 ^ 64 + v1 / 2 ^ (64 - s))) =
    (v0 + 2 ^ 64 * (v1 + 2 ^ 64 * v2)) * 2 ^ s := by
  have e0 := mul_two_pow_split v0 s hs
  have e1 := mul_two_pow_split v1 s hs
  rw [Nat.mod_eq_of_lt h2]
  have : (v0 + 2 ^ 64 * (v1 + 2 ^ 64 * v2)) * 2 ^ s =
      v0 * 2 ^ s + 2 ^ 64 * (v1 * 2 ^ s) + 2 ^ 128 * (v2 * 2 ^ s) := by ring
  rw [this]
  generalize v0 * 2 ^ s = P0 at e0 ⊢
  generalize v1 * 2 ^ s = P1 at e1 ⊢
  omega

/-- A word of a funnel shift left by `S` as the code computes it: the bits from the word below
shifted right by 1 and then by the complement of `S`. -/
theorem funnel_shl_val (a b S : BitVec 64) (hS : S.toNat < 64) :
    ((a <<< (S.toNat % 64)) ||| ((b >>> 1) >>> ((S ^^^ 18446744073709551615#64).toNat % 64))).toNat =
      a.toNat * 2 ^ S.toNat % 2 ^ 64 + b.toNat / 2 ^ (64 - S.toNat) := by
  rw [toNat_xor_allOnes_mod_64, Nat.mod_eq_of_lt hS, ushiftRight_one_ushiftRight b _ hS,
    toNat_shl_or_shr a b _ hS]

/-- A word of a funnel shift right by `S` as the code computes it: the bits from the word above
shifted left by 1 and then by the complement of `S`. -/
theorem funnel_shr_val (a b S : BitVec 64) (hS : S.toNat < 64) :
    (((b <<< 1) <<< ((S ^^^ 18446744073709551615#64).toNat % 64)) ||| (a >>> (S.toNat % 64))).toNat =
      b.toNat * 2 ^ (64 - S.toNat) % 2 ^ 64 + a.toNat / 2 ^ S.toNat := by
  rw [toNat_xor_allOnes_mod_64, Nat.mod_eq_of_lt hS, shiftLeft_one_shiftLeft b _ hS,
    toNat_shl_or_shr' a b _ hS]

/-- The words of the divisor of 4 words shifted left by `s`, with the top bits of each word in the
next one, and no bits out of the top word. -/
theorem norm4_val (v0 v1 v2 v3 s : Nat) (hs : s < 64) (h3 : v3 * 2 ^ s < 2 ^ 64) :
    v0 * 2 ^ s % 2 ^ 64 + 2 ^ 64 * ((v1 * 2 ^ s % 2 ^ 64 + v0 / 2 ^ (64 - s)) +
      2 ^ 64 * ((v2 * 2 ^ s % 2 ^ 64 + v1 / 2 ^ (64 - s)) +
        2 ^ 64 * (v3 * 2 ^ s % 2 ^ 64 + v2 / 2 ^ (64 - s)))) =
    (v0 + 2 ^ 64 * (v1 + 2 ^ 64 * (v2 + 2 ^ 64 * v3))) * 2 ^ s := by
  have e0 := mul_two_pow_split v0 s hs
  have e1 := mul_two_pow_split v1 s hs
  have e2 := mul_two_pow_split v2 s hs
  rw [Nat.mod_eq_of_lt h3]
  have : (v0 + 2 ^ 64 * (v1 + 2 ^ 64 * (v2 + 2 ^ 64 * v3))) * 2 ^ s =
      v0 * 2 ^ s + 2 ^ 64 * (v1 * 2 ^ s) + 2 ^ 128 * (v2 * 2 ^ s) + 2 ^ 192 * (v3 * 2 ^ s) := by
    ring
  rw [this]
  generalize v0 * 2 ^ s = P0 at e0 ⊢
  generalize v1 * 2 ^ s = P1 at e1 ⊢
  generalize v2 * 2 ^ s = P2 at e2 ⊢
  omega

end IntxRV

namespace IntxRV.Api
open IntxRV IntxRV.Gen

section
open Lean Meta Elab Tactic

/-- Substitutes the names `w` of the run with their values `v` (`Defn w v`), from the last one.
`subst_vars` also tries every other equation of the context, which is slow in a large one. -/
elab "rv_subst" : tactic => withMainContext do
  let defs := (← getLCtx).foldl (init := #[]) fun acc d =>
    if !d.isImplementationDetail && d.type.isAppOfArity ``Defn 2 then acc.push d.fvarId else acc
  for fv in defs.reverse do
    let g ← getMainGoal
    let g' ← g.withContext do
      let d ← fv.getDecl
      let args := d.type.getAppArgs
      let g1 ← g.replaceLocalDeclDefEq fv (← mkEq args[0]! args[1]!)
      Lean.Meta.subst g1 fv
    replaceMainGoal [g']

end

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

variable {hi0 hi1 hi2 hi3 : BitVec 20} {lo0 lo1 lo2 lo3 : BitVec 12}

-- The instructions of `udivrem<512, 256>()` and its callees with the immediates of the address of
-- the table in each callee.
set_option hygiene false in
local notation "P512" => udivrem_512_256_progAt hi0 lo0 hi1 lo1 hi2 lo2 hi3 lo3

/-- The addresses of the words of `udivrem<512, 256>()`: u, v, the result, the frame of 240 bytes
with the frames of the callees and `D`. -/
abbrev u512Bufs (x : Regs) (D : List (BitVec 64)) : List (BitVec 64) :=
  bufWords (x.get 11#5) 8 ++ bufWords (x.get 12#5) 4 ++ bufWords (x.get 10#5) 12 ++
    bufWords (x.get 2#5 - 240#64) 30 ++ D

/-- The frame of `udivrem<512, 256>()` after its prologue: sp 160 bytes lower, ra and s0 to s5
saved, and the memory outside the result and the frame of 240 bytes unchanged. -/
def U512Frame (x : Regs) (m : Mem) (x' : Regs) (m' : Mem) : Prop :=
  x'.get 2#5 = x.get 2#5 + 18446744073709551456#64 ∧
  memWord m' (x.get 2#5 + 18446744073709551608#64).toNat = x.get 1#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551600#64).toNat = x.get 8#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551592#64).toNat = x.get 9#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551584#64).toNat = x.get 18#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551576#64).toNat = x.get 19#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551568#64).toNat = x.get 20#5 ∧
  memWord m' (x.get 2#5 + 18446744073709551560#64).toNat = x.get 21#5 ∧
  UnchangedExcept2 m m' (x.get 10#5) 96 (x.get 2#5 - 240#64) 240 ∧
  ∀ r ∈ calleeSaved, r ∉ [2#5, 8#5, 9#5, 18#5, 19#5, 20#5, 21#5] → x'.get r = x.get r

/-- A callee-saved register after a call. -/
theorem get_of_calleeSaved {x2 x1 : Regs} (hcs : ∀ i ∈ calleeSaved, x2 i = x1 i) {i : BitVec 5}
    (hi : i ∈ calleeSaved) : x2.get i = x1.get i := by
  have h0 : ∀ i ∈ calleeSaved, i ≠ 0 := by decide
  rw [← Regs.eq_get x2 (h0 i hi), hcs i hi, Regs.eq_get x1 (h0 i hi)]


set_option hygiene false in
/-- The callee-saved registers that the frame keeps, through the sets of the other registers. -/
macro "u512_cs" : tactic => `(tactic| (
  intro r hr' hn
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte,
      List.mem_cons, List.not_mem_nil, or_false, not_true_eq_false, not_false_eq_true] at hn ⊢))

set_option hygiene false in
/-- `u512_cs` after a call with the callee-saved registers `h`. -/
macro "u512_cs'" h:ident : tactic => `(tactic| (
  intro r hr' hn
  rw [get_of_calleeSaved $h hr']
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte,
      List.mem_cons, List.not_mem_nil, or_false, not_true_eq_false, not_false_eq_true] at hn ⊢))

/-- The end of `udivrem<512, 256>()` at 327: the restore of ra and s0 to s5 and the return, with
the result stored. -/
theorem u512_epi {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hr : x.get 1#5 &&& 3 = 0) (x4 : Regs) (m4 : Mem) (hF : U512Frame x m x4 m4)
    (hq : words m4 (x.get 10#5) 8 = words m (x.get 11#5) 8 / words m (x.get 12#5) 4)
    (hrem : words m4 (x.get 10#5 + 64#64) 4 = if words m (x.get 12#5) 4 = 0 then 0
      else words m (x.get 11#5) 8 % words m (x.get 12#5) 4) :
    Reach (u512Bufs x D) P512 base (pcAt base 327) x4 m4 (x.get 1#5)
      (udivrem_512_256.post x m) := by
  obtain ⟨hsp, hfra, hfs0, hfs1, hfs2, hfs3, hfs4, hfs5, hunF, hcsF⟩ := hF
  rw [← regs_set_of_get' (by decide) hsp]
  rv_exec
  rename_i wra hwra ws0 hws0 ws1 hws1 ws2 hws2 ws3 hws3 ws4 hws4 ws5 hws5
  rw [hfra] at hwra
  rw [hfs0] at hws0
  rw [hfs1] at hws1
  rw [hfs2] at hws2
  rw [hfs3] at hws3
  rw [hfs4] at hws4
  rw [hfs5] at hws5
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.reduceSignExtend,
    BitVec.add_zero]
  rw [hwra.eq, update_aligned hr]
  refine Reach.refl ?_
  simp only [udivrem_512_256.post]
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
         | exact hws0 | exact hws1 | exact hws2 | exact hws3 | exact hws4 | exact hws5)

/-- The frame after a change of the memory only in the result and below the saved registers. -/
theorem U512Frame.mem {x : Regs} {m : Mem} {x' : Regs} {m1 m2 : Mem} (hF : U512Frame x m x' m1)
    (hpre : udivrem_512_256.pre x m)
    (h : UnchangedExcept2 m1 m2 (x.get 10#5) 96 (x.get 2#5 - 240#64) 184) :
    U512Frame x m x' m2 := by
  simp only [udivrem_512_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, -, -, -, -, ⟨hsa, hsn⟩, -, -, hdsr⟩ := hpre
  obtain ⟨hsp, hfra, hfs0, hfs1, hfs2, hfs3, hfs4, hfs5, hunF, hcsF⟩ := hF
  have hw : ∀ c : BitVec 64, (x.get 2#5 - 240#64).toNat + 184 ≤ (x.get 2#5 + c).toNat →
      (x.get 2#5 + c).toNat + 8 ≤ (x.get 2#5 - 240#64).toNat + 240 →
      memWord m2 (x.get 2#5 + c).toNat = memWord m1 (x.get 2#5 + c).toNat := fun c h1 h2 =>
    memWord_of_unchangedExcept2 h _ (by omega) (by omega)
  refine ⟨hsp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hcsF⟩
  · rw [hw 18446744073709551608#64 (by bv_omega) (by bv_omega)]; exact hfra
  · rw [hw 18446744073709551600#64 (by bv_omega) (by bv_omega)]; exact hfs0
  · rw [hw 18446744073709551592#64 (by bv_omega) (by bv_omega)]; exact hfs1
  · rw [hw 18446744073709551584#64 (by bv_omega) (by bv_omega)]; exact hfs2
  · rw [hw 18446744073709551576#64 (by bv_omega) (by bv_omega)]; exact hfs3
  · rw [hw 18446744073709551568#64 (by bv_omega) (by bv_omega)]; exact hfs4
  · rw [hw 18446744073709551560#64 (by bv_omega) (by bv_omega)]; exact hfs5
  intro k hka hkb
  rw [h k hka (by omega)]; exact hunF k hka hkb

/-- The frame after a change of the registers that keeps sp and the callee-saved registers that
the frame keeps. -/
theorem U512Frame.regs {x : Regs} {m : Mem} {x' x'' : Regs} {m' : Mem} (hF : U512Frame x m x' m')
    (h2 : x''.get 2#5 = x'.get 2#5)
    (hcs : ∀ r ∈ calleeSaved, r ∉ [2#5, 8#5, 9#5, 18#5, 19#5, 20#5, 21#5] → x''.get r = x'.get r) :
    U512Frame x m x'' m' := by
  obtain ⟨hsp, hfra, hfs0, hfs1, hfs2, hfs3, hfs4, hfs5, hunF, hcsF⟩ := hF
  exact ⟨h2.trans hsp, hfra, hfs0, hfs1, hfs2, hfs3, hfs4, hfs5, hunF,
    fun r hr hn => (hcs r hr hn).trans (hcsF r hr hn)⟩

/-- A word of u in the memory of the frame. -/
theorem U512Frame.memWord_u {x : Regs} {m : Mem} {x' : Regs} {m' : Mem} (hF : U512Frame x m x' m')
    (hpre : udivrem_512_256.pre x m) (c : BitVec 64) (hc : c.toNat + 8 ≤ 64) :
    memWord m' (x.get 11#5 + c).toNat = memWord m (x.get 11#5 + c).toNat := by
  simp only [udivrem_512_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, -, hdru, -, ⟨hsa, hsn⟩, hdsu, -, -⟩ := hpre
  exact memWord_of_unchangedExcept2 hF.2.2.2.2.2.2.2.2.1 _ (by bv_omega) (by bv_omega)

/-- A word of v in the memory of the frame. -/
theorem U512Frame.memWord_v {x : Regs} {m : Mem} {x' : Regs} {m' : Mem} (hF : U512Frame x m x' m')
    (hpre : udivrem_512_256.pre x m) (c : BitVec 64) (hc : c.toNat + 8 ≤ 32) :
    memWord m' (x.get 12#5 + c).toNat = memWord m (x.get 12#5 + c).toNat := by
  simp only [udivrem_512_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, -, ⟨hva, hvn⟩, -, hdrv, ⟨hsa, hsn⟩, -, hdsv, -⟩ := hpre
  exact memWord_of_unchangedExcept2 hF.2.2.2.2.2.2.2.2.1 _ (by bv_omega) (by bv_omega)

/-- An instruction address in aligned code. -/
theorem pcAt_aligned {base : BitVec 64} (hb3 : base &&& 3 = 0) (r : Nat) : pcAt base r &&& 3 = 0 := by
  simp only [pcAt]
  refine aligned_add hb3 ?_
  rw [aligned_iff, BitVec.toNat_ofNat]
  omega

/-- The call of `memset()` that zeroes the 96 bytes of the result, with the return at `r`. -/
theorem u512_memset {D : List (BitVec 64)} {Q : Regs → Mem → Prop} (base : BitVec 64) (x : Regs)
    (m : Mem) (hb3 : base &&& 3 = 0) (hpre : udivrem_512_256.pre x m) (x' : Regs) (m' : Mem)
    (h10 : x'.get 10#5 = x.get 10#5) (h11 : x'.get 11#5 = 0#64) (h12 : x'.get 12#5 = 96#64)
    (r : Nat) (h1 : x'.get 1#5 = pcAt base r)
    (hcont : ∀ x'' m'', m'' = memFill m' (x.get 10#5).toNat 0#8 96 → x''.get 10#5 = x.get 10#5 →
      (∀ i ∈ calleeSaved, x'' i = x' i) →
      Reach (u512Bufs x D) P512 base (pcAt base r) x'' m'' (x.get 1#5) Q) :
    Reach (u512Bufs x D) P512 base (pcAt base 1308) x' m' (x.get 1#5) Q := by
  simp only [udivrem_512_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, -⟩ := hpre
  refine Reach.call_sub (r := r) udivrem_512_256_progAt_memset_in
    (by rw [udivrem_512_256_progAt_length]; decide)
    (memset.reach (A := bufWords (x.get 10#5) 12) (pcAt base 1308) x' m' ?_ ?_ ?_) h1 ?_ ?_
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

/-- The low `k` words of a number less than `2^(64 k)`. -/
theorem lo_of_lt {W lo hi k : Nat} (h : W = lo + 2 ^ (64 * k) * hi) (hW : W < 2 ^ (64 * k)) :
    lo = W := by
  have : hi = 0 := by
    rcases Nat.eq_zero_or_pos hi with h0 | h0
    · exact h0
    · have : 2 ^ (64 * k) ≤ 2 ^ (64 * k) * hi := Nat.le_mul_of_pos_right _ h0
      omega
  subst this; omega

/-- The path of `udivrem<512, 256>()` for u < v from 84: the quotient 0 and the remainder u. -/
theorem u512_ult {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hr : x.get 1#5 &&& 3 = 0) (hpre : udivrem_512_256.pre x m) (x' : Regs) (m' : Mem)
    (hF : U512Frame x m x' m') (h10 : x'.get 10#5 = x.get 10#5) (h8 : x'.get 8#5 = x.get 11#5)
    (hlt : words m (x.get 11#5) 8 < words m (x.get 12#5) 4) :
    Reach (u512Bufs x D) P512 base (pcAt base 84) x' m' (x.get 1#5)
      (udivrem_512_256.post x m) := by
  have hpre0 := hpre
  simp only [udivrem_512_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr⟩ := hpre
  have hz : x'.get 0#5 = 0#64 := by rw [show (0#5 : BitVec 5) = 0 from rfl, Regs.get_zero]; rfl
  rw [← regs_set_of_get' (by decide) h10, ← regs_set_of_get' (by decide) h8]
  rv_exec_cut 327
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
  refine u512_epi base x m hr _ _ (U512Frame.regs (U512Frame.mem hF hpre0 ?_) ?_ ?_) ?_ ?_
  · simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
    exact unchangedExcept2_refl _ _ _ _ _
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · u512_cs
  · rw [Nat.div_eq_of_lt hlt]
    simp (disch := first | bv_omega | fail) only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd, memWord_memStore_self, memWord_memStore_of_ne, BitVec.toNat_zero,
      Nat.mul_zero, Nat.add_zero]
  · have hV : words m (x.get 12#5) 4 ≠ 0 := by omega
    rw [if_neg hV, Nat.mod_eq_of_lt hlt]
    have hs := words_split m 4 4 (x.get 11#5)
    rw [show 4 + 4 = 8 from rfl] at hs
    rw [← lo_of_lt hs (lt_trans hlt (words_lt m 4 _))]
    simp (disch := first | bv_omega | fail) only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd, memWord_memStore_self, memWord_memStore_of_ne, Nat.mul_zero, Nat.add_zero]

/-- The frame after a call, which keeps the callee-saved registers. -/
theorem U512Frame.callee {x : Regs} {m : Mem} {x' x3 : Regs} {m' : Mem} (hF : U512Frame x m x' m')
    (hcs : ∀ i ∈ calleeSaved, x3 i = x' i) : U512Frame x m x3 m' := by
  have h0 : ∀ i ∈ calleeSaved, i ≠ 0 := by decide
  refine U512Frame.regs hF ?_ fun r hr _ => ?_
  · rw [← Regs.eq_get x3 (by decide), hcs _ (by decide), Regs.eq_get x' (by decide)]
  · rw [← Regs.eq_get x3 (h0 r hr), hcs r hr, Regs.eq_get x' (h0 r hr)]

/-- The frame after `memset()` of the result. -/
theorem U512Frame.memFill {x : Regs} {m : Mem} {x' : Regs} {m' : Mem} (hF : U512Frame x m x' m')
    (hpre : udivrem_512_256.pre x m) :
    U512Frame x m x' (IntxRV.memFill m' (x.get 10#5).toNat 0#8 96) :=
  U512Frame.mem hF hpre (unchangedExcept2_of _ _ (unchangedExcept_memFill m' (x.get 10#5) 0#8 96))

/-- A word of the result after `memset()`. -/
theorem u512_memFill_zero {x : Regs} {m : Mem} (m' : Mem) (hpre : udivrem_512_256.pre x m)
    (c : BitVec 64) (hc : c.toNat + 8 ≤ 96) :
    memWord (IntxRV.memFill m' (x.get 10#5).toNat 0#8 96) (x.get 10#5 + c).toNat = 0#64 := by
  simp only [udivrem_512_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, -⟩ := hpre
  exact memWord_memFill_zero _ _ _ _ (by bv_omega)

/-- The path of `udivrem<512, 256>()` for v = 0 from 336: `memset()` of the result. -/
theorem u512_vzero {D : List (BitVec 64)} (base : BitVec 64) (x : Regs) (m : Mem)
    (hb3 : base &&& 3 = 0) (hr : x.get 1#5 &&& 3 = 0) (hpre : udivrem_512_256.pre x m)
    (x' : Regs) (m' : Mem) (hF : U512Frame x m x' m') (h10 : x'.get 10#5 = x.get 10#5)
    (hv : words m (x.get 12#5) 4 = 0) :
    Reach (u512Bufs x D) P512 base (pcAt base 336) x' m' (x.get 1#5)
      (udivrem_512_256.post x m) := by
  rw [← regs_set_of_get' (by decide) h10]
  rv_exec_cut 1308
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  rw [show pcAt base 338 + 4096#64 + BitVec.signExtend 64 3880#12 = pcAt base 1308 by
      simp only [pcAt, BitVec.reduceSignExtend]; bv_omega,
    update_aligned (pcAt_aligned hb3 1308)]
  have hF1 : U512Frame x m ((((((x'.set (10#5) (x.get 10#5)).set 12#5 96#64).set 11#5 0#64).set
      (1#5) (pcAt base 338 + 4096#64)).set (1#5) (pcAt base 340))) m' :=
    U512Frame.regs hF (by simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte])
      (by u512_cs)
  refine u512_memset base x m hb3 hpre _ m' ?_ ?_ ?_ 340 ?_ ?_
  all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  intro x'' m'' hm hx10 hcs
  subst hm
  have hF2 := (hF1.memFill hpre).callee hcs
  rv_exec_cut 327
  have hz : ∀ c : BitVec 64, c.toNat + 8 ≤ 96 →
      memWord (IntxRV.memFill m' (x.get 10#5).toNat 0#8 96) (x.get 10#5 + c).toNat = 0#64 :=
    u512_memFill_zero m' hpre
  have hz0 := hz 0#64 (by decide)
  rw [BitVec.add_zero] at hz0
  refine u512_epi base x m hr _ _ (U512Frame.regs hF2 ?_ ?_) ?_ ?_
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  · u512_cs
  · rw [hv, Nat.div_zero]
    simp (disch := decide) only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
      hz, hz0, BitVec.toNat_zero, Nat.mul_zero, Nat.add_zero]
  · rw [if_pos hv]
    simp (disch := decide) only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
      hz, BitVec.toNat_zero, Nat.mul_zero, Nat.add_zero]

/-- The table of the reciprocal after a change of the memory outside it. -/
theorem holdsData_of_unchangedExcept2 {m m' : Mem} {a b : BitVec 64} {la lb : Nat}
    (h : UnchangedExcept2 m m' a la b lb) :
    ∀ (data : List (BitVec 64)) (T : BitVec 64), T.toNat + 8 * data.length ≤ 2 ^ 64 →
      (a.toNat + la ≤ T.toNat ∨ T.toNat + 8 * data.length ≤ a.toNat) →
      (b.toNat + lb ≤ T.toNat ∨ T.toNat + 8 * data.length ≤ b.toNat) →
      HoldsData m T data → HoldsData m' T data
  | [], _, _, _, _, _ => trivial
  | w :: ws, T, hT, ha, hb, ⟨hw, hws⟩ => by
    simp only [List.length_cons] at hT ha hb
    refine ⟨?_, ?_⟩
    · rw [memWord_of_unchangedExcept2 h T.toNat (by omega) (by omega)]; exact hw
    · cases ws with
      | nil => trivial
      | cons w' ws' =>
        simp only [List.length_cons] at hT ha hb ⊢
        have h8 : (T + 8).toNat = T.toNat + 8 := by rw [BitVec.toNat_add]; simp; omega
        exact holdsData_of_unchangedExcept2 h (w' :: ws') (T + 8)
          (by simp only [List.length_cons]; omega) (by simp only [List.length_cons]; omega)
          (by simp only [List.length_cons]; omega) hws

/-- The words of the result after `memset()`. -/
theorem u512_memFill_words {x : Regs} {m : Mem} (m' : Mem) (hpre : udivrem_512_256.pre x m) :
    ∀ (j k : Nat), 8 * (k + j) ≤ 96 →
      words (IntxRV.memFill m' (x.get 10#5).toNat 0#8 96) (x.get 10#5 + BitVec.ofNat 64 (8 * k)) j
        = 0
  | 0, _, _ => rfl
  | j + 1, k, h => by
    rw [words, u512_memFill_zero m' hpre _ (by rw [BitVec.toNat_ofNat]; omega),
      show x.get 10#5 + BitVec.ofNat 64 (8 * k) + 8 = x.get 10#5 + BitVec.ofNat 64 (8 * (k + 1)) by
        rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega,
      u512_memFill_words m' hpre j (k + 1) (by omega)]
    rfl

/-- The `U` words of u that hold its `mm` significant words. -/
theorem u512_words_u (m : Mem) (u : BitVec 64) (mm U : Nat) (hU : mm ≤ U) (hU8 : U ≤ 8)
    (hum : words m u 8 < 2 ^ (64 * mm)) : words m u U = words m u 8 := by
  have hs := words_split m U (8 - U) u
  rw [show U + (8 - U) = 8 by omega] at hs
  exact lo_of_lt hs (lt_of_lt_of_le hum (Nat.pow_le_pow_right (by norm_num) (by omega)))

/-- The words outside the bytes that may change. -/
theorem words_of_unchangedExcept2 {m m' : Mem} {a b : BitVec 64} {la lb : Nat}
    (h : UnchangedExcept2 m m' a la b lb) : ∀ (n : Nat) (c : BitVec 64), c.toNat + 8 * n ≤ 2 ^ 64 →
      (c.toNat + 8 * n ≤ a.toNat ∨ a.toNat + la ≤ c.toNat) →
      (c.toNat + 8 * n ≤ b.toNat ∨ b.toNat + lb ≤ c.toNat) → words m' c n = words m c n
  | 0, _, _, _, _ => rfl
  | n + 1, c, hc, ha, hb => by
    rw [words, words, memWord_of_unchangedExcept2 h c.toNat (by omega) (by omega)]
    cases n with
    | zero => rfl
    | succ k =>
      have h8 : (c + 8).toNat = c.toNat + 8 := by
        rw [BitVec.toNat_add]; simp; omega
      rw [words_of_unchangedExcept2 h (k + 1) (c + 8) (by omega) (by omega) (by omega)]

/-- The words of u in the memory of the frame. -/
theorem U512Frame.words_u {x : Regs} {m : Mem} {x' : Regs} {m' : Mem} (hF : U512Frame x m x' m')
    (hpre : udivrem_512_256.pre x m) (k : Nat) (hk : k ≤ 8) :
    words m' (x.get 11#5) k = words m (x.get 11#5) k := by
  simp only [udivrem_512_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, -, hdru, -, ⟨hsa, hsn⟩, hdsu, -, -⟩ := hpre
  exact words_of_unchangedExcept2 hF.2.2.2.2.2.2.2.2.1 k _ (by omega) (by omega) (by omega)

/-- The table of the reciprocal in the memory of the frame. -/
theorem U512Frame.holdsData {x : Regs} {m : Mem} {x' : Regs} {m' : Mem} {T : BitVec 64}
    (hF : U512Frame x m x' m') (hw : T.toNat + 8 * 256 ≤ 2 ^ 64)
    (hTr : (x.get 10#5).toNat + 96 ≤ T.toNat ∨ T.toNat + 8 * 256 ≤ (x.get 10#5).toNat)
    (hTs : (x.get 2#5 - 240#64).toNat + 240 ≤ T.toNat ∨
      T.toNat + 8 * 256 ≤ (x.get 2#5 - 240#64).toNat)
    (hhold : HoldsData m T reciprocal_2by1_image_data) :
    HoldsData m' T reciprocal_2by1_image_data :=
  holdsData_of_unchangedExcept2 hF.2.2.2.2.2.2.2.2.1 _ T hw hTr hTs hhold

/-- The words of the result from the word `k` after `memset()` and a callee that writes its first
`U ≤ k` words and the `lb` bytes at `b` outside the result. -/
theorem u512_res_zero {x : Regs} {m : Mem} (m' m4 : Mem) (hpre : udivrem_512_256.pre x m)
    (U : Nat) {b : BitVec 64} {lb : Nat}
    (hunc : UnchangedExcept2 (IntxRV.memFill m' (x.get 10#5).toNat 0#8 96) m4 (x.get 10#5)
      (8 * U) b lb)
    (hb : (x.get 10#5).toNat + 96 ≤ b.toNat ∨ b.toNat + lb ≤ (x.get 10#5).toNat)
    (k j : Nat) (hk : U ≤ k) (hkj : k + j ≤ 12) :
    words m4 (x.get 10#5 + BitVec.ofNat 64 (8 * k)) j = 0 := by
  have hpre' := hpre
  simp only [udivrem_512_256.pre, Buf, Disjoint] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hra, hrn⟩, -⟩ := hpre'
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rfl
  have ha : (x.get 10#5 + BitVec.ofNat 64 (8 * k)).toNat = (x.get 10#5).toNat + 8 * k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [words_of_unchangedExcept2 hunc j _ (by omega) (by omega) (by omega)]
  exact u512_memFill_words m' hpre j k (by omega)

/-- The 8 words of the quotient after `memset()` and a callee that writes its first `U` words and
the `lb` bytes at `b` outside the result. -/
theorem u512_quot_words {x : Regs} {m : Mem} (m' m4 : Mem) (hpre : udivrem_512_256.pre x m)
    (U : Nat) (hU8 : U ≤ 8) {b : BitVec 64} {lb : Nat}
    (hunc : UnchangedExcept2 (IntxRV.memFill m' (x.get 10#5).toNat 0#8 96) m4 (x.get 10#5)
      (8 * U) b lb)
    (hb : (x.get 10#5).toNat + 96 ≤ b.toNat ∨ b.toNat + lb ≤ (x.get 10#5).toNat) :
    words m4 (x.get 10#5) 8 = words m4 (x.get 10#5) U := by
  have hs := words_split m4 U (8 - U) (x.get 10#5)
  rw [show U + (8 - U) = 8 by omega,
    u512_res_zero m' m4 hpre U hunc hb U (8 - U) le_rfl (by omega), Nat.mul_zero,
    Nat.add_zero] at hs
  exact hs

/-- The bytes of a store of 0. -/
theorem getElem?_memStore_zero (m : Mem) (c k : Nat) (h : c ≤ k ∧ k < c + 8) :
    (memStore m c 0#64)[k]? = some 0#8 := by
  obtain ⟨i, hi, rfl⟩ : ∃ i, i < 8 ∧ k = c + i := ⟨k - c, by omega, by omega⟩
  simp only [memStore, Std.ExtHashMap.getElem?_insert, beq_iff_eq]
  interval_cases i <;> simp

/-- A store of 0 in the bytes that `memset()` zeroed. -/
theorem unchangedExcept_memFill_memStore_zero {m' m5 : Mem} {a : BitVec 64} {n : Nat}
    {R : BitVec 64} {lr : Nat} (h : UnchangedExcept (IntxRV.memFill m' a.toNat 0#8 n) m5 R lr)
    (c : Nat) (hc : a.toNat ≤ c ∧ c + 8 ≤ a.toNat + n) :
    UnchangedExcept (IntxRV.memFill m' a.toNat 0#8 n) (memStore m5 c 0#64) R lr := by
  intro k hk
  by_cases hkc : c ≤ k ∧ k < c + 8
  · rw [getElem?_memStore_zero _ _ _ hkc, getElem?_memFill, if_pos (by omega)]
  · rw [getElem?_memStore_of_ne _ _ _ _ (by omega)]; exact h k hk

/-- The changes in the bytes at `b` and `c` are in the bytes at `B`. -/
theorem unchangedExcept2_of_3 {m m' : Mem} {a b c : BitVec 64} {la lb lc : Nat} (B : BitVec 64)
    (LB : Nat) (h : UnchangedExcept3 m m' a la b lb c lc)
    (hb : B.toNat ≤ b.toNat ∧ b.toNat + lb ≤ B.toNat + LB)
    (hc : B.toNat ≤ c.toNat ∧ c.toNat + lc ≤ B.toNat + LB) : UnchangedExcept2 m m' a la B LB :=
  fun k ha hB => h k ha (by omega) (by omega)

/-- A change in the bytes at `R` in the bytes at `B`, and then in the bytes at `A` and `B`. -/
theorem unchangedExcept2_comp {m0 m1 m2 : Mem} {R A B : BitVec 64} {lr la lb : Nat}
    (h1 : UnchangedExcept m0 m1 R lr) (hR : B.toNat ≤ R.toNat ∧ R.toNat + lr ≤ B.toNat + lb)
    (h2 : UnchangedExcept2 m1 m2 A la B lb) : UnchangedExcept2 m0 m2 A la B lb :=
  fun k ha hb => (h2 k ha hb).trans (h1 k (by omega))

/-- The bound of the words of u by its top significant word `mm - 1`. -/
theorem words_top_bound (m : Mem) (u : BitVec 64) (mm : Nat) (h1 : 1 ≤ mm) (h8 : mm ≤ 8)
    (hum : words m u 8 < 2 ^ (64 * mm)) :
    words m u 8 < ((memWord m (u + BitVec.ofNat 64 (8 * (mm - 1))).toNat).toNat + 1) *
      2 ^ (64 * (mm - 1)) := by
  have hs := words_split m (mm - 1) (8 - (mm - 1)) u
  rw [show mm - 1 + (8 - (mm - 1)) = 8 by omega] at hs
  obtain ⟨k, hk⟩ : ∃ k, 8 - (mm - 1) = k + 1 := ⟨7 - (mm - 1), by omega⟩
  have hW : words m (u + BitVec.ofNat 64 (8 * (mm - 1))) (k + 1) =
      (memWord m (u + BitVec.ofNat 64 (8 * (mm - 1))).toNat).toNat +
        2 ^ 64 * words m (u + BitVec.ofNat 64 (8 * (mm - 1)) + 8) k := rfl
  rw [hk, hW] at hs
  have hlo := words_lt m (mm - 1) u
  have hP : 2 ^ (64 * mm) = 2 ^ (64 * (mm - 1)) * 2 ^ 64 := by
    rw [← pow_add]; congr 1; omega
  generalize words m (u + BitVec.ofNat 64 (8 * (mm - 1)) + 8) k = R at hs
  generalize (memWord m (u + BitVec.ofNat 64 (8 * (mm - 1))).toNat).toNat = a at hs ⊢
  generalize 2 ^ (64 * (mm - 1)) = P at hs hlo hP ⊢
  rcases Nat.eq_zero_or_pos R with rfl | hR
  · rw [hs]; nlinarith
  · have : P * 2 ^ 64 ≤ P * (a + 2 ^ 64 * R) := Nat.mul_le_mul_left _ (by nlinarith)
    omega

/-- The normalized divisor is below `2^(64 (k + 1))`: its top word `b` shifted left by `s` fits
in a word. -/
theorem norm_top_lt {V b s k : Nat} (hV : V < (b + 1) * 2 ^ (64 * k)) (hb : b * 2 ^ s < 2 ^ 64)
    (hs : s < 64) : V * 2 ^ s < 2 ^ (64 * (k + 1)) := by
  have e : (2 : Nat) ^ 64 = 2 ^ (64 - s) * 2 ^ s := by rw [← pow_add]; congr 1; omega
  have hb' : b + 1 ≤ 2 ^ (64 - s) := by
    rw [e] at hb; exact Nat.lt_of_mul_lt_mul_right hb
  calc V * 2 ^ s < (b + 1) * 2 ^ (64 * k) * 2 ^ s := Nat.mul_lt_mul_of_pos_right hV (by positivity)
    _ ≤ 2 ^ (64 - s) * 2 ^ (64 * k) * 2 ^ s :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hb')
    _ = 2 ^ (64 * (k + 1)) := by rw [← pow_add, ← pow_add]; congr 1; omega

/-- The count of the words to divide: `mm` and the word with the bits shifted out of the top. -/
theorem num_toNat (mm : Nat) (hmm : mm < 2 ^ 63) (a b : BitVec 64) :
    (BitVec.ofNat 64 mm + ((if a < b then 1#64 else 0#64) ^^^ 1#64)).toNat =
      mm + if b.toNat ≤ a.toNat then 1 else 0 := by
  by_cases hab : a < b
  · rw [if_pos hab, if_neg (by rw [BitVec.lt_def] at hab; omega),
      show (1#64 ^^^ 1#64 : BitVec 64) = 0#64 from rfl, BitVec.add_zero, BitVec.toNat_ofNat,
      Nat.add_zero]
    omega
  · rw [if_neg hab, if_pos (by rw [BitVec.lt_def] at hab; omega),
      show (0#64 ^^^ 1#64 : BitVec 64) = 1#64 from rfl, BitVec.toNat_add]
    simp only [BitVec.toNat_ofNat]; omega

/-- The words of a buffer are 0 if each word is. -/
theorem words_eq_zero (m : Mem) : ∀ (n : Nat) (a : BitVec 64),
    (∀ i < n, memWord m (a + BitVec.ofNat 64 (8 * i)).toNat = 0#64) → words m a n = 0
  | 0, _, _ => rfl
  | n + 1, a, h => by
    have h0 := h 0 (by omega)
    rw [Nat.mul_zero, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at h0
    rw [words, h0, words_eq_zero m n (a + 8) fun i hi => by
      rw [BitVec.add_assoc, show (8 : BitVec 64) + BitVec.ofNat 64 (8 * i) =
        BitVec.ofNat 64 (8 * (i + 1)) by apply BitVec.eq_of_toNat_eq; simp; omega]
      exact h (i + 1) (by omega)]
    rfl

/-- The words of u below `2^(64 mm)` if its words from `mm` are 0. -/
theorem words8_lt_of_zero (m : Mem) (u : BitVec 64) (mm : Nat) (hmm : mm ≤ 8)
    (h : ∀ i, mm ≤ i → i < 8 → memWord m (u + BitVec.ofNat 64 (8 * i)).toNat = 0#64) :
    words m u 8 < 2 ^ (64 * mm) := by
  have hs := words_split m mm (8 - mm) u
  rw [show mm + (8 - mm) = 8 by omega] at hs
  rw [hs, words_eq_zero m (8 - mm) _ fun i hi => by
    rw [BitVec.add_assoc, show BitVec.ofNat 64 (8 * mm) + BitVec.ofNat 64 (8 * i) =
      BitVec.ofNat 64 (8 * (mm + i)) by apply BitVec.eq_of_toNat_eq; simp; omega]
    exact h (mm + i) (by omega) (by omega), Nat.mul_zero, Nat.add_zero]
  exact words_lt _ _ _

/-- The words of v are at least their word `n - 1` times `2^(64 (n - 1))`. -/
theorem words4_ge_top (m : Mem) (v : BitVec 64) (n : Nat) (hn1 : 1 ≤ n) (hn4 : n ≤ 4) :
    (memWord m (v + BitVec.ofNat 64 (8 * (n - 1))).toNat).toNat * 2 ^ (64 * (n - 1)) ≤
      words m v 4 := by
  have hs := words_split m (n - 1) (4 - (n - 1)) v
  rw [show n - 1 + (4 - (n - 1)) = 4 by omega] at hs
  obtain ⟨k, hk⟩ : ∃ k, 4 - (n - 1) = k + 1 := ⟨3 - (n - 1), by omega⟩
  rw [hk] at hs
  have hW : words m (v + BitVec.ofNat 64 (8 * (n - 1))) (k + 1) =
      (memWord m (v + BitVec.ofNat 64 (8 * (n - 1))).toNat).toNat +
        2 ^ 64 * words m (v + BitVec.ofNat 64 (8 * (n - 1)) + 8) k := rfl
  rw [hs, hW]
  generalize (memWord m (v + BitVec.ofNat 64 (8 * (n - 1))).toNat).toNat = b
  generalize 2 ^ (64 * (n - 1)) = P
  calc b * P = P * b := Nat.mul_comm _ _
    _ ≤ P * (b + 2 ^ 64 * words m (v + BitVec.ofNat 64 (8 * (n - 1)) + 8) k) :=
      Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
    _ ≤ _ := Nat.le_add_left _ _

end IntxRV.Api
