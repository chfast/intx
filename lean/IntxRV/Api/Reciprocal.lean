import IntxRV.Gen.Api
import IntxRV.Arith
import IntxRV.EnvImage
import IntxRV.ApiModel
import Mathlib.Tactic.Ring
/-!
# The proof of `reciprocal_2by1()`

The function reads the entry of `RECIPROCAL_TABLE` for the top 9 bits of `d` (two `lwu` from the
image data) and computes the reciprocal with the Newton steps and the correction of
`internal::reciprocal()`. `rv_exec` runs its 40 instructions, the two loads read the table entry
(`table_addr`, `image_data_get`), and the result is the one of the model `Intx.Model.reciprocal`:
the terms of the machine and of the model are equal after naming their common parts. Its value is
`reciprocal_spec`.
-/

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
-- The paths use different lemmas of the same simp calls.
set_option linter.unusedSimpArgs false

namespace IntxRV.Api
open IntxRV IntxRV.Gen

/-- The index of the table entry: `(d >> 52) & ~7` is `8 * (d >> 55)`. -/
theorem shr52_and (d : BitVec 64) : (d >>> 52) &&& 0xfffffffffffffff8#64 = (d >>> 55) <<< 3 := by
  rw [show (0xfffffffffffffff8#64) = ~~~(BitVec.ofNat 64 (2 ^ 3 - 1)) from by decide]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_not, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one, hi, decide_true,
    Bool.true_and]
  by_cases h3 : i < 3
  · simp [h3]
  · simp only [h3, decide_false, Bool.not_false, Bool.and_true, Bool.true_and]
    rw [show 55 + (i - 3) = 52 + i by omega]


/-- The address of the table entry of `d`. -/
theorem table_addr (d base : BitVec 64) (hd : 2 ^ 63 ≤ d.toNat) :
    (d >>> 52 &&& 0xfffffffffffffff8#64) + (pcAt base 1 + 18446744073709549724#64) =
      base + BitVec.ofNat 64 160 + BitVec.ofNat 64 (8 * (d.toNat / 2 ^ 55 - 256)) := by
  rw [shr52_and, pcAt]
  have := d.isLt
  bv_omega

/-- The address of the high half of the table entry of `d`. -/
theorem table_addr_hi (d base : BitVec 64) (hd : 2 ^ 63 ≤ d.toNat) :
    (d >>> 52 &&& 0xfffffffffffffff8#64) + (pcAt base 1 + 18446744073709549728#64) =
      base + BitVec.ofNat 64 160 + BitVec.ofNat 64 (8 * (d.toNat / 2 ^ 55 - 256)) + 4 := by
  rw [shr52_and, pcAt]
  have := d.isLt
  bv_omega

/-- The carry of `a + d`: the test of the compiler. -/
theorem add_lt_iff_not_lt (a d : BitVec 64) :
    a + d < d ↔ d ^^^ 18446744073709551615#64 < a := by
  rw [show d ^^^ 18446744073709551615#64 = ~~~d by
    rw [show (18446744073709551615#64) = BitVec.allOnes 64 from rfl, BitVec.xor_allOnes]]
  bv_omega

theorem image_data_get : ∀ i < 256, image_data.getD i 0 =
    BitVec.ofNat 64 (523520 / (i + 256) * (523520 / (i + 256)) +
      2 ^ 32 * (2 ^ 11 * (523520 / (i + 256)) - 1)) := by
  decide

theorem reciprocal_2by1.proof : reciprocal_2by1.spec := by
  apply runsI_of_reach image_decodes
  intro base ret hb hr hc hl hw x m hx1 hbufs hhold hpre
  simp only [reciprocal_2by1.pre, reciprocal_2by1.bufs, List.nil_append] at hpre ⊢
  simp (disch := decide) only [Regs.eq_get x] at hpre hx1 ⊢
  simp only [reciprocal_2by1_entry, show image_data.length = 256 from rfl,
    show image_dataOff = 160 from rfl] at *
  rv_exec
  refine Reach.step (by decide) rfl ?_
  simp only [StepGoal, Nat.reduceAdd, true_and]
  simp only [Defn] at *
  subst_vars
  rv_val
  have hi : (x.get 10#5).toNat / 2 ^ 55 - 256 < 256 := by have := (x.get 10#5).isLt; omega
  rw [table_addr _ _ hpre]
  refine ⟨Or.inl (mem_bufWords hi), fun w hw => ?_⟩
  rw [memHalf_lo, holdsData_get hhold (by rw [show image_data.length = 256 from rfl]; exact hi),
    ← List.getD_eq_getElem _ 0, image_data_get _ hi] at hw
  rv_exec
  refine Reach.step (by decide) rfl ?_
  simp only [StepGoal, Nat.reduceAdd]
  rv_val
  rw [table_addr_hi _ _ hpre]
  have hnw : (base + BitVec.ofNat 64 160 + BitVec.ofNat 64 (8 * ((x.get 10#5).toNat / 2 ^ 55 - 256))
      + 4).toNat = (base + BitVec.ofNat 64 160 +
        BitVec.ofNat 64 (8 * ((x.get 10#5).toNat / 2 ^ 55 - 256))).toNat + 4 := by bv_omega
  refine ⟨Or.inr (by
    rw [show ∀ a : BitVec 64, a + 4 - 4#64 = a from fun a => by bv_omega]; exact mem_bufWords hi),
    fun w hw => ?_⟩
  rw [hnw, memHalf_hi,
    holdsData_get hhold (by rw [show image_data.length = 256 from rfl]; exact hi),
    ← List.getD_eq_getElem _ 0, image_data_get _ hi] at hw
  rv_exec
  rv_val
  simp only [update_aligned hr]
  refine Reach.refl ?_
  simp only [reciprocal_2by1.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, and_true, true_and]
  simp (disch := decide) only [Regs.eq_get x]
  refine ⟨?_, ?_⟩
  rotate_left
  · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte, BitVec.ofNat_eq_ofNat,
      and_self, and_true, true_and]
    simp (disch := decide) only [Regs.eq_get x, and_self]
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  simp only [Defn] at *
  subst_vars
  obtain ⟨v, hv, hv1, hv2⟩ :=
    Intx.Model.reciprocal_spec (.ofBitVec (x.get 10#5)) (by simpa using hpre)
  simp only [Intx.Model.reciprocal, Intx.Model.reciprocal_approx, Intx.Model.require] at hv
  generalize hdd : x.get 10#5 = d at *
  generalize hI : d.toNat / 2 ^ 55 - 256 = i at *
  obtain ⟨hv0a, hv0b, hsq, hsc⟩ := Intx.Model.reciprocal_table_entry i hi
  have hidx : UInt64.toNat (UInt64.ofBitVec d >>> 55 - 256) = i := by
    show (d >>> 55 - 256#64).toNat = i
    rw [← hI]; bv_omega
  have hreq : ({ toBitVec := d } : UInt64) &&& 9223372036854775808 ≠ 0 :=
    Intx.Model.and_top_ne_zero _ (by simpa using hpre)
  simp only [hidx, Vector.getElem?_eq_getElem hi, hreq, dite_true, Option.bind_some,
    Option.pure_def, Option.bind_eq_bind, bind, Option.some.injEq, ne_eq, not_false_eq_true] at hv
  generalize hV : 523520 / (i + 256) = V at *
  have hVV : V * V ≤ 2045 * 2045 := Nat.mul_le_mul hv0b hv0b
  have hlo : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64
      (V * V + 2 ^ 32 * (2 ^ 11 * V - 1)))) =
      Intx.Model.RECIPROCAL_TABLE[i].1.toUInt64.toBitVec := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, UInt32.toNat_toUInt64,
      UInt64.toNat_toBitVec, hsq]
    omega
  have hhi : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64
      (V * V + 2 ^ 32 * (2 ^ 11 * V - 1)) >>> 32)) =
      Intx.Model.RECIPROCAL_TABLE[i].2.toUInt64.toBitVec := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      UInt32.toNat_toUInt64, UInt64.toNat_toBitVec, hsc, Nat.shiftRight_eq_div_pow]
    omega
  rw [hlo, hhi]
  generalize Intx.Model.RECIPROCAL_TABLE[i].1.toUInt64 = L at *
  generalize Intx.Model.RECIPROCAL_TABLE[i].2.toUInt64 = H at *
  have hv' := congrArg UInt64.toBitVec hv
  simp only [UInt64.toBitVec_sub, UInt64.toBitVec_add, UInt64.toBitVec_mul,
    UInt64.toBitVec_shiftRight, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_and,
    Intx.Model.U128.getElem_one, Intx.Model.U128.getElem_zero, umul_hi_toBitVec,
    umul_lo_toBitVec, apply_ite UInt64.toBitVec, UInt64.lt_iff_toBitVec_lt, UInt64.toBitVec_one,
    UInt64.toBitVec_zero, UInt64.toBitVec_ofNat, BitVec.reduceMod, BitVec.ushiftRight_eq',
    BitVec.shiftLeft_eq', BitVec.reduceToNat] at hv'
  have hdv : (2 ^ 128 - 1) / d.toNat - 2 ^ 64 = v.toBitVec.toNat := by
    have hd := d.isLt
    simp only [UInt64.toNat_ofBitVec] at hv1 hv2
    rw [Nat.div_eq_of_lt_le (k := 2 ^ 64 + v.toNat) (by omega) (by omega)]
    simp
  rw [hdv]
  refine congrArg BitVec.toNat ?_
  clear hv hdv hv1 hv2 hsq hsc hlo hhi hidx hreq hnw hhold hbufs
  generalize d >>> 24 + 1#64 = D at *
  rw [BitVec.mul_comm L.toBitVec D] at hv'
  generalize H.toBitVec - (D * L.toBitVec) >>> 40 = v1 at *
  rw [BitVec.mul_comm v1 (1152921504606846976#64 - v1 * D), BitVec.add_comm (v1 <<< 13)] at hv'
  generalize ((1152921504606846976#64 - v1 * D) * v1) >>> 47 + v1 <<< 13 = v2 at *
  simp only [BitVec.ofNat_eq_ofNat] at hv' ⊢
  rw [BitVec.and_comm (v2 >>> 1), mulhu_comm v2] at hv'
  generalize ((0#64 - (d &&& 1#64) &&& v2 >>> 1) - v2 * (d >>> 1 + (d &&& 1#64))) = e at *
  rw [BitVec.add_comm (mulhu e v2 >>> 1)] at hv'
  generalize v2 <<< 31 + mulhu e v2 >>> 1 = v3 at *
  simp only [add_lt_iff_not_lt] at hv'
  generalize (if d ^^^ 18446744073709551615#64 < v3 * d then 1#64 else 0#64) = c at *
  rw [← hv']
  ring

theorem reciprocal_2by1.nonvacuous :
    NonVacuousI image_code image_data image_dataOff reciprocal_2by1.bufs reciprocal_2by1.pre :=
  nonVacuousI_of (fun i => if i = 10#5 then 0x8000000000000000#64 else 0) (by decide) (by decide)
    (by decide) (by decide) (by simp [reciprocal_2by1.bufs])
    (fun _ => by simp (config := { decide := true }) [reciprocal_2by1.pre])

end IntxRV.Api
