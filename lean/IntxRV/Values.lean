import IntxRV.Semantics
import Intx.Proofs.Div
/-!
# Values

The values computed by the instructions (`rtypeVal`, `mulVal`, ...) in terms of `BitVec`
operations, and the model of the C++ code (`Intx.Model`, on `UInt64`) in terms of the same
operations: `umul` is the multiplication `mul` and the high part `mulhu` of the RISC-V `M`
extension. `bv_omega` and `ring` prove the rest.
-/

open Sail LeanRV64D LeanRV64D.Functions LeanRV64D.Defs
open Intx Intx.Model

namespace IntxRV

/-- The high word of the 128-bit product, the `mulhu` instruction. -/
def mulhu (a b : BitVec 64) : BitVec 64 := BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64)

theorem mulhu_comm (a b : BitVec 64) : mulhu a b = mulhu b a := by
  simp [mulhu, Nat.mul_comm]

theorem mulVal_hu_toNat (a b : BitVec 64) :
    (mulVal ⟨.High, .Unsigned, .Unsigned⟩ a b).toNat = a.toNat * b.toNat / 2 ^ 64 := by
  simp only [mulVal, mult_to_bits_half, to_bits_truncate, get_slice_int, Sail.BitVec.extractLsb,
    Sail.BitVec.toNatInt]
  have ha := a.isLt
  have hb := b.isLt
  have hp : a.toNat * b.toNat < 2 ^ 128 := by
    calc a.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' ha hb
      _ = 2 ^ 128 := by norm_num
  simp
  rw [← Int.natCast_mul]
  generalize a.toNat * b.toNat = p at hp ⊢
  rw [Int.emod_eq_of_lt (by positivity) (by omega), Int.toNat_natCast, Nat.shiftRight_eq_div_pow]
  norm_num at hp ⊢
  omega

theorem mulVal_lo (a b : BitVec 64) : mulVal ⟨.Low, .Signed, .Signed⟩ a b = a * b := by
  simp only [mulVal, mult_to_bits_half, to_bits_truncate, get_slice_int, Sail.BitVec.extractLsb]
  apply BitVec.eq_of_toNat_eq
  simp
  have hr0 : 0 ≤ a.toInt * b.toInt % 680564733841876926926749214863536422912 :=
    Int.emod_nonneg _ (by norm_num)
  apply Int.natCast_inj.mp
  rw [Int.natCast_mod, Int.toNat_of_nonneg hr0, Int.emod_emod_of_dvd _ (by norm_num),
    Int.mul_emod, BitVec.toInt_eq_toNat_bmod a, BitVec.toInt_eq_toNat_bmod b, Int.bmod_emod,
    Int.bmod_emod, ← Int.mul_emod]
  push_cast; rfl
theorem mulVal_hu (a b : BitVec 64) : mulVal ⟨.High, .Unsigned, .Unsigned⟩ a b = mulhu a b := by
  apply BitVec.eq_of_toNat_eq
  rw [mulVal_hu_toNat, mulhu, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  exact Nat.div_lt_of_lt_mul (Nat.mul_lt_mul'' a.isLt b.isLt)

theorem umul_lo_toBitVec (x y : Word) : (umul x y).lo.toBitVec = x.toBitVec * y.toBitVec := by
  have h := umul_spec x y
  have hl := (umul x y).lo.toNat_lt
  apply BitVec.eq_of_toNat_eq
  simp only [UInt64.toNat_toBitVec, BitVec.toNat_mul] at *
  omega

theorem umul_hi_toBitVec (x y : Word) :
    (umul x y).hi.toBitVec = mulhu x.toBitVec y.toBitVec := by
  have h := umul_spec x y
  have hl := (umul x y).lo.toNat_lt
  have hh := (umul x y).hi.toNat_lt
  apply BitVec.eq_of_toNat_eq
  simp only [UInt64.toNat_toBitVec, mulhu, BitVec.toNat_ofNat] at *
  omega

theorem zopz0zI_u_eq (a b : BitVec 64) : zopz0zI_u a b = decide (a < b) := by
  simp [zopz0zI_u, Sail.BitVec.toNatInt, BitVec.lt_def]

theorem shiftiopVal_srli (sh : BitVec 6) (a : BitVec 64) :
    shiftiopVal .SRLI sh a = a >>> sh.toNat := by
  simp [shiftiopVal, shift_bits_right, Sail.BitVec.extractLsb, Functions.log2_xlen,
    Sail.shift_bits_right]
  have : BitVec.extractLsb 5 0 sh = sh := by apply BitVec.eq_of_toNat_eq; simp; omega
  rw [this]; rfl

/-- The sign of an xor: whether the signs differ. -/
theorem sign_xor (a b : BitVec 64) :
    9223372036854775808 ≤ (a ^^^ b).toNat ↔
      ¬(9223372036854775808 ≤ a.toNat ↔ 9223372036854775808 ≤ b.toNat) := by
  have h : ∀ c : BitVec 64, 9223372036854775808 ≤ c.toNat ↔ c.msb = true := fun c => by
    rw [BitVec.msb_eq_true_iff_two_mul_ge]; omega
  rw [h, h, h, BitVec.msb_xor]
  cases a.msb <;> cases b.msb <;> simp

/-- The signed comparison with 0 of `blt`/`bge`: the sign bit. -/
theorem zopz0zI_s_zero (a : BitVec 64) : zopz0zI_s a 0#64 = decide (2 ^ 63 ≤ a.toNat) := by
  simp only [zopz0zI_s, BitVec.toInt_zero]
  rw [BitVec.toInt_eq_toNat_cond]
  split <;> simp <;> omega

theorem zero_extend_bool_to_bit (c : Bool) :
    zero_extend (m := 64) (bool_to_bit c) = if c then 1#64 else 0#64 := by
  cases c <;> rfl

/-! ## The values of the instructions of the verified functions -/

theorem rtypeVal_add (a b : BitVec 64) : rtypeVal .ADD a b = a + b := rfl
theorem rtypeVal_sub (a b : BitVec 64) : rtypeVal .SUB a b = a - b := rfl
theorem rtypeVal_and (a b : BitVec 64) : rtypeVal .AND a b = a &&& b := rfl
theorem rtypeVal_or (a b : BitVec 64) : rtypeVal .OR a b = a ||| b := rfl
theorem rtypeVal_xor (a b : BitVec 64) : rtypeVal .XOR a b = a ^^^ b := rfl
theorem rtypeVal_sltu (a b : BitVec 64) : rtypeVal .SLTU a b = if a < b then 1#64 else 0#64 := by
  simp [rtypeVal, zopz0zI_u_eq, zero_extend_bool_to_bit]
theorem itypeVal_addi (imm : BitVec 12) (a : BitVec 64) :
    itypeVal .ADDI imm a = a + imm.signExtend 64 := rfl
theorem itypeVal_xori (imm : BitVec 12) (a : BitVec 64) :
    itypeVal .XORI imm a = a ^^^ imm.signExtend 64 := rfl
theorem itypeVal_andi (imm : BitVec 12) (a : BitVec 64) :
    itypeVal .ANDI imm a = a &&& imm.signExtend 64 := rfl
theorem itypeVal_ori (imm : BitVec 12) (a : BitVec 64) :
    itypeVal .ORI imm a = a ||| imm.signExtend 64 := rfl

theorem extractLsb_5_toNat (b : BitVec 64) : (BitVec.extractLsb 5 0 b).toNat = b.toNat % 64 := by
  simp [BitVec.extractLsb]
theorem rtypeVal_sll (a b : BitVec 64) : rtypeVal .SLL a b = a <<< (b.toNat % 64) := by
  simp [rtypeVal, shift_bits_left, Sail.BitVec.extractLsb, Functions.log2_xlen,
    Sail.shift_bits_left]
  exact congrArg (fun n => a <<< n) (extractLsb_5_toNat b)
theorem rtypeVal_srl (a b : BitVec 64) : rtypeVal .SRL a b = a >>> (b.toNat % 64) := by
  simp [rtypeVal, shift_bits_right, Sail.BitVec.extractLsb, Functions.log2_xlen,
    Sail.shift_bits_right]
  exact congrArg (fun n => a >>> n) (extractLsb_5_toNat b)
theorem rtypewVal_subw (a b : BitVec 64) :
    rtypewVal .SUBW a b = (a.setWidth 32 - b.setWidth 32).signExtend 64 := by
  have ha : Sail.BitVec.extractLsb a 31 0 = a.setWidth 32 := BitVec.eq_of_toNat_eq rfl
  have hb : Sail.BitVec.extractLsb b 31 0 = b.setWidth 32 := BitVec.eq_of_toNat_eq rfl
  simp only [rtypewVal, ha, hb]
  rfl

end IntxRV
