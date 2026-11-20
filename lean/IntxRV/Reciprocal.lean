import IntxRV.Gen.Api
import IntxRV.Arith
import IntxRV.EnvImage
import IntxRV.ApiModel
import Mathlib.Tactic.Ring
/-!
# The table of `reciprocal_2by1()` in the image

The lemmas of the proof of `reciprocal_2by1()`: the address of the entry of `RECIPROCAL_TABLE` for
`d` and the entries in the data of the image.
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

theorem image_data_get : ∀ i < 256, reciprocal_2by1_image_data.getD i 0 =
    BitVec.ofNat 64 (523520 / (i + 256) * (523520 / (i + 256)) +
      2 ^ 32 * (2 ^ 11 * (523520 / (i + 256)) - 1)) := by
  decide

end IntxRV.Api
