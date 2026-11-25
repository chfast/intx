import IntxRV.Gen.Api.ctz_256
import IntxRV.Arith
import IntxRV.Image
import IntxRV.EnvImage
import IntxRV.Ctz
import IntxRV.Bits
import Mathlib.Tactic.Ring
/-!
# `ctz()` of `uint256`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Counts the trailing zero bits of x.
/// @post x % 2^result = 0
/// @post result = N ∨ x.testBit result
template <unsigned N>
constexpr unsigned ctz(const uint<N>& x) noexcept
```

`ctz_256.spec` states it for the RV64 machine code of `ctz_256` in `IntxRV/Api.cpp` (generated in
`IntxRV/Gen/Api/`, see `IntxRV/README.md`). The function is in its image with its data: the
multiplier of a de Bruijn sequence and a table of 64 bytes.

The code finds the first nonzero word `w`, at `i`, and returns `64 * i | t`, where `t` is the
entry of the table at `(w & -w) * 0x0218a392cd3d5dbf >> 58`, read with `lbu`; 256 if `x` is 0.
`and_neg_self` (`IntxRV/Ctz.lean`) gives the lowest set bit `2 ^ t` of `w`, `ctz_table` checks
the entry of every `t`, and `ctz_spec_of_word` gives the specification.
-/

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
-- The paths use different lemmas of the same simp calls.
set_option linter.unusedSimpArgs false

namespace IntxRV.Api
open IntxRV IntxRV.Gen

/-- The table entry of every lowest set bit `t`, at the byte `8 + deBruijnIdx t` of the data. -/
theorem ctz_table : ∀ t : Fin 64,
    (ctz_256_image_data.getD ((8 + deBruijnIdx t) / 8) 0 >>>
      (8 * ((8 + deBruijnIdx t) % 8))).setWidth 8 = BitVec.ofNat 8 t := by
  decide

/-- The address of the multiplier, the data word 0. -/
theorem ctz_mul_addr (base : BitVec 64) :
    pcAt base 15 + 60#64 = base + 120#64 + BitVec.ofNat 64 (8 * 0) := by
  rw [pcAt]; bv_omega

theorem zero_sub' (W : BitVec 64) : (0 : BitVec 64) - W = -W := by simp

/-- The index of the table entry of a nonzero word. -/
theorem ctz_idx {W : BitVec 64} (hW : W ≠ 0) :
    ((W &&& -W) * 151050438420815295#64) >>> 58 = BitVec.ofNat 64 (deBruijnIdx W.ctz.toNat) := by
  rw [and_neg_self hW]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, deBruijnIdx, Nat.mod_eq_of_lt (BitVec.isLt _)]

theorem deBruijnIdx_lt (t : Nat) : deBruijnIdx t < 64 := by
  unfold deBruijnIdx
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := (BitVec.twoPow 64 t * 0x0218a392cd3d5dbf#64).isLt
  omega

/-- The address of the table entry `j`, the data byte `8 + j`. -/
theorem ctz_tbl_addr (base : BitVec 64) (j : Nat) (_hj : j < 64) :
    pcAt base 20 + (48#64 + BitVec.ofNat 64 j) = base + 120#64 + BitVec.ofNat 64 (8 + j) := by
  rw [pcAt]; bv_omega

/-- The result `c ||| t` of the word index `c` and the count `t`. -/
theorem toNat_or_byte (c : BitVec 64) (t : Nat) (hc : c.toNat % 64 = 0) (ht : t < 64) :
    (c ||| BitVec.setWidth 64 (BitVec.ofNat 8 t)).toNat = c.toNat + t := by
  rw [BitVec.setWidth_ofNat_of_le_of_lt (by omega) (by omega : t < 2 ^ 8),
    show c = BitVec.ofNat 64 (64 * (c.toNat / 64)) by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; have := c.isLt; omega,
    toNat_or_lt _ _ (by have := c.isLt; omega) ht, BitVec.toNat_ofNat]
  have := c.isLt; omega

set_option hygiene false in
/-- The `lbu` of the table entry of the nonzero word `W` and the rest of the path. -/
macro "ctz_lbu" W:term ", " c:term ", " i:term ", " R:term : tactic => `(tactic| (
  have hW0 : $W ≠ 0 := by simpa using (‹($W == 0) = false›)
  rw [zero_sub', ctz_idx hW0, ctz_tbl_addr _ _ (deBruijnIdx_lt _)]
  simp only [BitVec.reduceNot]
  have hT := ctz_table ⟨($W).ctz.toNat, ctz_lt hW0⟩
  simp only [Fin.val_mk] at hT
  have hi : 8 + deBruijnIdx ($W).ctz.toNat < 8 * ctz_256_image_data.length := by
    have := deBruijnIdx_lt ($W).ctz.toNat
    rw [show ctz_256_image_data.length = 9 from rfl]; omega
  refine ⟨List.mem_append.mpr (.inr (byte_mem_dataWords hb (by decide) (by omega)
    (by rw [show ctz_256_image_data.length = 9 from rfl] at hi; exact hi))), fun wb hwb => ?_⟩
  rw [memByte_data hhold (by rw [show ctz_256_image_data.length = 9 from rfl]; bv_omega) hi,
    ← List.getD_eq_getElem _ 0, hT] at hwb
  rv_exec
  rv_val
  simp only [update_aligned hr]
  refine Reach.refl ?_
  simp only [ctz_256.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, and_true, true_and]
  simp (disch := decide) only [Regs.eq_get x]
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  simp only [Defn] at *
  subst_vars
  have ht := ctz_lt hW0
  have hres := toNat_or_byte $c ($W).ctz.toNat (by decide) ht
  simp only [BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl] at hres
  have hS := ctz_spec_of_word $i ($W).ctz.toNat ($W).toNat $R ($W).isLt ht
    (toNat_mod_two_pow_ctz _) (testBit_ctz hW0)
  have hwords : words m (x.get 10#5) 4 = 2 ^ (64 * $i) * (($W).toNat + 2 ^ 64 * $R) := by
    simp only [words, BitVec.add_assoc, BitVec.reduceAdd, show (8 : BitVec 64) = 8#64 from rfl]
    simp only [*, show (0 : BitVec 64).toNat = 0 from rfl, Nat.zero_add, Nat.mul_zero, Nat.add_zero]
    all_goals ring
  have hr32 : ($c ||| BitVec.setWidth 64 (BitVec.ofNat 8 ($W).ctz.toNat)).toNat % 2 ^ 32 =
      64 * $i + ($W).ctz.toNat := by rw [hres]; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hr32, hwords]; exact hS.1
  · rw [hr32, hwords]; exact Or.inr hS.2
  · exact signExtend_setWidth_of_lt (by rw [hres]; omega)
  · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte, BitVec.ofNat_eq_ofNat,
      and_self, and_true, true_and]
    simp (disch := decide) only [Regs.eq_get x, and_self]))

theorem ctz_256.proof_of_decodes (hdec : ctz_256.decodes) : ctz_256.spec := by
  apply runsI_of_reach hdec
  intro base ret hb hr hc hl hw x m hx1 hbufs hhold hpre
  simp only [ctz_256.pre, ctz_256.bufs, Buf] at hpre ⊢
  simp (disch := decide) only [Regs.eq_get x] at hpre hx1 ⊢
  simp only [ctz_256_entry, show ctz_256_image_data.length = 9 from rfl,
    show ctz_256_image_dataOff = 120 from rfl] at *
  rv_exec
  · simp only [Defn] at *
    subst_vars
    rv_val
    simp only [update_aligned hr]
    refine Reach.refl ?_
    simp only [ctz_256.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, and_true, true_and]
    simp (disch := decide) only [Regs.eq_get x]
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    have hwords : words m (x.get 10#5) 4 = 0 := by
      simp only [words, BitVec.add_assoc, BitVec.reduceAdd, show (8 : BitVec 64) = 8#64 from rfl]
      simp only [*, show (0 : BitVec 64).toNat = 0 from rfl, Nat.zero_add, Nat.mul_zero,
        Nat.add_zero]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hwords]; exact Nat.zero_mod _
    · exact Or.inl (by decide)
    · decide
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte, BitVec.ofNat_eq_ofNat,
        and_self, and_true, true_and]
      simp (disch := decide) only [Regs.eq_get x, and_self]
  all_goals
    refine Reach.step (by decide) rfl ?_
    simp only [StepGoal, Nat.reduceAdd]
    rv_val
    rw [ctz_mul_addr]
    refine ⟨List.mem_append.mpr (.inr (mem_bufWords (by decide))), fun wc hwc => ?_⟩
    rw [holdsData_get hhold (by decide)] at hwc
    simp only [show ctz_256_image_data[0] = 0x0218a392cd3d5dbf#64 from rfl] at hwc
    rv_exec
  all_goals
    simp only [Defn] at *
    subst_vars
    refine Reach.step (by decide) rfl ?_
    simp only [StepGoal, Nat.reduceAdd]
    rv_val
  · ctz_lbu (memWord m (x.get 10#5 + 24#64).toNat), 192#64, 3, 0
  · ctz_lbu (memWord m (x.get 10#5 + 16#64).toNat), 128#64, 2,
      (memWord m (x.get 10#5 + 24#64).toNat).toNat
  · ctz_lbu (memWord m (x.get 10#5 + 8#64).toNat), 64#64, 1,
      ((memWord m (x.get 10#5 + 16#64).toNat).toNat +
        2 ^ 64 * (memWord m (x.get 10#5 + 24#64).toNat).toNat)
  · ctz_lbu (memWord m (x.get 10#5).toNat), (0 : BitVec 64), 0,
      ((memWord m (x.get 10#5 + 8#64).toNat).toNat + 2 ^ 64 *
        ((memWord m (x.get 10#5 + 16#64).toNat).toNat +
          2 ^ 64 * (memWord m (x.get 10#5 + 24#64).toNat).toNat))

theorem ctz_256.nonvacuous :
    NonVacuousI ctz_256_image_code ctz_256_image_data ctz_256_image_dataOff ctz_256.bufs
      ctz_256.pre :=
  nonVacuousI_of (fun i => if i = 10#5 then 0x80000800#64 else 0) (by decide) (by decide)
    (by decide) (by decide)
    (by simp only [ctz_256.bufs, bufWords, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq]; decide)
    (fun _ => by simp only [ctz_256.pre, Buf]; decide)

end IntxRV.Api
