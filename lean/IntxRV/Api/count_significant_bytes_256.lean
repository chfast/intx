import IntxRV.Gen.Api.count_significant_bytes_256
import IntxRV.Arith
import IntxRV.Image
import IntxRV.Clz
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases
import IntxRV.Bits
import IntxRV.Loop
/-!
# `count_significant_bytes()` of `uint256`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Counts the significant bytes of x: the bytes up to the highest non-zero byte.
/// @post result = if x = 0 then 0 else Nat.log2 x / 8 + 1
template <unsigned N>
constexpr unsigned count_significant_bytes(const uint<N>& x) noexcept
```

`count_significant_bytes_256.spec` states it for the RV64 machine code of
`count_significant_bytes_256` in `IntxRV/Api.cpp` (generated in `IntxRV/Gen/Api/`, see
`IntxRV/README.md`). The function finds the top nonzero word, counts its leading zeros with the
SWAR code of `swarClz` (`IntxRV/Clz.lean`) and computes `(71 - clz) / 8` in 32 bits (`srliw`) plus
8 bytes for each word below it. `csb_words4` gives the count from the top nonzero word.
-/

set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace IntxRV.Api
open IntxRV IntxRV.Gen

/-- The significant bytes of a number of 4 words by its top nonzero word. -/
theorem csb_words4 (w0 w1 w2 w3 : BitVec 64) :
    (if w0.toNat + 2 ^ 64 * (w1.toNat + 2 ^ 64 * (w2.toNat + 2 ^ 64 * w3.toNat)) = 0 then 0
      else Nat.log2 (w0.toNat + 2 ^ 64 * (w1.toNat + 2 ^ 64 * (w2.toNat + 2 ^ 64 * w3.toNat))) /
        8 + 1) =
      if w3 ≠ 0 then Nat.log2 w3.toNat / 8 + 25 else if w2 ≠ 0 then Nat.log2 w2.toNat / 8 + 17
      else if w1 ≠ 0 then Nat.log2 w1.toNat / 8 + 9 else if w0 ≠ 0 then Nat.log2 w0.toNat / 8 + 1
      else 0 := by
  have h := bit_width_words4 w0 w1 w2 w3
  generalize w0.toNat + 2 ^ 64 * (w1.toNat + 2 ^ 64 * (w2.toNat + 2 ^ 64 * w3.toNat)) = X at *
  split_ifs at h ⊢ <;> omega

/-- `(71 - clz) >> 3` in 32 bits (`subw` and `srliw`) for the count of the leading zeros of a
nonzero word. -/
theorem csb_core (L : Nat) (hL : L < 64) :
    BitVec.signExtend 64 (BitVec.setWidth 32 (BitVec.signExtend 64
      (BitVec.setWidth 32 71#64 - BitVec.setWidth 32 (BitVec.ofNat 64 (63 - L)))) >>> 3) =
      BitVec.ofNat 64 (L / 8 + 1) := by
  interval_cases L <;> decide

set_option maxHeartbeats 4000000 in
theorem count_significant_bytes_256.reach (base : BitVec 64) (x : Regs) (m : Mem)
    (hra : x.get 1#5 &&& 3 = 0) (hpre : count_significant_bytes_256.pre x m) :
    Reach (count_significant_bytes_256.bufs x) count_significant_bytes_256_prog base (pcAt base 0)
      x m (x.get 1#5) (count_significant_bytes_256.post x m) := by
  simp only [count_significant_bytes_256.pre, count_significant_bytes_256.bufs, Buf] at hpre ⊢
  simp (disch := decide) only [Regs.eq_get x] at hpre ⊢
  rv_exec
  -- The load of the top nonzero word at x + 0 stops the run: its address is a name.
  all_goals first
    | (rv_not_at 17; skip)
    | ((try simp only [Defn] at *); (try subst_vars); (try rv_val); rv_exec)
  all_goals try rv_val
  all_goals try simp only [update_aligned hra]
  all_goals refine Reach.refl ?_
  all_goals simp only [count_significant_bytes_256.post, calleeSaved, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, and_true, true_and]
  all_goals simp (disch := decide) only [Regs.eq_get x]
  all_goals simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  all_goals try simp only [Defn] at *
  all_goals try subst_vars
  all_goals try simp only [BitVec.reduceAdd, BitVec.reduceHShiftLeft, BitVec.reduceShiftLeft,
    BitVec.reduceSub, BitVec.reduceMul]
  all_goals try simp only [← smear_expand, ← swarClz_expand, clz_ite]
  all_goals refine ⟨?_, ?_, ?_⟩
  all_goals first
    | (simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte,
        BitVec.ofNat_eq_ofNat, and_self, and_true, true_and]
       simp (disch := decide) only [Regs.eq_get x, and_self]; done)
    | skip
  all_goals try simp only [beq_eq_false_iff_ne, ne_eq] at *
  all_goals first | contradiction | skip
  all_goals try simp only [words, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero, Nat.add_zero]
  all_goals generalize memWord m (x.get 10#5).toNat = w0 at *
  all_goals generalize memWord m (x.get 10#5 + 8#64).toNat = w1 at *
  all_goals generalize memWord m (x.get 10#5 + 16#64).toNat = w2 at *
  all_goals generalize memWord m (x.get 10#5 + 24#64).toNat = w3 at *
  all_goals subst_vars
  all_goals try rw [csb_words4]
  all_goals try simp only [*, ne_eq, not_true_eq_false, not_false_eq_true, ↓reduceIte,
    BitVec.toNat_ofNat]
  all_goals first | decide | skip
  all_goals
    first
      | have hL := log2_lt_64 (w := w3) (by assumption)
        rw [csb_core _ hL]
      | have hL := log2_lt_64 (w := w2) (by assumption)
        rw [csb_core _ hL]
      | have hL := log2_lt_64 (w := w1) (by assumption)
        rw [csb_core _ hL]
      | have hL := log2_lt_64 (w := w0) (by assumption)
        rw [csb_core _ hL]
    generalize Nat.log2 _ = L at *
    first
      | (simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
      | (apply signExtend_setWidth_of_lt
         simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)

theorem count_significant_bytes_256.proof_of_decodes (hdec : count_significant_bytes_256.decodes) :
    count_significant_bytes_256.spec :=
  runsM_of_reach hdec fun base ret _ hr _ x m hx1 hpre => by
    have hx : x.get 1#5 = ret := by rw [← Regs.eq_get x (by decide)]; exact hx1
    have h := count_significant_bytes_256.reach base x m (hx ▸ hr) hpre
    rwa [pcAt_zero, hx] at h

end IntxRV.Api
