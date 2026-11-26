import IntxRV.Gen.Api.shr_256
import IntxRV.Arith
import IntxRV.Shift
/-!
# `operator>>` of `uint256` by `uint64_t`

The specification, from `include/intx/intx.hpp`:

```cpp
/// The shift right.
/// @post result = x / 2^shift
friend constexpr uint operator>>(const uint& x, uint64_t shift) noexcept
```

`shr_256.spec` states it for the RV64 machine code of `shr_256` in `IntxRV/Api.cpp` (generated in
`IntxRV/Gen/Api/`, see `IntxRV/README.md`). The instance has `[[gnu::flatten]]`: its code is
the operator, which clang does not inline otherwise.

The code returns 0 for a shift by 256 or more. For the shift `s = 64 * k + t`, `t < 64`, it stores
the funnel shifts `(a >>> t) ||| (b <<< (64 - t))` of the words from `k`, the top word shifted
right by `t`, and `k` zero words. `rv_exec` runs the 5 paths; the lemmas of `IntxRV/Shift.lean`
bring the words that clang computes to the funnel shifts, and `shr_val_ge`, `shr_val_0` to
`shr_val_3` give the value.
-/

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
-- The paths use different lemmas of the same simp calls, and some steps close every goal they
-- apply to.
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option hygiene false in
/-- Closes the value of a path of the shift right by the lemma `lem` of its `k`. -/
local macro "shr_close" lem:ident : tactic => `(tactic| (
  have := $lem (memWord m (x.get 11#5).toNat).toNat (memWord m (x.get 11#5 + 8#64).toNat).toNat
    (memWord m (x.get 11#5 + 16#64).toNat).toNat (memWord m (x.get 11#5 + 24#64).toNat).toNat
    (x.get 12#5).toNat ((x.get 12#5).toNat % 64) (BitVec.isLt _) (BitVec.isLt _)
    (BitVec.isLt _) (BitVec.isLt _) (Nat.mod_lt _ (by decide)) (by bv_omega)
  omega))

/-- The run from the start of the code to the return address in ra. -/
theorem shr_256.reach (base : BitVec 64) (x : Regs) (m : Mem) (hra : x.get 1#5 &&& 3 = 0)
    (hpre : shr_256.pre x m) :
    Reach (shr_256.bufs x) shr_256_prog base (pcAt base 0) x m (x.get 1#5) (shr_256.post x m) := by
  simp only [shr_256.pre, shr_256.bufs, Buf, Disjoint] at hpre ⊢
  simp (disch := decide) only [Regs.eq_get x] at hpre ⊢
  rv_exec
  all_goals try rv_val
  all_goals simp only [update_aligned hra]
  all_goals refine Reach.refl ?_
  all_goals simp only [shr_256.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  all_goals simp (disch := decide) only [Regs.eq_get x]
  all_goals refine ⟨?_, ?_, ?_⟩
  all_goals try (simp (disch := first | bv_omega | fail) only [unchangedExcept_memStore,
    unchangedExcept_refl]; done)
  all_goals try (simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte,
    BitVec.ofNat_eq_ofNat, and_self, and_true, true_and] <;>
    simp (disch := decide) only [Regs.eq_get x, and_self] <;> done)
  -- The value: the words stored, as funnel shifts of the words of x by t = shift % 64.
  all_goals try simp only [Defn] at *
  all_goals simp (config := { decide := true }) (disch := first | bv_omega | fail) only [words,
    BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero,
    memWord_memStore_self, memWord_memStore_of_ne, Nat.mul_zero, Nat.add_zero]
  all_goals try simp only [*]
  all_goals try simp only [zopz0zI_u_eq, zopz0zKzJ_u_eq, show x.get 0#5 = 0#64 from Regs.get_zero x,
    BitVec.zero_add, decide_eq_true_eq, decide_eq_false_iff_not] at *
  all_goals try simp (disch := omega) only [toNat_xor_allOnes_mod_64, toNat_add_neg128_mod_64,
    shiftLeft_one_shiftLeft, shiftLeft_shiftLeft_one, shr_funnel_bot, BitVec.zero_or,
    BitVec.or_zero, or_zero', zero_or', toNat_shr_funnel, toNat_shl_or_shr', toNat_ushiftRight',
    BitVec.toNat_zero, Nat.zero_add, Nat.mul_zero, Nat.add_zero]
  all_goals first
    | exact shr_val_ge _ _ _ _ _ (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)
        (by bv_omega)
    | shr_close shr_val_0
    | shr_close shr_val_1
    | shr_close shr_val_2
    | shr_close shr_val_3

theorem shr_256.proof_of_decodes (hdec : shr_256.decodes) : shr_256.spec :=
  runsM_of_reach hdec fun base ret _ hr _ x m hx1 hpre => by
    have hx : x.get 1#5 = ret := by rw [← Regs.eq_get x (by decide)]; exact hx1
    have h := shr_256.reach base x m (hx ▸ hr) hpre
    rwa [pcAt_zero, hx] at h

end IntxRV.Api
