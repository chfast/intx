import IntxRV.Gen.Api.udivrem_3by2
import IntxRV.Arith
import IntxRV.Div3by2
import IntxRV.EnvM
/-!
# `udivrem_3by2()`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Divides u2:u1:u0 by the normalized d with its reciprocal v (Moller and Granlund, Algorithm 5).
/// @pre 2^127 ≤ d
/// @pre u2 * 2^64 + u1 < d
/// @pre v = (2^192 - 1) / d - 2^64
/// @post result.quot = (u2 * 2^128 + u1 * 2^64 + u0) / d
/// @post result.rem = (u2 * 2^128 + u1 * 2^64 + u0) % d
constexpr div_result<uint64_t, uint128> udivrem_3by2(
    uint64_t u2, uint64_t u1, uint64_t u0, uint128 d, uint64_t v) noexcept
```

`udivrem_3by2.spec` states it for the RV64 machine code of `udivrem_3by2` in `IntxRV/Api.cpp`
(generated in `IntxRV/Gen/Api/`, see `IntxRV/README.md`). The result has 24 bytes and is
returned in memory at a0.

`rv_exec` runs the 8 paths of the 3 branches: the selection of the remainder of `q1` or `q1 + 1`
by its high word, and the comparison of the remainder with `d` for the rare correction.
`div3by2BV_spec` (`IntxRV/Div3by2.lean`) gives the quotient and the remainder of the words that the
code computes, by Möller and Granlund, Theorem 3 (`Intx.div3by2_bounds`). On each path `rv_fold`
writes it with the names of the run, and the branch conditions (`rv_conds`) select the words that
the code stores.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 4000000

theorem udivrem_3by2.proof_of_decodes (hdec : udivrem_3by2.decodes) : udivrem_3by2.spec :=
  runsM_of_reach hdec fun base ret _ hr _ x m hx1 hpre => by
    simp only [udivrem_3by2.pre, udivrem_3by2.bufs, Buf] at hpre ⊢
    simp (disch := decide) only [Regs.eq_get x] at hpre hx1 ⊢
    subst hx1
    refine Reach.start ?_
    rv_exec
    all_goals
      rv_val
      simp only [update_aligned hr]
      refine Reach.refl ?_
      have hs := div3by2BV_spec (x.get 11#5) (x.get 12#5) (x.get 13#5) (x.get 14#5) (x.get 15#5)
        (x.get 16#5) hpre.2.1 hpre.2.2.1 hpre.2.2.2
      simp only [div3by2BV] at hs
      rv_fold hs
      simp only [zopz0zI_u_eq, decide_eq_true_eq, decide_eq_false_iff_not, beq_eq_false_iff_ne,
        ne_eq] at *
      rv_conds
      simp (disch := assumption) only [if_pos, if_neg] at hs
      rv_fold hs
      simp only [udivrem_3by2.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq]
      simp (disch := decide) only [Regs.eq_get x]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp (config := { decide := true }) (disch := first | bv_omega | fail) only [words,
          memWord_memStore_self, memWord_memStore_of_ne, Nat.mul_zero, Nat.add_zero]
        exact hs.1
      · simp (config := { decide := true }) (disch := first | bv_omega | fail) only [words,
          BitVec.add_assoc, BitVec.reduceAdd, memWord_memStore_self, memWord_memStore_of_ne,
          Nat.mul_zero, Nat.add_zero]
        -- The correction recomputes rd0 - d0 and rd1 - d1, which have the names of r0 and the
        -- high word of r: with the names substituted, the words are the same.
        first | exact hs.2 | (simp only [Defn] at *; subst_vars; exact hs.2)
      · simp (disch := first | bv_omega | fail) only [unchangedExcept_memStore,
          unchangedExcept_refl]
      · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte,
          BitVec.ofNat_eq_ofNat]
        simp (disch := decide) only [Regs.eq_get x, and_self]

/-- The zero registers do not satisfy the preconditions: the divisor `d = 2^127` with its
reciprocal `v = 2^64 - 1`. -/
theorem udivrem_3by2.nonvacuous :
    NonVacuous udivrem_3by2_code udivrem_3by2.bufs udivrem_3by2.pre := by
  obtain ⟨S, val, e, -, hw⟩ := envM_exists
  refine ⟨S, val, fun i => if i = 15#5 then 0x8000000000000000#64 else if i = 16#5 then -1#64
    else ramArgs [10] i, e, ?_, ?_⟩
  · simp (config := { decide := true }) only [ramArgs, bufWords, List.forall_mem_cons, and_true,
      udivrem_3by2.bufs]
    repeat' apply And.intro
    all_goals first
      | exact (hw _ (by decide) (by decide) (by decide)).1
      | exact (hw _ (by decide) (by decide) (by decide)).2
      | simp (config := { decide := true }) [udivrem_3by2_code]
  · simp (config := { decide := true }) [Buf, udivrem_3by2.pre]

end IntxRV.Api
