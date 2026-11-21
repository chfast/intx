import IntxRV.Div256By1
import IntxRV.Div256By2
/-!
# `udivrem()` of `uint256` by `uint256`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Divides u by v. A division by 0 gives 0 as the quotient and the remainder.
/// @post result.quot = u / v
/// @post result.rem = if v = 0 then 0 else u % v
template <unsigned M, unsigned N>
constexpr div_result<uint<M>, uint<N>> udivrem(const uint<M>& u, const uint<N>& v) noexcept
```

`udivrem_256.spec` states it for the RV64 machine code of `udivrem_256` in `IntxRV/Api.cpp`. The
function saves ra and s0 in a frame of 16 bytes and dispatches on the significant words: it calls
`udivrem_top1<3>()` if v[3] ≠ 0 (`u256_top13`), `udivrem_top1<2>()` or `udivrem_top2<3>()` by
u[3] < v[2] if v[2] ≠ 0 (`u256_top12`, `u256_top23`). For a divisor of n ≤ 2 words it counts the
significant words m of u and returns 0 and u if m < n, or m = n with u[m - 1] < v[n - 1]
(`u256_ult`). Otherwise it zeroes the result and calls `udivrem_by2()` with max(m, 3) words of u
(`u256_by2`) or `udivrem_by1()` with max(m, 2) words (`u256_by1`), unless v = 0 (`u256_vzero`).
Each callee runs by its proof for the immediates of the address of the table in this image
(`Reach.call_sub`), and all the paths end in the epilogue at 0x1c (`u256_epi`). The lemmas are in
`IntxRV/Div256.lean`, `IntxRV/Div256By2.lean` and `IntxRV/Div256By1.lean`.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false





theorem udivrem_256.proof : udivrem_256.spec := by
  apply runsI_of_reach udivrem_256_image_decodes
  intro base ret hb hr _ _ hw x m hx1 hbufs hhold hpre
  rw [show udivrem_256_image_dataOff = 5272 from rfl] at hw hhold hbufs ⊢
  rw [show udivrem_256_image_data.length = 256 from rfl] at hw hbufs ⊢
  have hb3 : base &&& 3 = 0 := by
    have := congrArg (· &&& 3#64) hb
    simpa [BitVec.and_assoc] using this
  have hx : x.get 1#5 = ret := by rw [← Regs.eq_get x (by decide)]; exact hx1
  have hr' : x.get 1#5 &&& 3 = 0 := hx ▸ hr
  have hpre0 := hpre
  simp only [udivrem_256.pre, Buf] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hua, hun⟩, ⟨hva, hvn⟩, hdru, hdrv, ⟨hsa, hsn⟩, hdsu, hdsv, hdsr⟩ := hpre
  have hTr := buf_outside (x 10#5) base 8 5272 (8 * 256) (by norm_num)
    (hbufs _ (List.mem_append_left _ (List.mem_append_right _ (mem_bufWords_zero (by norm_num)))))
    (hbufs _ (List.mem_append_left _ (List.mem_append_right _ (mem_bufWords (by norm_num)))))
    (by rw [Regs.eq_get x (by decide)]; exact hrn) (by norm_num)
  have hTs := buf_outside (x 2#5 - 48#64) base 6 5272 (8 * 256) (by norm_num)
    (hbufs _ (List.mem_append_right _ (mem_bufWords_zero (by norm_num))))
    (hbufs _ (List.mem_append_right _ (mem_bufWords (by norm_num))))
    (by rw [Regs.eq_get x (by decide)]; exact hsn) (by norm_num)
  rw [Regs.eq_get x (by decide)] at hTr hTs
  simp only [Disjoint] at hdru hdrv hdsu hdsv hdsr
  simp only [udivrem_256.bufs]
  simp (disch := decide) only [Regs.eq_get x]
  rw [show udivrem_256_entry = 0 from rfl, dataWords, ← hx]
  generalize hDe : bufWords (base + BitVec.ofNat 64 5272) 256 = D
  have hD : ∀ a ∈ bufWords (base + BitVec.ofNat 64 5272) 256, a ∈ D := fun _ h => hDe ▸ h
  clear hDe
  have hTr' : (x.get 10#5).toNat + 64 ≤ base.toNat ∨
      base.toNat + 5272 + 8 * 256 ≤ (x.get 10#5).toNat := by omega
  have hTs' : (x.get 2#5 - 48#64).toNat + 48 ≤ base.toNat ∨
      base.toNat + 5272 + 8 * 256 ≤ (x.get 2#5 - 48#64).toNat := by omega
  clear hTr hTs
  rv_exec_cut 5 15 25 39
  all_goals
    try simp only [Defn] at *
    try subst_vars
  -- The load of v[n - 1] for n = 1 or 2 by v[1], and the paths to the calls and returns.
  all_goals first
    | (rv_not_at 39; skip)
    | (by_cases hv1 : memWord m (x.get 12#5 + 8#64).toNat = 0#64
       all_goals
         simp (disch := assumption) only [ite_zero_lt_of_ne, ite_zero_lt_of_eq, BitVec.reduceAdd]
         refine Reach.step (by decide) rfl ?_
         simp only [StepGoal, Nat.reduceAdd]
         rv_val
         first
           | rw [show 16#64 + (x.get 12#5 + 18446744073709551608#64) = x.get 12#5 + 8#64 by
               bv_omega]
           | rw [show 8#64 + (x.get 12#5 + 18446744073709551608#64) = x.get 12#5 by bv_omega]
         refine ⟨by rv_mem, fun wv hwv => ?_⟩
         rv_exec_cut 45 66 81 99)
  all_goals
    try simp only [Defn] at *
    try subst_vars
    try simp only [zopz0zKzJ_u_eq, decide_eq_true_eq, decide_eq_false_iff_not, BitVec.not_le] at *
    try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte,
      BitVec.reduceSignExtend, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero]
  -- The paths that the branch conditions exclude.
  all_goals try contradiction
  all_goals first
    | (rv_not_at 5; skip)
    | (refine u256_top13 base x m hb3 hr' hpre0 hw hTs' hhold hD _ ?_ ?_ ?_ ?_ ?_ ?_
       u256_regs)
  all_goals first
    | (rv_not_at 15; skip)
    | (refine u256_top12 base x m hb3 hr' hpre0 hw hTs' hhold hD _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
       u256_regs)
  all_goals first
    | (rv_not_at 25; skip)
    | (refine u256_top23 base x m hb3 hr' hpre0 hw hTs' hhold hD _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
       u256_regs)
  all_goals first
    | (rv_not_at 45; skip)
    | (refine u256_by2 base x m hb3 hr' hpre0 hw hTr' hTs' hhold hD _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
         ?_ ?_
       u256_regs)
  all_goals first
    | (rv_not_at 81; skip)
    | (refine u256_by1 base x m hb3 hr' hpre0 hw hTr' hhold hTs' hD _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
         ?_ ?_ ?_
       u256_regs)
  all_goals first
    | (rv_not_at 99; skip)
    | (refine u256_vzero base x m hr' hrn hsn hdsr _ ?_ ?_ ?_
         (words4_zero _ _ (by assumption) (by assumption) (by assumption) (by assumption))
       u256_regs)
  -- u < v: m < n, or m = n with u[m - 1] < v[n - 1].
  all_goals first
    | (rv_not_at 66; skip)
    | (split_ifs at * with hc
       all_goals
         simp (config := { decide := true }) only [BitVec.reduceXOr, BitVec.reduceAdd] at *
       all_goals
         refine u256_ult base x m hr' hrn hun hsn hdru hdsu hdsr _ ?_ ?_ ?_ ?_ ?_
       all_goals first
         | u256_regs
         | (rw [words4_unfold, words4_unfold]
            bv_omega))

/-- The registers of the nonvacuous instance: the result, u and v above the data, and the frame
below sp. -/
theorem udivrem_256.nonvacuous :
    NonVacuousI udivrem_256_image_code udivrem_256_image_data udivrem_256_image_dataOff
      udivrem_256.bufs udivrem_256.pre :=
  nonVacuousI_of (fun i => if i = 10#5 then 0x80000C00#64 else if i = 11#5 then 0x80000C40#64
      else if i = 12#5 then 0x80000C60#64 else if i = 2#5 then 0x80000CB0#64 else 0)
    (by decide) (by decide) (by decide) (by decide)
    (by rw [show udivrem_256_image_dataOff = 5272 from rfl,
          show udivrem_256_image_data.length = 256 from rfl]
        simp only [udivrem_256.bufs, ↓reduceIte, BitVec.reduceEq, BitVec.reduceSub, bufWords,
          List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq]
        repeat' apply And.intro
        all_goals decide)
    (fun _ => by simp only [udivrem_256.pre, Buf, Disjoint]; decide)

end IntxRV.Api
