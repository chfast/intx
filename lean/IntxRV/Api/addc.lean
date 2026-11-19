import IntxRV.Gen.Api
import IntxRV.Tactic
import Intx.Proofs.Div
/-!
# `addc()`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Addition with carry.
/// @post result.value + 2 ^ 64 * result.carry.toNat = x + y + carry.toNat
constexpr result_with_carry<uint64_t> addc(uint64_t x, uint64_t y, bool carry = false) noexcept
```

`addc.spec` states it for the RV64 machine code of `addc` in `IntxRV/Api.cpp` (generated in
`IntxRV/Gen/Api.lean`, see `IntxRV/README.md`). The `bool` argument and the carry are 0 or 1 in a
register. `rv_run` proves that the machine code computes the model `Intx.Model.addc`, and the
specification follows from its proof `addc_spec`.
-/

-- rv_run evaluates the runs with simp, and passes it lemmas some paths do not use.
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace IntxRV.Api
open IntxRV IntxRV.Gen Intx Intx.Model

/-- With the `bool` argument `c` in a2, the `bool` result is 0 or 1 in a1. -/
theorem addc.model (c : Bool) : Runs addc_code (fun x => x 12#5 = if c then 1 else 0)
    fun x x' =>
      x'.get 10#5 = (Model.addc (.ofBitVec (x 10#5)) (.ofBitVec (x 11#5)) c).1.toBitVec ∧
      x'.get 11#5 = (if (Model.addc (.ofBitVec (x 10#5)) (.ofBitVec (x 11#5)) c).2 then 1 else 0) ∧
      ∀ i ∈ calleeSaved, x' i = x i := by
  rv_run addc_decodes with addc_code addc_prog using [Model.addc]

theorem addc.proof : addc.spec := by
  intro S val e base ret hb hr hl s npc x hs hx hp
  have hc : x 12#5 = if decide (x 12#5 = 1) then 1 else 0 := by
    rcases hp with h | h <;> rw [h] <;> rfl
  obtain ⟨n, s', npc', x', hrun, hs', h0, h1, hcs⟩ :=
    addc.model (decide (x 12#5 = 1)) S val e base ret hb hr hl s npc x hs hx hc
  refine ⟨n, s', npc', x', hrun, hs', ?_, ?_, hcs⟩
  · have := addc_spec (.ofBitVec (x 10#5)) (.ofBitVec (x 11#5)) (decide (x 12#5 = 1))
    rw [h0, h1]
    clear hc hp hcs h0 h1
    split <;> simp_all
  · rw [h1]
    split <;> simp

theorem addc.nonvacuous : ∃ x, addc.pre x := ⟨fun _ => 0, Or.inl rfl⟩

end IntxRV.Api
