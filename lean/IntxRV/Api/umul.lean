import IntxRV.Gen.Api
import IntxRV.Tactic
import Intx.Proofs.Div
/-!
# `umul()` of two words

The specification, from `include/intx/intx.hpp`:

```cpp
/// Full unsigned multiplication 64 x 64 -> 128.
/// @post result = x * y
constexpr uint128 umul(uint64_t x, uint64_t y) noexcept
```

`umul.spec` states it for the RV64 machine code of `umul` in `IntxRV/Api.cpp` (generated in
`IntxRV/Gen/Api.lean`, see `IntxRV/README.md`). `rv_run` proves that the machine code computes the
model `Intx.Model.umul`, and the specification follows from its proof `umul_spec`.
-/

-- rv_run evaluates the runs with simp, and passes it lemmas some paths do not use.
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace IntxRV.Api
open IntxRV IntxRV.Gen Intx Intx.Model

theorem umul.model : Runs umul_code umul.pre fun x x' =>
    x'.get 10#5 = (Model.umul (.ofBitVec (x 10#5)) (.ofBitVec (x 11#5))).lo.toBitVec ∧
    x'.get 11#5 = (Model.umul (.ofBitVec (x 10#5)) (.ofBitVec (x 11#5))).hi.toBitVec ∧
    ∀ i ∈ calleeSaved, x' i = x i := by
  rv_run umul_decodes with umul_code umul_prog using []

theorem umul.proof : umul.spec :=
  umul.model.mono (fun _ h => h) fun x _ _ ⟨h0, h1, hc⟩ =>
    ⟨by simpa [h0, h1] using umul_spec (.ofBitVec (x 10#5)) (.ofBitVec (x 11#5)), hc⟩

end IntxRV.Api
