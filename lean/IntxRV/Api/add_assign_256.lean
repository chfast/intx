import IntxRV.Gen.Api
import IntxRV.TacticM
/-!
# `operator+=` of `uint256`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Adds y modulo 2^N.
/// @post self = (old(self) + y) % 2 ^ N
/// @note FV: not proved for x += x.
constexpr uint& operator+=(const uint& y) noexcept { return *this = *this + y; }
```

`add_assign_256.spec` states it for the RV64 machine code of `add_assign_256` in `IntxRV/Api.cpp`
(generated in `IntxRV/Gen/Api.lean`, see `IntxRV/README.md`). The object is the written buffer at a0
and y the argument at a1. As for `operator+` (`IntxRV/Api/add_256.lean`), `rv_runm` proves that the
machine code computes the model `add4`, the chain of `addc()`, and `add4_spec` gives the number.
-/

-- rv_runm evaluates the runs with simp, and passes it lemmas some paths do not use.
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace IntxRV.Api
open IntxRV IntxRV.Gen Intx Intx.Model

theorem add_assign_256.model :
    RunsM add_assign_256_code add_assign_256.bufs add_assign_256.pre fun x m x' m' =>
      wordList m' (x 10#5) 4 = add4 (wordList m (x 10#5) 4) (wordList m (x 11#5) 4) ∧
      UnchangedExcept m m' (x 10#5) 32 ∧ ∀ i ∈ calleeSaved, x' i = x i := by
  rv_runm add_assign_256_decodes with add_assign_256_code add_assign_256_prog using
    [add_assign_256.bufs, add_assign_256.pre, Buf, Disjoint, add4]

theorem add_assign_256.proof : add_assign_256.spec :=
  add_assign_256.model.mono (fun _ _ h => h) fun x m x' m' _ ⟨h, hu, hc⟩ => by
    refine ⟨?_, hu, hc⟩
    simp only [← val_wordList, h]
    simpa only [wordList] using add4_spec ..

end IntxRV.Api
