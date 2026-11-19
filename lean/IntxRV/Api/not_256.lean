import IntxRV.Gen.Api
import IntxRV.TacticM
/-!
# `operator~` of `uint256`

The specification, from `include/intx/intx.hpp`:

```cpp
/// The bitwise complement.
/// @post result = 2 ^ N - 1 - self
constexpr uint operator~() const noexcept
```

`not_256.spec` states it for the RV64 machine code of `not_256` in `IntxRV/Api.cpp` (generated in
`IntxRV/Gen/Api.lean`, see `IntxRV/README.md`). `rv_runm` proves that the machine code computes
`List.map` of the complement of the words, and `val_map_not` gives the number.
-/

-- rv_runm evaluates the runs with simp, and passes it lemmas some paths do not use.
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace IntxRV.Api
open IntxRV IntxRV.Gen Intx Intx.Model

theorem not_256.model : RunsM not_256_code not_256.bufs not_256.pre fun x m x' m' =>
    wordList m' (x 10#5) 4 = (wordList m (x 11#5) 4).map (~~~·) ∧
    UnchangedExcept m m' (x 10#5) 32 ∧ ∀ i ∈ calleeSaved, x' i = x i := by
  rv_runm not_256_decodes with not_256_code not_256_prog using [not_256.bufs, not_256.pre, Buf,
    Disjoint, List.map_cons, List.map_nil, UInt64.toBitVec_not]

theorem not_256.proof : not_256.spec :=
  not_256.model.mono (fun _ _ h => h) fun x m x' m' _ ⟨h, hu, hc⟩ => by
    refine ⟨?_, hu, hc⟩
    simp only [← val_wordList, h, val_map_not, length_wordList]

end IntxRV.Api
