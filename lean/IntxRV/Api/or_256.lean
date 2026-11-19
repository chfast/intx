import IntxRV.Gen.Api
import IntxRV.TacticM
/-!
# `operator|` of `uint256`

The specification, from `include/intx/intx.hpp`:

```cpp
/// @post result = x ||| y
friend constexpr uint operator|(const uint& x, const uint& y) noexcept
```

`or_256.spec` states it for the RV64 machine code of `or_256` in `IntxRV/Api.cpp` (generated in
`IntxRV/Gen/Api.lean`, see `IntxRV/README.md`). `rv_runm` proves that the machine code computes
`List.zipWith` of the word operation, and `val_zipWith_or` gives the number.
-/

-- rv_runm evaluates the runs with simp, and passes it lemmas some paths do not use.
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace IntxRV.Api
open IntxRV IntxRV.Gen Intx Intx.Model

theorem or_256.model : RunsM or_256_code or_256.bufs or_256.pre fun x m x' m' =>
    wordList m' (x 10#5) 4 =
      List.zipWith (· ||| ·) (wordList m (x 11#5) 4) (wordList m (x 12#5) 4) ∧
    UnchangedExcept m m' (x 10#5) 32 ∧ ∀ i ∈ calleeSaved, x' i = x i := by
  rv_runm or_256_decodes with or_256_code or_256_prog using [or_256.bufs, or_256.pre, Buf,
    Disjoint]

theorem or_256.proof : or_256.spec :=
  or_256.model.mono (fun _ _ h => h) fun x m x' m' _ ⟨h, hu, hc⟩ => by
    refine ⟨?_, hu, hc⟩
    simp only [← val_wordList, h]
    exact val_zipWith_or _ _ (by simp only [length_wordList])

end IntxRV.Api
