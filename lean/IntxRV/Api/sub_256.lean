import IntxRV.Gen.Api.sub_256
import IntxRV.TacticM
/-!
# `operator-` of `uint256`

The specification, from `include/intx/intx.hpp`:

```cpp
/// The difference modulo 2^N.
/// @post result = (x + 2^N - y) % 2^N
friend constexpr uint operator-(const uint& x, const uint& y) noexcept
```

`sub_256.spec` states it for the RV64 machine code of `sub_256` in `IntxRV/Api.cpp` (generated in
`IntxRV/Gen/Api/`, see `IntxRV/README.md`). `rv_runm` proves that the machine code computes the
model `sub4`, the chain of `subc()` (`IntxRV/ApiModel.lean`), and the specification follows from
`sub4_spec`.
-/

-- rv_runm evaluates the runs with simp, and passes it lemmas some paths do not use.
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace IntxRV.Api
open IntxRV IntxRV.Gen Intx Intx.Model

theorem sub_256.model (hdec : sub_256.decodes) :
    RunsM sub_256_code sub_256.bufs sub_256.pre fun x m x' m' =>
      wordList m' (x 10#5) 4 = sub4 (wordList m (x 11#5) 4) (wordList m (x 12#5) 4) ∧
      UnchangedExcept m m' (x 10#5) 32 ∧ ∀ i ∈ calleeSaved, x' i = x i := by
  rv_runm hdec with sub_256_code sub_256_prog using [sub_256.bufs, sub_256.pre, Buf,
    Disjoint, sub4]

theorem sub_256.proof_of_decodes (hdec : sub_256.decodes) : sub_256.spec :=
  (sub_256.model hdec).mono (fun _ _ h => h) fun x m x' m' _ ⟨h, hu, hc⟩ => by
    refine ⟨?_, hu, hc⟩
    simp only [← val_wordList, h]
    simpa only [wordList] using sub4_spec ..

end IntxRV.Api
