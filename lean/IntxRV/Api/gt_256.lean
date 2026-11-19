import IntxRV.Gen.Api
import IntxRV.TacticM
/-!
# `operator>` of `uint256`

The specification, from `include/intx/intx.hpp`:

```cpp
/// @post result <-> x > y
friend constexpr bool operator>(const uint& x, const uint& y) noexcept { return y < x; }
```

`gt_256.spec` states it for the RV64 machine code of `gt_256` in `IntxRV/Api.cpp` (generated in
`IntxRV/Gen/Api.lean`, see `IntxRV/README.md`). `rv_runm` runs the machine code on symbolic words,
splits the paths at the branches and proves the specification on each path.
-/

-- rv_runm evaluates the runs with simp, and passes it lemmas some paths do not use.
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace IntxRV.Api
open IntxRV IntxRV.Gen Intx Intx.Model

theorem gt_256.proof : gt_256.spec := by
  rv_runm gt_256_decodes with gt_256_code gt_256_prog using [gt_256.bufs, gt_256.pre,
    gt_256.post, Buf]

end IntxRV.Api
