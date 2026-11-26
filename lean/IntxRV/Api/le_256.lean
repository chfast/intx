import IntxRV.Gen.Api.le_256
import IntxRV.TacticM
/-!
# `operator<=` of `uint256`

The specification, from `include/intx/intx.hpp`:

```cpp
/// @post result ↔ x ≤ y
friend constexpr bool operator<=(const uint& x, const uint& y) noexcept { return !(y < x); }
```

`le_256.spec` states it for the RV64 machine code of `le_256` in `IntxRV/Api.cpp` (generated in
`IntxRV/Gen/Api/`, see `IntxRV/README.md`). `rv_runm` runs the machine code on symbolic words,
splits the paths at the branches and proves the specification on each path.
-/

-- rv_runm evaluates the runs with simp, and passes it lemmas some paths do not use.
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace IntxRV.Api
open IntxRV IntxRV.Gen Intx Intx.Model

theorem le_256.proof_of_decodes (hdec : le_256.decodes) : le_256.spec := by
  rv_runm hdec with le_256_code le_256_prog using [le_256.bufs, le_256.pre,
    le_256.post, Buf]

end IntxRV.Api
