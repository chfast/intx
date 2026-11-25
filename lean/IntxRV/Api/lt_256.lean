import IntxRV.Gen.Api.lt_256
import IntxRV.TacticM
/-!
# `operator<` of `uint256`

The specification, from `include/intx/intx.hpp`:

```cpp
/// @post result ↔ x < y
friend constexpr bool operator<(const uint& x, const uint& y) noexcept
```

`lt_256.spec` states it for the RV64 machine code of `lt_256` in `IntxRV/Api.cpp` (generated in
`IntxRV/Gen/Api/`, see `IntxRV/README.md`). `rv_runm` runs the machine code on symbolic words,
splits the paths at the branches and proves the specification on each path.
-/

-- rv_runm evaluates the runs with simp, and passes it lemmas some paths do not use.
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace IntxRV.Api
open IntxRV IntxRV.Gen Intx Intx.Model

theorem lt_256.proof_of_decodes (hdec : lt_256.decodes) : lt_256.spec := by
  rv_runm hdec with lt_256_code lt_256_prog using [lt_256.bufs, lt_256.pre,
    lt_256.post, Buf]

end IntxRV.Api
