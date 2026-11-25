import IntxRV.Gen.Api.ne_256
import IntxRV.TacticM
/-!
# `operator!=` of `uint256`

The specification, from `include/intx/intx.hpp`:

```cpp
/// @post result ↔ x = y
friend constexpr bool operator==(const uint& x, const uint& y) noexcept
```

`ne_256.spec` states it for the RV64 machine code of `ne_256` in `IntxRV/Api.cpp` (generated in
`IntxRV/Gen/Api/`, see `IntxRV/README.md`). C++20 rewrites `x != y` to `!(x == y)`, so the
specification is the one of `operator==` with the result negated. `rv_runm` runs the machine code on
symbolic words, splits the paths at the branches and proves the specification on each path.
-/

-- rv_runm evaluates the runs with simp, and passes it lemmas some paths do not use.
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace IntxRV.Api
open IntxRV IntxRV.Gen Intx Intx.Model

theorem ne_256.proof_of_decodes (hdec : ne_256.decodes) : ne_256.spec := by
  rv_runm hdec with ne_256_code ne_256_prog using [ne_256.bufs, ne_256.pre,
    ne_256.post, Buf]

end IntxRV.Api
