import IntxRV.Gen.Api.ge_256
import IntxRV.TacticM
/-!
# `operator>=` of `uint256`

The specification, from `include/intx/intx.hpp`:

```cpp
/// @post result ↔ x ≥ y
friend constexpr bool operator>=(const uint& x, const uint& y) noexcept { return !(x < y); }
```

`ge_256.spec` states it for the RV64 machine code of `ge_256` in `IntxRV/Api.cpp` (generated in
`IntxRV/Gen/Api/`, see `IntxRV/README.md`). `rv_runm` runs the machine code on symbolic words,
splits the paths at the branches and proves the specification on each path.
-/

-- rv_runm evaluates the runs with simp, and passes it lemmas some paths do not use.
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace IntxRV.Api
open IntxRV IntxRV.Gen Intx Intx.Model

theorem ge_256.proof_of_decodes (hdec : ge_256.decodes) : ge_256.spec := by
  rv_runm hdec with ge_256_code ge_256_prog using [ge_256.bufs, ge_256.pre,
    ge_256.post, Buf]

end IntxRV.Api
