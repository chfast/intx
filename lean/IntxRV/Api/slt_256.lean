import IntxRV.Gen.Api.slt_256
import IntxRV.TacticM
/-!
# `slt()` of `uint256`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Signed less than comparison.
///
/// Interprets the arguments as two's complement signed integers
/// and checks the "less than" relation.
/// @post result ↔ signed N x < signed N y
template <unsigned N>
constexpr bool slt(const uint<N>& x, const uint<N>& y) noexcept
```

`slt_256.spec` states it for the RV64 machine code of `slt_256` in `IntxRV/Api.cpp` (generated in
`IntxRV/Gen/Api/`, see `IntxRV/README.md`). The code has no branches: the `xor` of the top words
and `slti` tell whether the signs differ (`itypeVal_slti_zero`, `sign_xor`), and this flips the
unsigned comparison. `rv_runm` runs the machine code on symbolic words, splits the paths at the
branches and proves the specification on each path.
-/

-- rv_runm evaluates the runs with simp, and passes it lemmas some paths do not use.
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace IntxRV.Api
open IntxRV IntxRV.Gen Intx Intx.Model

theorem slt_256.proof_of_decodes (hdec : slt_256.decodes) : slt_256.spec := by
  rv_runm hdec with slt_256_code slt_256_prog using [slt_256.bufs, slt_256.pre,
    slt_256.post, Buf] finish [signed, itypeVal_slti_zero]

end IntxRV.Api
