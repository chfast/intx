import IntxRV.Gen.Api
import IntxRV.Api.be_store_256
/-!
# `be::store<evmc::bytes32>()` of `uint256`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Stores an SrcT value in .bytes field of type DstT. The .bytes must be an array of uint8_t
/// of the size matching the size of uint.
/// @post bigEndian result.bytes = x
template <typename DstT, typename SrcT>
inline DstT store(const SrcT& x) noexcept
```

`be_store_bytes32.spec` states it for the RV64 machine code of `be_store_bytes32` in
`IntxRV/Api.cpp` (generated in `IntxRV/Gen/Api.lean`, see `IntxRV/README.md`). Its code is the
code of `be::unsafe::store()` of `uint256` (`IntxRV/Api/be_store_256.lean`), with the result at a0
as the buffer of bytes: the specifications are equal, so the proof of that instance proves it.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

theorem be_store_bytes32.proof : be_store_bytes32.spec := be_store_256.proof

end IntxRV.Api
