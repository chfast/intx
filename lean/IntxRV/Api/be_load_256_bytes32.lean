import IntxRV.Gen.Api
import IntxRV.Api.be_load_256_32
/-!
# `be::load<uint256>()` from `evmc::bytes32`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Loads an integer value from the bytes of big-endian order in the .bytes field of t.
/// @post result = bigEndian t.bytes
template <typename IntT, typename T>
inline IntT load(const T& t) noexcept
```

`be_load_256_bytes32.spec` states it for the RV64 machine code of the image of `be_load_256_bytes32` in `IntxRV/Api.cpp`
(generated in `IntxRV/Gen/Api.lean`, see `IntxRV/README.md`). Its image is the image of
`be::load<uint256>()` from `uint8_t[32]` (`IntxRV/Api/be_load_256_32.lean`), with the bytes of the
struct as the array: the specifications are equal, so the proofs of that instance prove it.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

theorem be_load_256_bytes32.proof : be_load_256_bytes32.spec := be_load_256_32.proof

theorem be_load_256_bytes32.nonvacuous :
    NonVacuousI be_load_256_bytes32_image_code be_load_256_bytes32_image_data be_load_256_bytes32_image_dataOff
      be_load_256_bytes32.bufs be_load_256_bytes32.pre :=
  be_load_256_32.nonvacuous

end IntxRV.Api
