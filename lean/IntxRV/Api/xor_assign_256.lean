import IntxRV.Gen.Api.xor_assign_256
import IntxRV.TacticM
/-!
# `operator^=` of `uint256`

The specification, from `include/intx/intx.hpp`:

```cpp
/// The bitwise exclusive or with y.
/// @post self = old(self) ^^^ y
/// @note FV: not proved for x ^= x.
constexpr uint& operator^=(const uint& y) noexcept { return *this = *this ^ y; }
```

`xor_assign_256.spec` states it for the RV64 machine code of `xor_assign_256` in `IntxRV/Api.cpp`
(generated in `IntxRV/Gen/Api/`, see `IntxRV/README.md`). The object is the written buffer at a0
and y the argument at a1. As for `operator^` (`IntxRV/Api/xor_256.lean`), `rv_runm` proves that the
machine code computes `List.zipWith` of the word operation, and `val_zipWith_xor` gives the number.
-/

-- rv_runm evaluates the runs with simp, and passes it lemmas some paths do not use.
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace IntxRV.Api
open IntxRV IntxRV.Gen Intx Intx.Model

theorem xor_assign_256.model (hdec : xor_assign_256.decodes) :
    RunsM xor_assign_256_code xor_assign_256.bufs xor_assign_256.pre fun x m x' m' =>
      wordList m' (x 10#5) 4 =
        List.zipWith (· ^^^ ·) (wordList m (x 10#5) 4) (wordList m (x 11#5) 4) ∧
      UnchangedExcept m m' (x 10#5) 32 ∧ ∀ i ∈ calleeSaved, x' i = x i := by
  rv_runm hdec with xor_assign_256_code xor_assign_256_prog using
    [xor_assign_256.bufs, xor_assign_256.pre, Buf, Disjoint]

theorem xor_assign_256.proof_of_decodes (hdec : xor_assign_256.decodes) : xor_assign_256.spec :=
  (xor_assign_256.model hdec).mono (fun _ _ h => h) fun x m x' m' _ ⟨h, hu, hc⟩ => by
    refine ⟨?_, hu, hc⟩
    simp only [← val_wordList, h]
    exact val_zipWith_xor _ _ (by simp only [length_wordList])

end IntxRV.Api
