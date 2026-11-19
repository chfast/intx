import IntxRV.Gen.Api
import IntxRV.Arith
import IntxRV.Image
import IntxRV.Clz
import Mathlib.Tactic.Ring
import IntxRV.Bits
/-!
# `bit_width()` of `uint256`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Counts the number of bits needed to represent the value. For 0 returns 0.
/// @post result = if x = 0 then 0 else Nat.log2 x + 1
template <unsigned N>
constexpr unsigned bit_width(const uint<N>& x) noexcept
```

`bit_width_256.spec` states it for the RV64 machine code of `bit_width_256` in `IntxRV/Api.cpp`
(generated in `IntxRV/Gen/Api.lean`, see `IntxRV/README.md`). The function counts the leading zeros
of the top nonzero word with the SWAR code of `swarClz` (`IntxRV/Clz.lean`). `rv_clz_paths`
(`IntxRV/Bits.lean`) runs the paths; `clz_ite` gives the count of the word and `bit_width_words4`
its relation to `log2`.
-/

set_option maxRecDepth 100000
-- The paths use different lemmas of the same simp calls.
set_option linter.unusedSimpArgs false

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 4000000 in
theorem bit_width_256.reach (base : BitVec 64) (x : Regs) (m : Mem) (hra : x.get 1#5 &&& 3 = 0)
    (hpre : bit_width_256.pre x m) :
    Reach (bit_width_256.bufs x) bit_width_256_prog base (pcAt base 0) x m (x.get 1#5)
      (bit_width_256.post x m) := by
  simp only [bit_width_256.pre, bit_width_256.bufs, Buf] at hpre ⊢
  simp (disch := decide) only [Regs.eq_get x] at hpre ⊢
  rv_clz_paths bit_width_256.post

theorem bit_width_256.proof : bit_width_256.spec :=
  runsM_of_reach bit_width_256_decodes fun base ret _ hr _ x m hx1 hpre => by
    have hx : x.get 1#5 = ret := by rw [← Regs.eq_get x (by decide)]; exact hx1
    have h := bit_width_256.reach base x m (hx ▸ hr) hpre
    rwa [pcAt_zero, hx] at h

end IntxRV.Api
