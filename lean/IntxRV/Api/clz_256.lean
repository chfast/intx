import IntxRV.Gen.Api.clz_256
import IntxRV.Arith
import IntxRV.Image
import IntxRV.Clz
import Mathlib.Tactic.Ring
import IntxRV.Bits
/-!
# `clz()` of `uint256`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Counts the leading zero bits of x.
/// @post result = N - (if x = 0 then 0 else Nat.log2 x + 1)
template <unsigned N>
constexpr unsigned clz(const uint<N>& x) noexcept
```

`clz_256.spec` states it for the RV64 machine code of `clz_256` in `IntxRV/Api.cpp` (generated in
`IntxRV/Gen/Api/`, see `IntxRV/README.md`). The function counts the leading zeros of the top
nonzero word with the SWAR code of `swarClz` (`IntxRV/Clz.lean`). `rv_clz_paths`
(`IntxRV/Bits.lean`) runs the paths; `clz_ite` gives the count of the word and `clz_words4` its
relation to `log2`.
-/

set_option maxRecDepth 100000
-- The paths use different lemmas of the same simp calls.
set_option linter.unusedSimpArgs false

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 4000000 in
theorem clz_256.reach (base : BitVec 64) (x : Regs) (m : Mem) (hra : x.get 1#5 &&& 3 = 0)
    (hpre : clz_256.pre x m) :
    Reach (clz_256.bufs x) clz_256_prog base (pcAt base 0) x m (x.get 1#5)
      (clz_256.post x m) := by
  simp only [clz_256.pre, clz_256.bufs, Buf] at hpre ⊢
  simp (disch := decide) only [Regs.eq_get x] at hpre ⊢
  rv_clz_paths clz_256.post

theorem clz_256.proof_of_decodes (hdec : clz_256.decodes) : clz_256.spec :=
  runsM_of_reach hdec fun base ret _ hr _ x m hx1 hpre => by
    have hx : x.get 1#5 = ret := by rw [← Regs.eq_get x (by decide)]; exact hx1
    have h := clz_256.reach base x m (hx ▸ hr) hpre
    rwa [pcAt_zero, hx] at h

end IntxRV.Api
