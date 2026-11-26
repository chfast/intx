import IntxRV.Gen.Api.count_significant_words_256
import IntxRV.Arith
import IntxRV.Image
import IntxRV.Clz
import Mathlib.Tactic.Ring
import IntxRV.Bits
/-!
# `count_significant_words()` of `uint256`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Counts the words of x up to its highest nonzero word.
/// @post result = if x = 0 then 0 else Nat.log2 x / 64 + 1
template <unsigned N>
constexpr unsigned count_significant_words(const uint<N>& x) noexcept
```

`count_significant_words_256.spec` states it for the RV64 machine code of
`count_significant_words_256` in `IntxRV/Api.cpp` (generated in `IntxRV/Gen/Api/`, see
`IntxRV/README.md`). The function tests the words from the top. `rv_runm` proves the index of the
top nonzero word, and `count_significant_words4` (`IntxRV/Bits.lean`) its relation to `log2`.
-/

set_option maxRecDepth 100000
-- The paths use different lemmas of the same simp calls.
set_option linter.unusedSimpArgs false

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 4000000 in
theorem count_significant_words_256.model (hdec : count_significant_words_256.decodes) :
    RunsM count_significant_words_256_code
      count_significant_words_256.bufs count_significant_words_256.pre fun x m x' m' =>
      x'.get 10#5 = (if memWord m (x 10#5 + 24#64).toNat ≠ 0 then 4#64
        else if memWord m (x 10#5 + 16#64).toNat ≠ 0 then 3#64
        else if memWord m (x 10#5 + 8#64).toNat ≠ 0 then 2#64
        else if memWord m (x 10#5).toNat ≠ 0 then 1#64 else 0#64) ∧
      m' = m ∧ ∀ i ∈ calleeSaved, x' i = x i := by
  rv_runm hdec with count_significant_words_256_code
    count_significant_words_256_prog using [count_significant_words_256.bufs,
    count_significant_words_256.pre, Buf]

theorem count_significant_words_256.proof_of_decodes (hdec : count_significant_words_256.decodes) :
    count_significant_words_256.spec :=
  (count_significant_words_256.model hdec).mono (fun _ _ h => h) fun x m x' m' _ ⟨h, hm, hc⟩ => by
    simp only [count_significant_words_256.post, words, BitVec.add_assoc, BitVec.ofNat_eq_ofNat,
      BitVec.reduceAdd, Nat.mul_zero, Nat.add_zero]
    have h0 := (memWord m (x 10#5).toNat).isLt
    have h1 := (memWord m (x 10#5 + 8#64).toNat).isLt
    have h2 := (memWord m (x 10#5 + 16#64).toNat).isLt
    have h3 := (memWord m (x 10#5 + 24#64).toNat).isLt
    refine ⟨?_, ?_, hm, hc⟩ <;> rw [h]
    all_goals generalize memWord m (x 10#5).toNat = w0 at *
    all_goals generalize memWord m (x 10#5 + 8#64).toNat = w1 at *
    all_goals generalize memWord m (x 10#5 + 16#64).toNat = w2 at *
    all_goals generalize memWord m (x 10#5 + 24#64).toNat = w3 at *
    · rw [count_significant_words4]
      split_ifs <;> rfl
    · split_ifs <;> decide

end IntxRV.Api
