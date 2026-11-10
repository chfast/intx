import IntxRV.Gen.Api
import IntxRV.TacticM
/-!
# The proofs of the uint256 operators

`operator+` and `operator-` are proved through their models `add4` and `sub4` (the chains of
`addc()` and `subc()` of `Intx.Model`): `rv_runm` proves that the machine code computes the
model, and the specification follows from `add4_spec` and `sub4_spec`. The comparisons are proved
from their specifications directly.
-/

-- rv_runm evaluates the runs with simp, and passes it lemmas some paths do not use.
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace IntxRV.Api
open IntxRV IntxRV.Gen Intx Intx.Model

theorem add_256.model : RunsM add_256_code add_256.bufs add_256.pre fun x m x' m' =>
    wordList m' (x 10#5) 4 = add4 (wordList m (x 11#5) 4) (wordList m (x 12#5) 4) ∧
    UnchangedExcept m m' (x 10#5) 32 ∧ ∀ i ∈ calleeSaved, x' i = x i := by
  rv_runm add_256_decodes with add_256_code add_256_prog using [add_256.bufs, add_256.pre, Buf,
    Disjoint, add4]

theorem add_256.proof : add_256.spec :=
  add_256.model.mono (fun _ _ h => h) fun x m x' m' _ ⟨h, hu, hc⟩ => by
    refine ⟨?_, hu, hc⟩
    simp only [← val_wordList, h]
    simpa only [wordList] using add4_spec ..

theorem sub_256.model : RunsM sub_256_code sub_256.bufs sub_256.pre fun x m x' m' =>
    wordList m' (x 10#5) 4 = sub4 (wordList m (x 11#5) 4) (wordList m (x 12#5) 4) ∧
    UnchangedExcept m m' (x 10#5) 32 ∧ ∀ i ∈ calleeSaved, x' i = x i := by
  rv_runm sub_256_decodes with sub_256_code sub_256_prog using [sub_256.bufs, sub_256.pre, Buf,
    Disjoint, sub4]

theorem sub_256.proof : sub_256.spec :=
  sub_256.model.mono (fun _ _ h => h) fun x m x' m' _ ⟨h, hu, hc⟩ => by
    refine ⟨?_, hu, hc⟩
    simp only [← val_wordList, h]
    simpa only [wordList] using sub4_spec ..

theorem eq_256.proof : eq_256.spec := by
  rv_runm eq_256_decodes with eq_256_code eq_256_prog using [eq_256.bufs, eq_256.pre,
    eq_256.post, Buf]

theorem lt_256.proof : lt_256.spec := by
  rv_runm lt_256_decodes with lt_256_code lt_256_prog using [lt_256.bufs, lt_256.pre,
    lt_256.post, Buf]

end IntxRV.Api
