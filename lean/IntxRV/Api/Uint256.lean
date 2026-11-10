import IntxRV.Gen.Api
import IntxRV.TacticM
/-!
# The proofs of the uint256 operators

`operator+` and `operator-` are proved through their models `add4` and `sub4` (the chains of
`addc()` and `subc()` of `Intx.Model`): `rv_runm` proves that the machine code computes the
model, and the specification follows from `add4_spec` and `sub4_spec`; the bitwise operators
likewise through `List.zipWith` of the word operation. The comparisons are proved from their
specifications directly.
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

theorem ne_256.proof : ne_256.spec := by
  rv_runm ne_256_decodes with ne_256_code ne_256_prog using [ne_256.bufs, ne_256.pre,
    ne_256.post, Buf]

theorem not_256.model : RunsM not_256_code not_256.bufs not_256.pre fun x m x' m' =>
    wordList m' (x 10#5) 4 = (wordList m (x 11#5) 4).map (~~~·) ∧
    UnchangedExcept m m' (x 10#5) 32 ∧ ∀ i ∈ calleeSaved, x' i = x i := by
  rv_runm not_256_decodes with not_256_code not_256_prog using [not_256.bufs, not_256.pre, Buf,
    Disjoint, List.map_cons, List.map_nil, UInt64.toBitVec_not]

theorem not_256.proof : not_256.spec :=
  not_256.model.mono (fun _ _ h => h) fun x m x' m' _ ⟨h, hu, hc⟩ => by
    refine ⟨?_, hu, hc⟩
    simp only [← val_wordList, h, val_map_not, length_wordList]

theorem lt_256.proof : lt_256.spec := by
  rv_runm lt_256_decodes with lt_256_code lt_256_prog using [lt_256.bufs, lt_256.pre,
    lt_256.post, Buf]

theorem or_256.model : RunsM or_256_code or_256.bufs or_256.pre fun x m x' m' =>
    wordList m' (x 10#5) 4 =
      List.zipWith (· ||| ·) (wordList m (x 11#5) 4) (wordList m (x 12#5) 4) ∧
    UnchangedExcept m m' (x 10#5) 32 ∧ ∀ i ∈ calleeSaved, x' i = x i := by
  rv_runm or_256_decodes with or_256_code or_256_prog using [or_256.bufs, or_256.pre, Buf,
    Disjoint]

theorem or_256.proof : or_256.spec :=
  or_256.model.mono (fun _ _ h => h) fun x m x' m' _ ⟨h, hu, hc⟩ => by
    refine ⟨?_, hu, hc⟩
    simp only [← val_wordList, h]
    exact val_zipWith_or _ _ (by simp only [length_wordList])

theorem and_256.model : RunsM and_256_code and_256.bufs and_256.pre fun x m x' m' =>
    wordList m' (x 10#5) 4 =
      List.zipWith (· &&& ·) (wordList m (x 11#5) 4) (wordList m (x 12#5) 4) ∧
    UnchangedExcept m m' (x 10#5) 32 ∧ ∀ i ∈ calleeSaved, x' i = x i := by
  rv_runm and_256_decodes with and_256_code and_256_prog using [and_256.bufs, and_256.pre, Buf,
    Disjoint]

theorem and_256.proof : and_256.spec :=
  and_256.model.mono (fun _ _ h => h) fun x m x' m' _ ⟨h, hu, hc⟩ => by
    refine ⟨?_, hu, hc⟩
    simp only [← val_wordList, h]
    exact val_zipWith_and _ _ (by simp only [length_wordList])

theorem xor_256.model : RunsM xor_256_code xor_256.bufs xor_256.pre fun x m x' m' =>
    wordList m' (x 10#5) 4 =
      List.zipWith (· ^^^ ·) (wordList m (x 11#5) 4) (wordList m (x 12#5) 4) ∧
    UnchangedExcept m m' (x 10#5) 32 ∧ ∀ i ∈ calleeSaved, x' i = x i := by
  rv_runm xor_256_decodes with xor_256_code xor_256_prog using [xor_256.bufs, xor_256.pre, Buf,
    Disjoint]

theorem xor_256.proof : xor_256.spec :=
  xor_256.model.mono (fun _ _ h => h) fun x m x' m' _ ⟨h, hu, hc⟩ => by
    refine ⟨?_, hu, hc⟩
    simp only [← val_wordList, h]
    exact val_zipWith_xor _ _ (by simp only [length_wordList])

theorem gt_256.proof : gt_256.spec := by
  rv_runm gt_256_decodes with gt_256_code gt_256_prog using [gt_256.bufs, gt_256.pre,
    gt_256.post, Buf]

theorem ge_256.proof : ge_256.spec := by
  rv_runm ge_256_decodes with ge_256_code ge_256_prog using [ge_256.bufs, ge_256.pre,
    ge_256.post, Buf]

theorem le_256.proof : le_256.spec := by
  rv_runm le_256_decodes with le_256_code le_256_prog using [le_256.bufs, le_256.pre,
    le_256.post, Buf]

theorem slt_256.proof : slt_256.spec := by
  rv_runm slt_256_decodes with slt_256_code slt_256_prog using [slt_256.bufs, slt_256.pre,
    slt_256.post, Buf] finish [signed]

end IntxRV.Api
