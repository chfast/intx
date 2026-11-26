import IntxRV.Api.udivrem_256

/-!
# The frame of `/` and `%` of `uint256`

`operator/` and `operator%` of `uint256` save ra and s0 in a frame of 80 bytes, call
`udivrem<256, 256>()` with the result at sp, below the saved registers, and copy the quotient or
the remainder to their result. The lemmas state the words of the arguments after the saves
(`div_frame_words`) and the memory after the call (`div_frame_mem`).
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

/-- The registers `x` with a register set to its value. -/
theorem regs_set_of_get {x : Regs} {i : BitVec 5} {v : BitVec 64} (hi : i ≠ 0)
    (h : x.get i = v) : x.set i v = x := by
  funext j
  rw [Regs.set_apply, if_neg hi]
  split_ifs with hj
  · subst hj; rw [Regs.eq_get x hi, h]
  · rfl

/-- The saved ra and s0 in the frame of 80 bytes keep the words outside the 128 bytes below sp. -/
theorem div_frame_words (m : Mem) (sp ra s0 u : BitVec 64) (hun : u.toNat + 32 ≤ 2 ^ 64)
    (hdsu : (sp - 128#64).toNat + 128 ≤ u.toNat ∨ u.toNat + 32 ≤ (sp - 128#64).toNat)
    (hsn : (sp - 128#64).toNat + 128 ≤ 2 ^ 64) :
    words (memStore (memStore m (sp + 18446744073709551608#64).toNat ra)
      (sp + 18446744073709551600#64).toNat s0) u 4 = words m u 4 := by
  simp (disch := first | bv_omega | fail) only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
    BitVec.reduceAdd, memWord_memStore_of_ne]

/-- The memory after the call of `udivrem<256, 256>()` with the result at sp - 80 and its frame
below: the saved ra and s0, and the bytes outside the result `r` and the 128 bytes below sp. -/
theorem div_frame_mem (m m3 : Mem) (r sp ra s0 : BitVec 64)
    (hrn : r.toNat + 32 ≤ 2 ^ 64) (hsn : (sp - 128#64).toNat + 128 ≤ 2 ^ 64)
    (hdsr : (sp - 128#64).toNat + 128 ≤ r.toNat ∨ r.toNat + 32 ≤ (sp - 128#64).toNat)
    (hunc : UnchangedExcept2 (memStore (memStore m (sp + 18446744073709551608#64).toNat ra)
      (sp + 18446744073709551600#64).toNat s0) m3 (sp + 18446744073709551536#64) 64
      (sp - 128#64) 48) :
    memWord m3 (sp + 18446744073709551608#64).toNat = ra ∧
      memWord m3 (sp + 18446744073709551600#64).toNat = s0 ∧
      UnchangedExcept2 m m3 r 32 (sp - 128#64) 128 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [memWord_of_unchangedExcept2 hunc _ (by bv_omega) (by bv_omega)]
    simp (disch := first | bv_omega | fail) only [memWord_memStore_of_ne, memWord_memStore_self]
  · rw [memWord_of_unchangedExcept2 hunc _ (by bv_omega) (by bv_omega)]
    simp only [memWord_memStore_self]
  · intro k hkr hks
    rw [hunc k (by bv_omega) (by bv_omega)]
    have h0 : UnchangedExcept2 m (memStore (memStore m (sp + 18446744073709551608#64).toNat ra)
        (sp + 18446744073709551600#64).toNat s0) r 32 (sp - 128#64) 128 := by
      simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
      exact unchangedExcept2_refl _ _ _ _ _
    exact h0 k hkr hks

end IntxRV.Api
