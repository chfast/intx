import IntxRV.Arith
/-!
# The negation of 4 words

clang computes `-x` of `uint256`, `uint{} - x`, as `0 - x[i]` for each word, the borrow of the
low word as `x[0] != 0` (`snez`) and the borrows of the next words as in a subtraction from 0:
`neg4_words` gives the number of the result words from the definitions of the values of the run.
It is the negation of `operator-()` (`IntxRV/Api/neg_256.lean`) and the four negations of
`sdivrem()` (`IntxRV/Api/sdivrem_256.lean`).
-/

namespace IntxRV

/-- The words of `-x` modulo 2^256 from the definitions of the run: the low word and its borrow,
the middle words with the borrows as in `defn_sub_borrow` from 0, and the top word. -/
theorem neg4_words {x0 x1 x2 x3 n0 b0 d1 e1 r1 f1 b1 d2 e2 r2 f2 b2 d3 r3 : BitVec 64}
    (hn0 : Defn n0 (0#64 - x0)) (hb0 : Defn b0 (if 0#64 < n0 then 1#64 else 0#64))
    (hd1 : Defn d1 (0#64 - x1)) (he1 : Defn e1 (if 0#64 < d1 then 1#64 else 0#64))
    (hr1 : Defn r1 (d1 - b0)) (hf1 : Defn f1 (if d1 < r1 then 1#64 else 0#64))
    (hb1 : Defn b1 (e1 ||| f1))
    (hd2 : Defn d2 (0#64 - x2)) (he2 : Defn e2 (if 0#64 < d2 then 1#64 else 0#64))
    (hr2 : Defn r2 (d2 - b1)) (hf2 : Defn f2 (if d2 < r2 then 1#64 else 0#64))
    (hb2 : Defn b2 (e2 ||| f2))
    (hd3 : Defn d3 (0#64 - x3)) (hr3 : Defn r3 (d3 - b2)) :
    n0.toNat + 2 ^ 64 * (r1.toNat + 2 ^ 64 * (r2.toNat + 2 ^ 64 * r3.toNat)) =
      (2 ^ 256 - (x0.toNat + 2 ^ 64 * (x1.toNat + 2 ^ 64 * (x2.toNat + 2 ^ 64 * x3.toNat)))) %
        2 ^ 256 := by
  have e0 := defn_sub_borrow0 hn0 hb0
  obtain ⟨e1', l1⟩ := defn_sub_borrow hd1 he1 hr1 hf1 hb1 (defn_bit_le hb0)
  obtain ⟨e2', l2⟩ := defn_sub_borrow hd2 he2 hr2 hf2 hb2 l1
  have e3 : r3.toNat = (2 ^ 64 + 2 ^ 64 - x3.toNat - b2.toNat) % 2 ^ 64 := by
    rw [hr3.eq, hd3.eq, BitVec.toNat_sub, BitVec.toNat_sub]
    have := x3.isLt; have := b2.isLt
    simp only [BitVec.toNat_ofNat, Nat.zero_mod]
    omega
  have := x0.isLt; have := x1.isLt; have := x2.isLt; have := x3.isLt
  have := n0.isLt; have := r1.isLt; have := r2.isLt
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_add] at e0 e1' e2'
  omega

end IntxRV
