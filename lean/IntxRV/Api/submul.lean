import IntxRV.Gen.Api
import IntxRV.Loop
import IntxRV.Arith
import IntxRV.EnvM
import IntxRV.Call
import IntxRV.DivWords
/-!
# `internal::submul()`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Subtract y multiplied by multiplier from x as: x[] -= multiplier * y[].
/// @pre 0 < y.size()
/// @pre x.size() = y.size()
/// @post x + multiplier * y = old(x) + result * 2^(64 * y.size())
constexpr uint64_t submul(uint64_t x[], std::span<const uint64_t> y, uint64_t multiplier) noexcept
```

`submul.spec` states it for the RV64 machine code of `submul` in `IntxRV/Api.cpp` (generated in
`IntxRV/Gen/Api.lean`, see `IntxRV/README.md`). The code is a loop over the words: the product of
the word of y by the multiplier and the high word of the previous product (`mul`, `mulhu` and the
carry of `add`), its subtraction with the borrow from the word of x, and the store. `Reach.loop`
runs it with the invariant `submulLoop`: the words of x below the word `i` and the words of y and
x that it read, with the high word and the borrow of the next word. The other functions call it
through `submul.reach`, which holds at any address.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
-- The goals of the start of the loop take different simp calls.
set_option linter.unusedTactic false

namespace IntxRV.Api
open IntxRV IntxRV.Gen

/-- One word of `submul()`: the sum of the words after `i + 1` words from the sum after `i` words,
the product of the word `wy` by `M` (`t0`, `hi`), its sum with the high word `k` (`t1`, carry `c`)
and the subtraction from the word `wx` (`r`, borrow `b'`). -/
theorem submul_step {R X Y M k b wx wy t0 hi t1 c k' r b' P : Nat}
    (hm : t0 + 2 ^ 64 * hi = wy * M) (hc : t1 + 2 ^ 64 * c = t0 + k) (hk : k' = c + hi)
    (hs : r + t1 + b = wx + 2 ^ 64 * b') (hinv : R + M * Y = X + (k + b) * P) :
    R + P * r + M * (Y + P * wy) = X + P * wx + (k' + b') * (P * 2 ^ 64) := by
  have h : k + b + r + M * wy = wx + 2 ^ 64 * (k' + b') := by
    subst hk; rw [Nat.mul_comm M wy]; omega
  calc R + P * r + M * (Y + P * wy) = (R + M * Y) + P * (r + M * wy) := by ring
    _ = X + P * (k + b + r + M * wy) := by rw [hinv]; ring
    _ = _ := by rw [h]; ring

/-- The high word of `submul()` fits in a word: `S * P = R + M * Y - X` with `R`, `Y` below `P`. -/
theorem submul_high_lt {R X Y M S P : Nat} (hR : R < P) (hY : Y < P) (hM : M < 2 ^ 64)
    (h : R + M * Y = X + S * P) : S < 2 ^ 64 := by
  by_contra hS
  have h1 : 2 ^ 64 * P ≤ S * P := Nat.mul_le_mul_right _ (by omega)
  have h2 : M * Y ≤ (2 ^ 64 - 1) * P := Nat.mul_le_mul (by omega) hY.le
  omega

/-- The registers and the memory at the head of the loop of `submul()` after `i` of the `n` words
of y at a1 subtracted, multiplied by a3, from the words of x at a0: the pointers a0 and a1 at the
word `i`, the end of x in a2, the high word of the product in a4 and the borrow in a5. -/
def submulLoop (x : Regs) (m : Mem) (k : Nat) (x' : Regs) (m' : Mem) : Prop :=
  ∃ i, i < (x.get 12#5).toNat ∧ k = (x.get 12#5).toNat - i ∧
    x'.get 10#5 = x.get 10#5 + BitVec.ofNat 64 (8 * i) ∧
    x'.get 11#5 = x.get 11#5 + BitVec.ofNat 64 (8 * i) ∧
    x'.get 12#5 = x.get 10#5 + BitVec.ofNat 64 (8 * (x.get 12#5).toNat) ∧
    x'.get 13#5 = x.get 13#5 ∧ x'.get 1#5 = x.get 1#5 ∧ (x'.get 15#5).toNat ≤ 1 ∧
    words m' (x.get 10#5) i + (x.get 13#5).toNat * words m (x.get 11#5) i =
      words m (x.get 10#5) i + ((x'.get 14#5).toNat + (x'.get 15#5).toNat) * 2 ^ (64 * i) ∧
    UnchangedExcept m m' (x.get 10#5) (8 * i) ∧
    ∀ r ∈ calleeSaved, x' r = x r

/-- The run from the start of the code to the return address in ra. -/
theorem submul.reach (base : BitVec 64) (x : Regs) (m : Mem) (hr : x.get 1#5 &&& 3 = 0)
    (hpre : submul.pre x m) :
    Reach (submul.bufs x) submul_prog base (pcAt base 0) x m (x.get 1#5) (submul.post x m) := by
  have hpre' := hpre
  simp only [submul.pre, Buf, Disjoint] at hpre'
  simp (disch := decide) only [Regs.eq_get x] at hpre'
  obtain ⟨⟨hxa, hxn⟩, ⟨hya, hyn⟩, hdis, hn0⟩ := hpre'
  simp only [submul.bufs]
  simp (disch := decide) only [Regs.eq_get x]
  rv_exec_cut 4
  rename_i w1 hw1 w2 hw2
  unfold Defn at hw1 hw2
  subst hw1 hw2
  rw [show (0#5 : BitVec 5) = 0 from rfl, Regs.get_zero]
  have hsh : x.get 12#5 <<< 3 = BitVec.ofNat 64 (8 * (x.get 12#5).toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    congr 1; ring
  refine Reach.loop (submulLoop x m) ?_ (x.get 12#5).toNat _ _
    ⟨0, hn0, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, unchangedExcept_refl _ _ _, ?_⟩
  rotate_left
  all_goals try (simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, hsh]; done)
  all_goals try (simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, hsh]; simp; done)
  all_goals try (simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, words]; simp; done)
  all_goals try (intro r hr
                 simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
                 rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                   rfl | rfl | rfl <;>
                 simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte]; done)
  intro k x' m' ⟨i, hi, hk, h10, h11, h12, h13, h1, h15, hw, hun, hcs⟩ ih
  subst hk
  have hi8 : 8 * i < 2 ^ 64 := by omega
  have hx8 : (x.get 10#5 + BitVec.ofNat 64 (8 * i)).toNat = (x.get 10#5).toNat + 8 * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi8]; omega
  have hy8 : (x.get 11#5 + BitVec.ofNat 64 (8 * i)).toNat = (x.get 11#5).toNat + 8 * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi8]; omega
  -- y[i]
  refine Reach.step (by decide) rfl ?_
  simp only [StepGoal, Nat.reduceAdd, BitVec.reduceSignExtend, BitVec.add_zero]
  refine ⟨by rw [h11]; exact List.mem_append_left _ (mem_bufWords hi), fun wy hwy => ?_⟩
  -- x[i]
  refine Reach.step (by decide) rfl ?_
  simp only [StepGoal, Nat.reduceAdd, BitVec.reduceSignExtend, BitVec.add_zero]
  rv_val
  refine ⟨by rw [h10]; exact List.mem_append_right _ (mem_bufWords hi), fun wx hwx => ?_⟩
  rv_exec_cut 4
  rename_i t0 ht0 ph hph t1 ht1 c hc k' hk' d hd e he r hr' f hf
  -- The word of the product, its sum with the high word and the words read.
  have hm := defn_mul_mulhu ht0 hph
  have hcar := defn_carry_left ht1 hc
  have hkn : k'.toNat = c.toNat + ph.toNat :=
    defn_add_exact hk' (by have := defn_mulhu_le hph; have := defn_bit hc; omega)
  have hwy' : wy = memWord m (x.get 11#5 + BitVec.ofNat 64 (8 * i)).toNat := by
    rw [hwy.eq, h11, memWord_of_unchangedExcept hun _ (by rw [hy8]; omega)]
  have hwx' : wx = memWord m (x.get 10#5 + BitVec.ofNat 64 (8 * i)).toNat := by
    rw [hwx.eq, h10, memWord_of_unchangedExcept hun _ (by rw [hx8]; omega)]
  rw [h13] at hm
  -- The words after the store of x[i].
  have hR : ∀ v : BitVec 64, words (memStore m' (x'.get 10#5).toNat v) (x.get 10#5) (i + 1) =
      words m' (x.get 10#5) i + 2 ^ (64 * i) * v.toNat := by
    intro v
    rw [words_succ_top, words_memStore_of_disjoint _ _ _ _ _ (by omega) (by rw [h10, hx8]; omega),
      h10, memWord_memStore_self]
  have hun' : ∀ v : BitVec 64, UnchangedExcept m (memStore m' (x'.get 10#5).toNat v)
      (x.get 10#5) (8 * (i + 1)) := by
    intro v
    rw [unchangedExcept_memStore _ _ (by rw [h10, hx8]; omega)]
    exact fun k hk => hun k (by omega)
  have hp8 : ∀ a : BitVec 64, a + BitVec.ofNat 64 (8 * i) + 8#64 =
      a + BitVec.ofNat 64 (8 * (i + 1)) := by
    intro a
    rw [BitVec.add_assoc]; congr 1
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  -- The sum of the words after the word i, with the borrow b' of its subtraction.
  have hnext : ∀ b', Defn b' (e ||| f) → b'.toNat ≤ 1 ∧
      words (memStore m' (x'.get 10#5).toNat r) (x.get 10#5) (i + 1) +
        (x.get 13#5).toNat * words m (x.get 11#5) (i + 1) =
      words m (x.get 10#5) (i + 1) + (k'.toNat + b'.toNat) * 2 ^ (64 * (i + 1)) := by
    intro b' hb'
    have hs := defn_sub_borrow hd he hr' hf hb' h15
    refine ⟨hs.2, ?_⟩
    rw [hR, words_succ_top m i (x.get 11#5), words_succ_top m i (x.get 10#5), ← hwy', ← hwx',
      show 64 * (i + 1) = 64 * i + 64 by ring, pow_add]
    exact submul_step hm hcar hkn hs.1 hw
  -- The store of x[i].
  refine Reach.step (by decide) rfl ?_
  simp only [StepGoal, Nat.reduceAdd, BitVec.reduceSignExtend, BitVec.add_zero]
  rv_val
  refine ⟨by rw [h10]; exact List.mem_append_right _ (mem_bufWords hi), ?_⟩
  rv_exec_cut 4
  · -- The next word.
    rename_i b' hb' hb
    obtain ⟨hb1, hwords⟩ := hnext b' hb'
    have hi1 : i + 1 < (x.get 12#5).toNat := by
      rcases Nat.lt_or_ge (i + 1) (x.get 12#5).toNat with h | h
      · exact h
      · exfalso; apply hb
        rw [h10, h12, hp8, show i + 1 = (x.get 12#5).toNat by omega]
    refine ih ((x.get 12#5).toNat - (i + 1)) (by omega) _ _ ?_
    refine ⟨i + 1, hi1, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hun' r, ?_⟩
    all_goals try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    · rw [h10, hp8]
    · rw [h11, hp8]
    · exact h12
    · exact h13
    · exact h1
    · exact hb1
    · exact hwords
    · intro rr hrr
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hrr
      rcases hrr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;>
      simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] <;>
      exact hcs _ (by decide)
  · -- The last word: the return.
    rename_i b' hb' hb res hres
    obtain ⟨hb1, hwords⟩ := hnext b' hb'
    have hin : i + 1 = (x.get 12#5).toNat := by
      have := congrArg BitVec.toNat hb
      rw [h10, h12] at this
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
      omega
    have hres' : res.toNat = k'.toNat + b'.toNat := by
      refine defn_add_exact hres ?_
      rw [hin] at hwords
      exact submul_high_lt (words_lt _ _ _) (words_lt _ _ _) (x.get 13#5).isLt hwords
    simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, h1,
      BitVec.reduceSignExtend, BitVec.add_zero, update_aligned hr]
    refine Reach.refl ?_
    simp only [submul.post]
    simp (disch := decide) only [Regs.eq_get x]
    refine ⟨?_, ?_, ?_⟩
    · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
      rw [hres', ← hin]
      exact hwords
    · rw [← hin]; exact hun' r
    · intro rr hrr
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hrr
      rcases hrr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;>
      simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte] <;>
      exact hcs _ (by decide)

theorem submul.proof : submul.spec := by
  apply runsM_of_reach submul_decodes
  intro base ret _ hr _ x m hx1 hpre
  have hx : x.get 1#5 = ret := by rw [← Regs.eq_get x (by decide)]; exact hx1
  have h := submul.reach base x m (hx ▸ hr) hpre
  rwa [pcAt_zero, hx] at h

/-- The assumptions hold for 1 word: the arguments 0 have no words. -/
theorem submul.nonvacuous : NonVacuous submul_code submul.bufs submul.pre := by
  obtain ⟨S, val, e, -, hw⟩ := envM_exists
  refine ⟨S, val, fun i => if i = 12#5 then 1#64 else ramArgs [10, 11] i, e, ?_, ?_⟩
  · simp (config := { decide := true }) only [submul.bufs, ↓reduceIte, BitVec.toNat_ofNat,
      Nat.reducePow, Nat.reduceMod, bufWords, List.cons_append, List.nil_append,
      List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    repeat' apply And.intro
    all_goals first
      | exact (hw _ (by decide) (by decide) (by decide)).1
      | exact (hw _ (by decide) (by decide) (by decide)).2
  · simp (config := { decide := true }) [Buf, Disjoint, submul.pre]

end IntxRV.Api
