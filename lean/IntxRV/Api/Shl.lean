import IntxRV.Gen.Api
import IntxRV.Arith
import IntxRV.ApiModel
/-!
# The proof of `shl()` of 8 words into 9

`shl<9, 8>` shifts a 512-bit number left by less than 64 bits into 9 words. The function stores the
funnel shifts of the words (`sll`, `srl`) on one path and copies the words for the shift 0 on the
other; `val_shl_words` gives the value from the words, through the model `Intx.Model.shl` and its
proof `shl_spec`.
-/

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000
-- The paths use different lemmas of the same simp calls.
set_option linter.unusedSimpArgs false

namespace IntxRV.Api
open IntxRV IntxRV.Gen

/-- The run from the start of the code to the return address in ra. -/
theorem shl_9_8.reach (base : BitVec 64) (x : Regs) (m : Mem) (hra : x.get 1#5 &&& 3 = 0)
    (hpre : shl_9_8.pre x m) :
    Reach (shl_9_8.bufs x) shl_9_8_prog base (pcAt base 0) x m (x.get 1#5) (shl_9_8.post x m) := by
  simp only [shl_9_8.pre, shl_9_8.bufs, Buf, Disjoint] at hpre ⊢
  simp (disch := decide) only [Regs.eq_get x] at hpre ⊢
  obtain ⟨hbr, hbx, habi, hdis, hsh⟩ := hpre
  have hs : (x.get 12#5).toNat < 64 := by
    have := toNat_of_signExtend habi (by omega); omega
  rw [← toNat_of_signExtend habi (by omega)] at hsh
  rv_exec
  all_goals try rv_val
  all_goals simp only [update_aligned hra]
  all_goals refine Reach.refl ?_
  all_goals simp only [shl_9_8.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  all_goals simp (disch := decide) only [Regs.eq_get x]
  all_goals refine ⟨?_, ?_, ?_⟩
  all_goals try (simp (disch := first | bv_omega | fail) only [unchangedExcept_memStore,
    unchangedExcept_refl]; done)
  all_goals try (simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte,
    BitVec.ofNat_eq_ofNat, and_self, and_true, true_and] <;>
    simp (disch := decide) only [Regs.eq_get x, and_self] <;> done)
  all_goals
    rw [← toNat_of_signExtend habi (by omega), ← val_wordList, ← val_wordList]
    apply val_shl_words _ _ (length_wordList ..) (length_wordList ..) _ hs
    intro i hi
  all_goals simp only [Defn] at *
  all_goals subst_vars
  all_goals interval_cases i
  all_goals simp (config := { decide := true }) (disch := first | bv_omega | fail) only [wordList,
    List.getElem_cons_zero, List.getElem_cons_succ, UInt64.toNat_ofBitVec, BitVec.ofNat_eq_ofNat,
    BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, memWord_memStore_self,
    memWord_memStore_of_ne, ↓reduceIte, Nat.reduceSub, Nat.reduceAdd, BitVec.reduceSetWidth,
    subw_64_toNat _ hs, Nat.mod_eq_of_lt hs, dite_true, dite_false, Nat.lt_irrefl]
  all_goals by_cases hz : x.get 12#5 = 0#64
  all_goals try (simp only [hz, BitVec.ofNat_eq_ofNat, beq_self_eq_true, Bool.true_eq_false,
    not_true_eq_false] at *; done)
  all_goals first
    | (simp only [hz, BitVec.toNat_zero, pow_zero, Nat.mul_one, Nat.sub_zero, BitVec.shiftLeft_zero,
        ↓reduceIte, Nat.mod_eq_of_lt (BitVec.isLt _), Nat.div_eq_of_lt (BitVec.isLt _),
        Nat.add_zero, BitVec.reduceAdd, BitVec.zero_and, BitVec.reduceToNat, Nat.reduceSub,
        Nat.reducePow, Nat.reduceMod, BitVec.toNat_ofNat]; done)
    | (have h0 : 0 < (x.get 12#5).toNat
       · first | bv_omega | fail
       have hk : (64#64 - x.get 12#5).toNat % 64 = 64 - (x.get 12#5).toNat
       · first | bv_omega | fail
       simp only [hk, hz, ↓reduceIte, BitVec.zero_add, mask_all, BitVec.toNat_shiftLeft,
         Nat.shiftLeft_eq, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.zero_mul,
         Nat.zero_mod, Nat.zero_add]
       try rw [BitVec.or_comm, toNat_funnel _ _ _ h0 hs])

theorem shl_9_8.proof : shl_9_8.spec :=
  runsM_of_reach shl_9_8_decodes fun base ret _ hr _ x m hx1 hpre => by
    have hx : x.get 1#5 = ret := by rw [← Regs.eq_get x (by decide)]; exact hx1
    have h := shl_9_8.reach base x m (hx ▸ hr) hpre
    rwa [pcAt_zero, hx] at h

end IntxRV.Api
