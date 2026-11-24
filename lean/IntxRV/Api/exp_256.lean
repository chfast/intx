import IntxRV.ExpLoop
/-!
# `exp()` of `uint256`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Raises base to the power of exponent modulo 2^N.
/// @post result = base ^ exponent % 2 ^ N
template <unsigned N>
constexpr uint<N> exp(uint<N> base, uint<N> exponent) noexcept
```

`exp_256.spec` states it for the RV64 machine code of `exp_256` in `IntxRV/Api.cpp`. The base and
the exponent by value are the addresses of the copies of the caller, which the code leaves
unchanged. The function saves ra and s0 to s3 in a frame of 112 bytes (`EXFrame`,
`IntxRV/Exp.lean`) with the result 1 at sp + 8. For the base 2 it calls `operator<<` by the low
word of the exponent by its proof, or gives 0 for an exponent of at least 2^64 (`ex_main`,
`IntxRV/ExpLoop.lean`). Otherwise it computes the bit width of the exponent (`ex_bw`) and runs the
loop over its bits (`ex_loop`): the square of the result (`ex_sq`) and, for a bit 1, the product
with the base (`ex_mb`), each the code of `operator*` inlined with the product in a temporary of the
frame, which `mul256_words` gives modulo 2^256.
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

set_option hygiene false in
/-- The frame after the prologue of `exp()`. -/
local macro "ex_pro_frame" : tactic => `(tactic| (
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
  all_goals try (simp (disch := first | bv_omega | fail) only [memWord_memStore_self,
    memWord_memStore_of_ne]; done)
  · simp (disch := first | bv_omega | fail) only [unchangedExcept2_memStore]
    exact unchangedExcept2_refl _ _ _ _ _
  · intro r hr' hn
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte] at hn ⊢))

/-- The run of `exp()` and the `operator<<` that it calls. -/
theorem exp_256.reach (base : BitVec 64) (x : Regs) (m : Mem) (hb3 : base &&& 3 = 0)
    (hr : x.get 1#5 &&& 3 = 0) (hpre : exp_256.pre x m) :
    Reach (exp_256.bufs x ++ []) exp_256_image_prog base (pcAt base 0) x m (x.get 1#5)
      (exp_256.post x m) := by
  have hpre0 := hpre
  simp only [exp_256.pre, Buf, Disjoint] at hpre
  simp (disch := decide) only [Regs.eq_get x] at hpre
  obtain ⟨⟨hra, hrn⟩, ⟨hba, hbn⟩, ⟨hea, hen⟩, hdrb, hdre, ⟨hsa, hsn⟩, hdsb, hdse, hdsr⟩ := hpre
  simp only [exp_256.bufs]
  simp (disch := decide) only [Regs.eq_get x]
  show Reach (exBufs x []) _ _ _ _ _ _ _
  rv_exec_cut 6
  simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte, BitVec.reduceSignExtend,
    BitVec.add_assoc, BitVec.reduceAdd]
  generalize hM1 : memStore (memStore (memStore (memStore (memStore m _ _) _ _) _ _) _ _) _ _ = M1
  have hF1 : EXFrame x m (x.set 2#5 (x.get 2#5 + 18446744073709551504#64)) M1 := by
    rw [← hM1]; ex_pro_frame
  exact ex_main base x m hb3 hr hpre0 _ _ hF1
    (by simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte])
    (by simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte])
    (by simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte])

theorem exp_256.proof : exp_256.spec := by
  apply runsI_of_reach exp_256_image_decodes
  intro base ret hb hr _ _ _ x m hx1 _ _ hpre
  have hb3 : base &&& 3 = 0 := by
    have := congrArg (· &&& 3#64) hb
    simpa [BitVec.and_assoc] using this
  have hx : x.get 1#5 = ret := by rw [← Regs.eq_get x (by decide)]; exact hx1
  rw [show exp_256_image_data.length = 0 from rfl, show exp_256_entry = 0 from rfl, ← hx]
  have h := exp_256.reach base x m hb3 (hx ▸ hr) hpre
  simpa [dataWords, bufWords] using h

/-- The registers of the nonvacuous instance: the result, the base, the exponent and the frame of
112 bytes above the image. -/
theorem exp_256.nonvacuous :
    NonVacuousI exp_256_image_code exp_256_image_data exp_256_image_dataOff exp_256.bufs
      exp_256.pre :=
  nonVacuousI_of (fun i => if i = 10#5 then 0x80000800#64 else if i = 11#5 then 0x80000900#64
      else if i = 12#5 then 0x80000a00#64 else if i = 2#5 then 0x80001000#64 else 0)
    (by decide) (by decide) (by decide) (by decide)
    (by simp only [exp_256.bufs, bufWords, List.cons_append, List.nil_append,
          List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        simp (config := { decide := true }) only [↓reduceIte])
    (fun _ => by simp only [exp_256.pre, Buf, Disjoint]; decide)

end IntxRV.Api
