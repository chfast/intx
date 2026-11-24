import IntxRV.Gen.Api
import IntxRV.Arith
import IntxRV.Conv
/-!
# The constructor of `uint256` from an `int`

The specification, from `include/intx/intx.hpp`:

```cpp
/// Constructs from the words v, the first the least significant, each converted to uint64_t
/// (modulo 2^64).
/// @post self = v.foldr (fun a s ↦ (a % 2^64).toNat + 2^64 * s) 0
template <typename... T>
constexpr explicit(false) uint(T... v) noexcept
    requires std::conjunction_v<std::is_convertible<T, uint64_t>...> &&
             (!internal::wide_integer<T> && ...)
  : words_{static_cast<uint64_t>(v)...}
```

`from_i32_256.spec` states it for the RV64 machine code of `from_i32_256` in `IntxRV/Api.cpp`
(generated in `IntxRV/Gen/Api.lean`, see `IntxRV/README.md`). The function stores the register of v,
sign-extended from 32 bits, and three words 0: v modulo 2^64 (`toInt_emod_toNat`,
`IntxRV/Conv.lean`).
-/

namespace IntxRV.Api
open IntxRV IntxRV.Gen

set_option maxHeartbeats 4000000

theorem from_i32_256.proof : from_i32_256.spec :=
  runsM_of_reach from_i32_256_decodes fun base ret _ hr _ x m hx1 hpre => by
    simp only [from_i32_256.pre, from_i32_256.bufs, Buf] at hpre ⊢
    simp (disch := decide) only [Regs.eq_get x] at hpre hx1 ⊢
    subst hx1
    refine Reach.start ?_
    rv_exec
    try rv_val
    simp only [update_aligned hr]
    refine Reach.refl ?_
    simp only [from_i32_256.post, calleeSaved, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    simp (disch := decide) only [Regs.eq_get x]
    try simp (config := { decide := true }) only [Regs.get_set, ↓reduceIte]
    try simp only [Defn] at *
    try subst_vars
    refine ⟨?_, ?_, ?_⟩
    · simp only [words, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, Nat.mul_zero,
        Nat.add_zero]
      simp (disch := first | bv_omega | fail) only [memWord_memStore_self, memWord_memStore_of_ne]
      have hz : (x.get 0#5).toNat = 0 := by
        rw [show (0#5 : BitVec 5) = 0 from rfl, Regs.get_zero]; rfl
      simp only [hz, Nat.mul_zero, Nat.add_zero]
      try simp only [List.foldr, toInt_emod_toNat, Nat.mul_zero, Nat.add_zero]
    · simp (disch := first | bv_omega | fail) only [unchangedExcept_memStore,
        unchangedExcept_refl]
    · simp (config := { decide := true }) only [Regs.set_apply, ↓reduceIte, BitVec.ofNat_eq_ofNat]
      simp (disch := decide) only [Regs.eq_get x, and_self]

end IntxRV.Api
