import Intx.Model.Uint
set_option warningAsError true
/-!
# Model: the divisions

`udivrem_2by1()` and `udivrem_top1()` of `include/intx/intx.hpp`.
-/

namespace Intx.Model

/-- `div_wide_x86(hi, lo, d)`: the x86-64 `div` instruction, the quotient and the remainder of
`hi:lo` by `d`. The CPU faults if the quotient does not fit in 64 bits.

```cpp
INTX_REQUIRE(hi < d);
asm("div %[d]" : "+a"(q), "+d"(r) : [d] "r"(d) : "cc");
```
-/
def div_wide_x86 (hi lo d : Word) : Option (Word × Word) := do
  let ⟨_⟩ ← require (hi < d)
  let n := hi.toNat * 2 ^ 64 + lo.toNat
  return (UInt64.ofNat (n / d.toNat), UInt64.ofNat (n % d.toNat))

/-- `udivrem_2by1(u, d)` on x86-64, outside constant evaluation:

```cpp
return internal::div_wide_x86(u[1], u[0], d);
```

Constant evaluation and the other architectures use `udivrem_2by1(u, d, reciprocal_2by1(d))`; that
it computes the same is a separate goal (`Intx.AdditionalGoals`). -/
def udivrem_2by1 (u : U128) (d : Word) : Option (Word × Word) := div_wide_x86 u[1] u[0] d

/-- The correction loop of `udivrem_top1()`, at most `fuel` iterations.

```cpp
while (borrow != 0) [[unlikely]]
{
    --q;
    borrow -= add(as_words(r).data(), vw);
}
```
-/
def correctLoop (TOP : Nat) {nv : Nat} (vw : Vector Word (TOP + 1)) (fuel : Nat) (q : Word)
    (r : Vector Word nv) (borrow : Word) (_h : 1 ≤ TOP ∧ TOP < nv := by omega) :
    Option (Word × Vector Word nv) :=
  if borrow = 0 then some (q, r)
  else
    match fuel with
    | 0 => none
    | fuel + 1 =>
      let (w, c) := add (span r 0 (TOP + 1)) vw
      correctLoop TOP vw fuel (q - 1) (setSpan r 0 w) (borrow - (if c then 1 else 0))

/-- `udivrem_top1<TOP>(u, v)` for `u : uint<M>` and `v : uint<N>`: the quotient and the remainder.

```cpp
static_assert(TOP >= 1 && TOP < uint<N>::num_words);
static_assert(uint<M>::num_words == TOP + 1 || uint<M>::num_words == TOP + 2);
constexpr auto WIDER = uint<M>::num_words > uint<N>::num_words;

uint64_t ue = 0;
if constexpr (uint<M>::num_words == TOP + 2)
    ue = u[TOP + 1];

if constexpr (!WIDER)
{
    if (uint128{u[TOP], ue} < v[TOP])  // u < v.
        return {0, static_cast<uint<N>>(u)};
}

const auto s = clz_nonzero<true>(v[TOP]);
const auto vt = fshl(v[TOP], v[TOP - 1], s);
const auto ut_hi = fshl(ue, u[TOP], s);
const auto ut_lo = fshl(u[TOP], u[TOP - 1], s);

auto q = udivrem_2by1({ut_lo, ut_hi}, vt).quot;

auto r = [&] {
    if constexpr (WIDER)
        return uint<N>{};
    else
        return static_cast<uint<N>>(u);
}();
const auto vw = as_words(v).template first<TOP + 1>();
uint64_t borrow = 0;
if constexpr (WIDER)
    borrow = submul(as_words(r).data(), as_words(u).data(), vw, q) - ue;
else
    borrow = submul(as_words(r).data(), vw, q) - ue;
// The correction runs at most 2 times (usually 0).
while (borrow != 0) [[unlikely]]
{
    --q;
    borrow -= add(as_words(r).data(), vw);
}
if constexpr (TOP + 1 < uint<N>::num_words)
    r[TOP + 1] = 0;
return {q, r};
```

The correction loop gets the 2 iterations its comment promises. -/
def udivrem_top1 (TOP : Nat) {nu nv : Nat} (u : Vector Word nu) (v : Vector Word nv)
    (_h1 : 1 ≤ TOP ∧ TOP < nv := by omega) (_h2 : nu = TOP + 1 ∨ nu = TOP + 2 := by omega) :
    Option (Vector Word nu × Vector Word nv) := do
  let WIDER := decide (nu > nv)
  let ue : Word := if _h : nu = TOP + 2 then u[TOP + 1] else 0
  if !WIDER then
    if U128.lt ⟨u[TOP], ue⟩ (U128.ofWord v[TOP]) then
      return (resize nu #v[0], resize nv u)
  let s ← clz_nonzero v[TOP]
  let vt := fshl v[TOP] v[TOP - 1] s
  let ut_hi := fshl ue u[TOP] s
  let ut_lo := fshl u[TOP] u[TOP - 1] s
  let q := (← udivrem_2by1 ⟨ut_lo, ut_hi⟩ vt).1
  let r : Vector Word nv := if WIDER then Vector.replicate nv 0 else resize nv u
  let vw := span v 0 (TOP + 1)
  let (w, b) :=
    if WIDER then submul (span u 0 (TOP + 1)) vw q else submul (span r 0 (TOP + 1)) vw q
  let r := setSpan r 0 w
  let (q, r) ← correctLoop TOP vw 2 q r (b - ue)
  let r := if _h : TOP + 1 < nv then r.set (TOP + 1) 0 else r
  return (resize nu #v[q], r)

end Intx.Model
