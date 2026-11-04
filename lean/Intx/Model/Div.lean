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

/-- `internal::RECIPROCAL_TABLE`: the entries `{v0 * v0, (v0 << 11) - 1}` of the 11-bit
approximations `v0` of `2^19 / d9` (Möller and Granlund, Algorithm 2). An entry, the struct
`reciprocal_table_entry` of the two `uint32_t` fields `squared` and `scaled`, is a pair.

```cpp
std::array<reciprocal_table_entry, 256> table{};
for (size_t i = 0; i < table.size(); ++i)
{
    const auto v0 = static_cast<uint32_t>(0x7fd00 / (i + 256));
    table[i] = {v0 * v0, (v0 << 11) - 1};
}
return table;
```
-/
def RECIPROCAL_TABLE : Vector (UInt32 × UInt32) 256 := Id.run do
  let mut table := Vector.replicate 256 ((0 : UInt32), (0 : UInt32))
  for _h : i in (0 : Nat)...<256 do
    let v0 := (0x7fd00 / (i + 256)).toUInt32
    table := table.set i (v0 * v0, (v0 <<< 11) - 1)
  return table

/-- `internal::reciprocal_approx(d)`: `v2` of Algorithm 2, from the table and two Newton steps. The
table index comes from `d`, so it is checked: out of bounds is undefined behavior.

```cpp
INTX_REQUIRE(d & 0x8000000000000000);  // Must be normalized.

const auto d9 = d >> 55;
const auto& [v0v0, v0s] = RECIPROCAL_TABLE[static_cast<size_t>(d9 - 256)];
const auto d40 = (d >> 24) + 1;
const auto v1 = v0s - (uint64_t{v0v0} * d40 >> 40);
const auto v2 = (v1 << 13) + (v1 * (0x1000000000000000 - v1 * d40) >> 47);
return v2;
```
-/
def reciprocal_approx (d : Word) : Option Word := do
  let ⟨_⟩ ← require (d &&& 0x8000000000000000 ≠ 0)
  let d9 := d >>> 55
  let (v0v0, v0s) ← RECIPROCAL_TABLE[(d9 - 256).toNat]?
  let d40 := (d >>> 24) + 1
  let v1 := v0s.toUInt64 - ((v0v0.toUInt64 * d40) >>> 40)
  let v2 := (v1 <<< 13) + ((v1 * (0x1000000000000000 - v1 * d40)) >>> 47)
  return v2

/-- `internal::reciprocal<uint64_t>(d)`: the reciprocal `(2^128 - 1) / d - 2^64`, from `v2` with the
third Newton step and the exact correction of Algorithm 2.

```cpp
uint64_t d1 = 0;  // The top word.
d1 = d;
const auto v2 = reciprocal_approx(d1);
const auto d1_odd = d1 & 1;
const auto d63 = (d1 >> 1) + d1_odd;  // ceil(d1/2)
auto e = ((v2 >> 1) & (0 - d1_odd)) - (v2 * d63);
const auto v3 = (umul(v2, e)[1] >> 1) + (v2 << 31);  // The reciprocal or one less.
const auto p1 = umul(v3, d1);
return v3 - p1[1] - ((p1[0] + d1) < d1) - d1;  // v3 - hi(v3 * d + d) - d
```
-/
def reciprocal (d : Word) : Option Word := do
  let d1 := d
  let v2 ← reciprocal_approx d1
  let d1_odd := d1 &&& 1
  let d63 := (d1 >>> 1) + d1_odd
  let e := ((v2 >>> 1) &&& (0 - d1_odd)) - v2 * d63
  let v3 := ((umul v2 e)[1] >>> 1) + (v2 <<< 31)
  let p1 := umul v3 d1
  return v3 - p1[1] - (if p1[0] + d1 < d1 then 1 else 0) - d1

/-- `reciprocal_2by1(d)`.

```cpp
INTX_REQUIRE(d & 0x8000000000000000);  // Must be normalized.
#if INTX_HAS_DIV_WIDE_X86
if (!std::is_constant_evaluated())
    return internal::div_wide_x86(~d, ~uint64_t{0}, d).quot;
#endif
return internal::reciprocal(d);
```
-/
def reciprocal_2by1 (P : Platform) (d : Word) : Option Word := do
  let ⟨_⟩ ← require (d &&& 0x8000000000000000 ≠ 0)
  if P.div_wide_x86 then
    return (← div_wide_x86 (~~~d) (~~~0) d).1
  reciprocal d

/-- `udivrem_2by1(u, d, v)` with the reciprocal `v` of `d` (Möller and Granlund, Algorithm 4).

```cpp
auto q = umul(v, u[1]);
q += u;

++q[1];

auto r = u[0] - (q[1] * d);

if (r > q[0])
{
    --q[1];
    r += d;
}

if (r >= d)
{
    ++q[1];
    r -= d;
}

return {q[1], r};
```
-/
def udivrem_2by1_v (u : U128) (d v : Word) : Word × Word := Id.run do
  let mut q := umul v u[1]
  q := q + u
  q := { q with hi := q.hi + 1 }
  let mut r := u[0] - q[1] * d
  if r > q[0] then
    q := { q with hi := q.hi - 1 }
    r := r + d
  if r ≥ d then
    q := { q with hi := q.hi + 1 }
    r := r - d
  return (q[1], r)

/-- `udivrem_2by1(u, d)`.

```cpp
#if INTX_HAS_DIV_WIDE_X86
if (!std::is_constant_evaluated())
    return internal::div_wide_x86(u[1], u[0], d);
#endif
return udivrem_2by1(u, d, reciprocal_2by1(d));
```
-/
def udivrem_2by1 (P : Platform) (u : U128) (d : Word) : Option (Word × Word) := do
  if P.div_wide_x86 then
    return ← div_wide_x86 u[1] u[0] d
  return udivrem_2by1_v u d (← reciprocal_2by1 P d)

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
def udivrem_top1 (P : Platform) (TOP : Nat) {nu nv : Nat} (u : Vector Word nu) (v : Vector Word nv)
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
  let q := (← udivrem_2by1 P ⟨ut_lo, ut_hi⟩ vt).1
  let r : Vector Word nv := if WIDER then Vector.replicate nv 0 else resize nv u
  let vw := span v 0 (TOP + 1)
  let (w, b) :=
    if WIDER then submul (span u 0 (TOP + 1)) vw q else submul (span r 0 (TOP + 1)) vw q
  let r := setSpan r 0 w
  let (q, r) ← correctLoop TOP vw 2 q r (b - ue)
  let r := if _h : TOP + 1 < nv then r.set (TOP + 1) 0 else r
  return (resize nu #v[q], r)

end Intx.Model
