import Intx.Model.Uint
set_option warningAsError true
/-!
# Model: the divisions

`udivrem_2by1()` and the reciprocal of `include/intx/intx.hpp`.
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

// The first correction, taken about half the time, is branch-free: q[1] - 1 and r + d if
// r > q[0]. r gets a mask because GCC turns two ternaries into a branch.
// The second correction is rare.
const auto c = r > q[0];
q[1] = c ? q[1] - 1 : q[1];
r += d & (uint64_t{0} - uint64_t{c});

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
  let c := r > q[0]
  q := { q with hi := if c then q.hi - 1 else q.hi }
  r := r + (d &&& (0 - (if c then 1 else 0)))
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

end Intx.Model
