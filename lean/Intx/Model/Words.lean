import Intx.Model.Word
set_option warningAsError true
/-!
# Model: the word-array helpers

`shl()`, `shr()`, `add()`, `submul()` and `addmul()` of `include/intx/intx.hpp`. The arrays the
helpers write do not alias the arrays they read in `mulmod()`, except where the helper is in place.
-/

namespace Intx.Model

/-- `shl(r, x, shift)` with `r.size() == rn`: the words of `r`.

```cpp
INTX_REQUIRE(!x.empty());
INTX_REQUIRE(r.size() == x.size() || r.size() == x.size() + 1);
INTX_REQUIRE(shift < 64);
const auto n = x.size();
if (r.size() > n)
    r[n] = fshl(0, x[n - 1], shift);
for (size_t i = n - 1; i != 0; --i)
    r[i] = fshl(x[i], x[i - 1], shift);
r[0] = x[0] << shift;
```

The loop counts `k` from 0, so `i` is `n - 1 - k`. -/
def shl {n : Nat} (rn : Nat) (x : Vector Word n) (shift : Fin 64)
    (_hx : 0 < n := by omega) (_hr : rn = n ∨ rn = n + 1 := by omega) : Vector Word rn := Id.run do
  let mut r := Vector.replicate rn 0
  if _h : rn > n then
    r := r.set n (fshl 0 x[n - 1] shift)
  for _h : k in 0...<(n - 1) do
    let i := n - 1 - k
    r := r.set i (fshl x[i] x[i - 1] shift)
  r := r.set 0 (x[0] <<< shift.val.toUInt64)
  return r

/-- `shr(r, x, shift)`: the words of `r`.

```cpp
INTX_REQUIRE(!x.empty());
INTX_REQUIRE(r.size() == x.size());
INTX_REQUIRE(shift < 64);
for (size_t i = 1; i < x.size(); ++i)
    r[i - 1] = fshr(x[i], x[i - 1], shift);
r[x.size() - 1] = x[x.size() - 1] >> shift;
```
-/
def shr {n : Nat} (x : Vector Word n) (shift : Fin 64) (_hx : 0 < n := by omega) :
    Vector Word n := Id.run do
  let mut r := Vector.replicate n 0
  for _h : i in 1...<n do
    r := r.set (i - 1) (fshr x[i] x[i - 1] shift)
  r := r.set (n - 1) (x[n - 1] >>> shift.val.toUInt64)
  return r

/-- `add(x, y)`: `x[] += y[]`, the words of `x` and the carry.

```cpp
INTX_REQUIRE(y.size() >= 2);
bool carry = false;
for (size_t i = 0; i < y.size(); ++i)
    std::tie(x[i], carry) = addc(x[i], y[i], carry);
return carry;
```
-/
def add {n : Nat} (x y : Vector Word n) (_hy : 2 ≤ n := by omega) : Vector Word n × Bool :=
  Id.run do
  let mut x := x
  let mut carry := false
  for _h : i in 0...<n do
    let t := addc x[i] y[i] carry
    x := x.set i t.1
    carry := t.2
  return (x, carry)

/-- `submul(r, x, y, multiplier)`: `r[] = x[] - multiplier * y[]`, the words of `r` and the
borrow word. The in-place `submul(x, y, multiplier)` is `submul(x, x, y, multiplier)`.

```cpp
INTX_REQUIRE(!y.empty());
uint64_t k = 0;
bool borrow = false;
for (size_t i = 0; i < y.size(); ++i)
{
    const auto p = umul(y[i], multiplier) + k;
    k = p[1];
    std::tie(r[i], borrow) = subc(x[i], p[0], borrow);
}
return k + uint64_t{borrow};
```

Every word of `r` is written, so its initial words do not matter: they are the words of `x`. -/
def submul {n : Nat} (x y : Vector Word n) (multiplier : Word) (_hy : 0 < n := by omega) :
    Vector Word n × Word := Id.run do
  let mut r := x
  let mut k : Word := 0
  let mut borrow := false
  for _h : i in 0...<n do
    let p := umul y[i] multiplier + U128.ofWord k
    k := p[1]
    let t := subc x[i] p[0] borrow
    r := r.set i t.1
    borrow := t.2
  return (r, k + (if borrow then 1 else 0))

/-- `addmul(x, y, multiplier)`: `x[] += multiplier * y[]`, the words of `x` and the carry word.

```cpp
INTX_REQUIRE(!y.empty());
uint64_t carry = 0;
for (size_t i = 0; i < y.size(); ++i)
{
    const auto t = umul(y[i], multiplier) + x[i] + carry;
    x[i] = t[0];
    carry = t[1];
}
return carry;
```
-/
def addmul {n : Nat} (x y : Vector Word n) (multiplier : Word) (_hy : 0 < n := by omega) :
    Vector Word n × Word := Id.run do
  let mut x := x
  let mut carry : Word := 0
  for _h : i in 0...<n do
    let t := umul y[i] multiplier + U128.ofWord x[i] + U128.ofWord carry
    x := x.set i t[0]
    carry := t[1]
  return (x, carry)

end Intx.Model
