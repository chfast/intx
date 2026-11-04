import Intx.Spec
set_option warningAsError true
/-!
# Model: the word operations

The model renders the C++ code of `include/intx/intx.hpp` statement by statement, with the C++
types as Lean types:

* a `uint64_t` is a `Word`, a `uint128` is `U128`;
* a `uint<64 * n>`, a `std::array<uint64_t, n>` and a `std::span` of `n` words are `Vector Word n`;
  a pointer argument `uint64_t x[]` of a helper is the `Vector` of the words the helper accesses
  (`span`), and the words it writes go back to the array with `setSpan`;
* a shift amount, `unsigned` with `INTX_REQUIRE(shift < 64)`, is `Fin 64`.

The array sizes are types and every array access carries the proof that its index is in bounds,
as the C++ compiler knows the sizes and indices for each `N`. A `static_assert` and an
`INTX_REQUIRE` on sizes are arguments with proofs (checked by `omega` when the model is compiled).

A function returns `Option` where the C++ code can have undefined behavior depending on values:
`none` is a false `INTX_REQUIRE` (release builds make the compiler assume the condition), a `div`
the CPU rejects, or a loop running longer than the C++ code says. The theorems of `Intx.Proofs`
show that `mulmod()` never gets there.

The C++ arrays left uninitialized are vectors of zeros here: the C++ code writes every word of
them before reading it.

This file has the 64-bit word operations, with the semantics of their portable (constexpr) C++
code. The builtins (`__builtin_addcll`, `__builtin_subcll`, `unsigned __int128`) and the x86-64
asm (`shld`, `shrd`, `bsr`) that the C++ code uses at run time compute the same results.
-/

namespace Intx.Model

/-- `INTX_REQUIRE(c)`: release builds make a false `c` undefined behavior
(`__builtin_unreachable()`), and the code after it may assume `c`. -/
def require (c : Prop) [Decidable c] : Option (PLift c) := if h : c then some ⟨h⟩ else none

/-- The `len` words of `a` from the word `off`: a `std::span` of them, or the words a helper
accesses through the pointer `&a[off]`. -/
def span {n : Nat} (a : Vector Word n) (off len : Nat) (_h : off + len ≤ n := by omega) :
    Vector Word len :=
  Vector.ofFn fun i => a[off + i.val]

/-- `a` with the words `w` written from the word `off`. -/
def setSpan {n m : Nat} (a : Vector Word n) (off : Nat) (w : Vector Word m)
    (_h : off + m ≤ n := by omega) : Vector Word n :=
  Vector.ofFn fun i => if _h' : off ≤ i.val ∧ i.val < off + m then w[i.val - off] else a[i]

/-- `std::ranges::copy(src, dst.begin())`. -/
def copy {m n : Nat} (src : Vector Word m) (dst : Vector Word n) (_h : m ≤ n := by omega) :
    Vector Word n :=
  setSpan dst 0 src

/-- `uint128`, the words `lo` (`[0]`) and `hi` (`[1]`). -/
structure U128 where
  lo : Word
  hi : Word
  deriving DecidableEq, Repr

instance : GetElem U128 Nat Word (fun _ i => i < 2) where
  getElem p i _ := if i = 0 then p.lo else p.hi

/-- The conversion of a `uint64_t` to `uint128`. -/
def U128.ofWord (x : Word) : U128 := ⟨x, 0⟩

/-- `addc(x, y, carry)`: the sum and the carry out.

```cpp
const auto s = x + y;
const auto carry1 = s < x;
const auto t = s + carry;
const auto carry2 = t < s;
return {t, static_cast<bool>(carry1 | carry2)};
```
-/
def addc (x y : Word) (carry : Bool := false) : Word × Bool :=
  let s := x + y
  let carry1 := decide (s < x)
  let t := s + (if carry then 1 else 0)
  let carry2 := decide (t < s)
  (t, carry1 || carry2)

/-- `subc(x, y, carry)`: the difference and the borrow out.

```cpp
const auto d = x - y;
const auto carry1 = x < y;
const auto e = d - carry;
const auto carry2 = d < uint64_t{carry};
return {e, static_cast<bool>(carry1 | carry2)};
```
-/
def subc (x y : Word) (carry : Bool := false) : Word × Bool :=
  let d := x - y
  let carry1 := decide (x < y)
  let e := d - (if carry then 1 else 0)
  let carry2 := decide (d < (if carry then 1 else 0))
  (e, carry1 || carry2)

/-- `operator+(uint128, uint128)`, `addc(x, y).value` on the words (GCC uses the builtin type):
the sum modulo 2^128. A `uint64_t` operand converts to `uint128` first. -/
def U128.add (a b : U128) : U128 :=
  let (lo, c) := addc a.lo b.lo
  let (hi, _) := addc a.hi b.hi c
  ⟨lo, hi⟩

instance : Add U128 := ⟨U128.add⟩

/-- `operator<(uint128, uint128)`: the comparison of the numbers. -/
def U128.lt (a b : U128) : Bool :=
  decide (a.hi.toNat * 2 ^ 64 + a.lo.toNat < b.hi.toNat * 2 ^ 64 + b.lo.toNat)

/-- `umul(uint64_t x, uint64_t y)`: the 128-bit product, `builtin_uint128{x} * builtin_uint128{y}`. -/
def umul (x y : Word) : U128 :=
  let p := x.toNat * y.toNat
  ⟨UInt64.ofNat p, UInt64.ofNat (p / 2 ^ 64)⟩

/-- `fshl(hi, lo, shift)`: the high word of `hi:lo` shifted left.

```cpp
return shift == 0 ? hi : (hi << shift) | (lo >> (64 - shift));
```
-/
def fshl (hi lo : Word) (shift : Fin 64) : Word :=
  if shift = 0 then hi else (hi <<< shift.val.toUInt64) ||| (lo >>> (64 - shift.val).toUInt64)

/-- `fshr(hi, lo, shift)`: the low word of `hi:lo` shifted right.

```cpp
return shift == 0 ? lo : (lo >> shift) | (hi << (64 - shift));
```
-/
def fshr (hi lo : Word) (shift : Fin 64) : Word :=
  if shift = 0 then lo else (lo >>> shift.val.toUInt64) ||| (hi <<< (64 - shift.val).toUInt64)

/-- `clz_nonzero(x)`: the number of leading zero bits (`lzcnt`, or `bsr` xor 63).

```cpp
INTX_REQUIRE(x != 0);
```
-/
def clz_nonzero (x : Word) : Option (Fin 64) := do
  let ⟨_⟩ ← require (x ≠ 0)
  return ⟨63 - Nat.log2 x.toNat, by omega⟩

end Intx.Model
