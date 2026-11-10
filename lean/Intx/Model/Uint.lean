import Intx.Model.Words
set_option warningAsError true
/-!
# Model: the `uint<N>` operations

The `intx::uint<N>` operations. A `uint<64 * n>` is `Vector Word n`.
-/

namespace Intx.Model

/-- `uint<N>{v...}` (the words `v`, then zeros: `words_` is value-initialized), and the conversions
between the `uint<N>` types (the low words, or the words then zeros). -/
def resize {m : Nat} (n : Nat) (v : Vector Word m) : Vector Word n :=
  Vector.ofFn fun i => if _h : i.val < m then v[i.val] else 0

/-- The constructor `uint<N>(std::span<const uint64_t> words)`.

```cpp
INTX_REQUIRE(words.size() <= num_words);
std::ranges::copy(words, words_);
```
-/
def ofSpan {m : Nat} (n : Nat) (words : Vector Word m) (_h : m ≤ n := by omega) : Vector Word n :=
  copy words (Vector.replicate n 0)

/-- `umul(const uint<N>& x, const uint<N>& y)`: the full product.

```cpp
uint<2 * N> p;
for (size_t j = 0; j < num_words; ++j)
{
    uint64_t k = 0;
    for (size_t i = 0; i < num_words; ++i)
    {
        auto a = addc(p[i + j], k);
        auto t = umul(x[i], y[j]) + uint128{a.value, a.carry};
        p[i + j] = t[0];
        k = t[1];
    }
    p[j + num_words] = k;
}
return p;
```
-/
def umulWords {n : Nat} (x y : Vector Word n) : Vector Word (2 * n) := Id.run do
  let mut p := Vector.replicate (2 * n) 0
  for _h : j in 0...<n do
    let mut k : Word := 0
    for _h : i in 0...<n do
      let a := addc p[i + j] k
      let t := umul x[i] y[j] + ⟨a.1, if a.2 then 1 else 0⟩
      p := p.set (i + j) t[0]
      k := t[1]
    p := p.set (j + n) k
  return p

/-- `subc(const uint<N>& x, const uint<N>& y, bool carry)`: the difference and the borrow.

```cpp
uint<N> z;
bool k = carry;
for (size_t i = 0; i < uint<N>::num_words; ++i)
{
    auto t = subc(x[i], y[i], k);
    z[i] = t.value;
    k = t.carry;
}
return {z, k};
```
-/
def subcWords {n : Nat} (x y : Vector Word n) (carry : Bool := false) : Vector Word n × Bool :=
  Id.run do
  let mut z := Vector.replicate n 0
  let mut k := carry
  for _h : i in 0...<n do
    let t := subc x[i] y[i] k
    z := z.set i t.1
    k := t.2
  return (z, k)

/-- `operator-(const uint& x, const uint& y)`: `subc(x, y).value`. -/
def subWords {n : Nat} (x y : Vector Word n) : Vector Word n := (subcWords x y).1

/-- `operator&(const uint& x, const uint& y)`.

```cpp
uint z;
for (size_t i = 0; i < num_words; ++i)
    z[i] = x[i] & y[i];
return z;
```
-/
def andWords {n : Nat} (x y : Vector Word n) : Vector Word n := Id.run do
  let mut z := Vector.replicate n 0
  for _h : i in 0...<n do
    z := z.set i (x[i] &&& y[i])
  return z

end Intx.Model
