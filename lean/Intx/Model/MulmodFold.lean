import Intx.Model.Div
set_option warningAsError true
/-!
# Model: `mulmod()`

`internal::mulmod_fold<N>()` and `mulmod()` of `include/intx/intx.hpp`.
-/

namespace Intx.Model

/-- `internal::mulmod_fold<N>(x, y, m)`.

```cpp
static_assert(N >= 1 && N <= 4);
INTX_REQUIRE(m[N - 1] != 0);

const auto s = clz_nonzero(m[N - 1]);
std::array<uint64_t, N> d;
shl(std::span{d}, as_words(m).first<N>(), s);

uint<64 * (N + 1)> c0b;  // C0 * B.
submul(as_words(c0b).template last<N>().data(), d, 1);
const std::span<const uint64_t, N> c0 = as_words(c0b).template last<N>();

const auto p = umul(x, y);
if (INTX_UNLIKELY(c0[N - 1] == d[N - 1]))  // m is a power of 2: C0 = d, not reduced.
    return static_cast<uint256>(p) & (m - 1);

uint64_t q;
std::array<uint64_t, N> c1;
if constexpr (N == 1)
    std::tie(q, c1[0]) = udivrem_2by1(c0b, d[0]);
else
{
    const auto [quot, rem] =
        udivrem_top1<N - 1>(c0b, uint<64 * N>{std::span<const uint64_t>{d}});
    q = quot[0];
    std::ranges::copy(as_words(rem), c1.begin());
}

std::array<uint64_t, 9> pw;
shl(std::span{pw}, as_words(p), s);
std::array<uint64_t, N + 1> r;
for (size_t i = 0; i <= N; ++i)
    r[i] = pw[8 - N + i];
for (size_t j = 8 - N; j != 0; --j)
{
    std::array<uint64_t, N + 1> acc{};
    acc[0] = pw[j - 1];
    for (size_t i = 1; i < N; ++i)
        acc[i] = r[i - 1];
    acc[N] += addmul(acc.data(), c0, r[N - 1]);
    acc[N] += addmul(acc.data(), c1, r[N]);
    r = acc;
}

const auto qh = umul(uint128{r[N - 1], r[N]}, uint128{q, 1});
r[N] -= submul(r.data(), d, qh[2]);
if (qh[3] != 0)  // qh >= B: subtract d * B too.
    submul(std::span{r}.template last<N>().data(), d, 1);

std::array<uint64_t, N> t;
if (r[N] >= submul(t.data(), r.data(), d, 1))
    std::ranges::copy(t, r.begin());

uint256 res;
shr(as_words(res).first<N>(), std::span{r}.template first<N>(), s);
return res;
```

The fold loop counts `k` from 0, so `j` is `8 - N - k`. In `acc[N] += addmul(...)` and
`r[N] -= submul(...)` the call is sequenced before the read of the left operand (C++17). The
`uint128` arguments of the generic `umul()` are its words. -/
def mulmod_fold (N : Nat) (x y m : U256) (_hN : 1 ≤ N ∧ N ≤ 4 := by omega) : Option U256 := do
  let ⟨_⟩ ← require (m[N - 1] ≠ 0)

  let s ← clz_nonzero m[N - 1]
  let d : Vector Word N := shl N (span m 0 N) s

  let c0b : Vector Word (N + 1) := Vector.replicate (N + 1) 0
  let c0b := setSpan c0b 1 (submul (span c0b 1 N) d 1).1
  let c0 := span c0b 1 N

  let p := umulWords x y
  if c0[N - 1] = d[N - 1] then
    return andWords (resize 4 p) (subWords m (resize 4 #v[1]))

  let (q, c1) ← if _h : N = 1 then do
      let (q, c10) ← udivrem_2by1 ⟨c0b[0], c0b[1]⟩ d[0]
      pure (q, (Vector.replicate N 0).set 0 c10)
    else do
      let (quot, rem) ← udivrem_top1 (N - 1) c0b (ofSpan N d)
      pure (quot[0], copy rem (Vector.replicate N 0))

  let pw : Vector Word 9 := shl 9 (span p 0 8) s
  let mut r : Vector Word (N + 1) := Vector.replicate (N + 1) 0
  for _h : i in 0...<(N + 1) do
    r := r.set i pw[8 - N + i]
  for _h : k in 0...<(8 - N) do
    let j := 8 - N - k
    let mut acc : Vector Word (N + 1) := Vector.replicate (N + 1) 0
    acc := acc.set 0 pw[j - 1]
    for _h : i in 1...<N do
      acc := acc.set i r[i - 1]
    let (a, c) := addmul (span acc 0 N) c0 r[N - 1]
    acc := setSpan acc 0 a
    acc := acc.set N (acc[N] + c)
    let (a, c) := addmul (span acc 0 N) c1 r[N]
    acc := setSpan acc 0 a
    acc := acc.set N (acc[N] + c)
    r := acc

  let qh := umulWords #v[r[N - 1], r[N]] #v[q, 1]
  let (a, b) := submul (span r 0 N) d qh[2]
  r := setSpan r 0 a
  r := r.set N (r[N] - b)
  if qh[3] ≠ 0 then
    r := setSpan r 1 (submul (span r 1 N) d 1).1

  let (t, b) := submul (span r 0 N) d 1
  if r[N] ≥ b then
    r := copy t r

  let res : U256 := Vector.replicate 4 0
  return setSpan res 0 (shr (span r 0 N) s)

/-- `mulmod(x, y, mod)`.

```cpp
if (mod[3] != 0)
    return internal::mulmod_fold<4>(x, y, mod);
if (mod[2] != 0)
    return internal::mulmod_fold<3>(x, y, mod);
if (mod[1] != 0)
    return internal::mulmod_fold<2>(x, y, mod);
return internal::mulmod_fold<1>(x, y, mod);
```
-/
def mulmod (x y m : U256) : Option U256 :=
  if m[3] ≠ 0 then mulmod_fold 4 x y m
  else if m[2] ≠ 0 then mulmod_fold 3 x y m
  else if m[1] ≠ 0 then mulmod_fold 2 x y m
  else mulmod_fold 1 x y m

end Intx.Model
