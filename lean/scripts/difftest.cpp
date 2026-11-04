// Prints the vectors for the differential test of the Lean model (difftest.sh):
// the lines "x y m mulmod(x, y, m)" in hex.

#include <intx/intx.hpp>
#include <array>
#include <iostream>
#include <random>
#include <string>

using intx::uint256;

namespace
{
std::mt19937_64 rng;  // NOLINT(cert-msc32-c,cert-msc51-cpp)

/// A random word, or one of the words at the carry and normalization boundaries.
uint64_t word()
{
    static constexpr std::array<uint64_t, 7> SPECIAL{
        0, 1, 2, 0x7fffffffffffffff, 0x8000000000000000, 0x8000000000000001, ~uint64_t{0}};
    const auto r = rng();
    if (r % 2 == 0)
        return SPECIAL[(r >> 1) % SPECIAL.size()];
    return rng();
}

/// A number of n words.
uint256 number(size_t n)
{
    uint256 x;
    for (size_t i = 0; i < n; ++i)
        x[i] = word();
    return x;
}

uint256 modulus()
{
    const auto k = static_cast<unsigned>(rng() % 256);
    switch (rng() % 8)
    {
    case 0:
        return uint256{1} << k;
    case 1:
        return (uint256{2} << k) - 1;  // All ones, up to 2^256 - 1.
    case 2:
        return (uint256{1} << k) + 1;
    default:
    {
        const auto n = 1 + rng() % 4;
        auto m = number(n);
        while (m[n - 1] == 0)
            m[n - 1] = word();
        return m;
    }
    }
}

uint256 operand(const uint256& m)
{
    switch (rng() % 8)
    {
    case 0:
        return m - 1;
    case 1:
        return ~uint256{};
    case 2:
        return m * (rng() % 4) + rng() % 2;
    default:
        return number(1 + rng() % 4);
    }
}
}  // namespace

int main(int argc, char* argv[])
{
    const auto count = argc > 1 ? std::stoull(argv[1]) : 100000;
    rng.seed(argc > 2 ? std::stoull(argv[2]) : 0);
    for (unsigned long long i = 0; i < count; ++i)
    {
        const auto m = modulus();
        const auto x = operand(m);
        const auto y = operand(m);
        std::cout << hex(x) << ' ' << hex(y) << ' ' << hex(m) << ' ' << hex(mulmod(x, y, m))
                  << '\n';
    }
}
