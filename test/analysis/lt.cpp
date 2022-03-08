#include <intx/intx.hpp>

using namespace intx;

extern "C" bool LT128(uint128 x, const uint128 y)
{
    return x < y;
}

extern "C" bool LT256(uint256& x, const uint256& y)
{
    return x < y;
}

extern "C" bool LE256(uint256& x, const uint256& y)
{
    return x <= y;
}
