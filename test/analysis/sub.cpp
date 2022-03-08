#include <intx/intx.hpp>

using namespace intx;

extern "C" void SUB256(uint256& x, const uint256& y)
{
    x -= y;
}
