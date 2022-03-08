#include <intx/intx.hpp>

using namespace intx;

extern "C" div_result<uint64_t> UDIVREM_2BY1(uint128 u, uint64_t d, uint64_t v)
{
    return udivrem_2by1(u, d, v);
}
