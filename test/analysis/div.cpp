#include <intx/intx.hpp>

using namespace intx;

extern "C" div_result<uint64_t> UDIVREM_2BY1(uint128 u, uint64_t d, uint64_t v)
{
    return udivrem_2by1(u, d, v);
}

extern "C" void UDIVREM_4BY4(uint256& q, uint256& r, const uint256& u, const uint256& d) noexcept
{
    std::tie(q, r) = udivrem(u, d);
}
