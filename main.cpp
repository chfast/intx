
#include <cassert>
#include <intx.hpp>

int main()
{
	uint256 a = 1;

	uint256 b = 10000000000;

	uint256 m = std::numeric_limits<uint64_t>::max();

	auto c = a + b;

	assert(c == 10000000001);

	auto d = m + 1;
	assert(d.limbs[0] == 0);
	assert(d.limbs[1] == 1);
	return 0;
}