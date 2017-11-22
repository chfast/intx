


using i64 = unsigned long long;

#ifndef _MSC_VER
using i128 = unsigned __int128;

void mul_full64_int128(i64* oh, i64* ol, i64 a, i64 b)
{
	auto p = static_cast<i128>(a) * b;
	*oh = p >> 64;
	*ol = static_cast<i64>(p);
}
#else

#include <intrin.h>
void mul_full64_msvc(i64* oh, i64* ol, i64 a, i64 b)
{
	__int64 h;
	__int64 l = _mul128(a, b, &h);
	*ol = static_cast<i64>(l);
	*oh = static_cast<i64>(h);
}

#endif

void mul_full64_portable(i64* oh, i64* ol, i64 a, i64 b)
{
	i64 al = a & 0xffffffff;
	i64 ah = a >> 32;

	i64 bl = b & 0xffffffff;
	i64 bh = b >> 32;

	i64 t = al * bl;
	i64 u = ah * bl;
	i64 v = al * bh;
	i64 w = ah * bh;

	i64 ul = u & 0xffffffff;
	i64 uh = u >> 32;

	i64 vl = v & 0xffffffff;
	i64 vh = v >> 32;

	i64 l1 = t + (ul << 32);
	int c1 = l1 < t;

	i64 l2 = l1 + (vl << 32);
	int c2 = l2 < l1;



	*ol = l2;
	*oh = uh + vh + w + c1 + c2;
}