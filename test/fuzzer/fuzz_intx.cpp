// intx: extended precision integer library.
// Copyright 2019 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

/// @file
/// The fuzzer input is a program for a stack machine. A stack item is an intx::uint<N> of one of
/// the WIDTHS paired with its GMP value. Every instruction runs on both and the results are
/// compared. The program is validated up front and invalid programs are rejected.

#include <gmp.h>
#include <intx/intx.hpp>
#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdio>
#include <cstring>
#include <initializer_list>
#include <memory>
#include <new>
#include <span>
#include <stdexcept>
#include <string>
#include <utility>

namespace
{
using namespace intx;

/// The widths in words: 128 to 1024 bits in 64-bit steps, 2048, 4096 and 8192 bits.
constexpr unsigned WIDTHS[] = {2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 32, 64, 128};
constexpr unsigned MAX_WORDS = WIDTHS[std::size(WIDTHS) - 1];

constexpr bool is_width(unsigned words) noexcept
{
    return std::ranges::find(WIDTHS, words) != std::end(WIDTHS);
}

constexpr size_t MAX_DEPTH = 16;
constexpr size_t MAX_PROGRAM_SIZE = 64;

enum Op : uint8_t
{
    load_le,     // [w] [N/8 bytes]: push a value loaded from little-endian bytes.
    load_be,     // [w] [N/8 bytes]: push a value loaded from big-endian bytes.
    push_small,  // [w] [1 byte]: push a small value.
    push_pow2,   // [w] [2 bytes]: push 2^(imm % N).
    cast,        // [w]: change the width of the top item.
    dup,         // [k]: push a copy of the k-th item from the top.
    swap,        // [k]: swap the top item with the (k+1)-th one below it.
    pop,
    add,
    sub,
    mul,
    umul,     // The result has the double width, which must be one of the WIDTHS.
    addc,     // [1 byte]: the carry-in (imm & 1). Pushes the sum and the carry.
    subc,     // [1 byte]: the borrow-in (imm & 1). Pushes the difference and the borrow.
    udivrem,  // Pushes the quotient and the remainder. The widths may differ.
    sdivrem,  // Pushes the quotient and the remainder.
    shl,
    shr,
    shli,  // [2 bytes]: shift by an immediate uint64_t.
    shri,  // [2 bytes]: shift by an immediate uint64_t.
    bit_and,
    bit_or,
    bit_xor,
    bit_not,
    neg,
    exp,  // The exponent is truncated to 64 bits: higher bits only repeat the loop.
    lt,
    slt,
    eq,
    clz,
    ctz,
    bit_width,
    count_words,
    count_bytes,
    bit_test,  // [2 bytes]: test the bit (imm % N).
    bswap,
    to_string,  // [1 byte]: check to_string() in the base 2..36 and the from_string() round trip.
    store_le,   // Check the little-endian store and the load round trip.
    store_be,   // Check the big-endian store and the load round trip.
    addmod,     // uint256 only.
    mulmod,     // uint256 only.

    // The procedures on the words or the bytes of the items as spans of dynamic extent.
    shl_words,       // [1 byte]: r = x << (imm % 64); r has the width of x or one word more.
    shr_words,       // [1 byte]: x >>= (imm % 64) in place.
    add_words,       // Adds y to the low words of x. Pushes x and the carry.
    submul_words,    // Subtracts y * m[0] from the low words of x. Pushes x and the borrow.
    from_words,      // [w]: construct uint<w> from the words of the top item.
    load_be_bytes,   // [w]: load uint<w> from the bytes of the top item.
    trunc_be_bytes,  // Store x truncated to the bytes of the item below it.

    cmp,        // Pushes the bits of all comparisons of x and y and of bool(x).
    assign_op,  // [1 byte]: x op= y, or ++x, x++, --x, x--, +x with y dropped.
    bytes_io,   // [1 byte]: store x with a byte API and load it back, or check hex(x).

    from_string,  // [w] [2 bytes: n] [n bytes]: push from_string() of the bytes up to the first 0.
    num_ops
};

struct OpInfo
{
    Op op;
    const char* name;
    uint8_t num_args;
    uint8_t num_results;
    bool has_width;    ///< Followed by a width byte.
    uint8_t imm_size;  ///< The size of the immediate after the width byte.
};

constexpr OpInfo op_info[] = {
    {load_le, "load_le", 0, 1, true, 0},
    {load_be, "load_be", 0, 1, true, 0},
    {push_small, "push_small", 0, 1, true, 1},
    {push_pow2, "push_pow2", 0, 1, true, 2},
    {cast, "cast", 1, 1, true, 0},
    {dup, "dup", 0, 1, false, 1},
    {swap, "swap", 0, 0, false, 1},
    {pop, "pop", 1, 0, false, 0},
    {add, "add", 2, 1, false, 0},
    {sub, "sub", 2, 1, false, 0},
    {mul, "mul", 2, 1, false, 0},
    {umul, "umul", 2, 1, false, 0},
    {addc, "addc", 2, 2, false, 1},
    {subc, "subc", 2, 2, false, 1},
    {udivrem, "udivrem", 2, 2, false, 0},
    {sdivrem, "sdivrem", 2, 2, false, 0},
    {shl, "shl", 2, 1, false, 0},
    {shr, "shr", 2, 1, false, 0},
    {shli, "shli", 1, 1, false, 2},
    {shri, "shri", 1, 1, false, 2},
    {bit_and, "and", 2, 1, false, 0},
    {bit_or, "or", 2, 1, false, 0},
    {bit_xor, "xor", 2, 1, false, 0},
    {bit_not, "not", 1, 1, false, 0},
    {neg, "neg", 1, 1, false, 0},
    {exp, "exp", 2, 1, false, 0},
    {lt, "lt", 2, 1, false, 0},
    {slt, "slt", 2, 1, false, 0},
    {eq, "eq", 2, 1, false, 0},
    {clz, "clz", 1, 1, false, 0},
    {ctz, "ctz", 1, 1, false, 0},
    {bit_width, "bit_width", 1, 1, false, 0},
    {count_words, "count_words", 1, 1, false, 0},
    {count_bytes, "count_bytes", 1, 1, false, 0},
    {bit_test, "bit_test", 1, 1, false, 2},
    {bswap, "bswap", 1, 1, false, 0},
    {to_string, "to_string", 1, 1, false, 1},
    {store_le, "store_le", 1, 1, false, 0},
    {store_be, "store_be", 1, 1, false, 0},
    {addmod, "addmod", 3, 1, false, 0},
    {mulmod, "mulmod", 3, 1, false, 0},
    {shl_words, "shl_words", 2, 1, false, 1},
    {shr_words, "shr_words", 1, 1, false, 1},
    {add_words, "add_words", 2, 2, false, 0},
    {submul_words, "submul_words", 3, 2, false, 0},
    {from_words, "from_words", 1, 1, true, 0},
    {load_be_bytes, "load_be_bytes", 1, 1, true, 0},
    {trunc_be_bytes, "trunc_be_bytes", 2, 1, false, 0},
    {cmp, "cmp", 2, 1, false, 0},
    {assign_op, "assign_op", 2, 1, false, 1},
    {bytes_io, "bytes_io", 1, 1, false, 1},
    {from_string, "from_string", 0, 1, true, 2},
};
static_assert(std::size(op_info) == num_ops);
static_assert([] {
    for (size_t i = 0; i < num_ops; ++i)
    {
        if (op_info[i].op != i)
            return false;
    }
    return true;
}());

/// A GMP integer with value semantics.
struct Mpz
{
    mpz_t z;

    Mpz() noexcept { mpz_init(z); }
    Mpz(const Mpz& o) noexcept { mpz_init_set(z, o.z); }
    Mpz& operator=(const Mpz& o) noexcept
    {
        mpz_set(z, o.z);
        return *this;
    }
    ~Mpz() { mpz_clear(z); }

    operator mpz_ptr() noexcept { return z; }
    operator mpz_srcptr() const noexcept { return z; }
};

/// Calls f.template operator()<N>() for the width N of the given number of words.
template <typename F>
void with_width(unsigned words, F f) noexcept
{
    [&]<size_t... I>(std::index_sequence<I...>) {
        (void)((words == WIDTHS[I] && (f.template operator()<WIDTHS[I] * 64>(), true)) || ...);
    }(std::make_index_sequence<std::size(WIDTHS)>{});
}

/// A stack item: the intx::uint<N> object living in the storage and its GMP value.
struct Item
{
    unsigned words = 0;  ///< The width of the intx object, 0 if there is none.
    alignas(uint64_t) std::byte storage[MAX_WORDS * sizeof(uint64_t)];
    Mpz z;

    Item() noexcept = default;
    Item(const Item& o) noexcept : z{o.z} { copy_value(o); }
    Item& operator=(const Item& o) noexcept
    {
        if (this != &o)
        {
            copy_value(o);
            z = o.z;
        }
        return *this;
    }
    ~Item() { destroy(); }

    template <unsigned N>
    [[nodiscard]] const intx::uint<N>& get() const noexcept
    {
        return *std::launder(reinterpret_cast<const intx::uint<N>*>(storage));
    }

    template <unsigned N>
    [[nodiscard]] intx::uint<N>& get() noexcept
    {
        return *std::launder(reinterpret_cast<intx::uint<N>*>(storage));
    }

    [[nodiscard]] std::span<uint64_t> words_span() noexcept
    {
        std::span<uint64_t> s;
        with_width(words, [&]<unsigned N> { s = as_words(get<N>()); });
        return s;
    }

    [[nodiscard]] std::span<uint8_t> bytes_span() noexcept
    {
        std::span<uint8_t> s;
        with_width(words, [&]<unsigned N> { s = {as_bytes(get<N>()), sizeof(intx::uint<N>)}; });
        return s;
    }

    template <unsigned N>
    void set(const intx::uint<N>& x) noexcept
    {
        static_assert(sizeof(x) <= sizeof(storage) && alignof(intx::uint<N>) <= alignof(uint64_t));
        destroy();
        new (storage) intx::uint<N>(x);
        words = N / 64;
    }

private:
    void destroy() noexcept
    {
        with_width(words, [this]<unsigned N> { std::destroy_at(&get<N>()); });
        words = 0;
    }

    void copy_value(const Item& o) noexcept
    {
        if (o.words == 0)
            destroy();
        with_width(o.words, [&]<unsigned N> { set(o.get<N>()); });
    }
};

struct Instr
{
    Op op;
    unsigned words;          ///< The width for the ops with the width byte.
    unsigned imm;            ///< The immediate value.
    const uint8_t* payload;  ///< The load bytes or the string.
};

/// Reduces z modulo 2^num_bits.
void wrap(mpz_ptr z, unsigned num_bits) noexcept
{
    mpz_fdiv_r_2exp(z, z, num_bits);
}

/// Sets r to the two's complement signed value of z.
void to_signed(mpz_ptr r, mpz_srcptr z, unsigned num_bits) noexcept
{
    if (mpz_tstbit(z, num_bits - 1) == 0)
    {
        mpz_set(r, z);
        return;
    }
    // z - 2^N = -(~z + 1) where ~z is the num_bits-bit complement.
    mpz_com(r, z);
    wrap(r, num_bits);
    mpz_add_ui(r, r, 1);
    mpz_neg(r, r);
}

/// Returns the number of bits of z, 0 for 0.
size_t bit_width_of(mpz_srcptr z) noexcept
{
    return mpz_sgn(z) == 0 ? 0 : mpz_sizeinbase(z, 2);
}

/// Exports z as num_bytes bytes in the given order (-1: little-endian, 1: big-endian).
void export_bytes(uint8_t* out, mpz_srcptr z, size_t num_bytes, int order) noexcept
{
    std::memset(out, 0, num_bytes);
    if (mpz_sgn(z) == 0)
        return;
    const auto n = (mpz_sizeinbase(z, 2) + 7) / 8;
    mpz_export(order < 0 ? out : out + (num_bytes - n), nullptr, order, 1, 0, 0, z);
}

/// Sets r to x shifted left or right by the amount, the result of num_bits bits.
void shift(mpz_ptr r, mpz_srcptr x, mpz_srcptr amount, unsigned num_bits, bool left) noexcept
{
    if (mpz_cmp_ui(amount, num_bits) >= 0)
        mpz_set_ui(r, 0);
    else if (left)
    {
        mpz_mul_2exp(r, x, mpz_get_ui(amount));
        wrap(r, num_bits);
    }
    else
        mpz_fdiv_q_2exp(r, x, mpz_get_ui(amount));
}

/// Packs the bits into an integer, the first one is the lowest.
constexpr uint64_t pack_bits(std::initializer_list<bool> bits) noexcept
{
    uint64_t r = 0;
    unsigned i = 0;
    for (const auto bit : bits)
        r |= uint64_t{bit} << i++;
    return r;
}

/// A struct with the .bytes field, like evmc::bytes32.
template <size_t Size>
struct Bytes
{
    uint8_t bytes[Size];
};

enum class ParseResult
{
    value,
    invalid_argument,
    out_of_range,
};

/// Parses s like intx::from_string() into z: the 0x prefix selects the hex digits. A value
/// not less than 2^num_bits is out of range unless an invalid digit comes before the overflow.
ParseResult parse(mpz_ptr z, const char* s, unsigned num_bits) noexcept
{
    const bool is_hex = s[0] == '0' && (s[1] == 'x' || s[1] == 'X');
    if (is_hex)
        s += 2;
    const auto n = std::strlen(s);
    const auto k = std::strspn(s, is_hex ? "0123456789abcdefABCDEF" : "0123456789");

    mpz_set_ui(z, 0);
    if (k != 0)
        mpz_set_str(z, std::string(s, k).c_str(), is_hex ? 16 : 10);
    if (mpz_sizeinbase(z, 2) > num_bits)  // The overflow comes before the invalid digit.
        return ParseResult::out_of_range;
    return k == n ? ParseResult::value : ParseResult::invalid_argument;
}

class Machine
{
    std::array<Instr, MAX_PROGRAM_SIZE> program_{};
    size_t program_size_ = 0;
    size_t step_ = 0;
    std::array<Item, MAX_DEPTH> stack_{};
    size_t sp_ = 0;
    Mpz t1_, t2_;

    [[noreturn]] void fail(const char* what, const Item* result = nullptr) noexcept;
    void check(const Item& item) noexcept;

    template <unsigned N>
    bool exec(const Instr& in) noexcept;

public:
    bool decode(const uint8_t* data, size_t size) noexcept;
    void run() noexcept;
};

/// Decodes and validates the program: every immediate and payload is present and every
/// instruction finds its arguments of matching widths on the stack.
bool Machine::decode(const uint8_t* data, size_t size) noexcept
{
    std::array<unsigned, MAX_DEPTH> widths{};
    size_t depth = 0;

    for (size_t pos = 0; pos < size;)
    {
        if (program_size_ == MAX_PROGRAM_SIZE || data[pos] >= num_ops)
            return false;
        const auto& info = op_info[data[pos++]];
        auto& in = program_[program_size_++];
        in.op = info.op;

        if (info.has_width)
        {
            if (pos == size)
                return false;
            in.words = WIDTHS[data[pos++] % std::size(WIDTHS)];
        }
        if (in.op == load_le || in.op == load_be)
        {
            if (size - pos < in.words * 8)
                return false;
            in.payload = &data[pos];
            pos += in.words * 8;
        }
        if (size - pos < info.imm_size)
            return false;
        for (unsigned i = 0; i < info.imm_size; ++i)
            in.imm = (in.imm << 8) | data[pos++];
        if (in.op == from_string)
        {
            if (size - pos < in.imm)
                return false;
            in.payload = &data[pos];
            pos += in.imm;
        }

        if (depth < info.num_args)
            return false;
        const auto top = depth != 0 ? widths[depth - 1] : 0;
        const auto below = depth >= 2 ? widths[depth - 2] : 0;
        std::array results{info.has_width ? in.words : top, top};
        switch (in.op)
        {
        case umul:
            if (below != top || !is_width(2 * top))
                return false;
            results[0] = 2 * top;
            break;
        case udivrem:
            results[0] = below;
            break;
        case shl_words:
            if (below != top && below != top + 1)
                return false;
            results[0] = below;
            break;
        case add_words:
            if (below < top)
                return false;
            results[0] = below;
            break;
        case submul_words:
            if (widths[depth - 3] < below)
                return false;
            results[0] = widths[depth - 3];
            break;
        case from_words:
        case load_be_bytes:
            if (top > in.words)
                return false;
            break;
        case trunc_be_bytes:
            if (below > top)
                return false;
            results[0] = below;
            break;
        default:
            for (unsigned i = 1; i < info.num_args; ++i)
            {
                if (widths[depth - 1 - i] != top)
                    return false;
            }
            if ((in.op == addmod || in.op == mulmod) && top != 4)
                return false;
        }

        if (in.op == dup)
        {
            if (in.imm >= depth || depth == MAX_DEPTH)
                return false;
            widths[depth] = widths[depth - 1 - in.imm];
            ++depth;
        }
        else if (in.op == swap)
        {
            if (in.imm + 2 > depth)
                return false;
            std::swap(widths[depth - 1], widths[depth - 2 - in.imm]);
        }
        else
        {
            depth -= info.num_args;
            for (unsigned i = 0; i < info.num_results; ++i)
            {
                if (depth == MAX_DEPTH)
                    return false;
                widths[depth++] = results[i];
            }
        }
    }
    return program_size_ != 0;
}

void Machine::fail(const char* what, const Item* result) noexcept
{
    std::fprintf(stderr, "MISMATCH: %s\n", what);
    for (size_t i = 0; i < program_size_; ++i)
    {
        const auto& in = program_[i];
        const auto& info = op_info[in.op];
        std::fprintf(stderr, "%s %2zu: %s", i == step_ ? ">>" : "  ", i, info.name);
        if (info.has_width)
            std::fprintf(stderr, " %u", in.words * 64);
        if (info.imm_size != 0)
            std::fprintf(stderr, " %u", in.imm);
        if (in.payload != nullptr)
        {
            std::fprintf(stderr, " 0x");
            const auto payload_size = in.op == from_string ? in.imm : in.words * 8;
            for (size_t j = 0; j < payload_size; ++j)
                std::fprintf(stderr, "%02x", in.payload[j]);
        }
        std::fprintf(stderr, "\n");
    }
    if (result != nullptr)
    {
        mpz_import(t1_, result->words, -1, sizeof(uint64_t), 0, 0, result->storage);
        gmp_fprintf(stderr, "  intx: %#Zx\n  gmp:  %#Zx\n", t1_.z, result->z.z);
    }
    __builtin_trap();
}

void Machine::check(const Item& item) noexcept
{
    mpz_import(t1_, item.words, -1, sizeof(uint64_t), 0, 0, item.storage);
    if (mpz_cmp(t1_, item.z) != 0)
        fail("result", &item);
}

/// Executes one instruction for the width N. Returns false to stop the program
/// (a division by zero).
template <unsigned N>
bool Machine::exec(const Instr& in) noexcept
{
    using T = intx::uint<N>;
    static constexpr auto num_bytes = N / 8;

    if (op_info[in.op].num_args == 0)  // Push.
    {
        auto& r = stack_[sp_++];
        switch (in.op)
        {
        case load_le:
            r.set(le::unsafe::load<T>(in.payload));
            mpz_import(r.z, num_bytes, -1, 1, 0, 0, in.payload);
            break;
        case load_be:
            r.set(be::unsafe::load<T>(in.payload));
            mpz_import(r.z, num_bytes, 1, 1, 0, 0, in.payload);
            break;
        case push_small:
        {
            T v;
            v = uint64_t{in.imm};
            r.set(v);
            mpz_set_ui(r.z, in.imm);
            break;
        }
        case from_string:
        {
            const std::string s(reinterpret_cast<const char*>(in.payload), in.imm);
            const auto expected = parse(r.z, s.c_str(), N);
            auto result = ParseResult::value;
            try
            {
                r.set(intx::from_string<T>(s));
            }
            catch (const std::invalid_argument&)
            {
                result = ParseResult::invalid_argument;
            }
            catch (const std::out_of_range&)
            {
                result = ParseResult::out_of_range;
            }
            if (result != expected)
                fail("from_string", result == ParseResult::value ? &r : nullptr);
            if (result != ParseResult::value)
                return false;
            break;
        }
        default:  // push_pow2
            r.set(T{1} << (in.imm % N));
            mpz_set_ui(r.z, 0);
            mpz_setbit(r.z, in.imm % N);
            break;
        }
        check(r);
        return true;
    }

    // The ops with the arguments of different widths. N is the width of the top item
    // or the width byte.
    switch (in.op)
    {
    case cast:  // The words are truncated or zero-extended.
    {
        auto& a = stack_[sp_ - 1];
        with_width(a.words, [&]<unsigned M> {
            const auto x = a.get<M>();
            if constexpr (M <= N)
            {
                T r;
                r = x;
                a.set(r);
            }
            else
                a.set(static_cast<T>(x));
        });
        wrap(a.z, N);
        check(a);
        return true;
    }
    case udivrem:
    {
        auto& b = stack_[sp_ - 1];
        auto& r = stack_[sp_ - 2];
        const auto y = b.get<N>();
        if (y == 0)
            return false;
        with_width(r.words, [&]<unsigned M> {
            const auto x = r.get<M>();
            if constexpr (M == N)
            {
                r.set(x / y);
                b.set(x % y);
            }
            else
            {
                const auto [q, rem] = intx::udivrem(x, y);
                r.set(q);
                b.set(rem);
            }
        });
        mpz_tdiv_qr(r.z, b.z, r.z, b.z);
        check(r);
        check(b);
        return true;
    }
    case shl_words:
    {
        auto& x = stack_[sp_ - 1];
        auto& r = stack_[sp_ - 2];
        const auto shift = in.imm % 64;
        intx::shl(r.words_span(), std::span<const uint64_t>{x.words_span()}, shift);
        mpz_mul_2exp(r.z, x.z, shift);
        wrap(r.z, r.words * 64);
        --sp_;
        check(r);
        return true;
    }
    case shr_words:
    {
        auto& a = stack_[sp_ - 1];
        const auto shift = in.imm % 64;
        const auto w = a.words_span();
        intx::shr(w, std::span<const uint64_t>{w}, shift);
        mpz_fdiv_q_2exp(a.z, a.z, shift);
        check(a);
        return true;
    }
    case add_words:
    case submul_words:
    {
        const auto is_add = in.op == add_words;
        auto& y = stack_[sp_ - (is_add ? 1 : 2)];
        auto& x = stack_[sp_ - (is_add ? 2 : 3)];
        const auto m = stack_[sp_ - 1].get<N>()[0];
        const auto y_words = std::span<const uint64_t>{y.words_span()};
        const auto carry = is_add ? uint64_t{internal::add(x.words_span().data(), y_words)} :
                                    internal::submul(x.words_span().data(), y_words, m);
        // x = x_high + x_low ± y [* m], the low words wrap and the carry or borrow comes out.
        const auto low_bits = y.words * 64;
        mpz_fdiv_r_2exp(t1_, x.z, low_bits);
        mpz_sub(x.z, x.z, t1_);
        if (is_add)
            mpz_add(t1_, t1_, y.z);
        else
            mpz_submul_ui(t1_, y.z, m);
        mpz_fdiv_q_2exp(t2_, t1_, low_bits);
        mpz_fdiv_r_2exp(t1_, t1_, low_bits);
        mpz_add(x.z, x.z, t1_);
        if (!is_add)
        {
            mpz_neg(t2_, t2_);
            --sp_;
        }
        auto& c = stack_[sp_ - 1];
        c.set(T{carry});
        mpz_set(c.z, t2_);
        check(x);
        check(c);
        return true;
    }
    case from_words:
    {
        auto& a = stack_[sp_ - 1];
        a.set(T{std::span<const uint64_t>{a.words_span()}});
        check(a);
        return true;
    }
    case load_be_bytes:
    {
        auto& a = stack_[sp_ - 1];
        const auto bytes = a.bytes_span();
        mpz_import(a.z, bytes.size(), 1, 1, 0, 0, bytes.data());
        a.set(be::load<T>(std::span<const uint8_t>{bytes}));
        check(a);
        return true;
    }
    case trunc_be_bytes:
    {
        const auto& x = stack_[sp_ - 1];
        auto& r = stack_[sp_ - 2];
        const auto dst = r.bytes_span();
        be::trunc(dst, x.get<N>());
        uint8_t expected[MAX_WORDS * sizeof(uint64_t)];
        mpz_fdiv_r_2exp(t1_, x.z, dst.size() * 8);
        export_bytes(expected, t1_, dst.size(), 1);
        if (std::memcmp(dst.data(), expected, dst.size()) != 0)
            fail("be::trunc");
        mpz_import(r.z, r.words, -1, sizeof(uint64_t), 0, 0, r.storage);
        --sp_;
        return true;
    }
    default:
        break;
    }

    if (op_info[in.op].num_args == 1)
    {
        auto& a = stack_[sp_ - 1];
        const auto x = a.get<N>();
        switch (in.op)
        {
        case shli:
            a.set(x << in.imm);
            mpz_mul_2exp(a.z, a.z, in.imm);
            wrap(a.z, N);
            break;
        case shri:
            a.set(x >> in.imm);
            mpz_fdiv_q_2exp(a.z, a.z, in.imm);
            break;
        case bit_not:
            a.set(~x);
            mpz_com(a.z, a.z);
            wrap(a.z, N);
            break;
        case neg:
            a.set(-x);
            mpz_neg(a.z, a.z);
            wrap(a.z, N);
            break;
        case clz:
            a.set(T{uint64_t{intx::clz(x)}});
            mpz_set_ui(a.z, N - bit_width_of(a.z));
            break;
        case ctz:
            a.set(T{uint64_t{intx::ctz(x)}});
            mpz_set_ui(a.z, mpz_sgn(a.z.z) == 0 ? N : mpz_scan1(a.z, 0));
            break;
        case bit_width:
            a.set(T{uint64_t{intx::bit_width(x)}});
            mpz_set_ui(a.z, bit_width_of(a.z));
            break;
        case count_words:
            a.set(T{uint64_t{intx::count_significant_words(x)}});
            mpz_set_ui(a.z, (bit_width_of(a.z) + 63) / 64);
            break;
        case count_bytes:
            a.set(T{uint64_t{intx::count_significant_bytes(x)}});
            mpz_set_ui(a.z, (bit_width_of(a.z) + 7) / 8);
            break;
        case bit_test:
            a.set(T{uint64_t{intx::bit_test(x, in.imm % N)}});
            mpz_set_ui(a.z, mpz_tstbit(a.z, in.imm % N) != 0);
            break;
        case bswap:
        {
            a.set(intx::bswap(x));
            uint8_t bytes[num_bytes];
            export_bytes(bytes, a.z, num_bytes, 1);
            mpz_import(a.z, num_bytes, -1, 1, 0, 0, bytes);
            break;
        }
        case to_string:
        {
            const auto base = 2 + static_cast<int>(in.imm % 35);
            const auto s = intx::to_string(x, base);
            std::string expected(mpz_sizeinbase(a.z, base) + 1, '\0');
            mpz_get_str(expected.data(), base, a.z);
            expected.resize(expected.find('\0'));
            if (s != expected)
                fail("to_string", &a);
            if (base == 10 && intx::from_string<T>(s) != x)
                fail("from_string (dec)", &a);
            if (base == 16 && intx::from_string<T>("0x" + s) != x)
                fail("from_string (hex)", &a);
            break;
        }
        case bytes_io:
        {
            uint8_t expected[num_bytes];
            const auto variant = in.imm % 6;
            if (variant == 5)
            {
                std::string hex_expected(mpz_sizeinbase(a.z, 16) + 1, '\0');
                mpz_get_str(hex_expected.data(), 16, a.z);
                hex_expected.resize(hex_expected.find('\0'));
                if (intx::hex(x) != hex_expected)
                    fail("hex", &a);
                break;
            }
            if (variant == 4)  // Truncated to the lower half.
            {
                constexpr auto H = num_bytes / 2;
                uint8_t half[H];
                be::trunc(half, x);
                const auto t = be::trunc<Bytes<H>>(x);
                wrap(a.z, H * 8);
                export_bytes(expected, a.z, H, 1);
                if (std::memcmp(half, expected, H) != 0 || std::memcmp(t.bytes, expected, H) != 0)
                    fail("be::trunc", &a);
                a.set(be::load<T>(half));
                break;
            }
            uint8_t bytes[num_bytes];
            T loaded;
            switch (variant)
            {
            case 0:
                le::store(bytes, x);
                loaded = le::load<T>(bytes);
                break;
            case 1:
                be::store(bytes, x);
                loaded = be::load<T>(bytes);
                break;
            case 2:
                be::store(std::span<uint8_t, num_bytes>{bytes}, x);
                loaded = be::load<T>(std::span<const uint8_t, num_bytes>{bytes});
                break;
            default:
            {
                const auto t = be::store<Bytes<num_bytes>>(x);
                std::memcpy(bytes, t.bytes, num_bytes);
                loaded = be::load<T>(t);
                break;
            }
            }
            export_bytes(expected, a.z, num_bytes, variant == 0 ? -1 : 1);
            if (std::memcmp(bytes, expected, num_bytes) != 0)
                fail("store", &a);
            a.set(loaded);
            break;
        }
        default:  // store_le, store_be
        {
            uint8_t bytes[num_bytes];
            uint8_t expected[num_bytes];
            const auto is_le = in.op == store_le;
            if (is_le)
                le::unsafe::store(bytes, x);
            else
                be::unsafe::store(bytes, x);
            export_bytes(expected, a.z, num_bytes, is_le ? -1 : 1);
            if (std::memcmp(bytes, expected, num_bytes) != 0)
                fail("store", &a);
            if ((is_le ? le::unsafe::load<T>(bytes) : be::unsafe::load<T>(bytes)) != x)
                fail("store/load round trip", &a);
            break;
        }
        }
        check(a);
        return true;
    }

    if (op_info[in.op].num_args == 3)  // addmod, mulmod: uint256 only.
    {
        if constexpr (N == 256)
        {
            const auto& m = stack_[sp_ - 1];
            const auto& c = stack_[sp_ - 2];
            auto& r = stack_[sp_ - 3];
            const auto mv = m.get<N>();
            if (mv == 0)
                return false;
            if (in.op == addmod)
            {
                r.set(intx::addmod(r.get<N>(), c.get<N>(), mv));
                mpz_add(r.z, r.z, c.z);
            }
            else
            {
                r.set(intx::mulmod(r.get<N>(), c.get<N>(), mv));
                mpz_mul(r.z, r.z, c.z);
            }
            mpz_mod(r.z, r.z, m.z);
            sp_ -= 2;
            check(r);
        }
        return true;
    }

    // Binary: r = x op y, where y is the top item and x the one below it.
    // The second result, if any, replaces y.
    auto& b = stack_[sp_ - 1];
    auto& r = stack_[sp_ - 2];
    const auto x = r.get<N>();
    const auto y = b.get<N>();

    if (op_info[in.op].num_results == 2)
    {
        switch (in.op)
        {
        case addc:
        case subc:
        {
            const bool carry_in = (in.imm & 1) != 0;
            const auto [v, carry] =
                in.op == addc ? intx::addc(x, y, carry_in) : intx::subc(x, y, carry_in);
            r.set(v);
            b.set(T{uint64_t{carry}});
            if (in.op == addc)
            {
                mpz_add(t1_, r.z, b.z);
                mpz_add_ui(t1_, t1_, carry_in);
            }
            else
            {
                mpz_sub(t1_, r.z, b.z);
                mpz_sub_ui(t1_, t1_, carry_in);
            }
            mpz_set_ui(b.z, in.op == addc ? mpz_sizeinbase(t1_, 2) > N : mpz_sgn(t1_.z) < 0);
            mpz_fdiv_r_2exp(r.z, t1_, N);
            break;
        }
        default:  // sdivrem
        {
            if (y == 0)
                return false;
            const auto [q, rem] = intx::sdivrem(x, y);
            r.set(q);
            b.set(rem);
            to_signed(t1_, r.z, N);
            to_signed(t2_, b.z, N);
            mpz_tdiv_qr(r.z, b.z, t1_, t2_);
            wrap(r.z, N);
            wrap(b.z, N);
            break;
        }
        }
        check(r);
        check(b);
        return true;
    }

    --sp_;

    switch (in.op)
    {
    case add:
        r.set(x + y);
        mpz_add(r.z, r.z, b.z);
        wrap(r.z, N);
        break;
    case sub:
        r.set(x - y);
        mpz_sub(r.z, r.z, b.z);
        wrap(r.z, N);
        break;
    case mul:
        r.set(x * y);
        mpz_mul(r.z, r.z, b.z);
        wrap(r.z, N);
        break;
    case umul:
        if constexpr (is_width(N / 32))
        {
            r.set(intx::umul(x, y));
            mpz_mul(r.z, r.z, b.z);
        }
        break;
    case shl:
    case shr:
        r.set(in.op == shl ? x << y : x >> y);
        shift(r.z, r.z, b.z, N, in.op == shl);
        break;
    case bit_and:
        r.set(x & y);
        mpz_and(r.z, r.z, b.z);
        break;
    case bit_or:
        r.set(x | y);
        mpz_ior(r.z, r.z, b.z);
        break;
    case bit_xor:
        r.set(x ^ y);
        mpz_xor(r.z, r.z, b.z);
        break;
    case exp:
        r.set(intx::exp(x, T{y[0]}));
        mpz_set_ui(t1_, 0);
        mpz_setbit(t1_, N);
        mpz_powm_ui(r.z, r.z, y[0], t1_);
        break;
    case lt:
        r.set(T{uint64_t{x < y}});
        mpz_set_ui(r.z, mpz_cmp(r.z, b.z) < 0);
        break;
    case slt:
        r.set(T{uint64_t{intx::slt(x, y)}});
        to_signed(t1_, r.z, N);
        to_signed(t2_, b.z, N);
        mpz_set_ui(r.z, mpz_cmp(t1_, t2_) < 0);
        break;
    case cmp:
    {
        const auto c = x <=> y;
        r.set(T{pack_bits({(x < y), (x <= y), (x > y), (x >= y), (x == y), (x != y), (c < 0),
            (c > 0), static_cast<bool>(x)})});
        const auto e = mpz_cmp(r.z, b.z);
        const auto nz = mpz_sgn(r.z.z) != 0;
        mpz_set_ui(
            r.z, pack_bits({e < 0, e <= 0, e > 0, e >= 0, e == 0, e != 0, e < 0, e > 0, nz}));
        break;
    }
    case assign_op:
    {
        auto v = x;
        const auto k = in.imm % 15;
        switch (k)
        {
        case 0:
            v += y;
            mpz_add(r.z, r.z, b.z);
            break;
        case 1:
            v -= y;
            mpz_sub(r.z, r.z, b.z);
            break;
        case 2:
            v *= y;
            mpz_mul(r.z, r.z, b.z);
            break;
        case 3:
            if (y == 0)
                return false;
            v /= y;
            mpz_tdiv_q(r.z, r.z, b.z);
            break;
        case 4:
            if (y == 0)
                return false;
            v %= y;
            mpz_tdiv_r(r.z, r.z, b.z);
            break;
        case 5:
            v |= y;
            mpz_ior(r.z, r.z, b.z);
            break;
        case 6:
            v &= y;
            mpz_and(r.z, r.z, b.z);
            break;
        case 7:
            v ^= y;
            mpz_xor(r.z, r.z, b.z);
            break;
        case 8:
            v <<= y;
            shift(r.z, r.z, b.z, N, true);
            break;
        case 9:
            v >>= y;
            shift(r.z, r.z, b.z, N, false);
            break;
        case 10:
        case 11:
        case 12:
        case 13:
        {
            // Only uint128 has the increment and decrement operators.
            const auto is_inc = k < 12;
            if constexpr (requires { ++v; })
            {
                if (k % 2 == 0)
                    is_inc ? ++v : --v;
                else if ((is_inc ? v++ : v--) != x)
                    fail("postfix increment or decrement");
            }
            else
                v = is_inc ? v + 1 : v - 1;
            (is_inc ? mpz_add_ui : mpz_sub_ui)(r.z, r.z, 1);
            break;
        }
        default:
            if constexpr (requires { +v; })
                v = +v;
            break;
        }
        r.set(v);
        wrap(r.z, N);
        break;
    }
    default:  // eq
        r.set(T{uint64_t{x == y}});
        mpz_set_ui(r.z, mpz_cmp(r.z, b.z) == 0);
        break;
    }
    check(r);
    return true;
}

void Machine::run() noexcept
{
    for (step_ = 0; step_ < program_size_; ++step_)
    {
        const auto& in = program_[step_];
        switch (in.op)
        {
        case dup:
            stack_[sp_] = stack_[sp_ - 1 - in.imm];
            ++sp_;
            break;
        case swap:
        {
            auto& p = stack_[sp_ - 1];
            auto& q = stack_[sp_ - 2 - in.imm];
            const auto tmp = p;
            p = q;
            q = tmp;
            break;
        }
        case pop:
            --sp_;
            break;
        default:
        {
            const auto words = op_info[in.op].has_width ? in.words : stack_[sp_ - 1].words;
            bool ok = true;
            with_width(words, [&]<unsigned N> { ok = exec<N>(in); });
            if (!ok)
                return;
        }
        }
    }
}
}  // namespace

extern "C" int LLVMFuzzerTestOneInput(const uint8_t* data, size_t data_size) noexcept
{
    Machine m;
    if (!m.decode(data, data_size))
        return -1;
    m.run();
    return 0;
}
