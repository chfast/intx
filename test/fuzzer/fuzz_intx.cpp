// intx: extended precision integer library.
// Copyright 2019 Pawel Bylica.
// Licensed under the Apache License, Version 2.0.

/// @file
/// The fuzzer input is a program for a stack machine. A stack item is an intx::uint<N> of any
/// width from 128 to 8192 bits paired with its GMP value. Every instruction runs on both and the
/// results are compared. The program is validated up front and invalid programs are rejected.

#include <gmp.h>
#include <intx/intx.hpp>
#include <array>
#include <cstddef>
#include <cstdio>
#include <cstring>
#include <memory>
#include <new>
#include <string>
#include <utility>

namespace
{
using namespace intx;

constexpr unsigned MIN_WORDS = 2;
constexpr unsigned MAX_WORDS = 128;
constexpr unsigned NUM_WIDTHS = MAX_WORDS - MIN_WORDS + 1;
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
    umul,     // The result has the double width (up to 4096-bit arguments).
    addc,     // [1 byte]: the carry-in (imm & 1). Pushes the sum and the carry.
    subc,     // [1 byte]: the borrow-in (imm & 1). Pushes the difference and the borrow.
    udivrem,  // Pushes the quotient and the remainder.
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
    [&]<unsigned... I>(std::integer_sequence<unsigned, I...>) {
        (void)((words == MIN_WORDS + I && (f.template operator()<(MIN_WORDS + I) * 64>(), true)) ||
               ...);
    }(std::make_integer_sequence<unsigned, NUM_WIDTHS>{});
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

    /// Returns the value zero-extended to the maximum width.
    [[nodiscard]] intx::uint<MAX_WORDS * 64> get_extended() const noexcept
    {
        intx::uint<MAX_WORDS * 64> x;
        with_width(words, [&]<unsigned N> { x = get<N>(); });
        return x;
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
        with_width(words, [this]<unsigned N> {
            std::destroy_at(std::launder(reinterpret_cast<intx::uint<N>*>(storage)));
        });
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
    const uint8_t* payload;  ///< The load bytes.
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

class Machine
{
    std::array<Instr, MAX_PROGRAM_SIZE> program_{};
    size_t program_size_ = 0;
    size_t step_ = 0;
    std::array<Item, MAX_DEPTH> stack_{};
    size_t sp_ = 0;
    Mpz t1_, t2_;

    using ExecFn = bool (Machine::*)(const Instr&) noexcept;

    template <size_t... I>
    static constexpr std::array<ExecFn, NUM_WIDTHS> make_exec_table(
        std::index_sequence<I...>) noexcept
    {
        return {&Machine::exec<(MIN_WORDS + I) * 64>...};
    }

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
            in.words = MIN_WORDS + data[pos++] % NUM_WIDTHS;
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

        if (depth < info.num_args)
            return false;
        const auto top = depth != 0 ? widths[depth - 1] : 0;
        for (unsigned i = 1; i < info.num_args; ++i)
        {
            if (widths[depth - 1 - i] != top)
                return false;
        }
        if ((in.op == addmod || in.op == mulmod) && top != 4)
            return false;
        if (in.op == umul && top > MAX_WORDS / 2)
            return false;

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
            const auto w = info.has_width ? in.words : in.op == umul ? 2 * top : top;
            for (unsigned i = 0; i < info.num_results; ++i)
            {
                if (depth == MAX_DEPTH)
                    return false;
                widths[depth++] = w;
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
            for (size_t j = 0; j < in.words * 8; ++j)
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
            r.set(T{in.imm});
            mpz_set_ui(r.z, in.imm);
            break;
        default:  // push_pow2
            r.set(T{1} << (in.imm % N));
            mpz_set_ui(r.z, 0);
            mpz_setbit(r.z, in.imm % N);
            break;
        }
        check(r);
        return true;
    }

    if (in.op == cast)  // The words are truncated or zero-extended.
    {
        auto& a = stack_[sp_ - 1];
        a.set(static_cast<T>(a.get_extended()));
        wrap(a.z, N);
        check(a);
        return true;
    }

    if (op_info[in.op].num_args == 1)
    {
        auto& a = stack_[sp_ - 1];
        const auto x = a.get<N>();
        switch (in.op)
        {
        case shli:
            a.set(x << uint64_t{in.imm});
            mpz_mul_2exp(a.z, a.z, in.imm);
            wrap(a.z, N);
            break;
        case shri:
            a.set(x >> uint64_t{in.imm});
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
            if (base == 10 && from_string<T>(s) != x)
                fail("from_string (dec)", &a);
            if (base == 16 && from_string<T>("0x" + s) != x)
                fail("from_string (hex)", &a);
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
        case udivrem:
        {
            if (y == 0)
                return false;
            r.set(x / y);
            b.set(x % y);
            mpz_tdiv_qr(r.z, b.z, r.z, b.z);
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
        if constexpr (N <= MAX_WORDS * 32)
        {
            r.set(intx::umul(x, y));
            mpz_mul(r.z, r.z, b.z);
        }
        break;
    case shl:
    case shr:
        r.set(in.op == shl ? x << y : x >> y);
        if (mpz_cmp_ui(b.z.z, N) >= 0)
            mpz_set_ui(r.z, 0);
        else if (in.op == shl)
        {
            mpz_mul_2exp(r.z, r.z, mpz_get_ui(b.z));
            wrap(r.z, N);
        }
        else
            mpz_fdiv_q_2exp(r.z, r.z, mpz_get_ui(b.z));
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
    static constexpr auto exec_table = make_exec_table(std::make_index_sequence<NUM_WIDTHS>{});

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
            if (!(this->*exec_table[words - MIN_WORDS])(in))
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
