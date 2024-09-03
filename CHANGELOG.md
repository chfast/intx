# Changelog for intx

Documentation of all notable changes to the **intx** project.

The format is based on [Keep a Changelog],
and this project adheres to [Semantic Versioning].

## [0.12.0] — 2024-09-03

### Added

- Consequent type aliases and literal suffixes:
  [#317](https://github.com/chfast/intx/pull/317)
  - `uint128`, `1_u128`
  - `uint192`, `1_u192`
  - `uint256`, `1_u256`
  - `uint320`, `1_u320`
  - `uint384`, `1_u384`
  - `uint448`, `1_u448`
  - `uint512`, `1_u512`

### Changed

- Restructure of the code by using `friend operator` and `if constexpr`.
  [#318](https://github.com/chfast/intx/pull/318)
  [#319](https://github.com/chfast/intx/pull/319)
  [#320](https://github.com/chfast/intx/pull/320)
  [#321](https://github.com/chfast/intx/pull/321)
  [#322](https://github.com/chfast/intx/pull/322)
  [#324](https://github.com/chfast/intx/pull/324)

## [0.11.0] — 2024-08-06

### Added

- Support `constexpr` context execution for all arithmetic including division.
  [#305](https://github.com/chfast/intx/pull/305)
  [#311](https://github.com/chfast/intx/pull/311)
  [#314](https://github.com/chfast/intx/pull/314)

### Changed

- Literal operators changed to `consteval`.
  [#298](https://github.com/chfast/intx/pull/298)
- Some C++20 modernization.
  [#297](https://github.com/chfast/intx/pull/297)
  [#308](https://github.com/chfast/intx/pull/308)

### Fixed

- Fixes to division for `constexpr` context.
  [#309](https://github.com/chfast/intx/pull/309)
  [#310](https://github.com/chfast/intx/pull/310)

## [0.10.1] — 2023-07-17

### Fixed

- Fixed buggy `__builtin_subcll` in Xcode 14.3.1 on arm64.
  [294](https://github.com/chfast/intx/pull/294)

## [0.10.0] — 2023-04-25

### Changed

- C++20 is now required to use intx.
  [#287](https://github.com/chfast/intx/pull/287)
  [#290](https://github.com/chfast/intx/pull/290)

## [0.9.3] — 2023-07-17

### Fixed

- Fixed buggy `__builtin_subcll` in Xcode 14.3.1 on arm64.
  [294](https://github.com/chfast/intx/pull/294)

## [0.9.2] — 2023-03-11

### Changed

- Increase tolerance to some compiler warnings (e.g. unknown pragma, unknown attribute)
  in case `intx.hpp` is used without CMake assistance.
  [#286](https://github.com/chfast/intx/pull/286) 

## [0.9.1] — 2023-01-25

### Fixed

- Fixed 32-bit Windows builds: the `_umul128` intrinsic is not available there.
  [#283](https://github.com/chfast/intx/pull/283)

## [0.9.0] — 2022-12-13

### Changed

- Optimizations for GCC compiler.
  [#279](https://github.com/chfast/intx/pull/279)
  [#281](https://github.com/chfast/intx/pull/281)
- Required CMake version increased from 3.10 to 3.16
  [#276](https://github.com/chfast/intx/pull/276)
- Simplification of many operators declarations by using `friend inline` functions.
  [#270](https://github.com/chfast/intx/pull/270)
  [#271](https://github.com/chfast/intx/pull/271)
- Benchmarks updates and fixes.
  [#274](https://github.com/chfast/intx/pull/274)
  [#275](https://github.com/chfast/intx/pull/275)
  [#277](https://github.com/chfast/intx/pull/277)

## [0.8.0] — 2022-03-15

### Added

- Added support for big-endian architectures.
  [#257](https://github.com/chfast/intx/pull/257)
- Extend endian-specific load/store helpers to work with builtin integer types.
  [#265](https://github.com/chfast/intx/pull/265)

### Changed

- The `addc()` and `subc()` have been optimized with compiler's builtins if available.
  [#250](https://github.com/chfast/intx/pull/250)
  [#251](https://github.com/chfast/intx/pull/251)
  [#253](https://github.com/chfast/intx/pull/253)
- Fixed and enabled CI testing for architectures other than x86.
  [#255](https://github.com/chfast/intx/pull/255)
- Small multiplication optimization.
  [#261](https://github.com/chfast/intx/pull/261)
- Small division optimization.
  [#263](https://github.com/chfast/intx/pull/263)
- Small comparison operators optimization for the `uint256` type.
  [#264](https://github.com/chfast/intx/pull/264)

## [0.7.1] — 2022-02-15

### Fixed

- Added support for `bswap()` of small unsigned types: `uint8_t`, `uint16_t` and `uint32_t`.
  Previously arguments where promoted to `uint64_t` what produced invalid results.
  [#247](https://github.com/chfast/intx/pull/247)

## [0.7.0] — 2021-12-17

### Changed

- The `int128.hpp` and `intx.hpp` header files have been merged. Now the whole
  library is included in single [`intx/intx.hpp`](./include/intx/intx.hpp) file.
  [#242](https://github.com/chfast/intx/pull/242)
- The `addmod()` implementation has optimized path for elliptic curve context.
  [#206](https://github.com/chfast/intx/pull/206)
- The implementation of `operator==` now explicitly performs XOR folding.
  [#245](https://github.com/chfast/intx/pull/245)


## [0.6.0] — 2021-06-25

### Changed

- **The internal representation of unsigned integers has been changed to be an array of 64-bit words. This provides types composed of any number of words** (e.g. `uint384`). 
  Previously only power-of-two numbers of words were allowed.
  This is big change that affects implementation of many operators.
  [#212](https://github.com/chfast/intx/pull/212)
  [#213](https://github.com/chfast/intx/pull/213)
- Subtraction has been slightly rewritten to make it easier for compilers to optimize it.
  The performance now matches the addition.
  [#189](https://github.com/chfast/intx/pull/189)
- Multiplication API has been cleaned up by using
  [`std::is_constant_evaluated`](https://en.cppreference.com/w/cpp/types/is_constant_evaluated)-like helpers internally.
  [#195](https://github.com/chfast/intx/pull/195)
  [#205](https://github.com/chfast/intx/pull/205)
- Shift API has been changed to use `uint64_t` as shift amount on the fundamental API level.
  [#202](https://github.com/chfast/intx/pull/202)


## [0.5.1] — 2020-12-14

### Changed

- The utility macros (e.g. `INTX_UNREACHABLE()`) have been redefined.
  [#182](https://github.com/chfast/intx/pull/182)
- Test and benchmarks improvements.
  [#175](https://github.com/chfast/intx/pull/175)


## [0.5.0] — 2020-06-23

### Added

- Support for using intx dependency as a CMake subproject
  (e.g. by git submodules or [FetchContent]).
  [#160](https://github.com/chfast/intx/pull/160)
- Support for building intx exceptions handling disabled ([-fno-exceptions]) and without RTTI ([-fno-rtti]).
  [#164](https://github.com/chfast/intx/pull/164)

### Changed

- Converted to header-only library.
  [#155](https://github.com/chfast/intx/pull/155)
  [#156](https://github.com/chfast/intx/pull/156)
- Addition / subtraction optimizations.
  [#115](https://github.com/chfast/intx/pull/115)
  [#117](https://github.com/chfast/intx/pull/117)
  [#130](https://github.com/chfast/intx/pull/130)
- Division optimizations.
  [#129](https://github.com/chfast/intx/pull/129)
  [#131](https://github.com/chfast/intx/pull/131)
  [#134](https://github.com/chfast/intx/pull/134)
  [#141](https://github.com/chfast/intx/pull/141)
  [#147](https://github.com/chfast/intx/pull/147)
  [#171](https://github.com/chfast/intx/pull/171)
- Exponentiation optimizations.
  [#128](https://github.com/chfast/intx/pull/128)
  [#146](https://github.com/chfast/intx/pull/146)
  
### Removed

- The unused `builtins.h` header has been deleted.
  [#173](https://github.com/chfast/intx/pull/173)


## [0.4.0] — 2019-08-21

### Added

- Added the `as_bytes()` casting helper.
  [#106](https://github.com/chfast/intx/pull/106)

### Changed

- The endian-specific API for converting intx types to/from bytes has been reworked.
  [#107](https://github.com/chfast/intx/pull/107)
- The `clz()` is now `constexpr` and produces correct answer for zero inputs.
  [#108](https://github.com/chfast/intx/pull/108)


## [0.3.0] — 2019-06-20

### Added

- New `addmod()` and `mulmod()` procedures have been added for the `uint256` type. 
  [#101](https://github.com/chfast/intx/pull/101)

### Changed

- Pedantic compiler warnings have been fixed.
  [#98](https://github.com/chfast/intx/pull/98)
- Performance of the division algorithm increased up to 40% 
  when dividing 256-bit values by 128-bit and 64-bit ones.
  [#99](https://github.com/chfast/intx/pull/99)


[0.12.0]: https://github.com/chfast/intx/releases/v0.12.0
[0.11.0]: https://github.com/chfast/intx/releases/v0.11.0
[0.10.1]: https://github.com/chfast/intx/releases/v0.10.1
[0.10.0]: https://github.com/chfast/intx/releases/v0.10.0
[0.9.3]: https://github.com/chfast/intx/releases/v0.9.3
[0.9.2]: https://github.com/chfast/intx/releases/v0.9.2
[0.9.1]: https://github.com/chfast/intx/releases/v0.9.1
[0.9.0]: https://github.com/chfast/intx/releases/v0.9.0
[0.8.0]: https://github.com/chfast/intx/releases/v0.8.0
[0.7.1]: https://github.com/chfast/intx/releases/v0.7.1
[0.7.0]: https://github.com/chfast/intx/releases/v0.7.0
[0.6.0]: https://github.com/chfast/intx/releases/v0.6.0
[0.5.1]: https://github.com/chfast/intx/releases/v0.5.1
[0.5.0]: https://github.com/chfast/intx/releases/v0.5.0
[0.4.0]: https://github.com/chfast/intx/releases/v0.4.0
[0.3.0]: https://github.com/chfast/intx/releases/v0.3.0

[-fno-exceptions]: https://gcc.gnu.org/onlinedocs/libstdc++/manual/using_exceptions.html#intro.using.exception.no
[-fno-rtti]: https://gcc.gnu.org/onlinedocs/gcc/C_002b_002b-Dialect-Options.html#index-fno-rtti
[FetchContent]: https://cmake.org/cmake/help/latest/module/FetchContent.html
[Keep a Changelog]: https://keepachangelog.com/en/1.0.0/
[Semantic Versioning]: https://semver.org
