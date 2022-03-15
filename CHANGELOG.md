# Changelog for intx

Documentation of all notable changes to the **intx** project.

The format is based on [Keep a Changelog],
and this project adheres to [Semantic Versioning].


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
