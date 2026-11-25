# intx

[![readme style: standard][readme style standard badge]][standard readme]
[![Conan Center](https://img.shields.io/conan/v/intx)](https://conan.io/center/recipes/intx)
[![GitPOAP Badge](https://public-api.gitpoap.io/v1/repo/chfast/intx/badge)](https://www.gitpoap.io/gh/chfast/intx)

High‑performance multiprecision integer library for C++

The intx header-only C++20 library provides allocation-free extended precision
integer types. They are implemented as arrays of `std::uint64_t` words
and closely match the behavior of built-in types.

## Usage

To build, test or benchmark.

```bash
git clone https://github.com/chfast/intx
cd intx

cmake -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build --parallel

build/test/intx-unittests
build/test/intx-bench
```

## Formal verification

The `@pre` and `@post` sections in the documentation of functions in
[`intx.hpp`](include/intx/intx.hpp) are specifications written in [Lean 4]
(the notation is introduced in [Theorem Proving in Lean 4]).
The `fv/main` branch contains proofs that the RV64 machine code
of these functions satisfies their specifications.
The proofs cover selected template instances, mostly for `uint256`.
See the [`fv/main` README][fv/main README]
for what is proved and what is assumed.
Functions without `@post` are not verified.
The `@note FV:` sections mark the cases not covered by the proofs.

## Maintainer

Paweł Bylica [@chfast]

## License

Licensed under the [Apache License, Version 2.0].


[@chfast]: https://github.com/chfast
[Lean 4]: https://lean-lang.org
[Theorem Proving in Lean 4]: https://lean-lang.org/theorem_proving_in_lean4/
[fv/main README]: https://github.com/chfast/intx/blob/fv/main/lean/README.md
[Apache License, Version 2.0]: LICENSE
[standard readme]: https://github.com/RichardLitt/standard-readme

[readme style standard badge]: https://img.shields.io/badge/readme%20style-standard-brightgreen.svg?style=flat-square

