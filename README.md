# intx

[![readme style: standard][readme style standard badge]][standard readme]
[![GitPOAP Badge](https://public-api.gitpoap.io/v1/repo/chfast/intx/badge)](https://www.gitpoap.io/gh/chfast/intx)

Extended precision integer C++ library

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

## Maintainer

Paweł Bylica [@chfast]

## License

Licensed under the [Apache License, Version 2.0].


[@chfast]: https://github.com/chfast
[Apache License, Version 2.0]: LICENSE
[standard readme]: https://github.com/RichardLitt/standard-readme

[readme style standard badge]: https://img.shields.io/badge/readme%20style-standard-brightgreen.svg?style=flat-square

