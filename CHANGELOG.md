# Changelog for intx

Documentation of all notable changes to the **intx** project.

The format is based on [Keep a Changelog],
and this project adheres to [Semantic Versioning].


## [0.3.0] - 2019-06-20
### Added
- New `addmod()` and `mulmod()` procedures have been added for the `uint256` type 
  ([#101](https://github.com/chfast/intx/pull/101)).
### Changed
- Pedantic compiler warnings have been fixed 
  ([#98](https://github.com/chfast/intx/pull/98)).
- Performance of the division algorithm increased up to 40% 
  when dividing 256-bit values by 128-bit and 64-bit ones 
  ([#99](https://github.com/chfast/intx/pull/99)).

[0.3.0]: https://github.com/chfast/intx/releases/v0.2.0

[Keep a Changelog]: https://keepachangelog.com/en/1.0.0/
[Semantic Versioning]: https://semver.org
