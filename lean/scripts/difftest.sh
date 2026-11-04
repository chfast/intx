#!/usr/bin/env bash
# The differential test of the Lean model: on the vectors of difftest.cpp the model must give the
# results of the C++ mulmod(), and they must be x * y % m.
# Usage: scripts/difftest.sh [count [seed]]
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p .lake/difftest
${CXX:-c++} -std=c++20 -O2 -I ../include scripts/difftest.cpp -o .lake/difftest/gen
lake build intxmodel
.lake/difftest/gen "${1:-100000}" "${2:-0}" | .lake/build/bin/intxmodel
