#!/usr/bin/env bash
# Build intx-bench, run reciprocal benchmarks and collect CPU info.
# Usage: scripts/bench_reciprocal.sh <out_dir> <runner_label>
set -euo pipefail

out=${1:-bench-out}
label=${2:-unknown}
src=$(cd "$(dirname "$0")/.." && pwd)
build=${BUILD_DIR:-$HOME/build-bench}
mkdir -p "$out"
out=$(cd "$out" && pwd)

{
    echo "label: $label"
    echo "os: $(uname -srm)"
    if [ "$(uname)" = Darwin ]; then
        echo "cpu: $(sysctl -n machdep.cpu.brand_string)"
        sysctl hw.model hw.ncpu hw.perflevel0.physicalcpu hw.perflevel1.physicalcpu 2>/dev/null || true
    else
        model=$(lscpu | sed -n 's/^Model name: *//p' | head -1)
        vendor=$(lscpu | sed -n 's/^Vendor ID: *//p' | head -1)
        echo "cpu: $vendor $model"
        for k in 'cpu family' 'model' 'stepping' 'microcode' 'CPU implementer' 'CPU part'; do
            grep -m1 -E "^$k\s*:" /proc/cpuinfo || true
        done
        lscpu
    fi
    echo "cxx: $(${CXX:-c++} --version | head -1)"
} > "$out/cpu.txt" 2>&1
cat "$out/cpu.txt"

cmake -S "$src" -B "$build" -DCMAKE_BUILD_TYPE=Release
cmake --build "$build" --parallel --target intx-bench intx-unittests
"$build/test/intx-unittests" --gtest_filter='div.reciprocal*'
"$build/test/intx-bench" --benchmark_filter=reciprocal \
    --benchmark_repetitions=${BENCH_REPS:-7} --benchmark_report_aggregates_only=true \
    --benchmark_out="$out/bench.json" --benchmark_out_format=json
