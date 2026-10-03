#!/usr/bin/env bash
# Build intx-bench with clang, run funnel shift (SHLD/SHRD) benchmarks and collect CPU info.
# On x86-64 also build with the LLVM "slow-shld" tuning (no SHLD/SHRD) and run intx benchmarks.
# Usage: scripts/bench_shld.sh <out_dir> <runner_label>
set -euo pipefail

out=${1:-bench-out}
label=${2:-unknown}
src=$(cd "$(dirname "$0")/.." && pwd)
mkdir -p "$out"
out=$(cd "$out" && pwd)
export CXX=${CXX:-clang++}
export CC=${CC:-clang}

{
    echo "label: $label"
    echo "os: $(uname -srm)"
    if [ "$(uname)" = Darwin ]; then
        echo "cpu: $(sysctl -n machdep.cpu.brand_string)"
        sysctl hw.model hw.ncpu 2>/dev/null || true
    else
        model=$(lscpu | sed -n 's/^Model name: *//p' | head -1)
        vendor=$(lscpu | sed -n 's/^Vendor ID: *//p' | head -1)
        echo "cpu: $vendor $model"
        for k in 'cpu family' 'model' 'stepping' 'microcode' 'flags'; do
            grep -m1 -E "^$k\s*:" /proc/cpuinfo || true
        done
        lscpu
    fi
    echo "cxx: $($CXX --version | head -1)"
} > "$out/cpu.txt" 2>&1
head -5 "$out/cpu.txt"

intx_filter='div<uint|mod<|shift<uint|div_normalize'
run() {  # run <build_dir> <filter> <json>
    "$1/test/intx-bench" --benchmark_filter="$2" \
        --benchmark_repetitions=${BENCH_REPS:-5} --benchmark_report_aggregates_only=true \
        --benchmark_out="$out/$3" --benchmark_out_format=json
}

build=$HOME/build-shld-default
cmake -S "$src" -B "$build" -DCMAKE_BUILD_TYPE=Release
cmake --build "$build" --parallel --target intx-bench
run "$build" 'fsh_|words' shld-micro.json
run "$build" "$intx_filter" intx-default.json

case "$(uname -m)" in
x86_64 | amd64)
    build=$HOME/build-shld-slow
    cmake -S "$src" -B "$build" -DCMAKE_BUILD_TYPE=Release \
        -DCMAKE_CXX_FLAGS="-Xclang -target-feature -Xclang +slow-shld"
    cmake --build "$build" --parallel --target intx-bench
    run "$build" "$intx_filter" intx-slow-shld.json
    ;;
esac
