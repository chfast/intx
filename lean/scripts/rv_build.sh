#!/usr/bin/env bash
# Compiles IntxRV/Examples.cpp for RV64 and regenerates IntxRV/Gen/Code.lean and
# IntxRV/Examples.lean from it.
#   CXX: clang++ with the RISC-V target (default: clang++; CI uses clang 21 of Ubuntu 26.04)
#   RV64_SYSROOT: the riscv64-linux-gnu sysroot with the libstdc++ headers
#                 (default: /usr/riscv64-linux-gnu of the g++-riscv64-linux-gnu package)
set -euo pipefail

lean_dir=$(cd "$(dirname "$0")/.." && pwd)
cxx=${CXX:-clang++}
sysroot=${RV64_SYSROOT:-/usr/riscv64-linux-gnu}
gcc_ver=$(ls "$sysroot/include/c++" | sort -V | tail -1)
obj=$lean_dir/.lake/build/rv/Examples.o
mkdir -p "$(dirname "$obj")"

# rv64imafd with the lp64d ABI of the Linux distributions; integer code has no F/D instructions.
# -mno-relax: the assembler resolves the branches, so the function sections have no relocations.
"$cxx" --target=riscv64-linux-gnu -march=rv64imafd -mabi=lp64d -mno-relax \
    -O2 -std=c++20 -DNDEBUG -ffunction-sections -fno-asynchronous-unwind-tables \
    -nostdinc++ -isystem "$sysroot/include/c++/$gcc_ver" \
    -isystem "$sysroot/include/c++/$gcc_ver/riscv64-linux-gnu" -isystem "$sysroot/include" \
    --sysroot="$sysroot" -I "$lean_dir/../include" \
    -c "$lean_dir/IntxRV/Examples.cpp" -o "$obj"

python3 "$lean_dir/scripts/rv_gen.py" "$obj" "$lean_dir/IntxRV/Examples.cpp" "$lean_dir"
