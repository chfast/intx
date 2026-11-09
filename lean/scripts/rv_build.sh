#!/usr/bin/env bash
# Compiles IntxRV/Api.cpp for RV64 and regenerates the Lean sources from it: the machine code
# IntxRV/Gen/Code.lean (rv_gen.py), the specifications from the documentation of intx.hpp
# IntxRV/Gen/Api.lean and Intx/Gen/Spec.lean, and their checks Checks/IntxRVApi.lean and
# Checks/IntxSpec.lean (rv_api.py).
#   CXX: clang++ with the RISC-V target (default: clang++; CI uses clang 21 of Ubuntu 26.04)
#   RV64_SYSROOT: the riscv64-linux-gnu sysroot with the libstdc++ headers
#                 (default: /usr/riscv64-linux-gnu of the g++-riscv64-linux-gnu package)
set -euo pipefail

lean_dir=$(cd "$(dirname "$0")/.." && pwd)
cxx=${CXX:-clang++}
sysroot=${RV64_SYSROOT:-/usr/riscv64-linux-gnu}
gcc_ver=$(ls "$sysroot/include/c++" | sort -V | tail -1)
out=$lean_dir/.lake/build/rv
mkdir -p "$out"

# rv64imafd with the lp64d ABI of the Linux distributions; integer code has no F/D instructions.
# -mno-relax: the assembler resolves the branches, so the function sections have no relocations.
flags=(--target=riscv64-linux-gnu -march=rv64imafd -mabi=lp64d -mno-relax
    -O2 -std=c++20 -DNDEBUG -ffunction-sections -fno-asynchronous-unwind-tables
    -nostdinc++ -isystem "$sysroot/include/c++/$gcc_ver"
    -isystem "$sysroot/include/c++/$gcc_ver/riscv64-linux-gnu" -isystem "$sysroot/include"
    --sysroot="$sysroot" -I "$lean_dir/../include")
"$cxx" "${flags[@]}" -c "$lean_dir/IntxRV/Api.cpp" -o "$out/Api.o"
# The declarations of the namespace intx with their documentation comments, for rv_api.py.
"$cxx" "${flags[@]}" -fsyntax-only -Xclang -ast-dump=json -Xclang -ast-dump-filter=intx \
    "$lean_dir/IntxRV/Api.cpp" > "$out/Api.json"

python3 "$lean_dir/scripts/rv_gen.py" "$lean_dir" "$out/stack.json" "$out/Api.o"
python3 "$lean_dir/scripts/rv_api.py" "$out/Api.json" "$out/stack.json" "$lean_dir"
