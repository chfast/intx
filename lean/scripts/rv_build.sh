#!/usr/bin/env bash
# Compiles IntxRV/Api.cpp for RV64 and generates the Lean sources from it, which are not in git:
# the machine code IntxRV/Gen/Code/ and the proofs of its decoding IntxRV/Gen/Decode/ and
# IntxRV/Gen/Decodes/ (rv_gen.py), the specifications from the documentation of intx.hpp
# IntxRV/Gen/Api/ and Intx/Gen/Spec.lean, the proofs of the specifications IntxRV/Gen/Proof/, and
# their checks Checks/Gen/IntxRVApi.lean and Checks/Gen/IntxSpec.lean (rv_api.py). Run it before
# lake build and after a change of intx.hpp or IntxRV/Api.cpp.
#   CXX: clang++ 21 with the RISC-V target (default: clang++; CI uses clang 21 of Ubuntu 26.04)
#   LD: the LLVM linker (default: ld.lld)
#   RV64_SYSROOT: the riscv64-linux-gnu sysroot with the libstdc++ headers
#                 (default: /usr/riscv64-linux-gnu of the g++-riscv64-linux-gnu package)
set -euo pipefail

lean_dir=$(cd "$(dirname "$0")/.." && pwd)
cxx=${CXX:-clang++}
ld=${LD:-ld.lld}
sysroot=${RV64_SYSROOT:-/usr/riscv64-linux-gnu}
gcc_ver=$(ls "$sysroot/include/c++" | sort -V | tail -1)
out=$lean_dir/.lake/build/rv
mkdir -p "$out"

# The proofs are of the machine code of clang 21: another version emits other code.
cxx_major=$("$cxx" -dumpversion | cut -d. -f1)
if [ "$cxx_major" != 21 ]; then
    echo "$cxx is clang $cxx_major: set CXX to clang++ 21" >&2
    exit 1
fi

# rv64im with the lp64 ABI, the target of the zkVMs (the code is the same as of rv64imafd with
# lp64d: integer code has no F/D instructions).
# -mno-relax: the assembler resolves the branches, so the function sections have no relocations.
# The sysroot of the Linux distributions has the glibc headers of lp64d only: lp64 gets the list of
# the stub functions of glibc of lp64d (the same functions, none of which intx calls).
mkdir -p "$out/include/gnu"
if [ ! -e "$sysroot/include/gnu/stubs-lp64.h" ]; then
    cp "$sysroot/include/gnu/stubs-lp64d.h" "$out/include/gnu/stubs-lp64.h"
fi
flags=(--target=riscv64-linux-gnu -march=rv64im -mabi=lp64 -mno-relax
    -O2 -std=c++20 -DNDEBUG -ffunction-sections -fdata-sections -fno-asynchronous-unwind-tables
    -nostdinc++ -isystem "$sysroot/include/c++/$gcc_ver"
    -isystem "$sysroot/include/c++/$gcc_ver/riscv64-linux-gnu" -isystem "$sysroot/include"
    -isystem "$out/include" --sysroot="$sysroot" -I "$lean_dir/../include")
"$cxx" "${flags[@]}" -c "$lean_dir/IntxRV/Api.cpp" -o "$out/Api.o"
# The declarations of the namespace intx with their documentation comments, for rv_api.py.
"$cxx" "${flags[@]}" -fsyntax-only -Xclang -ast-dump=json -Xclang -ast-dump-filter=intx \
    "$lean_dir/IntxRV/Api.cpp" > "$out/Api.json"

LD="$ld" python3 "$lean_dir/scripts/rv_gen.py" "$lean_dir" "$out/stack.json" "$out/Api.o" \
    "$out/image.elf"
python3 "$lean_dir/scripts/rv_api.py" "$out/Api.json" "$out/stack.json" "$lean_dir"
