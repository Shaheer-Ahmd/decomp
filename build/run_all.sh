#!/bin/bash

# 1. Check for correct number of arguments
if [ "$#" -ne 2 ]; then
    echo "Usage: $0 <path_to_c_file> <specialize_arguments>"
    echo "Example: $0 ./demotest/main.c \"tcas 1 2 3 ...\""
    exit 1
fi

# 2. Assign Input Variables
INPUT_C="$1"
SPEC_ARGS="$2"

# 3. Derive Directory and Base Filenames
# If input is ./demotest/main.c:
# DIR_NAME  -> ./demotest
# BASE_NAME -> main
DIR_NAME=$(dirname "$INPUT_C")
BASE_NAME=$(basename "$INPUT_C" .c)

# 4. Construct Intermediate File Paths
LL_FILE="${DIR_NAME}/${BASE_NAME}.ll"            # ./demotest/main.ll
SP_FILE="${DIR_NAME}/${BASE_NAME}_sp.ll"         # ./demotest/main_sp.ll
OPT_FILE="${DIR_NAME}/${BASE_NAME}_sp_opt.ll"    # ./demotest/main_sp_opt.ll
EC_FILE="${DIR_NAME}/${BASE_NAME}_sp_opt_ec.ll"  # ./demotest/main_sp_opt_ec.ll

# ==============================================================================
# Execution Steps
# ==============================================================================

echo "[1/5] Compiling C to LLVM IR..."
# Assuming runclang.sh accepts the input file as an argument. 
# If runclang.sh is hardcoded, replace this line with: clang -S -emit-llvm -Xclang -disable-O0-optnone "$INPUT_C" -o "$LL_FILE"
./runclang.sh optnone "$INPUT_C"

echo "[2/5] Running Argument Specialization..."
/usr/bin/opt -load-pass-plugin=/root/llvm/llvm/llvm-project/TrimmerPass/SpecializeArguments.so \
  -passes=specialize-args \
  -args="$SPEC_ARGS" \
  -S "$LL_FILE" -o "$SP_FILE"

echo "[3/5] Running Optimization Pipeline (Unroll + IPSCCP + DCE)..."
/usr/bin/opt -S -passes='function(mem2reg,instcombine,loop(indvars,loop-unroll-full)),ipsccp,function(dce)' \
  "$SP_FILE" -o "$OPT_FILE"

echo "[4/5] Running P2S (Pointer to Stack)..."
./runp2s.sh "$OPT_FILE"

echo "[5/5] Running Edge Collapsing..."
/usr/bin/opt -load-pass-plugin=../CollapseEdges/CollapseEdges.so \
  -passes=collapse-edges \
  -S "$OPT_FILE" -o "$EC_FILE"

echo "--------------------------------------------------------"
echo "Success! Final output generated at:"
echo "$EC_FILE"