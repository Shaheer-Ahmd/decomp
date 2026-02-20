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
DIR_NAME=$(dirname "$INPUT_C")
BASE_NAME=$(basename "$INPUT_C" .c)

# 4. Construct Intermediate File Paths
LL_FILE="${DIR_NAME}/${BASE_NAME}.ll"            # ./demotest/main.ll
SP_FILE="${DIR_NAME}/${BASE_NAME}_sp.ll"         # ./demotest/main_sp.ll
OPT_FILE="${DIR_NAME}/${BASE_NAME}_sp_opt.ll"    # ./demotest/main_sp_opt.ll
EC_FILE="${DIR_NAME}/${BASE_NAME}_sp_opt_ec.ll"  # ./demotest/main_sp_opt_ec.ll

# Temporary files for the convergence loop
TEMP_CURRENT="${DIR_NAME}/${BASE_NAME}_temp_current.ll"
TEMP_NEXT="${DIR_NAME}/${BASE_NAME}_temp_next.ll"

# ==============================================================================
# Execution Steps
# ==============================================================================

echo "[1/6] Compiling C to LLVM IR..."
./runclang.sh optnone "$INPUT_C"

echo "[2/6] Running Argument Specialization..."
/usr/bin/opt -load-pass-plugin=/root/llvm/llvm/llvm-project/TrimmerPass/SpecializeArguments.so \
  -passes=specialize-args \
  -args="$SPEC_ARGS" \
  -S "$LL_FILE" -o "$SP_FILE"

echo "[3/6] Running Optimization Pipeline (Unroll + IPSCCP + DCE) until convergence..."
# Initialize the convergence loop by copying the input to our "current" temp file
cp "$SP_FILE" "$TEMP_CURRENT"
ITERATION=1

while true; do
    echo "      -> Iteration $ITERATION..."
    
    # Run the opt passes, outputting to our "next" temp file
    /usr/bin/opt -S -passes='function(mem2reg,instcombine,loop(indvars,loop-unroll-full)),ipsccp,function(dce)' \
      "$TEMP_CURRENT" -o "$TEMP_NEXT"
      
    # Compare the current and next files silently. 
    # cmp returns 0 if they are identical, 1 if they differ.
    if cmp -s "$TEMP_CURRENT" "$TEMP_NEXT"; then
        echo "      -> Converged after $ITERATION iterations!"
        # Move the final, converged result to the expected output path
        mv "$TEMP_NEXT" "$OPT_FILE"
        break
    fi
    
    # If not converged, the "next" file becomes the "current" file for the next loop
    mv "$TEMP_NEXT" "$TEMP_CURRENT"
    ((ITERATION++))
done

# Clean up the remaining temp file
rm -f "$TEMP_CURRENT"

echo "[4/6] Running P2S (Phi to stores)..."
./runp2s.sh "$OPT_FILE"

echo "[5/6] Running Edge Collapsing..."
/usr/bin/opt -load-pass-plugin=../CollapseEdges/CollapseEdges.so \
  -passes=collapse-edges \
  -S "$OPT_FILE" -o "$EC_FILE"

echo "[6/6] Lifting back to C"
./runcbe.sh "$EC_FILE"

echo "--------------------------------------------------------"
echo "Success! Final output generated at:"
echo "$EC_FILE"