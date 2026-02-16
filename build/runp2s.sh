#!/bin/bash

# Check if a file path was provided
if [ -z "$1" ]; then
    echo "Usage: $0 <path_to_ll_file>"
    exit 1
fi

SRC="$1"
# Extract the base name without the .ll extension
# e.g., ./demotest/main.ll becomes ./demotest/main
BASE="${SRC%.*}"
OUT="${BASE}.ll"

./bin/opt -load-pass-plugin=../myplugin/build/RemovePhiToStores.so \
    -passes=remove-phi-to-stores \
    -S "$SRC" -o "$OUT"

echo "Processed: $SRC -> $OUT"