#!/bin/bash

# Default source file
SRC="./demotest/main.ll"
if [ -n "$1" ]; then
  SRC="$1"
fi

# Default destination file (based on source)
DST="${SRC%.ll}_opt.ll"
if [ -n "$2" ]; then
  DST="$2"
fi

./bin/opt -S -passes='mem2reg,instcombine,simplifycfg' "$SRC" -o "$DST" --color && ./runp2s.sh "$DST"
