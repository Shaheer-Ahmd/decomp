#!/bin/bash

if [ "$1" == "optnone" ]; then
  ./bin/clang -v -S -emit-llvm -fno-discard-value-names -O0 -Xclang -disable-O0-optnone ./demotest/main.c -o ./demotest/main.ll
else
  ./bin/clang -v -S -emit-llvm -fno-discard-value-names -O0 ./demotest/main.c -o ./demotest/main.ll
fi
