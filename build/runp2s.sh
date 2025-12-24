./bin/opt -load-pass-plugin=../myplugin/build/RemovePhiToStores.so -passes=remove-phi-to-stores -S ./demotest/main.ll -o ./demotest/main_p2s.ll
