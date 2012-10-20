#!/bin/bash

./main -s 1 -ipc ../arm6/arm6inst.arm -isyntax ../arm6/arm6syntax.dat -idec ../arm6/arm6dec.dat -oasm-test test_asm

./main -s 1 -ipc ../arm6/arm6inst.arm -isyntax ../arm6/arm6syntax.dat -idec ../arm6/arm6dec.dat -obin-test > test_bin.bin

../tools/bin2elf/bin2elf test_bin.bin test_bin.elf

../arm6/simlight2/simlight -Adec test_bin.elf | perl -p -e "s/[^\t]*\t//" >../../simgen/dec_test.asm

diff dec_test.asm test_asm.asm