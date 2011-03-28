#!/bin/bash 

# SimSoC-Cert, a toolkit for generating certified processor simulators
# See the COPYRIGHTS and LICENSE files.

if [ $# -eq 1 ]; then
    SEED=$1
    ./main -ipc ../arm6/arm6inst.arm -isyntax ../arm6/arm6syntax.dat \
           -idec ../arm6/arm6dec.dat -s $SEED -obin-test > test.bin
    ./main -ipc ../arm6/arm6inst.arm -isyntax ../arm6/arm6syntax.dat \
           -idec ../arm6/arm6dec.dat -s $SEED -oasm-test test
    ../elf/bin2elf test.bin test.elf 
    perl -pi -e "s/CPY/MOV/" test.asm
    ../simlight2/simlight -Adec ../pseudocode/test.elf | perl -p -e "s/[^\t]*\t//" | perl -p -e "s/CPY/MOV/" >tst.asm
    diff -b test.asm tst.asm

    exit 0
fi

# run tests for one hour
set -e
COUNTER=0
while [  $COUNTER -lt 36000 ]; do
    echo The counter is $COUNTER
    ./main -ipc ../arm6/arm6inst.arm -isyntax ../arm6/arm6syntax.dat \
           -idec ../arm6/arm6dec.dat -s $COUNTER -obin-test > test.bin
    ./main -ipc ../arm6/arm6inst.arm -isyntax ../arm6/arm6syntax.dat \
           -idec ../arm6/arm6dec.dat -s $COUNTER -oasm-test test
    ../elf/bin2elf test.bin test.elf
    perl -pi -e "s/CPY/MOV/" test.asm
    ../simlight2/simlight -Adec ../pseudocode/test.elf | perl -p -e "s/[^\t]*\t//" | perl -p -e "s/CPY/MOV/" >tst.asm
    diff -b test.asm tst.asm
    let COUNTER=COUNTER+1
done
