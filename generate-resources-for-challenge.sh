#!/bin/bash

for x in atq-bgw atq-spdz
do
    for y in 8 12 16 20 24 28 32
    do
	./psl example -r $x-$y &
    done
done
for x in quick-sort-bgw quick-sort-spdz 
do
    for y in 2 3 4 5 6 7 8 9 10
    do
	./psl example -r $x-$y &
    done
done

for y in 1 2 4 8 16
do
    ./psl example -r msort-dedup-$y
done

for y in 6 7 8 9 10 11 12
do
    ./psl example -r db-stats-$y &
done

for y in 1 2
do
    ./psl example -r karmarkar-iters-$y
done

./psl example -r gcd-bgv &
./psl example -r gcd-gc &
