#!/bin/bash

for x in quick-sort-bgw quick-sort-spdz atq-bgw atq-spdz
do
    for y in 8 12 16 20 24 28 32 36 40
    do
	./psl example -r $x-$y &
    done
done
for y in 8 16 32
do
    ./psl example -r msort-dedup-$y
done

./psl example -r db-stats-small
./psl example -r db-stats-medium
./psl example -r db-stats-large
./psl example -r karmakar
./psl example -r gcd-bgv
./psl example -r gcd-gc
