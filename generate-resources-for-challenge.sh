#!/bin/bash

for x in msort-dedup quick-sort-bgw quick-sort-spdz atq-bgw atq-spdz
do
    for y in 8 12 16 20 24 28 32 36 40
    do
	./psl example -r $x-$y
    done
done
./psl example -r db-stats
./psl example -r karmakar
