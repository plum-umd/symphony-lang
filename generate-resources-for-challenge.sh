#!/bin/bash

set -e -u -o pipefail

# Kill everything on exit, in particular on Ctrl-C.
trap 'kill $(jobs -p) &>/dev/null || :' EXIT

# Do a run, keeping track of the names and process IDs of all runs.
pids=()
names=()
run() {
  local psl=psl
  # Prefer ./psl to psl if it exists.
  if [[ -x ./psl ]]; then
    psl=./psl
  fi
  $psl example -r $1 &
  pid=$!
  pids+=($pid)
  names[$pid]=$1
  printf 'started: %s\n' $1
}

for x in quick-sort-bgw quick-sort-spdz atq-bgw atq-spdz
do
    for y in 8 12 16 20 24 28 32 36 40
    do
        run $x-$y
    done
done
for y in 8 16 32
do
    run msort-dedup-$y
done

run db-stats-small
run db-stats-medium
run db-stats-large
run karmakar
run gcd-bgv
run gcd-gc

for pid in ${pids[@]}; do
  printf 'waiting: %s\n' ${names[$pid]}
  wait $pid || printf 'FAILED: %s\n' ${names[$pid]}
done
