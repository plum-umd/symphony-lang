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
  printf 'starting: %s\n' $1
  >$1.log
  { printf 'Start time: ' && date; } >>$1.log
  (
    s=0
    $psl example -r $1 &>>$1.log || s=$?
    { printf 'Stop time: ' && date; } >>$1.log
    printf 'Exit status: %s\n' $s >>$1.log
    printf 'done: %s\n' $1
  ) &
  pid=$!
  pids+=($pid)
  names[$pid]=$1
}

for x in quick-sort-bgw quick-sort-spdz
do
    for y in 2 3 4 5 6 7 8 9 10
    do
        run $x-$y
    done
done

for x in atq-bgw atq-spdz
do
    for y in 8 12 16 20 24 28 32
    do
      	run $x-$y
    done
done

for y in 1 2 4 8 16
do
    run msort-dedup-$y
done

for y in 6 7 8 9 10 11 12
do
    run db-stats-$y
done

	 
run karmarkar-iters-1
run karmarkar-iters-2

run gcd-bgv
run gcd-gc

for pid in ${pids[@]}; do
  wait $pid || printf 'FAILED: %s\n' ${names[$pid]}
done
