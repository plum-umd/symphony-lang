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
  >$1.log
  printf 'Start time: '; date >>$1.log
  (
    s=0
    $psl example -r $1 &>>$1.log || s=$?
    printf 'Stop time: '; date >>$1.log
    printf 'Exit status: %s\n' $s >>$1.log
  ) &
  pid=$!
  pids+=($pid)
  names[$pid]=$1
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
  wait $pid || :
done
