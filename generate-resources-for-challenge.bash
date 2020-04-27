set -e -u -o pipefail

# Kill everything on exit, in particular on Ctrl-C.
trap 'kill $(jobs -p) &>/dev/null || :' EXIT

full=0

set x "$@"
while :; do
  shift
  case $1 in
    --full)
      full=1
    ;;
    --*)
      printf 'Unrecognized option: %s\n' "$1" >&2
    ;;
    *)
      printf 'Unrecognized operand: %s\n' "$1" >&2
    ;;
  esac
done

# Do a run and keep track of the process IDs of all runs.
pids=()
run_psl() {
  local psl=psl
  # Prefer ./psl to psl if it exists.
  if [[ -x ./psl ]]; then
    psl=./psl
  fi
  printf 'PSL starting: %s\n' $1
  >$1.log
  { printf 'Start time: ' && date; } >>$1.log
  (
    s=0
    $psl example -r $1 &>>$1.log || s=$?
    { printf 'Stop time: ' && date; } >>$1.log
    printf 'Exit status: %s\n' $s >>$1.log
    if ((s == 0)); then
      printf 'PSL done: %s\n' $1
    else
      printf 'PSL done: %s (FAILED)\n' $1
    fi
  ) &
  pid=$!
  pids+=($pid)
}

for x in quick-sort-bgw quick-sort-spdz; do
  if ((full)); then
    quick_sort_ys='2 3 4 5 6 7 8 9 10'
  else
    quick_sort_ys='2 3 4'
  fi
  for y in $quick_sort_ys; do
    run_psl $x-$y
  done
done

for x in atq-bgw atq-spdz; do
  if ((full)); then
    atq_ys='8 12 16 20 24 28 32'
  else
    atq_ys='8 12'
  fi
  for y in $atq_ys; do
    run_psl $x-$y
  done
done

if ((full)); then
  msort_ys='1 2 4 8 16'
else
  msort_ys='1 2'
fi
for y in $msort_ys; do
  run_psl msort-dedup-$y
done

if ((full)); then
  db_stats_ys='6 7 8 9 10 11 12'
else
  db_stats_ys='6 7 8 9'
fi
for y in $db_stats_ys; do
  run_psl db-stats-$y
done

run_psl karmarkar-iters-1
run_psl karmarkar-iters-2

run_psl gcd-bgv
run_psl gcd-gc

for pid in ${pids[@]}; do
  wait $pid
done

run_re() {
  printf 'traceEstimate: %s\n' $1
  printf '\nResource estimation:\n\n' >>$1.log
  python3 traceEstimate.py resources/$1.res "$@" >>$1.log
}

for y in $quick_sort_ys; do
  x=`python -c "from math import ceil; print int(ceil(float($y)/3)-1)"`
  z=`python -c "from math import ceil; print int(ceil(float($y)/2)-1)"`
  run_re quick-sort-bgw-$y -n$y -it -sm -sh -t$z
  run_re quick-sort-spdz-$y -n$y -s
done

for y in $atq_ys; do
  x=`python -c "from math import ceil; print int(ceil(float($y)/3)-1)"`
  z=`python -c "from math import ceil; print int(ceil(float($y)/2)-1)"`
  run_re atq-bgw-$y -it -n$y -t$x
  run_re atq-spdz-$y -n$y -s
done

for y in $msort_ys; do
  run_re msort-dedup-$y -n$y -df -f
done

for y in $db_stats_ys; do
  run_re db-stats-$y -f -df -n$y
done

run_re karmarkar-iters-1 -s
run_re karmarkar-iters-2 -s

run_re gcd-bgv -f
run_re gcd-gc -y -ve -n2 -s128
