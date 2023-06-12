#!/bin/bash
if [ "$#" -ne 3 ]; then
  echo "run-sematest.sh <dir (e.g., arm)> <N> <HOL Light command>"
  echo "This script runs the simulator ('<dir>/proofs/simulator.ml') that tests the semantics "
  echo "of instructions. It launches N simulators in parallel, and uses the given "
  echo "HOL Light command to run them."
  exit 1
fi

s2n_bignum_arch=$1
nproc=$2
hol_light_cmd=$3
cd $s2n_bignum_arch

log_paths=()
children_pids=()
for (( i = 1; i <= $nproc; i++ )) ; do
  log_path=`mktemp`
  log_paths[$i]=$log_path
  (cd ..; (echo 'loadt "arm/proofs/simulator.ml";;') | $hol_light_cmd >$log_path 2>&1) &
  background_pid=$!
  children_pids[$i]=$background_pid
  echo "- Child $i (pid $background_pid) has started (log path: $log_path)"
done

for (( i = 1; i <= $nproc; i++ )) ; do
  wait ${children_pids[$i]}
  exitcode=$?
  echo "- Last 7 lines of simulator $i's log (path: ${log_paths[$i]}):"
  tail -7 ${log_paths[$i]}
  if [ $exitcode -ne 0 ]; then
    echo "Simulator $i failed!"
    exit 1
  else
    echo "- Simulator $i finished successfully"
  fi
done
