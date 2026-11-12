#!/usr/bin/env bash
# tools/run-batch.sh PROVER RF_ORACLE_BIN OUT_DIR LOG_N [prover args...]
#
# WP-4 measurement: start the oracle service (`rf-oracle --socket`, service/PROTOCOL.md §6), wait for `ready`,
# run `PROVER batch --log-n LOG_N --sign` against it under `/usr/bin/time -v` (peak RSS), and record the
# service's CPU time over the prover's run (utime + stime of its process, /proc/PID/stat) and its `stats` line.
# Environment passes through (LVM_CPU, LEANVM_NUM_THREADS, LVM_PROF, LVM_ALLOC, …). Every wait has a timeout.
set -euo pipefail
prover=$1; svc=$2; out=$3; logn=$4; shift 4
mkdir -p "$out"
sock="$out/oracle.sock"
rm -f "$sock"
fifo="$out/svc.stdin"
rm -f "$fifo"; mkfifo "$fifo"
"$svc" --socket "$sock" < "$fifo" > "$out/service.log" 2>&1 &
spid=$!
exec 7> "$fifo"          # hold the service's stdin open; closing it stops the service
for _ in $(seq 1 600); do
  grep -q '^ready' "$out/service.log" 2>/dev/null && break
  kill -0 "$spid" 2>/dev/null || { echo "service died" >&2; cat "$out/service.log" >&2; exit 1; }
  sleep 0.2
done
grep -q '^ready' "$out/service.log" || { echo "service not ready" >&2; exit 1; }
ticks() { awk '{print $14 + $15}' "/proc/$spid/stat"; }
t0=$(ticks)
w0=$(date +%s.%N)
set +e
RF_ORACLE="$sock" /usr/bin/time -v "$prover" batch --log-n "$logn" --sign "$@" > "$out/prover.out" 2> "$out/prover.err"
rc=$?
set -e
w1=$(date +%s.%N)
t1=$(ticks)
exec 7>&-
for _ in $(seq 1 300); do kill -0 "$spid" 2>/dev/null || break; sleep 0.2; done
kill -0 "$spid" 2>/dev/null && kill "$spid"
hz=$(getconf CLK_TCK)
{
  echo "rc=$rc"
  echo "wall_s=$(echo "$w1 - $w0" | bc -l)"
  echo "service_cpu_s=$(echo "($t1 - $t0) / $hz" | bc -l)"
  grep -E 'Maximum resident|Elapsed|User time|System time|Percent of CPU' "$out/prover.err" | sed 's/^\s*//'
  grep -E '^stats' "$out/service.log" || true
} > "$out/summary.txt"
cat "$out/prover.out" "$out/summary.txt"
exit $rc
