#!/usr/bin/env bash
# tools/run-svc.sh RF_ORACLE_BIN OUT_DIR CMD [ARGS...]
#
# Start the oracle service (`rf-oracle --socket`, service/PROTOCOL.md §6) in OUT_DIR, wait for `ready`, run CMD with
# RF_ORACLE set under `/usr/bin/time -v`, record the service's CPU time over the run and its `stats` line
# (OUT_DIR/summary.txt). `{VK}` in the arguments is replaced by the service's key in hex. Every wait has a timeout.
set -euo pipefail
svc=$1; out=$2; shift 2
mkdir -p "$out"
sock="$out/oracle.sock"; fifo="$out/svc.stdin"
rm -f "$sock" "$fifo"; mkfifo "$fifo"
"$svc" --socket "$sock" < "$fifo" > "$out/service.log" 2>&1 &
spid=$!
exec 7> "$fifo"
for _ in $(seq 1 600); do
  grep -q '^ready' "$out/service.log" 2>/dev/null && break
  kill -0 "$spid" 2>/dev/null || { echo "service died" >&2; cat "$out/service.log" >&2; exit 1; }
  sleep 0.2
done
grep -q '^ready' "$out/service.log" || { echo "service not ready" >&2; exit 1; }
vk=$(awk '/^vk /{print $2}' "$out/service.log")
echo "$vk" > "$out/vk.hex"
args=(); for a in "$@"; do args+=("${a//\{VK\}/$vk}"); done
ticks() { awk '{print $14 + $15}' "/proc/$spid/stat"; }
t0=$(ticks); w0=$(date +%s.%N)
set +e
RF_ORACLE="$sock" /usr/bin/time -v "${args[@]}" > "$out/cmd.out" 2> "$out/cmd.err"
rc=$?
set -e
w1=$(date +%s.%N); t1=$(ticks)
exec 7>&-
for _ in $(seq 1 300); do kill -0 "$spid" 2>/dev/null || break; sleep 0.2; done
kill -0 "$spid" 2>/dev/null && kill "$spid"
hz=$(getconf CLK_TCK)
{
  echo "rc=$rc"
  echo "wall_s=$(echo "$w1 - $w0" | bc -l)"
  echo "service_cpu_s=$(echo "($t1 - $t0) / $hz" | bc -l)"
  grep -E 'Maximum resident|Elapsed|User time|System time|Percent of CPU' "$out/cmd.err" | sed 's/^\s*//'
  grep -E '^stats' "$out/service.log" || true
} > "$out/summary.txt"
cat "$out/cmd.out" "$out/summary.txt"
exit $rc
