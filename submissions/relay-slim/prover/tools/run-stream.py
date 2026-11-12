#!/usr/bin/env python3
"""tools/run-stream.py PROVER RF_ORACLE_BIN OUT [--steps M] [--n N | --lengths a,b,c,...] [--setup DIR] [--taskset CPUS]

A local imitation of the runner's stream (PROVER.md §3; untrusted, for development): one service lifetime;
`prover first` on chainA/chainB, then `prover step` M-1 times; per request the handshake (start the process,
read `ready` within 10 s, stage the inputs and rename them into the work directory, start the clock, write
`go`, wait for `done` or exit, stop the clock), the step time, and the checks a runner can make without the
badge: the file parses strictly (harness/FORMAT.md), the statement is the runner's own
(`rf-oracle --leaves` gives leafStmt(chainEnd s n) n), and the header's statement fields agree. The Lean V_S
is checked separately (logs/rptest). Environment passes through (LVM_PARAMS, LEANVM_NUM_THREADS, LVM_LOG...).
Every wait has a timeout.
"""
import hashlib, json, os, secrets, struct, subprocess, sys, time

def keccak256(data):
    # Keccak-256 (Ethereum padding 0x01 ... 0x80), pure Python
    RC = [0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000, 0x000000000000808B,
          0x0000000080000001, 0x8000000080008081, 0x8000000000008009, 0x000000000000008A, 0x0000000000000088,
          0x0000000080008009, 0x000000008000000A, 0x000000008000808B, 0x800000000000008B, 0x8000000000008089,
          0x8000000000008003, 0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
          0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]
    ROT = [[0, 36, 3, 41, 18], [1, 44, 10, 45, 2], [62, 6, 43, 15, 61], [28, 55, 25, 21, 56], [27, 20, 39, 8, 14]]
    M = (1 << 64) - 1
    rol = lambda x, n: ((x << n) | (x >> (64 - n))) & M if n else x
    def f(A):
        for rc in RC:
            C = [A[x][0] ^ A[x][1] ^ A[x][2] ^ A[x][3] ^ A[x][4] for x in range(5)]
            D = [C[(x - 1) % 5] ^ rol(C[(x + 1) % 5], 1) for x in range(5)]
            A = [[A[x][y] ^ D[x] for y in range(5)] for x in range(5)]
            B = [[0] * 5 for _ in range(5)]
            for x in range(5):
                for y in range(5):
                    B[y][(2 * x + 3 * y) % 5] = rol(A[x][y], ROT[x][y])
            A = [[B[x][y] ^ (~B[(x + 1) % 5][y] & B[(x + 2) % 5][y]) for y in range(5)] for x in range(5)]
            A[0][0] ^= rc
        return A
    rate = 136
    m = bytearray(data) + b"\x01"
    m += b"\x00" * ((-len(m)) % rate)
    m[-1] |= 0x80
    A = [[0] * 5 for _ in range(5)]
    for o in range(0, len(m), rate):
        blk = m[o:o + rate]
        for i in range(rate // 8):
            x, y = i % 5, i // 5
            A[x][y] ^= int.from_bytes(blk[8 * i:8 * i + 8], "little")
        A = f(A)
    out = b"".join(A[i % 5][i // 5].to_bytes(8, "little") for i in range(4))
    return out

def parse_signed(b):
    """FORMAT.md, strict: (pi, [(q, a)], (idx, ots, path)) or raise."""
    o = 0
    def take(n):
        nonlocal o
        if n > len(b) - o:
            raise ValueError("a length runs past the end")
        r = b[o:o + n]; o += n
        return r
    u64 = lambda: struct.unpack("<Q", take(8))[0]
    pi = take(u64())
    m = u64()
    tr = []
    for _ in range(m):
        q = take(u64()); a = take(32); tr.append((q, a))
    idx = u64(); ots = [take(32) for _ in range(133)]; path = [take(32) for _ in range(16)]
    if o != len(b):
        raise ValueError("bytes after path_15")
    return pi, tr, (idx, ots, path)

def leaf_stmt(svc, s_hex, n):
    r = subprocess.run([svc, "--leaves", "--threads", "4"], input=f"{s_hex} {n}\n", capture_output=True, text=True, timeout=120)
    assert r.returncode == 0, r.stderr
    return bytes.fromhex(r.stdout.strip())

def node_stmt(c1, c2):
    return keccak256(b"\x4e" + c1 + c2)

def main():
    a = sys.argv[1:]
    prover, svc, out = a[0], a[1], os.path.abspath(a[2])
    opt = lambda k, d=None: a[a.index(k) + 1] if k in a else d
    steps = int(opt("--steps", "3"))
    if opt("--lengths"):
        lengths = [int(x) for x in opt("--lengths").split(",")]
    else:
        lengths = [int(opt("--n", "100"))] * (steps + 1)
    assert len(lengths) >= steps + 1
    os.makedirs(out, exist_ok=True)
    sock = os.path.join(out, "oracle.sock")
    if os.path.exists(sock):
        os.remove(sock)
    service = subprocess.Popen([svc, "--socket", sock], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, text=True)
    vk = None
    t0 = time.time()
    while time.time() - t0 < 120:
        line = service.stdout.readline()
        if line.startswith("vk "):
            vk = line.split()[1]
        if line.strip() == "ready":
            break
    assert vk, "service not ready"
    env = dict(os.environ, RF_ORACLE=sock, HOME=out)
    if opt("--setup"):
        env["RF_SETUP"] = os.path.abspath(opt("--setup"))
    starts = [secrets.token_hex(32) for _ in lengths]
    prev_stmt, prev_bin, results = None, None, []
    for i in range(steps):
        work = os.path.join(out, f"step{i + 1}")
        stage = os.path.join(out, f"stage{i + 1}")
        for d in (work, stage):
            os.makedirs(d, exist_ok=True)
            for f in os.listdir(d):
                os.remove(os.path.join(d, f))
        open(os.path.join(work, "vk.hex"), "w").write(vk + "\n")
        if i == 0:
            mode = "first"
            files = {"chainA.json": json.dumps({"n": lengths[0], "start": starts[0]}),
                     "chainB.json": json.dumps({"n": lengths[1], "start": starts[1]})}
            want = node_stmt(leaf_stmt(svc, starts[0], lengths[0]), leaf_stmt(svc, starts[1], lengths[1]))
        else:
            mode = "step"
            files = {"prev.stmt": prev_stmt.hex() + "\n", "chain.json": json.dumps({"n": lengths[i + 1], "start": starts[i + 1]})}
            want = node_stmt(prev_stmt, leaf_stmt(svc, starts[i + 1], lengths[i + 1]))
        for k, v in files.items():
            open(os.path.join(stage, k), "w").write(v)
        if prev_bin is not None:
            open(os.path.join(stage, "prev.bin"), "wb").write(prev_bin)
        cmd = [prover, mode, work]
        if opt("--taskset"):
            cmd = ["taskset", "-c", opt("--taskset")] + cmd
        errf = open(os.path.join(out, f"step{i + 1}.err"), "w")
        ts = time.time()
        p = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=errf, text=True, env=env, cwd=work)
        line = p.stdout.readline()
        ready_s = time.time() - ts
        assert line.strip() == "ready", f"step {i + 1}: no ready ({line!r})"
        assert ready_s <= 10, f"ready after {ready_s:.1f} s"
        tc = time.time()
        for k in list(files) + (["prev.bin"] if prev_bin is not None else []):
            os.rename(os.path.join(stage, k), os.path.join(work, k))
        p.stdin.write("go\n"); p.stdin.flush()
        done = p.stdout.readline().strip()
        p.kill()
        p.wait(timeout=60)
        dt = time.time() - tc
        assert done == "done", f"step {i + 1}: {done!r} (exit {p.returncode}); see {errf.name}"
        b = open(os.path.join(work, "proof.bin"), "rb").read()
        pi, tr, sig = parse_signed(b)
        # the statement the header proves (b = 1: nodeStmt c_L (leafStmt h n))
        bflag, c_l, n, h = struct.unpack("<Q", pi[8:16])[0], pi[48:80], struct.unpack("<Q", pi[112:120])[0], pi[120:152]
        hdr = node_stmt(c_l, keccak256(b"\x4c" + h + struct.pack("<Q", n))) if bflag == 1 else keccak256(b"\x4c" + h + struct.pack("<Q", n))
        ok = hdr == want
        results.append(dict(step=i + 1, mode=mode, n=lengths[i + 1] if i else lengths[0] + lengths[1], time_s=round(dt, 3),
                            ready_s=round(ready_s, 3), file_bytes=len(b), pi_bytes=len(pi), queries=len(tr), sig_idx=sig[0],
                            statement_ok=ok))
        print(json.dumps(results[-1]), flush=True)
        assert ok, "the proof's statement is not the runner's"
        open(os.path.join(out, f"step{i + 1}.signed"), "wb").write(b)
        open(os.path.join(out, f"step{i + 1}.stmt"), "w").write(want.hex() + "\n")
        prev_stmt, prev_bin = want, b
    service.stdin.close()
    for line in service.stdout:
        if line.startswith("stats"):
            print(line.strip())
    service.wait(timeout=60)
    json.dump(results, open(os.path.join(out, "stream.json"), "w"), indent=1)

if __name__ == "__main__":
    main()
