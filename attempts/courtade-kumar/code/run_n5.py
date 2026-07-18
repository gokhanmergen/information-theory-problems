#!/usr/bin/env python3
"""Driver for exhaustive_n5: shards [0, 2^31) across processes, merges, and
independently recheck the winning masks in Python. Stdlib only."""
import itertools
import math
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).parent
TOTAL = 1 << 31
SHARDS = 8
TOL = 1e-9
N, SIZE = 5, 32

ANTI_DICTATORS = {sum(1 << x for x in range(SIZE) if not (x >> i) & 1) for i in range(N)}
DICTATORS = {m ^ 0xFFFFFFFF for m in ANTI_DICTATORS}
# single-input flips of all 10 (anti-)dictators, restricted to the f(11111)=0 half
SINGLE_FLIP_HALF = {m ^ (1 << x) for m in ANTI_DICTATORS | DICTATORS
                    for x in range(SIZE) if not ((m ^ (1 << x)) >> 31) & 1}


def mi_exact(mask, alpha):
    """Independent from-scratch recheck (no incremental updates)."""
    joint = {}
    for x in range(SIZE):
        fx = (mask >> x) & 1
        for y in range(SIZE):
            d = bin(x ^ y).count("1")
            joint[(fx, y)] = joint.get((fx, y), 0.0) + \
                (alpha ** d) * ((1 - alpha) ** (N - d)) / SIZE
    pf, py = {}, {}
    for (v, y), p in joint.items():
        pf[v] = pf.get(v, 0.0) + p
        py[y] = py.get(y, 0.0) + p
    return sum(p * math.log2(p / (pf[v] * py[y]))
               for (v, y), p in joint.items() if p > 0)


def run_alpha(alpha):
    step = TOTAL // SHARDS
    procs = [subprocess.Popen(
        [str(HERE / "exhaustive_n5"), str(alpha), str(k * step),
         str(TOTAL if k == SHARDS - 1 else (k + 1) * step)],
        stdout=subprocess.PIPE, text=True) for k in range(SHARDS)]
    tops = []  # (value, count, masks) from every shard's best and second
    for p in procs:
        out, _ = p.communicate()
        assert p.returncode == 0
        for line in out.strip().splitlines():
            parts = line.split()
            val, cnt = float(parts[1]), int(parts[3])
            masks = [int(m, 16) for m in parts[5:]]
            tops.append((val, cnt, masks))
    best = max(t[0] for t in tops)
    n_best = sum(c for v, c, _ in tops if abs(v - best) < TOL)
    best_masks = set(itertools.chain.from_iterable(
        m for v, _, m in tops if abs(v - best) < TOL))
    rest = [t for t in tops if t[0] < best - TOL]
    second = max(t[0] for t in rest)
    n_second = sum(c for v, c, _ in rest if abs(v - second) < TOL)
    second_masks = set(itertools.chain.from_iterable(
        m for v, _, m in rest if abs(v - second) < TOL))

    bound = 1 - (-alpha * math.log2(alpha) - (1 - alpha) * math.log2(1 - alpha))
    recheck_best = max(abs(mi_exact(m, alpha) - best) for m in best_masks)
    recheck_second = max(abs(mi_exact(m, alpha) - second)
                         for m in list(second_masks)[:20])
    print(f"alpha={alpha}")
    print(f"  bound 1-h(a)      = {bound:.12f}")
    print(f"  max over 2^31 fns = {best:.12f}  (count {n_best})")
    print(f"  max == bound      : {abs(best - bound) < 1e-9}")
    print(f"  maximizers == 5 anti-dictators : "
          f"{best_masks == ANTI_DICTATORS and n_best == 5}")
    print(f"  second            = {second:.12f}  (count {n_second}, "
          f"gap {best - second:.6f})")
    print(f"  second ⊆ single-flip class ({len(SINGLE_FLIP_HALF)} fns) : "
          f"{second_masks <= SINGLE_FLIP_HALF and n_second == len(SINGLE_FLIP_HALF)}")
    print(f"  from-scratch recheck max err: best {recheck_best:.2e}, "
          f"second {recheck_second:.2e}")
    sys.stdout.flush()


if __name__ == "__main__":
    for alpha in (float(a) for a in (sys.argv[1:] or ["0.05", "0.10", "0.20"])):
        run_alpha(alpha)
