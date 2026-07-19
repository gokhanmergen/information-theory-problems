#!/usr/bin/env python3
"""Certified verification of the Courtade-Kumar conjecture at n=5 over a
closed noise interval [10^-4, 0.495] using outward-rounded interval arithmetic.
Uses Mean Value Form (MVF) and unrolled de Casteljau for fast convergence.
"""
import sys
import os
import time
import numpy as np
from mpmath import iv, mp
from multiprocessing import Pool

N, SIZE = 5, 32
iv.prec = 90

# Precompute Hamming distances for speed
HAMMING_DIST = [[bin(x ^ y).count('1') for y in range(SIZE)] for x in range(SIZE)]

def poly_counts(f):
    """Compute c[v][y][k] = #{x : f(x)=v, d(x,y)=k}."""
    f = int(f)
    c = [[[0] * (N + 1) for _ in range(SIZE)] for _ in range(2)]
    for x in range(SIZE):
        v = (f >> x) & 1
        row = HAMMING_DIST[x]
        for y in range(SIZE):
            c[v][y][row[y]] += 1
    return c

LOG2 = iv.log(iv.mpf(2))

def xlog2x(p):
    """p*log2(p) for interval p with inf(p) > 0."""
    return p * iv.log(p) / LOG2

def de_casteljau(b, t):
    t_inv = 1 - t
    r1_0 = t_inv * b[0] + t * b[1]
    r1_1 = t_inv * b[1] + t * b[2]
    r1_2 = t_inv * b[2] + t * b[3]
    r1_3 = t_inv * b[3] + t * b[4]
    r1_4 = t_inv * b[4] + t * b[5]
    
    r2_0 = t_inv * r1_0 + t * r1_1
    r2_1 = t_inv * r1_1 + t * r1_2
    r2_2 = t_inv * r1_2 + t * r1_3
    r2_3 = t_inv * r1_3 + t * r1_4
    
    r3_0 = t_inv * r2_0 + t * r2_1
    r3_1 = t_inv * r2_1 + t * r2_2
    r3_2 = t_inv * r2_2 + t * r2_3
    
    r4_0 = t_inv * r3_0 + t * r3_1
    r4_1 = t_inv * r3_1 + t * r3_2
    
    r5_0 = t_inv * r4_0 + t * r4_1
    return (
        [b[0], r1_0, r2_0, r3_0, r4_0, r5_0],
        [r5_0, r4_1, r3_2, r2_3, r1_4, b[5]]
    )

def poly_range(b, t1, t2):
    _, right1 = de_casteljau(b, t1)
    left2, _ = de_casteljau(right1, t2)
    lo = min(x.a for x in left2)
    hi = max(x.b for x in left2)
    return iv.mpf([lo, hi])

def poly_val(b, t):
    return de_casteljau(b, t)[0][5]

def g_val(b_all, hf_num, t):
    t = iv.mpf(t)
    h_py_sum = iv.mpf(0)
    for y in range(SIZE):
        for v in (0, 1):
            py = poly_val(b_all[v][y], t)
            if py > 0:
                h_py_sum -= xlog2x(py)
    halpha = -xlog2x(t) - xlog2x(1 - t)
    if hf_num in (0, SIZE):
        hf = iv.mpf(0)
    else:
        p = iv.mpf(hf_num) / SIZE
        hf = -xlog2x(p) - xlog2x(1 - p)
    return h_py_sum - halpha - (N - 1) - hf

def de_casteljau_deg4(b, t):
    t_inv = 1 - t
    r1_0 = t_inv * b[0] + t * b[1]
    r1_1 = t_inv * b[1] + t * b[2]
    r1_2 = t_inv * b[2] + t * b[3]
    r1_3 = t_inv * b[3] + t * b[4]
    
    r2_0 = t_inv * r1_0 + t * r1_1
    r2_1 = t_inv * r1_1 + t * r1_2
    r2_2 = t_inv * r1_2 + t * r1_3
    
    r3_0 = t_inv * r2_0 + t * r2_1
    r3_1 = t_inv * r2_1 + t * r2_2
    
    r4_0 = t_inv * r3_0 + t * r3_1
    return (
        [b[0], r1_0, r2_0, r3_0, r4_0],
        [r4_0, r3_1, r2_2, r1_3, b[4]]
    )

def poly_range_deg4(b, t1, t2):
    _, right1 = de_casteljau_deg4(b, t1)
    left2, _ = de_casteljau_deg4(right1, t2)
    lo = min(x.a for x in left2)
    hi = max(x.b for x in left2)
    return iv.mpf([lo, hi])

def g_interval_mvf(b_all, d_all, hf_num, a_lo, a_hi):
    mid = (iv.mpf(a_lo) + iv.mpf(a_hi)) / 2
    g_mid = g_val(b_all, hf_num, mid)
    
    t1 = iv.mpf(a_lo)
    t2 = (iv.mpf(a_hi) - t1) / (1 - t1)
    
    dJ = iv.mpf(0)
    for y in range(SIZE):
        p1 = poly_range(b_all[1][y], t1, t2)
        dp1 = poly_range_deg4(d_all[y], t1, t2)
        val = (1 - p1) / p1
        dJ += dp1 * iv.log(val) / LOG2
        
    dJ = dJ / 16
    dg = dJ - (-iv.log((1 - iv.mpf([a_lo, a_hi])) / iv.mpf([a_lo, a_hi])) / LOG2)
    
    width = iv.mpf(a_hi) - iv.mpf(a_lo)
    enclosure = g_mid + dg * iv.mpf([-width/2, width/2])
    return enclosure

def certify(rep, hf_num, a_lo, a_hi, min_width=1e-7):
    # If it is a constant function, it is trivially certified
    if hf_num in (0, SIZE):
        return True, 0, 0.5
        
    counts = poly_counts(rep)
    comb = [1, 5, 10, 10, 5, 1]
    b_all = [[None] * SIZE for _ in range(2)]
    for v in (0, 1):
        for y in range(SIZE):
            b_all[v][y] = [iv.mpf(counts[v][y][k]) / (comb[k] * 32) for k in range(6)]
            
    d_all = [None] * SIZE
    for y in range(SIZE):
        d_all[y] = [5 * (b_all[1][y][k+1] - b_all[1][y][k]) for k in range(5)]
        
    stack = [(mp.mpf(a_lo), mp.mpf(a_hi))]
    evals, worst = 0, None
    while stack:
        lo, hi = stack.pop()
        g = g_interval_mvf(b_all, d_all, hf_num, lo, hi)
        evals += 1
        if g.a > 0:
            continue
        width = float(hi - lo)
        if worst is None or width < worst:
            worst = width
        if width < min_width:
            return False, evals, width
        mid = (lo + hi) / 2
        stack.append((lo, mid))
        stack.append((mid, hi))
    return True, evals, worst

def w1(f):
    """Level-1 Fourier weight of (-1)^f, exact rational as float."""
    f = int(f)
    tot = 0
    for i in range(5):
        s = sum((1 - 2 * ((f >> x) & 1)) * (1 - 2 * ((x >> i) & 1))
                for x in range(32))
        tot += s * s
    return tot / (32 ** 2)

def worker(args):
    idx, rep = args
    hf_num = bin(rep).count('1')
    
    # Check for dictator class
    if w1(rep) > 0.9999:
        return idx, rep, "dictator", -1.0, 0
        
    a_lo, a_hi = "1e-4", "0.495"
    ok, evals, worst = certify(rep, hf_num, a_lo, a_hi)
    status = "certified" if ok else "failed"
    worst_width = worst if worst is not None else 0.0
    return idx, rep, status, worst_width, evals

def main():
    if len(sys.argv) < 4:
        print("Usage: certify_n5.py <reps.bin> <start_idx> <end_idx>")
        sys.exit(1)
        
    reps_bin = sys.argv[1]
    start_idx = int(sys.argv[2])
    end_idx = int(sys.argv[3])
    
    reps = np.fromfile(reps_bin, dtype=np.uint32)
    n_reps = len(reps)
    print(f"Loaded {n_reps} class representatives from {reps_bin}")
    
    # Clamp bounds to actual array size
    start_idx = max(0, start_idx)
    end_idx = min(n_reps - 1, end_idx)
    
    # Setup ledger file
    ledger_dir = os.path.join(os.path.dirname(__file__), "n5_cert")
    os.makedirs(ledger_dir, exist_ok=True)
    ledger_path = os.path.join(ledger_dir, f"shard_{start_idx}_{end_idx}.txt")
    
    # Remove existing file to start fresh
    if os.path.exists(ledger_path):
        os.remove(ledger_path)
        
    print(f"Certifying indices {start_idx} to {end_idx} on [1e-4, 0.495]...")
    
    tasks = [(idx, int(reps[idx])) for idx in range(start_idx, end_idx + 1)]
    
    t0 = time.time()
    
    # Run in parallel using a process pool
    num_cpus = os.cpu_count() or 4
    print(f"Using {num_cpus} parallel processes")
    
    with Pool(num_cpus) as pool:
        with open(ledger_path, "w") as f_ledger:
            # imap preserves the order of tasks
            for idx, rep, status, worst_width, evals in pool.imap(worker, tasks):
                # Write to append-only ledger
                f_ledger.write(f"{idx},{rep},{status},{worst_width}\n")
                f_ledger.flush()
                
                # Print progress
                if (idx - start_idx) % 100 == 0 or idx == start_idx or idx == end_idx:
                    elapsed = time.time() - t0
                    rate = (idx - start_idx + 1) / elapsed if elapsed > 0 else 0
                    print(f"[{idx}] {rep:#010x}: {status} (evals: {evals}, worst width: {worst_width:.3e}) "
                          f"| {idx - start_idx + 1}/{len(tasks)} done | {rate:.1f} reps/s")
                    
    elapsed = time.time() - t0
    print(f"Finished {end_idx - start_idx + 1} classes in {elapsed:.1f}s")

if __name__ == "__main__":
    main()
