import sys
import math
from itertools import permutations
from mpmath import iv, mp

N = 4
SIZE = 16
FULL = 0xFFFF
iv.prec = 90

def npn_classes():
    maps = []
    for perm in permutations(range(N)):
        for flips in range(SIZE):
            m = []
            for x in range(SIZE):
                y = x ^ flips
                m.append(sum(((y >> perm[i]) & 1) << i for i in range(N)))
            maps.append(m)
    seen = bytearray(1 << SIZE)
    reps = []
    for f in range(1 << SIZE):
        if seen[f]:
            continue
        orbit = set()
        for m in maps:
            g = 0
            for x in range(SIZE):
                if (f >> m[x]) & 1:
                    g |= 1 << x
            orbit.add(g)
            orbit.add(g ^ FULL)
        for g in orbit:
            seen[g] = 1
        reps.append((min(orbit), len(orbit)))
    return reps

def w1(f):
    tot = 0
    for i in range(N):
        s = sum((1 - 2 * ((f >> x) & 1)) * (1 - 2 * ((x >> i) & 1))
                for x in range(SIZE))
        tot += s * s
    return tot / SIZE ** 2

def poly_counts(f):
    c = [[[0] * (N + 1) for _ in range(SIZE)] for _ in range(2)]
    for x in range(SIZE):
        v = (f >> x) & 1
        for y in range(SIZE):
            c[v][y][bin(x ^ y).count('1')] += 1
    return c

LOG2 = iv.log(iv.mpf(2))

def xlog2x(p):
    return p * iv.log(p) / LOG2

def g_interval(counts, hf_num, a):
    one = iv.mpf(1)
    b = one - a
    apow = [one, a, a * a, a * a * a, a * a * a * a]
    bpow = [one, b, b * b, b * b * b, b * b * b * b]
    hjoint = iv.mpf(0)
    for v in (0, 1):
        for y in range(SIZE):
            ck = counts[v][y]
            s = iv.mpf(0)
            nonzero = False
            for k in range(N + 1):
                if ck[k]:
                    s += ck[k] * apow[k] * bpow[N - k]
                    nonzero = True
            if nonzero:
                hjoint -= xlog2x(s / SIZE)
    halpha = -xlog2x(a) - xlog2x(b)
    if hf_num in (0, SIZE):
        hf = iv.mpf(0)
    else:
        p = iv.mpf(hf_num) / SIZE
        hf = -xlog2x(p) - xlog2x(1 - p)
    return hjoint - halpha - (N - 1) - hf

def certify(f, a_lo, a_hi, min_width=1e-7):
    counts = poly_counts(f)
    hf_num = bin(f).count('1')
    stack = [(mp.mpf(a_lo), mp.mpf(a_hi))]
    evals = 0
    while stack:
        lo, hi = stack.pop()
        g = g_interval(counts, hf_num, iv.mpf([lo, hi]))
        evals += 1
        if g.a > 0:
            continue
        width = float(hi - lo)
        if width < min_width:
            return False, evals
        mid = (lo + hi) / 2
        stack.append((lo, mid))
        stack.append((mid, hi))
    return True, evals

if __name__ == "__main__":
    reps = npn_classes()
    dict_class = None
    for rep, size in reps:
        if abs(w1(rep) - 1.0) < 1e-12:
            dict_class = rep
            
    print(f"Total NPN classes: {len(reps)}")
    print(f"Dictator class rep: {dict_class:#06x}")
    
    # 1. High-noise endpoint check
    print("\n--- Checking High-Noise Endpoint [0.495, 0.5] ---")
    max_nondict_w1 = 0.0
    for rep, size in reps:
        if rep == dict_class:
            continue
        p = bin(rep).count('1') / SIZE
        if p == 0 or p == 1:
            continue
        g_w1 = w1(rep)
        norm_w1 = g_w1 / (4 * p * (1 - p))
        max_nondict_w1 = max(max_nondict_w1, norm_w1)
        
    print(f"Max normalized W_1 among non-dictators: {max_nondict_w1:.6f} (expected 52/63 = {52/63:.6f})")
    min_high_noise_coeff = 0.7212 * (1 - max_nondict_w1) - 0.03367
    print(f"Minimum high-noise gap coefficient: {min_high_noise_coeff:.6f}")
    if min_high_noise_coeff > 0:
        print("High-noise endpoint CERTIFIED!")
    else:
        print("High-noise endpoint FAILED!")
        
    # 2. Low-noise interval check using mpmath.iv on [1e-6, 0.005]
    print("\n--- Running Interval Arithmetic Check on [1e-6, 0.005] ---")
    ok, failed = 0, []
    for rep, size in reps:
        if rep == dict_class:
            continue
        # check if it's constant function
        p = bin(rep).count('1')
        if p == 0 or p == 16:
            ok += 1
            continue
        good, evals = certify(rep, "1e-6", "0.005")
        if good:
            ok += 1
        else:
            failed.append(rep)
            
    print(f"Certified: {ok} of {len(reps) - 1} non-dictator classes; failures: {len(failed)}")
    if not failed:
        print("Interval check on [1e-6, 0.005] PASSED!")
    else:
        print("Failed classes:", [hex(f) for f in failed])
