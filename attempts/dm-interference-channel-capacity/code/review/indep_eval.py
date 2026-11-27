# Reviewer check (2026-11-27, Claim 10): evaluates the seven Lean HK quantities on W^{(x)k} for
# the attempt's 3-letter scheme, NXY's two-letter point and the bit-flipped variant (60 digits).
# Run: python3 indep_eval.py
# Runtime: under 1 s. Needs mpmath.
"""Independent evaluator (reviewer) for the k-letter schemes on the NXY binary CZI channel.

Builds the full two-output channel W((x1,x2) -> (y1,y2)) with Y2 = X2 from NXY Table 1 row 1
(P(Y1=0|x1,x2) = [[1, 1/2],[1, 0]], rows x1, cols x2), forms W^{(x)k} on X^k, and evaluates the
seven Lean hanKobayashiRegion quantities a1..d2 for a joint law p(q)p(u1,x1|q)p(u2,x2|q) with
generic (here trivial) Q,U1,U2, in mpmath at 60 digits.  Then checks the 7 constraints at
r = k*(R1,R2) and reports 2R1+R2.
"""
import itertools
import mpmath as mp

mp.mp.dps = 60
HALF = mp.mpf(1) / 2
P_Y1_0 = {(0, 0): mp.mpf(1), (0, 1): HALF, (1, 0): mp.mpf(1), (1, 1): mp.mpf(0)}


def w1(y1, x1, x2):
    p0 = P_Y1_0[(x1, x2)]
    return p0 if y1 == 0 else 1 - p0


def W(x1, x2, y1, y2):          # single-letter full channel
    return w1(y1, x1, x2) * (1 if y2 == x2 else 0)


def Wk(x1s, x2s, y1s, y2s):
    pr = mp.mpf(1)
    for a, b, c, d in zip(x1s, x2s, y1s, y2s):
        pr *= W(a, b, c, d)
        if pr == 0:
            return pr
    return pr


def joint(k, PQ, P1, P2):
    """PQ: dict q->prob; P1[q]: dict (u1, x1tuple)->prob; P2[q]: dict (u2, x2tuple)->prob.
    Returns dict (q,u1,x1,u2,x2,y1,y2)->prob (only nonzero)."""
    J = {}
    ys = list(itertools.product((0, 1), repeat=k))
    for qv, pq in PQ.items():
        for (u1, x1), a in P1[qv].items():
            if a == 0:
                continue
            for (u2, x2), b in P2[qv].items():
                if b == 0:
                    continue
                y2 = x2                    # clean link: only y2 = x2 has mass
                for y1 in ys:
                    t = pq * a * b * Wk(x1, x2, y1, y2)
                    if t != 0:
                        J[(qv, u1, x1, u2, x2, y1, y2)] = J.get((qv, u1, x1, u2, x2, y1, y2), 0) + t
    return J


def H(J, idx):
    m = {}
    for key, v in J.items():
        kk = tuple(key[i] for i in idx)
        m[kk] = m.get(kk, 0) + v
    return -mp.fsum(v * mp.log(v, 2) for v in m.values() if v > 0)


def CMI(J, A, B, C):  # I(A;B|C) with index lists
    return H(J, A + C) + H(J, B + C) - H(J, A + B + C) - H(J, C)


Qi, U1i, X1i, U2i, X2i, Y1i, Y2i = range(7)


def hk_quantities(J):
    a1 = CMI(J, [X1i], [Y1i], [U2i, Qi])
    a2 = CMI(J, [X2i], [Y2i], [U1i, Qi])
    b1 = CMI(J, [X1i, U2i], [Y1i], [Qi])
    b2 = CMI(J, [X2i, U1i], [Y2i], [Qi])
    c1 = CMI(J, [X1i], [Y1i], [U1i, U2i, Qi])
    c2 = CMI(J, [X2i], [Y2i], [U1i, U2i, Qi])
    d1 = CMI(J, [X1i, U2i], [Y1i], [U1i, Qi])
    d2 = CMI(J, [X2i, U1i], [Y2i], [U2i, Qi])
    return a1, a2, b1, b2, c1, c2, d1, d2


def check(k, p1, p2, label):
    """p1, p2: dicts x-tuple -> prob (TIN: Q, U1, U2 constant)."""
    assert abs(mp.fsum(p1.values()) - 1) < mp.mpf(10) ** -50 and abs(mp.fsum(p2.values()) - 1) < mp.mpf(10) ** -50
    assert all(v >= 0 for v in list(p1.values()) + list(p2.values()))
    PQ = {0: mp.mpf(1)}
    P1 = {0: {(0, x): v for x, v in p1.items()}}
    P2 = {0: {(0, x): v for x, v in p2.items()}}
    J = joint(k, PQ, P1, P2)
    a1, a2, b1, b2, c1, c2, d1, d2 = hk_quantities(J)
    S1, S2 = a1, a2               # TIN rates for W^{(x)k}: (I(X1^k;Y1^k), I(X2^k;Y2^k))
    cons = [S1 <= a1, S2 <= a2, S1 + S2 <= b1 + c2, S1 + S2 <= c1 + b2, S1 + S2 <= d1 + d2,
            2 * S1 + S2 <= b1 + c1 + d2, S1 + 2 * S2 <= b2 + c2 + d1]
    R1, R2 = S1 / k, S2 / k
    print(f"[{label}] k={k}: a1..d2 = {[mp.nstr(v, 12) for v in (a1, a2, b1, b2, c1, c2, d1, d2)]}")
    print(f"   7 Lean HK constraints at r=k*(R1,R2): {cons}")
    print(f"   R1 = {mp.nstr(R1, 15)}, R2 = {mp.nstr(R2, 15)}, 2R1+R2 = {mp.nstr(2 * R1 + R2, 18)}")
    return 2 * R1 + R2


def bits(k):
    return list(itertools.product((0, 1), repeat=k))


if __name__ == "__main__":
    # 1-letter NXY optimum (p0, q0)
    p0 = mp.mpf("0.507829413"); q0 = mp.mpf("0.436538150")
    check(1, {(0,): p0, (1,): 1 - p0}, {(0,): q0, (1,): 1 - q0}, "1-letter TIN at NXY (p0,q0)")
    # NXY 2-letter point
    p1 = {x: 0 for x in bits(2)}; p1[(0, 0)] = p0; p1[(1, 1)] = 1 - p0
    p2 = {(0, 0): mp.mpf("0.36") * q0, (0, 1): mp.mpf("0.64") * q0, (1, 0): mp.mpf("0.64") * q0,
          (1, 1): 1 - mp.mpf("1.64") * q0}
    check(2, p1, p2, "NXY 2-letter point")
    # attempt's 3-letter scheme (Claim 10)
    a = mp.mpf("0.434823"); b = mp.mpf("0.136205"); c = mp.mpf("0.154298"); d = 1 - 3 * b - 3 * c
    print("   d = 1-3b-3c =", d)
    p1 = {x: 0 for x in bits(3)}; p1[(0, 0, 0)] = a; p1[(1, 1, 1)] = 1 - a
    p2 = {}
    for x in bits(3):
        w = sum(x)
        p2[x] = mp.mpf(0) if w == 0 else (b if w == 1 else (c if w == 2 else d))
    v3 = check(3, p1, p2, "attempt 3-letter scheme")
    # Same with X2 relabelled so that 'weight' counts zeros (sanity: bit convention matters)
    p2s = {x: p2[tuple(1 - t for t in x)] for x in bits(3)}
    check(3, p1, p2s, "bit-flipped X2 (convention sanity, should be much worse)")
