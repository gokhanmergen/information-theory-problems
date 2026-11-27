"""
Crossed degraded product 3-DMBC (attempt Claim 5):
    X = (X1, X2),  Y2 = BSC_a(X1),  Y3 = BSC_a(X2),  Y1 = (BSC_b(X1), BSC_b(X2)),  b > a,
so Y1's first coordinate is a degraded version of Y2 and its second a degraded version of Y3.

(1) Evaluates the literal Lean transcription of `nairElGamalInnerBound` (ne_region_check.py)
    at U1 = const, U2 = X1, U3 = X2, X uniform, and checks that the corner
    P* = (2(c_s - c_w), 2(2 c_w - c_s)) of the capacity region lies in it
    (c_s = 1 - h(a), c_w = 1 - h(b)).
(2) [heuristic, non-certified] Multi-start maximisation of lam*R0 + R1 over the
    Borade-Zheng-Trott / straightforward Korner-Marton region
        R0 <= min_j I(U;Y_j),  R1 <= I(X;Y1|U)
    with |U| = 5 (Caratheodory-type bound |X|+1), for lam = 1.5, compared with the capacity
    value lam*R0* + R1*.
"""
import itertools, math, sys
import numpy as np
from scipy.optimize import minimize
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from ne_region_check import lean_region_constraints

def h(p):
    return 0.0 if p in (0.0, 1.0) else -(p*math.log2(p) + (1-p)*math.log2(1-p))

def channels(a, b):
    xs = list(itertools.product((0, 1), (0, 1)))
    W1 = {x: {(x[0] ^ e1, x[1] ^ e2): (b if e1 else 1-b)*(b if e2 else 1-b)
              for e1 in (0, 1) for e2 in (0, 1)} for x in xs}
    W2 = {x: {x[0]: 1-a, 1-x[0]: a} for x in xs}
    W3 = {x: {x[1]: 1-a, 1-x[1]: a} for x in xs}
    return xs, W1, W2, W3

def part1(a, b):
    xs, W1, W2, W3 = channels(a, b)
    cs, cw = 1-h(a), 1-h(b)
    R0, R1 = 2*(cs-cw), 2*(2*cw-cs)
    P = {(0, x[0], x[1], x): 0.25 for x in xs}
    cons, q = lean_region_constraints(P, W1, W2, W3)
    print(f'a={a}, b={b}: c_s={cs:.6f}, c_w={cw:.6f}; corner P*=({R0:.6f}, {R1:.6f})')
    ok = True
    for a0, a1, rhs in cons:
        lhs = a0*R0 + a1*R1
        flag = lhs <= rhs + 1e-12
        ok &= flag
        print(f'   {a0}R0+{a1}R1 = {lhs:.6f} <= {rhs:.6f}  {"ok" if flag else "VIOLATED"}')
    print('   P* in Lean NE region:', ok)
    return R0, R1, cs, cw

def bzt_value(z, lam, a, b, k=5):
    # z parameterises p(u) (k logits) and p(x|u) (k x 4 logits)
    pu = np.exp(z[:k]); pu /= pu.sum()
    px = np.exp(z[k:].reshape(k, 4)); px /= px.sum(1, keepdims=True)
    # outputs: Y2 depends on x1, Y3 on x2, Y1 on (x1,x2)
    x1 = np.array([0, 0, 1, 1]); x2 = np.array([0, 1, 0, 1])
    def bsc(bit, eps):  # P(Y=1|bit)
        return np.where(bit == 1, 1-eps, eps)
    py2u = px @ bsc(x1, a); py3u = px @ bsc(x2, a)          # P(Y=1|U=u)
    # Y1 = (y11, y12) in 4 values
    P1 = np.zeros((4, 4))
    for xi in range(4):
        for yi, (y11, y12) in enumerate(itertools.product((0, 1), (0, 1))):
            p11 = (1-b) if y11 == x1[xi] else b
            p12 = (1-b) if y12 == x2[xi] else b
            P1[xi, yi] = p11*p12
    py1u = px @ P1
    def Hrow(M):
        M = np.clip(M, 1e-300, 1); return -(M*np.log2(M)).sum(-1)
    def hb(t):
        t = np.clip(t, 1e-300, 1-1e-16); return -(t*np.log2(t)+(1-t)*np.log2(1-t))
    I2 = hb(pu @ py2u) - pu @ hb(py2u)
    I3 = hb(pu @ py3u) - pu @ hb(py3u)
    I1u = Hrow(pu @ py1u) - pu @ Hrow(py1u)
    HY1gX = 2*h(b)
    IXY1gU = pu @ Hrow(py1u) - HY1gX
    R0 = min(I1u, I2, I3)
    return lam*R0 + IXY1gU

def part2(a, b, lam=1.5, starts=300, seed=0):
    rng = np.random.default_rng(seed)
    best = -1
    for _ in range(starts):
        z0 = rng.normal(size=25)*2
        r = minimize(lambda z: -bzt_value(z, lam, a, b), z0, method='Nelder-Mead',
                     options=dict(maxiter=6000, xatol=1e-9, fatol=1e-12))
        best = max(best, -r.fun)
    return best

if __name__ == '__main__':
    a, b = 0.05, 0.11
    R0, R1, cs, cw = part1(a, b)
    lam = 1.5
    cap = lam*R0 + R1
    bzt = part2(a, b, lam)
    print(f'lam={lam}: capacity max lam*R0+R1 = {cap:.6f} (at P*); '
          f'best BZT value found = {bzt:.6f}; gap {cap-bzt:.6f}  [heuristic]')
