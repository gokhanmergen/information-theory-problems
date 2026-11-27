# Reviewer check (2026-11-27, Claim 4, numerical only): partial-decode-compress-forward with |U| <= 4,
# |Yhat| = 3, 40 random restarts; does it beat the DF/CF time-sharing envelope 0.557912 at R0 = 0.4?
# Run: python3 combined4.py 0.4 1 40   (the run logged in combined4_04.out used seed 1; the default
# seed 0 gives best 0.5579123752, also <= 0.5579124). Runtime: about 2-3 min. Needs numpy, scipy.
"""Combined partial-DF + CF superposition scheme for the primitive BSC relay
(p1 destination, p2 relay).  Derived (standard NNC-style analysis, see reviewer note):
  R < min{ I(U;Yr) + I(X;Y,Yh|U),
           I(U;Yr) + I(X;Y|U) + R0 - I(Yh;Yr|X,Y,U),
           I(X;Y) + R0 - I(Yh;Yr|X,Y,U) }
over p(u) p(x|u) p(yh|yr,u).  It contains the DF/CF time-sharing line
(U in {c, d0, d1}).  Question: does it beat the DF-CF time-sharing envelope at R0=0.4?
Floating point, local optimisation: numerical evidence only."""
import sys
import numpy as np
from scipy.optimize import minimize

p1, p2 = 0.2, 0.1
W1 = np.array([[1 - p1, p1], [p1, 1 - p1]])
W2 = np.array([[1 - p2, p2], [p2, 1 - p2]])


def H(P):
    P = P.ravel()
    P = P[P > 1e-300]
    return float(-(P * np.log2(P)).sum())


def sm(z, axis=-1):
    z = z - z.max(axis, keepdims=True)
    e = np.exp(z)
    return e / e.sum(axis, keepdims=True)


K, L = 4, 3


def unpack(x):
    pu = sm(x[:K])
    px_u = 1 / (1 + np.exp(-x[K:2 * K]))
    Px_u = np.stack([1 - px_u, px_u], 1)                    # [u, x]
    T = sm(x[2 * K:].reshape(K, 2, L), axis=2)              # [u, yr, yh]
    return pu, Px_u, T


def terms(x, R0):
    pu, Px_u, T = unpack(x)
    # J[u, x, y, yr, yh]
    J = (pu[:, None, None, None, None] * Px_u[:, :, None, None, None] * W1[None, :, :, None, None]
         * W2[None, :, None, :, None] * T[:, None, None, :, :])
    Hs = lambda keep: H(J.sum(tuple(i for i in range(5) if i not in keep)))
    I_u_yr = Hs((0,)) + Hs((3,)) - Hs((0, 3))
    # I(X;Y,Yh|U) = H(X,U)+H(Y,Yh,U)-H(X,Y,Yh,U)-H(U)
    I_x_yyh_u = Hs((0, 1)) + Hs((0, 2, 4)) - Hs((0, 1, 2, 4)) - Hs((0,))
    I_x_y_u = Hs((0, 1)) + Hs((0, 2)) - Hs((0, 1, 2)) - Hs((0,))
    I_x_y = Hs((1,)) + Hs((2,)) - Hs((1, 2))
    # I(Yh;Yr|X,Y,U) = H(Yh,X,Y,U)+H(Yr,X,Y,U)-H(all)-H(X,Y,U)
    I_c = Hs((0, 1, 2, 4)) + Hs((0, 1, 2, 3)) - H(J) - Hs((0, 1, 2))
    return (I_u_yr + I_x_yyh_u, I_u_yr + I_x_y_u + R0 - I_c, I_x_y + R0 - I_c)


def ts_init(lam):
    """U = c (prob 1-lam): X uniform, Yh = Yr; U = d_x (prob lam/2): X = x, Yh const."""
    big = 30.0
    x = np.zeros(K + K + K * 2 * L)
    x[:K] = np.log([1 - lam, lam / 2, lam / 2, 1e-9])
    x[K:2 * K] = [0.0, -big, big, 0.0]
    T = np.full((K, 2, L), -big)
    T[0, 0, 0] = big; T[0, 1, 1] = big
    T[1, :, 2] = big; T[2, :, 2] = big
    x[2 * K:] = T.ravel()
    return x


def optimise(R0, x0):
    n = len(x0)
    z0 = np.concatenate([x0, [min(terms(x0, R0))]])
    cons = [{'type': 'ineq', 'fun': (lambda z, i=i: terms(z[:n], R0)[i] - z[n])} for i in range(3)]
    res = minimize(lambda z: -z[n], z0, method='SLSQP', constraints=cons,
                   options={'maxiter': 2000, 'ftol': 1e-13})
    return min(terms(res.x[:n], R0)), res.x[:n]


if __name__ == '__main__':
    from math import log2
    h = lambda q: -(q * log2(q) + (1 - q) * log2(1 - q))
    R0 = float(sys.argv[1]) if len(sys.argv) > 1 else 0.4
    D = h(p1) - h(p2); SW = h(p1 * (1 - p2) + (1 - p1) * p2)
    lam = (SW - R0) / (SW - D)
    x0 = ts_init(lam)
    print('time-sharing init value', min(terms(x0, R0)), terms(x0, R0))
    best = optimise(R0, x0)
    print('optimised from TS init:', best[0])
    pu, Px_u, T = unpack(best[1])
    print(' p(u)=', np.round(pu, 4), ' P(X=1|u)=', np.round(Px_u[:, 1], 4))
    print(' T=', np.round(T, 4).tolist())
    rng = np.random.default_rng(int(sys.argv[2]) if len(sys.argv) > 2 else 0)
    for r in range(int(sys.argv[3]) if len(sys.argv) > 3 else 40):
        x0 = rng.normal(0, 3, K + K + K * 2 * L)
        v, xx = optimise(R0, x0)
        if v > best[0]:
            best = (v, xx)
            print(f'  restart {r}: new best {v:.7f}', flush=True)
    print('best combined value at R0=', R0, ':', best[0])
    pu, Px_u, T = unpack(best[1])
    print(' p(u)=', np.round(pu, 4), ' P(X=1|u)=', np.round(Px_u[:, 1], 4))
    print(' T=', np.round(T, 4).tolist())
    print(' terms', terms(best[1], R0))
