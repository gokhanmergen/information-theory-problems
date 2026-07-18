#!/usr/bin/env python3
"""Primitive relay channel with BSC components: exact DF / CF / cutset curves.

Model (Cover 1987 primitive relay channel):
    X uniform on {0,1};  Z = X xor N1, N1 ~ Bern(d1)  (relay observation)
                         Y = X xor N2, N2 ~ Bern(d2)  (direct link), N1 _|_ N2
    Relay -> destination: noiseless bit pipe of rate R0.

Bounds (Kim 2007, "Coding techniques for primitive relay channels"):
    cutset(R0) = min{ I(X;Y,Z),  I(X;Y) + R0 }
    DF(R0)     = min{ I(X;Z),    I(X;Y) + R0 }
    CF(R0)     = max_q I(X; Y, Zh)  s.t.  I(Z; Zh | Y) <= R0,
                 Zh = Z xor Q, Q ~ Bern(q)   (BSC test channel; a restriction)

All mutual informations computed by exact enumeration of the 16-atom joint
distribution of (X, Z, Zh, Y). Uniform X is optimal by channel symmetry for
the unrestricted expressions. Stdlib only.
"""
import math
import sys


def h(p):
    if p <= 0 or p >= 1:
        return 0.0
    return -p * math.log2(p) - (1 - p) * math.log2(1 - p)


def conv(a, b):  # crossover of two cascaded BSCs
    return a * (1 - b) + (1 - a) * b


def joint_atoms(d1, d2, q):
    """P(x, z, zh, y) for all 16 atoms."""
    atoms = {}
    for x in (0, 1):
        for z in (0, 1):
            for zh in (0, 1):
                for y in (0, 1):
                    p = 0.5
                    p *= d1 if z != x else 1 - d1
                    p *= q if zh != z else 1 - q
                    p *= d2 if y != x else 1 - d2
                    atoms[(x, z, zh, y)] = p
    return atoms


def mi(atoms, ivars, jvars, cond=()):
    """I(ivars; jvars | cond) from an atom dict keyed by (x, z, zh, y)."""
    def marg(sel):
        m = {}
        for k, p in atoms.items():
            kk = tuple(k[i] for i in sel)
            m[kk] = m.get(kk, 0.0) + p
        return m

    a = marg(ivars + jvars + cond)
    b = marg(ivars + cond)
    c = marg(jvars + cond)
    d = marg(cond) if cond else {(): 1.0}
    s = 0.0
    for k, p in a.items():
        if p <= 0:
            continue
        ki = k[:len(ivars)]
        kj = k[len(ivars):len(ivars) + len(jvars)]
        kc = k[len(ivars) + len(jvars):]
        s += p * math.log2(p * d[kc] / (b[ki + kc] * c[kj + kc]))
    return s


X, Z, ZH, Y = 0, 1, 2, 3


def bounds(d1, d2, r0, qgrid=2001):
    ixy = 1 - h(d2)
    ixz = 1 - h(d1)
    ixyz = mi(joint_atoms(d1, d2, 0.0), (X,), (Y, Z))
    cutset = min(ixyz, ixy + r0)
    df = min(ixz, ixy + r0)
    cf = ixy  # q = 1/2 always feasible
    for i in range(qgrid):
        q = 0.5 * i / (qgrid - 1)
        atoms = joint_atoms(d1, d2, q)
        if mi(atoms, (Z,), (ZH,), (Y,)) <= r0 + 1e-12:
            cf = max(cf, mi(atoms, (X,), (Y, ZH)))
    return ixy, ixz, ixyz, df, cf, cutset


def main():
    d1, d2 = (float(a) for a in sys.argv[1:3]) if len(sys.argv) >= 3 else (0.1, 0.2)
    ixy, ixz, ixyz, *_ = bounds(d1, d2, 0)
    hzy = h(conv(d1, d2))  # H(Z|Y): Z = Y xor (N1 xor N2)
    print(f"d1={d1} d2={d2}: I(X;Y)={ixy:.6f} I(X;Z)={ixz:.6f} "
          f"I(X;Y,Z)={ixyz:.6f} H(Z|Y)={hzy:.6f}")
    print(f"{'R0':>6} {'DF':>9} {'CF':>9} {'best':>9} {'cutset':>9} {'gap':>9}")
    for r0 in (0.0, 0.05, 0.1, 0.15, 0.2, 0.25, 0.3, 0.4, 0.5, 0.7, round(hzy, 6), 1.0):
        _, _, _, df, cf, cs = bounds(d1, d2, r0)
        best = max(df, cf)
        print(f"{r0:>6} {df:9.6f} {cf:9.6f} {best:9.6f} {cs:9.6f} {cs - best:9.6f}")


if __name__ == "__main__":
    main()
