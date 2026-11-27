# Reviewer check (2026-11-27, Claim 8): recomputes the noisy-CES certificate numbers without
# the author's code: exact MAP error, A1, A2, Blahut-Arimoto capacity bounds, rho* bounds (40 digits).
# Run: python3 indep_check.py
# Runtime: about 1 s. Needs mpmath.
# Independent recomputation of Claim 8 numbers (noisy CES variant), not reusing author code.
import mpmath as mp, itertools
mp.mp.dps = 40
d = mp.mpf(1)/100
def tsc(y): return [1-d if z==y else d/2 for z in range(3)]
W = {(a,b): tsc(a+b) for a in (0,1) for b in (0,1)}
lg = lambda x: mp.log(x,2)
def MI(px, rows):
    py = [sum(px[i]*rows[i][z] for i in range(len(rows))) for z in range(3)]
    return sum(px[i]*rows[i][z]*lg(rows[i][z]/py[z]) for i in range(len(rows)) for z in range(3) if px[i]>0 and rows[i][z]>0)
def BA(rows, it=3000):
    m=len(rows); p=[mp.mpf(1)/m]*m
    for _ in range(it):
        py=[sum(p[i]*rows[i][z] for i in range(m)) for z in range(3)]
        D=[sum(rows[i][z]*lg(rows[i][z]/py[z]) for z in range(3)) for i in range(m)]
        w=[p[i]*2**D[i] for i in range(m)]; s=sum(w); p=[x/s for x in w]
    py=[sum(p[i]*rows[i][z] for i in range(m)) for z in range(3)]
    D=[sum(rows[i][z]*lg(rows[i][z]/py[z]) for z in range(3)) for i in range(m)]
    return MI(p,rows), max(D)   # lower, upper bound on capacity
# A1: X1 uniform on {0,1}, x2=0
A1 = MI([mp.mpf(1)/2]*2, [W[(0,0)], W[(1,0)]])
A2 = MI([mp.mpf(1)/2]*2, [W[(0,0)], W[(0,1)]])
# C1 = max_x2 C(W(.|.,x2)) via BA bounds
C1 = [BA([W[(0,x2)], W[(1,x2)]]) for x2 in (0,1)]
# exact MAP error of uncoded code: source uniform on 3 pairs -> y bijective
src = [(0,0),(0,1),(1,1)]
err = 0
for (u,v) in src:
    for z in range(3):
        # MAP: argmax over pairs of P(pair) W(z|pair)
        best = max(src, key=lambda s: W[s][z])
        if best != (u,v): err += mp.mpf(1)/3 * W[(u,v)][z]
h = lambda e: 0 if e in (0,1) else -e*lg(e)-(1-e)*lg(1-e)
phi = h(err) + err*1*lg(4)
cert = 1/(1+phi*(1/A1+1/A2))
coop = BA([W[s] for s in itertools.product((0,1),(0,1))])
print("MAP err", mp.nstr(err,15))
print("A1", mp.nstr(A1,15), "A2", mp.nstr(A2,15))
print("C1 bounds per x2", [(mp.nstr(a,12),mp.nstr(b,12)) for a,b in C1])
print("phi", mp.nstr(phi,15), "cert lower bound on rho*", mp.nstr(cert,15))
print("coop capacity BA bounds", mp.nstr(coop[0],15), mp.nstr(coop[1],15))
print("cut-set rho* <=", mp.nstr(coop[1]/lg(3),15))
