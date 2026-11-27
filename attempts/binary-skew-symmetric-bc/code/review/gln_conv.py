# Reviewer check (2026-11-27, Claim 7): GLN (15), (16), (18) evaluated in GLN's own channel
# convention at the published Geng/GLN parameters, on grids N = 2e4, 2e5, 1e6.
# Run: python3 gln_conv.py
# Runtime: about 15 s. Needs numpy, mpmath (importing indep_check first prints its checks 1-2).
# Evaluate GLN (15),(16),(18) directly in GLN's own convention (T_{Y|X}=[[.5,.5],[0,1]], T_{Z|X}=[[1,0],[.5,.5]])
import os, sys, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from indep_check import hn, grid, hull_vals
def I_ch(T, P):  # P[x][y] = P(y|x), binary; T = P(X=1)
    py0 = (1-T)*P[0][0] + T*P[1][0]
    return hn(py0) - (1-T)*hn(np.array(P[0][0])) - T*hn(np.array(P[1][0]))
TY = [[.5,.5],[0,1]]; TZ = [[1,0],[.5,.5]]
TG = [[0.206404160918957, 0.793595839081043],[0.826329217311554, 0.173670782688446]]
TK = [[0.173670782688446, 0.826329217311554],[0.793595839081043, 0.206404160918957]]
a = 0.189986556858845
TJ = [[1-a, a],[a, 1-a]]
for N in [20000, 200000, 1000000]:
    T = grid(N); i = int(np.argmin(abs(T-.5)))
    Y, Z, G, K, J = (I_ch(T, P) for P in (TY, TZ, TG, TK, TJ))
    C = lambda f: hull_vals(T, f)
    SRJ = .5*Y + .5*C(Y - J + 2*C(J - Y)) + .5*Z + .5*C(Z - J + 2*C(J - Z))
    SRGK = .5*Y + .5*C(Y - G + 2*C(G - Y)) + .5*Z + .5*C(Z - K + 2*C(K - Z)) + .5*C(G - K) + .5*C(K - G)
    SRUV = .5*Y + .5*Z + .5*C(Y - Z) + .5*C(Z - Y)
    SRM_typo = .5*Y + .5*Z + .5*np.maximum(Y - Z, Z - Y)
    SRM = .5*Y + .5*Z + .5*C(np.maximum(Y - Z, Z - Y))
    print("N=%d SRJ=%.12f (pub 0.369316568804) SRGK=%.12f (pub 0.369296340638) SRUV=%.12f SRM=%.12f SRM_as_printed=%.6f"
          % (N, SRJ[i], SRGK[i], SRUV[i], SRM[i], SRM_typo[i]))
    print("   argmax over t: SRJ %.4f SRGK %.4f" % (T[np.argmax(SRJ)], T[np.argmax(SRGK)]))
