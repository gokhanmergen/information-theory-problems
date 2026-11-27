# Reviewer check (2026-11-27, Claim 4): replays the author's float B&B (../marton_noW_gap.py)
# and audits every vertex and midpoint in exact Fractions; output in exactness.txt.
# Run: python3 exactness_check.py [alpha [tau]]   (default alpha = 2.35, the run quoted in the note)
# Runtime: about 20 s at alpha = 2.35. Needs numpy, mpmath.
"""Reviewer check of the author's B&B: are all simplex vertices exact dyadics summing to 1,
and is every bisection midpoint the exact midpoint (so leaves tile the simplex exactly)?
Replays the author's float search (their Bounder, their split rule) and audits it in Fractions."""
import os, sys
from fractions import Fraction as Fr
import numpy as np
CODE = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')  # author's code/
alpha = float(sys.argv[1]) if len(sys.argv) > 1 else 2.35
TAU_ARG = sys.argv[2] if len(sys.argv) > 2 else None
sys.argv = [sys.argv[0]]
sys.path.insert(0, CODE)
import marton_noW_gap as M

tau = 0.1213158717 if abs(alpha - 2.35) < 1e-12 else float(TAU_ARG) if TAU_ARG else None
for name, f in M.ORBIT_REPS.items():
    B = M.Bounder(f, alpha)
    stack = [np.eye(4)]; nleaf = 0; maxden = 0; bad = 0; maxdepth = 0
    depth = {0: 0}
    st = [(np.eye(4), 0)]
    while st:
        S, d = st.pop(); maxdepth = max(maxdepth, d)
        for w in S:
            fr = [Fr(float(x)) for x in w]
            if sum(fr) != 1 or min(fr) < 0:
                bad += 1
            maxden = max(maxden, max(x.denominator for x in fr))
        b = B.bound(S)
        if b <= tau - 1e-9:
            nleaf += 1; continue
        best = (-1, None)
        for i in range(4):
            for j in range(i + 1, 4):
                dd = np.abs(S[i] - S[j]).sum()
                if dd > best[0]: best = (dd, (i, j))
        i, j = best[1]; m = 0.5 * (S[i] + S[j])
        exact = [(Fr(float(a)) + Fr(float(c))) / 2 for a, c in zip(S[i], S[j])]
        if [Fr(float(x)) for x in m] != exact:
            bad += 1
        S1 = S.copy(); S1[i] = m; S2 = S.copy(); S2[j] = m
        st.append((S1, d + 1)); st.append((S2, d + 1))
    print(f'{name}: leaves {nleaf}, max depth {maxdepth}, max denominator 2^{maxden.bit_length()-1}, inexact events {bad}', flush=True)
