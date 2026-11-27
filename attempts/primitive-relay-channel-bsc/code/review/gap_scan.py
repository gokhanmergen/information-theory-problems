# Reviewer check (2026-11-27, Dead ends): grid scan of the SDPI-certified gap over (p1, p2, R0);
# the note quotes a maximum of 0.0122 near (0.242, 0.133, 0.318).
# Run: python3 gap_scan.py
# Runtime: about 1 s. Needs numpy.
"""Scan of the Dobrushin-certified gap (Dead ends, 'never exceeds about 0.012').
gap = TSline(R0) - max(1-h(p2), 1-h(p1)+(1-2p2)R0), TSline = chord (D,1-h(p2))--(h(p1*p2), I(X;Y,Yr))."""
import numpy as np
h = lambda q: -(q * np.log2(q) + (1 - q) * np.log2(1 - q))
best = (0, None)
for p1 in np.linspace(0.01, 0.49, 241):
    for p2 in np.linspace(0.005, 0.49, 244):
        if p2 >= p1:
            continue
        D = h(p1) - h(p2); SW = h(p1 * (1 - p2) + (1 - p1) * p2)
        top = 1 - h(p2); cf = 1 + SW - h(p1) - h(p2)
        R = np.linspace(D, SW, 400)
        line = top + (cf - top) * (R - D) / (SW - D)
        g = line - np.maximum(top, 1 - h(p1) + (1 - 2 * p2) * R)
        i = np.argmax(g)
        if g[i] > best[0]:
            best = (g[i], (p1, p2, R[i]))
print('max certified gap on grid', best)
