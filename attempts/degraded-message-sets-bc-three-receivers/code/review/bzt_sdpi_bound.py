# Reviewer check (2026-11-27, Claim 8): SDPI outer bound on max 1.5 R0 + R1 over the BZT region
# for the symmetric crossed BSC product (a = 0.05, b = 0.11), plus c_s, c_w, P* at 30 digits.
# Run: python3 bzt_sdpi_bound.py
# Runtime: about 1 s. Needs mpmath, scipy.
"""Rigorous upper bound on max (lam*R0 + R1) over the BZT region for the symmetric crossed BSC product
(a = 0.05, b = 0.11), via strong data processing (eta_KL(BSC_c) = (1-2c)^2, a*c = b).
BZT subset of {R0 + R1 <= 2 c_w,  R1 <= 2 eta (c_s - R0),  0 <= R0 <= c_s, R1 >= 0}:
  R0 + R1 <= I(U;Y1) + I(X;Y1|U) = I(X;Y1) <= 2 c_w
  R1 <= I(X;Y1|U) <= I(A;Y1A|U) + I(B;Y1B|U) <= eta [I(A;Y2|U) + I(B;Y3|U)]
       = eta [I(A;Y2) - I(U;Y2) + I(B;Y3) - I(U;Y3)] <= 2 eta (c_s - R0).
Also independently recompute c_s, c_w, P* and the capacity value."""
from mpmath import mp, mpf, log
from scipy.optimize import linprog
mp.dps = 30
h = lambda p: -(p*log(p, 2) + (1-p)*log(1-p, 2))
a, b, lam = mpf('0.05'), mpf('0.11'), mpf('1.5')
cs, cw = 1 - h(a), 1 - h(b)
c = (b - a) / (1 - 2*a)
eta = (1 - 2*c)**2
R0s, R1s = 2*(cs - cw), 2*(2*cw - cs)
print('c_s =', mp.nstr(cs, 10), ' c_w =', mp.nstr(cw, 10), ' P* =', mp.nstr(R0s, 10), mp.nstr(R1s, 10))
print('capacity value lam*R0*+R1* =', mp.nstr(lam*R0s + R1s, 10))
print('c =', mp.nstr(c, 10), ' eta =', mp.nstr(eta, 10))
# LP: max lam R0 + R1  s.t. R0+R1 <= 2cw ; 2 eta R0 + R1 <= 2 eta cs ; R0 <= cs
res = linprog([-float(lam), -1], A_ub=[[1, 1], [2*float(eta), 1], [1, 0]],
              b_ub=[2*float(cw), 2*float(eta*cs), float(cs)], bounds=[(0, None)]*2, method='highs')
print('rigorous BZT upper bound on lam*R0+R1 =', -res.fun, ' at', res.x)
print('lower bound from U = X: lam*c_s =', mp.nstr(lam*cs, 10))
print('P* violates the BZT outer set: R1* =', mp.nstr(R1s, 8), ' > 2 eta (c_s - R0*) =', mp.nstr(2*eta*(cs - R0s), 8))
