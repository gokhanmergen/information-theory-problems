# Reviewer check (2026-11-27, Claims 2-3): mpmath.iv (40 digits) recomputation of the (p1, p2, R0) =
# (0.2, 0.1, 0.3) instance: time-shared rate, CF/PDF upper bounds, certified gap, DF/NNC side terms.
# Run: python3 partA.py
# Runtime: under 1 s. Needs mpmath.
# Independent recomputation of the Claim 3 instance with mpmath interval arithmetic.
from mpmath import iv
iv.dps = 40


def h(x):
    x = iv.mpf(x)
    return -(x * iv.log(x) + (1 - x) * iv.log(1 - x)) / iv.log(2)


def star(a, b):
    return a * (1 - b) + (1 - a) * b


p1, p2, R0 = iv.mpf('0.2'), iv.mpf('0.1'), iv.mpf('0.3')
D = h(p1) - h(p2)
SW = h(star(p1, p2))
rDF = 1 - h(p2)
rCF = 1 + SW - h(p1) - h(p2)
nnc2 = 1 - h(p1) + iv.mpf('0.8270') - h(p2)
print('Delta', D, ' SW thr', SW)
print('DF rate', rDF, ' DF 2nd term at 0.2530:', 1 - h(p1) + iv.mpf('0.2530'))
print('CF rate I(X;Y,Yr)', rCF, ' NNC 2nd term at .827', nnc2)
lam = (iv.mpf('0.8270') - iv.mpf('0.2999')) / (iv.mpf('0.8270') - iv.mpf('0.2530'))
ts = lam * rDF + (1 - lam) * rCF
print('lambda', lam, 'pipe', lam * iv.mpf('0.2530') + (1 - lam) * iv.mpf('0.8270'))
print('TS rate', ts)
ubPDF = 1 - h(p2)
ubCF = 1 - h(p1) + (1 - 2 * p2) * R0
print('ub PDF', ubPDF, ' ub CF', ubCF)
print('certified gap >= ', ts.a - max(ubPDF.b, ubCF.b))
s = (rCF - rDF) / (SW - D)
rstar = (rDF - s * D - (1 - h(p1))) / ((1 - 2 * p2) - s)
print('slope', s, ' right endpoint', rstar)
# cutset at (0.2,0.1,0.4)
print('cutset at R0=0.4:', min((1 - h(p1) + iv.mpf('0.4')).a, rCF.a))
