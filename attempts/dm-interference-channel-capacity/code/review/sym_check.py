# Reviewer check (2026-11-27, Claim 6): symbolic f, g and f_qq from the NXY channel vs the
# closed forms, and the tangency residual at q = 1 - 2p (sympy; numerics at 40 digits).
# Run: python3 sym_check.py
# Runtime: about 1 s. Needs sympy, mpmath.
# Independent symbolic check of NXY Lemma 2 ingredients (f from channel, f_qq, tangency at q=1-2p)
import sympy as sp
import mpmath as mp

p, q = sp.symbols('p q', positive=True)
ln2 = sp.log(2)


def h(x):  # binary entropy in nats
    return -x * sp.log(x) - (1 - x) * sp.log(1 - x)


# channel: P(Y1=0|x1,x2): (0,0)->1,(0,1)->1/2,(1,0)->1,(1,1)->0 ; p=P(X1=0), q=P(X2=0)
P0 = {(0, 0): 1, (0, 1): sp.Rational(1, 2), (1, 0): 1, (1, 1): 0}
px1 = {0: p, 1: 1 - p}
px2 = {0: q, 1: 1 - q}
s = sp.simplify(sum(px1[a] * px2[b] * P0[(a, b)] for a in (0, 1) for b in (0, 1)))
HY = h(s)
HY_X1 = sum(px1[a] * h(sp.simplify(sum(px2[b] * P0[(a, b)] for b in (0, 1)))) for a in (0, 1))
HY_X1X2 = sum(px1[a] * px2[b] * (ln2 if P0[(a, b)] == sp.Rational(1, 2) else 0)
              for a in (0, 1) for b in (0, 1))
f_direct = h(q) - (HY_X1 - HY_X1X2) + (HY - HY_X1)  # H(X2) - I(X2;Y1|X1) + I(X1;Y1), nats
f_att = ((2 * p - 1) * h(q) - 2 * p * h((1 + q) / 2) + h(q + (1 - q) * p / 2)) + p * (1 - q) * ln2
print("s =", s)
print("f_direct - f_attempt (nats):", sp.simplify(sp.expand(f_direct - f_att)))
g_direct = HY - HY_X1X2
g_att = h(q + (1 - q) * p / 2) - p * (1 - q) * ln2
print("g_direct - g_attempt (nats):", sp.simplify(sp.expand(g_direct - g_att)))

fqq = sp.diff(f_att, q, 2) / ln2  # bits
claimed = p * (1 - 3 * q - 2 * p * (1 - q)) / (q * (1 - q) * (1 + q) * (2 * q + p * (1 - q)) * ln2)
print("f_qq - claimed:", sp.simplify(sp.together(fqq - claimed)))

fq = sp.diff(f_att, q)
qh = 1 - 2 * p
f0 = sp.limit(f_att, q, 0, dir="+"); print("f(p,0) via limit [nats]:", sp.simplify(f0)); lhs = f_att.subs(q, qh) - f0
rhs = qh * fq.subs(q, qh)
d = sp.expand(sp.expand_log(sp.expand(lhs - rhs), force=True))
print("tangency lhs-rhs (expand_log, simplify):", sp.simplify(d))
mp.mp.dps = 40
for pv in ['0.001', '0.1', '0.3', '0.49', '0.4999']:
    val = (lhs - rhs).subs(p, sp.Float(pv, 50)).evalf(40)
    print("  numeric tangency residual at p =", pv, ":", val)

def phi(x):
    return -x * sp.log(x) / ln2

sigma = -phi(p) / 2 - phi(1 - 2 * p) + (p - 1) + 2 * (p - 1) * sp.log(1 - p) / ln2 + (1 - p / 2) * sp.log(2 - p) / ln2
print("sigma - f_q(p,1-2p) [bits]:",
      sp.simplify(sp.expand(sp.expand_log(sp.expand(sigma - fq.subs(q, qh) / ln2), force=True))))
print("qhat - qstar =", sp.factor(qh - (1 - 2 * p) / (3 - 2 * p)))
# f(p,0)

