#!/usr/bin/env python3
"""Gaussian evaluation of the El Gamal-Gohari-Nair (EGN 2022) upper bound and its low-SNR limit.

Companion code for
  attempts/gaussian-relay-channel-capacity/2026-11-27-claude-opus-5-5-egn-low-snr-slope.md

Channel (EGN eq. (17)):  Yr = g12 X + Zr,  Y = g13 X + g23 Xr + Z,  Zr, Z ~ N(0,1) independent,
E X^2 <= P1, E Xr^2 <= P2.  We write S12 = g12^2 P1, S13 = g13^2 P1, S23 = g23^2 P2.

EGN Corollary 1 (valid for relay channels without self-interference, which includes this one):
  R <= I(X;Y,Yr|Xr) - I(V;Y|Xr,Yr) - I(X;Yr|V,Xr,Y)
  s.t. I(V,Xr;Yr) - I(V,Xr;Y) <= min{ I(Xr;Yr), max_{p(u|x,xr)} [I(U;Yr) - I(U;Y)] }.
EGN Thm. 2 / Lemma 7: jointly Gaussian (X, Xr, V) suffice.  Parametrisation (EGN eqs. (50)-(51)):
  Cov(X, Xr) = rho sqrt(P1 P2);  given (V, Xr) the pair (X, Zr) has covariance
  [[Q alpha, sigma sqrt(Q alpha beta)], [sigma sqrt(Q alpha beta), beta]],  Q = (1 - rho^2) P1,
  with 0 <= alpha, beta <= 1, |sigma| < 1 and (1 - alpha)(1 - beta) >= sigma^2 alpha beta.
The max over U is EGN's closed form (their eq. (52), from Gohari-Nair Remark 20).

All quantities in this file are in NATS unless stated otherwise.

Low-SNR limit (first order in t, with P1 = t p1, P2 = t p2, t -> 0): set a12 = g12^2 p1,
a13 = g13^2 p1, a23 = g23^2 p2, q = 1 - rho^2, beta = 1 - b t, sigma = s sqrt(t).  Expanding
every term to first order (derivation in the attempt file) gives, in units of t/2 nats,
  rate      F   = q a12 + q a13 alpha - (sqrt(a12 q alpha) + s)^2
  PSD            (1 - alpha) b >= s^2 alpha
  constraint      q a12 - a12 q alpha + b - 2 s sqrt(a12 q alpha) - a13 q (1 - alpha)
               <= min(a12 rho^2, lam_plus) - a12 rho^2 + (rho sqrt(a13) + sqrt(a23))^2
where lam_plus = max(0, largest eigenvalue of K^{1/2}(a a^T - b b^T)K^{1/2}),
K = [[p1, rho sqrt(p1 p2)], [rho sqrt(p1 p2), p2]], a = (g12, 0), b = (g13, g23).
The cutset bound in the same units is max_rho min((1-rho^2)(a12+a13), a13+a23+2 rho sqrt(a13 a23)).

Run:  python3 egn_lowsnr.py   (prints first-order EGN vs cutset at a few gain triples;
      the global maximisation is done by egn2.py / egn_global_check.py)
Requires numpy.
"""
import numpy as np


def exact_terms(g12, g13, g23, P1, P2, rho, alpha, beta, sigma):
    """Exact Gaussian evaluation of EGN Corollary 1 at one parameter point (nats).

    Returns (R, slack, psd, maxU):
      R      the right-hand side of the rate bound,
      slack  rhs - lhs of the constraint (feasible iff slack >= 0),
      psd    (1-alpha)(1-beta) - sigma^2 alpha beta (valid covariance iff psd >= 0),
      maxU   EGN's max_U [I(U;Yr) - I(U;Y)] (eq. (52)).
    """
    Q = (1 - rho ** 2) * P1
    S12 = g12 ** 2 * P1
    S13 = g13 ** 2 * P1
    S23 = g23 ** 2 * P2
    c = sigma * np.sqrt(Q * alpha * beta)            # Cov(X, Zr | V, Xr)
    A1 = 0.5 * np.log1p(Q * (g12 ** 2 + g13 ** 2))   # I(X; Y, Yr | Xr)
    VarYr_V = g12 ** 2 * Q * alpha + beta + 2 * g12 * c
    VarY_V = g13 ** 2 * Q * alpha + 1
    Cov_V = g13 * (g12 * Q * alpha + c)
    VarY_Yr = g13 ** 2 * Q + 1 - (g12 * g13 * Q) ** 2 / (g12 ** 2 * Q + 1)
    VarY_VYr = VarY_V - Cov_V ** 2 / VarYr_V
    A2 = 0.5 * np.log(VarY_Yr / VarY_VYr)            # I(V; Y | Xr, Yr)
    VarYr_VY = VarYr_V - Cov_V ** 2 / VarY_V
    A3 = 0.5 * np.log(VarYr_VY / (beta * (1 - sigma ** 2)))   # I(X; Yr | V, Xr, Y)
    R = A1 - A2 - A3
    IVYr = 0.5 * np.log((g12 ** 2 * Q + 1) / VarYr_V)          # I(V; Yr | Xr)
    IVY = 0.5 * np.log((g13 ** 2 * Q + 1) / VarY_V)            # I(V; Y | Xr)
    IXrYr = 0.5 * np.log((S12 + 1) / (g12 ** 2 * Q + 1))       # I(Xr; Yr)
    mac = S13 + S23 + 2 * rho * np.sqrt(S13 * S23)
    IXrY = 0.5 * np.log((mac + 1) / (g13 ** 2 * Q + 1))        # I(Xr; Y)
    # Larger root lam of EGN eq. (52): A lam^2 + B lam + Cc = 0 with
    #   A = S12 + 1, B = -(S23 S12 (1-rho^2) + S13 + S23 + S12 + 2 + 2 rho sqrt(S13 S23)),
    #   Cc = 1 + S13 + S23 + 2 rho sqrt(S13 S23).
    # Written as lam = 1 + mu to avoid cancellation at low SNR:  A mu^2 + Bp mu - D = 0 with
    #   Bp = 2A + B = S12 - S13 - S23 - 2 rho sqrt(S13 S23) - S23 S12 (1-rho^2),
    #   D  = -(A + B + Cc) = S23 S12 (1-rho^2) >= 0.
    A = S12 + 1
    Bp = S12 - mac - S23 * S12 * (1 - rho ** 2)
    D = S23 * S12 * (1 - rho ** 2)
    disc = np.sqrt(Bp * Bp + 4 * A * D)
    if Bp >= 0:
        mu = 2 * D / (Bp + disc) if Bp + disc > 0 else 0.0
    else:
        mu = (disc - Bp) / (2 * A)
    maxU = 0.5 * np.log1p(S12) - 0.5 * np.log1p(mac) + 0.5 * np.log1p(mu)
    lhs = (IXrYr + IVYr) - (IXrY + IVY)
    rhs = min(IXrYr, maxU)
    psd = (1 - alpha) * (1 - beta) - sigma ** 2 * alpha * beta
    return R, rhs - lhs, psd, maxU


def lam_plus(a12, a13, a23, p1, p2, rho):
    """First-order (t -> 0) value of max_U [I(U;Yr) - I(U;Y)] in units of t/2 nats."""
    g12 = np.sqrt(a12 / p1)
    g13 = np.sqrt(a13 / p1)
    g23 = np.sqrt(a23 / p2)
    K = np.array([[p1, rho * np.sqrt(p1 * p2)], [rho * np.sqrt(p1 * p2), p2]])
    w, U = np.linalg.eigh(K)
    w = np.clip(w, 0, None)
    Kh = U @ np.diag(np.sqrt(w)) @ U.T
    av = np.array([g12, 0.0])
    bv = np.array([g13, g23])
    M = np.outer(av, av) - np.outer(bv, bv)
    return max(0.0, np.linalg.eigvalsh(Kh @ M @ Kh).max())


def first_order(a12, a13, a23, p1, p2, rho, alpha, s, b=None):
    """First-order rate F and constraint slack (units t/2 nats). If b is None, the smallest
    PSD-feasible b = s^2 alpha / (1 - alpha) is used (b only enters the constraint, positively)."""
    q = 1 - rho ** 2
    w = np.sqrt(a12 * q * alpha)
    if b is None:
        b = s ** 2 * alpha / (1 - alpha)
    F = q * a12 + q * a13 * alpha - (w + s) ** 2
    lhs = q * a12 - w ** 2 + b - 2 * s * w - a13 * q * (1 - alpha)
    lamp = lam_plus(a12, a13, a23, p1, p2, rho)
    Bc = min(a12 * rho ** 2, lamp) - a12 * rho ** 2 + (rho * np.sqrt(a13) + np.sqrt(a23)) ** 2
    return F, Bc - lhs


def cutset_first(a12, a13, a23, n=400001):
    """First-order cutset value (units t/2 nats)."""
    rho = np.linspace(0, 1, n)
    return np.max(np.minimum((1 - rho ** 2) * (a12 + a13),
                             a13 + a23 + 2 * rho * np.sqrt(a13 * a23)))


# ---------------------------------------------------------------- achievable rates (nats)
def C(x):
    return 0.5 * np.log1p(x)


def df_rate(g12, g13, g23, P1, P2):
    rho = np.linspace(0, 1, 200001)
    return np.max(np.minimum(C(g12 ** 2 * P1 * (1 - rho ** 2)),
                             C(g13 ** 2 * P1 + g23 ** 2 * P2
                               + 2 * rho * np.sqrt(g13 ** 2 * g23 ** 2 * P1 * P2))))


def cf_rate(g12, g13, g23, P1, P2):
    S12, S13, S23 = g12 ** 2 * P1, g13 ** 2 * P1, g23 ** 2 * P2
    return C(S13 + S12 * S23 / (S13 + S12 + S23 + 1))


def cutset_rate(g12, g13, g23, P1, P2):
    rho = np.linspace(0, 1, 200001)
    return np.max(np.minimum(C((g12 ** 2 + g13 ** 2) * P1 * (1 - rho ** 2)),
                             C(g13 ** 2 * P1 + g23 ** 2 * P2
                               + 2 * rho * np.sqrt(g13 ** 2 * g23 ** 2 * P1 * P2))))


def ex1_rate(g12, g13, g23, P1, P2):
    """EMZ 2006 Example 1 (block length 2 linear relaying), optimised over beta (nats/use)."""
    best = 0.0
    for beta in np.linspace(0.01, 1, 991):
        kap = np.sqrt((1 - beta) / beta)
        d = np.sqrt(2 * P2 / (2 * g12 ** 2 * beta * P1 + 1))
        snr = 2 * beta * P1 * (g13 ** 2 + (g13 * kap + g23 * g12 * d) ** 2 / (1 + g23 ** 2 * d ** 2))
        best = max(best, 0.25 * np.log1p(snr))
    return best


if __name__ == "__main__":
    # first-order check of the max_U closed form against its t -> 0 limit
    for rho in [-0.5, 0.0, 0.1547, 0.6]:
        t = 1e-7
        _, _, _, mU = exact_terms(1, 1, 1, t, t, rho, 0.5, 1.0, 0.0)
        print(f"rho={rho:+.4f}: (2/t)*maxU(eq.52) = {2 * mU / t:.6f},  lam_plus = "
              f"{lam_plus(1, 1, 1, 1, 1, rho):.6f}")
    print("cutset first-order value at a=(1,1,1):", cutset_first(1, 1, 1))
