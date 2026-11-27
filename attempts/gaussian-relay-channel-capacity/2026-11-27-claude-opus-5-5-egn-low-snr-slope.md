---
problem: gaussian-relay-channel-capacity
date: 2026-11-27
attempter: claude
model: claude-opus-5-5
type: numerical-evidence
status: unverified
---

## Summary

The frozen statement of commit 49c683f asks whether, at unit gains and equal powers $P_1 = P_2 = P$,
$C_{\mathrm{Gauss}}(1,1,1,P,P)/P \to 1/\ln 2$ (the cutset slope) as $P \to 0^+$. **It is very
probably false, because of a published bound.** I evaluated the Gaussian form of the El
Gamal–Gohari–Nair (EGN 2022) strengthened cutset bound (their Corollary 1 / Theorem 2). To first
order in $P$ it gives

  $C_{\mathrm{Gauss}}(1,1,1,P,P) \lesssim 1.1106\,P$ bits, against the cutset value $1.4427\,P$ (ratio 0.7698).

What is certified and what is not:
- The maximum of the closed-form first-order functional is certified by interval
  arithmetic: $\le 1.54$ in units of $P/2$ nats, i.e. ratio $\le 0.7700$, slope $\le 1.1109$ bits per unit power.
- The step "first-order functional = $\lim_{P\to 0}$ EGN$(P)/P$" is a `[sketch]`. A dense 4-D grid
  plus multistart at $P = 10^{-2},\dots,10^{-5}$ over the full feasible set supports it.
- EGN's own theorems are cited, not re-proved.
- My implementation reproduces EGN's Fig. 4.

The same evaluation gives $E^*(1,1,1) \gtrsim 0.934 \cdot 2\ln 2$ for the minimum energy per bit; the
cutset value is $0.75 \cdot 2 \ln 2$.

## Approach

1. Implement EGN Corollary 1 with jointly Gaussian $(X, X_r, V)$, using the parametrisation of their
   eqs. (50)–(51) and the closed form (52) for the $\max_U$ term. Validate it against their Fig. 4
   and against known achievable rates and the cutset bound.
2. Expand every term to first order as $P \to 0$, eliminate two variables exactly, and maximise
   the remaining 2-variable closed form globally (grid, then interval branch and bound).
3. Check that nothing is lost in step 2: maximise the exact finite-$P$ bound over the full 4-D
   feasible set on a dense grid, polish the best starts, and repeat for $P \downarrow 0$.
4. Compute the minimum energy per bit implied by the EGN bound, and probe linear relaying
   numerically. These feed the choice of the replacement statement (statement fix 2).

Units: $C(s) = \tfrac12\log(1+s)$. First-order values are given in units of $P/2$ nats, so the
cutset value at unit gains and equal powers is $2$. To get bits per unit power, multiply by $1/(2\ln 2)$.

## Claims

1. **[heuristic]** *(Implementation check.)* My exact Gaussian evaluation of EGN Corollary 1
   reproduces EGN Fig. 4 ($S_{13} = 3.7585$, $S_{12} = 1.2139$, $P = 1$). At $S_{23} = 0.1$ and $0.25$
   it gives the new bound 1.1319 / 1.1403 bits, CF 1.1283 / 1.1326 and cutset 1.2040 / 1.2381. The
   figure shows about 1.131 / 1.140, 1.128 / 1.1325 and 1.204 / 1.238. At 8 random (gain, power)
   points the evaluated bound lies between max(DF, CF, EMZ Example 1) and the cutset bound.
2. **[sketch]** *(First-order reduction.)* Take unit gains and $P_1 = P_2 = t \to 0$. Then
   $\lim_{t\to0} \tfrac{2}{t}\,\mathrm{EGN}(t) = \max_{(\rho,\alpha)\in[-1,1]\times[0,1]} G(\rho,\alpha)$, where
   $q = 1-\rho^2$, $w = \sqrt{q\alpha}$, $k = \alpha/(1-\alpha)$,
   $\lambda(\rho) = \tfrac12\big(\sqrt{5+4\rho} - 1 - 2\rho\big)$,
   $B(\rho) = \min(\rho^2, \lambda) - \rho^2 + (1+\rho)^2$, and
   $G = q(1+\alpha) - \max\!\big(0,\ w - B/(w + \sqrt{w^2 + kB})\big)^2$.
3. **[proved]** *(Interval certificate, `code/egn_interval_cert.py`.)*
   $\max_{[-1,1]\times[0,1]} G \le 1.54$. The float maximum is $1.539601$, at $\rho = 0.154701$,
   $\alpha = 0.702914$.
4. **[heuristic]** *(Global search of the exact bound, `code/egn_global_check.py`.)* Over the full
   feasible set $\rho\in[-1,1]$, $\alpha\in[0,1]$, $\beta\in(0,1]$, $\sigma\in(-1,1)$ (dense grid
   plus 40 polished starts), $\tfrac{2}{P}\mathrm{EGN}(P)$ is:

   | $P$ | $\tfrac{2}{P}\mathrm{EGN}(P)$ |
   |---|---|
   | $10^{-2}$ | 1.527869 |
   | $10^{-3}$ | 1.538412 |
   | $10^{-4}$ | 1.539473 |
   | $10^{-5}$ | 1.539588 |

   The values increase towards $1.539601$, and no grid point exceeds it. Differential evolution
   (`code/egn_exact.py`) agrees: 1.527869 and 1.538417 at $10^{-2}$ and $10^{-3}$. The first-order
   problem in its original four variables $(\rho,\alpha,b,s)$, without the eliminations, also has
   maximum 1.539601.
5. **[sketch]** *(The 49c683f statement is false.)* This is conditional on Claim 2 and on EGN's
   published Corollary 1, Lemma 7 and eq. (52). Since the EGN bound is an upper bound on capacity,
   $\limsup_{P\to0} C_{\mathrm{Gauss}}(1,1,1,P,P)/P \le \tfrac{1.54}{2\ln 2} = 1.1109$ bits per unit
   power $< 1/\ln 2 = 1.4427$. Hence `LowSnrCutsetSlopeStatement` (the 49c683f `Statement`) is false.
   In particular "the minimum energy per bit equals the cutset value along $P_1 = P_2$" is false.
6. **[heuristic]** *(Energy per bit, `code/egn_energy_per_bit.py`.)* Optimising the first-order
   EGN bound over the power ratio $\kappa = P_2/P_1$ gives $E^*(1,1,1) \ge 0.9336 \cdot 2\ln 2$,
   at $\kappa \approx 0.07$–$0.1$. The cutset gives $0.75 \cdot 2\ln 2$ (EMZ 2006, Table II).
   EMZ Example 1 with bursting never gets below $2\ln 2$ at these gains.
7. **[heuristic]** *(Linear relaying, `code/lr_energy.py`.)* At $a = b = 1$, local search over
   linear codes of block length $k\le 6$ (rank-1 and full-rank $\Sigma$) finds nothing below $2\ln 2$.
   Continuation in $b$ down to $1$ for $k \le 12$ finds nothing below $2\ln 2$ either. At $a = 1$,
   linear codes beat $2\ln 2$ for $b \ge 1.2$ ($k=4$), $b \ge 1.1$ ($k=6$, value 0.999996) and
   $b \ge 1.05$ ($k=12$, value 0.999993). The threshold falls with $k$, so whether
   $E^*_{\mathrm{lin}}(1,1,1) < 2\ln 2$ is unknown.
8. **[sketch]** *(Known schemes at unit gains.)*
   - Decode-forward satisfies $R \le C(g_{12}^2 P_1) = C(P_1)$, so its energy per bit is above
     $2\ln 2$.
   - Every Gaussian compress-forward variant uses source and relay signals that are independent
     (conditionally on the time-sharing variable). This covers bursty CF, time-shared CF and CF
     with a coded time-sharing variable. The multiple-access cut then gives $R \le C(P_1+P_2)$,
     so again $E \ge 2\ln 2$.
9. **[heuristic]** *(Side observation, to be checked.)* At strong relay gains the evaluated EGN
   bound coincides numerically with the decode-forward rate:
   - first order at $a = (4,1,1)$: EGN 3.000000 = DF, with optimum $V = X$;
   - finite power at $g = (2.481, 1.092, 0.643)$, $P = 0.3081$: EGN 0.299513 = DF 0.299513 nats;
   - finite power at $g = (0.935, 0.394, 0.604)$, $P = 0.4809$: EGN = DF 0.148814.

   If this is right, EGN's bound already determines the capacity (= DF) in a strong-relay regime.
   EGN do not claim this. I have not found an error, but I also have not verified it beyond these
   numerics.

## Details

### 2. First-order reduction

EGN Corollary 1 in Gaussian form (EGN eqs. (50)–(51)). We have $\mathrm{Cov}(X, X_r) = \rho P$. Given
$(V, X_r)$, the pair $(X, Z_r)$ has covariance
$\begin{psmallmatrix} Q\alpha & \sigma\sqrt{Q\alpha\beta}\\ \sigma\sqrt{Q\alpha\beta} & \beta\end{psmallmatrix}$
with $Q = qP$. Feasibility requires $0\le\alpha,\beta\le1$ and $(1-\alpha)(1-\beta)\ge\sigma^2\alpha\beta$.

Put $t = P$, $\beta = 1 - bt$, $\sigma = s\sqrt t$. The cross term is
$\sigma\sqrt{Q\alpha\beta} = s w t + O(t^2)$. Every conditional variance is $1 + O(t)$, and every
cross-covariance between $Y$ and $Y_r$ given $V$ is $O(t)$, so it enters only at second order.
Expanding each mutual information as $\tfrac12\ln(1+x) = x/2 + O(x^2)$ gives, in units of $t/2$ nats:

| term | first order |
|---|---|
| $I(X;Y,Y_r\mid X_r)$ | $2q$ |
| $I(V;Y\mid X_r,Y_r)$ | $q(1-\alpha)$ |
| $I(X;Y_r\mid V,X_r,Y)$ | $(q\alpha - b + 2sw) + b + s^2 = (w+s)^2$ |
| $I(X_r;Y_r)$ | $\rho^2$ |
| $I(X_r;Y)$ | $(1+\rho)^2 - q$ |
| $I(V;Y_r\mid X_r)$ | $q - q\alpha + b - 2sw$ |
| $I(V;Y\mid X_r)$ | $q(1-\alpha)$ |
| $\max_U[I(U;Y_r)-I(U;Y)]$ | $\lambda(\rho)$ |

The last row is the positive eigenvalue of $K^{1/2}(aa^\top - bb^\top)K^{1/2}$ with
$K = \begin{psmallmatrix}1&\rho\\\rho&1\end{psmallmatrix}$, $a = (1,0)$, $b = (1,1)$. This equals
$\tfrac12(\sqrt{5+4\rho} - 1 - 2\rho) \ge 0$. I checked in 50-digit arithmetic that EGN's closed form
(52) converges to it; see `egn_lowsnr.py`.

The first-order problem is therefore:
- maximise $q + q\alpha - (w+s)^2$;
- subject to $b - 2ws \le B(\rho)$, where the $q$-terms cancel;
- and to the PSD condition $(1-\alpha) b \ge \alpha s^2$, $b \ge 0$.

$b$ does not appear in the rate and enters the constraint with a plus sign, so the smallest value
$b = \alpha s^2/(1-\alpha)$ is optimal. This leaves the convex quadratic constraint
$k s^2 - 2ws \le B$, whose feasible set is the interval
$[s_-, s_+] \ni 0$, $s_- = -B/(w + \sqrt{w^2+kB})$, since $B\ge0$ for $\rho\in[-1,1]$. The rate is
maximised at $s^* = \max(-w, s_-)$, which gives $G$.

General gains are handled in `egn_lowsnr.py`/`egn2.py`.

**Gap (why this is a sketch).** The exchange "$\lim_{t\to0}\max = \max\lim$" is not proved. In
particular I do not prove that no other scaling of $(\beta,\sigma,\alpha)$ with $t$, such as
$1-\beta = \Theta(\sqrt t)$ or $\sigma = \Theta(1)$, gives a larger first-order rate.

Heuristic reasons it does not:
- the constraint's right-hand side is $O(t)$, which forces $I(V;Y_r\mid X_r) = O(t)$;
- a rate of order $t$ forces $I(X;Y_r\mid V,X_r,Y) = O(t)$;
- these two conditions push $1-\beta$ and $\sigma^2$ to $O(t)$.

Claim 4's grid covers $1-\beta\in[10^{-10},1]$ and $|\sigma|\in[10^{-8},1)$ on logarithmic scales,
so every such scaling is sampled. It finds nothing above $1.539601$.

### 3. Interval certificate

`egn_interval_cert.py` uses mpmath interval arithmetic (`iv`, 30 digits, outward rounding).
- $\alpha\in[0,10^{-6}]$: $G \le q(1+\alpha) \le 1 + 10^{-6}$.
- $\alpha\in[1-10^{-6},1]$: use $w + \sqrt{w^2+kB} \ge \sqrt{kB}$, $1/k \le 10^{-6}/(1-10^{-6})$ and
  $B \le 4$. This gives $G \le 2q - \max(0, \sqrt{q(1-10^{-6})} - \sqrt{4\cdot10^{-6}/(1-10^{-6})})^2$,
  checked on 100 $\rho$-intervals.
- Main domain: bisection on boxes until each box's interval upper bound is $\le 1.54$.

Result: PASS on $1{,}097{,}530$ leaf boxes, largest leaf bound $1.540000$, 3.6 min on one core. A
float cross-check confirms that the closed form agrees with `egn2.best_s` to $4\times10^{-16}$.

### 4. Global search (exact bound)

`egn_global_check.py`, section G1:
- $201$ values of $\rho$; $101$ values of $\alpha$;
- $91$ values of $1-\beta$ (logarithmic in $[10^{-10},1]$, plus $\beta = 1$);
- $143$ values of $\sigma$ ($\pm$ logarithmic in $[10^{-8}, 1)$, plus $0$);
- the 5 best feasible points per $\rho$ are kept, and the 40 best overall are polished with
  Nelder–Mead.

The $\max_U$ term uses a cancellation-free form of EGN (52) (with $\lambda = 1+\mu$; see
`exact_terms`). An earlier float version lost accuracy below $P\approx10^{-6}$.

Section G2 grids the first-order problem directly in $(\rho,\alpha,b,s)$:
$201\times201\times82\times161$ points, then 40 polished starts.

### 6. Energy per bit

By EMZ 2006 Thm. 1, $E^* = \inf_{\kappa}\lim_{t\to0}(1+\kappa)t/C(t,\kappa t)$. With the first-order
EGN value $F(\kappa)$ (gains $a_{12}=a_{13}=1$, $a_{23}=\kappa$, direction $(1,\kappa)$) this gives
$E^*/(2\ln2) \ge \inf_\kappa (1+\kappa)/F(\kappa)$. The output of `egn_energy_per_bit.py`:

| $\kappa$ | 0.01 | 0.05 | 0.07 | 0.1 | 0.2 | 1 |
|---|---|---|---|---|---|---|
| cutset | 0.8851 | 0.8002 | 0.7824 | 0.7661 | 0.7500 | 1.0000 |
| EGN | 0.9653 | 0.9369 | 0.9336 | 0.9336 | 0.9539 | 1.2990 |
| EMZ Ex. 1 + burst (upper) | 1.0061 | 1.0264 | 1.0376 | 1.0548 | 1.1150 | 1.6304 |

This depends on Claim 2 for each $\kappa$ and is not certified.

## Verification

All scripts are in `attempts/gaussian-relay-channel-capacity/code/` and need numpy and scipy;
`egn_interval_cert.py` also needs mpmath. Runtimes are on one core.

| script | what it does | runtime |
|---|---|---|
| `egn_lowsnr.py` | Library (exact terms, first-order terms, achievable rates); self-check of the $\max_U$ limit | seconds |
| `egn2.py` | First-order maxima for several gain triples (Claim 2 values) | ~1 min |
| `egn_exact.py` | V1 Fig. 4 reproduction, V2 sanity at random points, V3 differential evolution at $P\in\{1,0.1,10^{-2},10^{-3}\}$ (Claims 1, 4) | ~3 min |
| `egn_global_check.py` | G1, G2 (Claim 4) | ~3 min |
| `egn_interval_cert.py` | Claim 3; prints PASS/FAIL | ~4 min |
| `egn_energy_per_bit.py` | Claim 6 | ~2 min |
| `lr_energy.py` | Claim 7 | ~15 min |

What this establishes and what it does not:
- Claim 3 is rigorous for the stated closed form $G$.
- Claims 1, 4, 6, 7 and 9 are floating-point computations.
- Claim 5 is rigorous only modulo Claim 2 and EGN's theorems.

Not independently reviewed.

Turning Claim 5 into a full proof needs two things. The first is a uniform first-order upper bound
on the exact EGN functional: explicit inequalities $\ln(1+x)\le x$ and $\ln(1+x)\ge x - x^2/2$ with
an $O(t^{3/2})$ remainder, uniform over the feasible set. The second is the same interval branch
and bound applied to the resulting perturbed functional.

## Dead ends

- **Local optimisation only.** My first pass used multistart Nelder–Mead with a penalty. It missed
  the decode-forward point at $a = (4,1,1)$ and reported 1.15 instead of 3.00. After that I
  eliminated $s$ exactly (`egn2.py`) and used grids everywhere.
- **Naive float evaluation of EGN (52) at tiny $P$.** The discriminant $B^2 - 4AC$ cancels
  catastrophically. At $P = 10^{-7}$ the $\max_U$ value was off by about 2%. The fix is the
  substitution $\lambda = 1+\mu$, whose coefficients have no cancellation.
- **Finite-$P$ bounds cannot refute a limit statement directly.** $C(P)/P$ is nonincreasing in
  $P$ (EMZ 2006, Lemma 1(iv)), so an upper bound at one fixed $P_0$ says nothing about
  $\lim_{P\to0}$. This is why the first-order analysis is needed.

## Novelty check

- EGN 2022 (arXiv:2101.11139v3, full text) has no mention of low SNR, energy per bit or
  capacity per unit cost. Their Gaussian results are Theorem 2 and Fig. 4 at $S_{13} = 3.7585$.
- Kosut–Effros–Langberg 2024 (ISIT; arXiv:2401.15495, full text) use only the cutset bound (their
  eq. (9)) as a lower bound on $E^*$.
- EMZ 2006 (preprint read in full) gives the cutset bound in Table II.
- Web searches ("minimum energy per bit Gaussian relay channel cutset not tight", "Gaussian relay
  channel capacity decode-forward optimal new regime upper bound", plus author searches) found no
  paper stating that EGN's bound improves the low-SNR slope or $E^*$. They also found no paper
  stating that it meets DF anywhere.
- New 2026 relay papers seen: arXiv:2609.18727 (binary relay counterexample) and arXiv:2610.12034
  (primitive diamond relay). Neither concerns this question.

As far as I can tell, Claims 2–6 and 9 are new consequences of a published bound. They are
computations, not new theory.

## References

- Prior attempt: `2026-11-26-claude-opus-5-5-time-sharing-catalog-error.md` (status verified).
  This attempt contradicts its proposal (b), the low-SNR slope question, which the 49c683f
  statement fix adopted. That attempt already flagged the risk: "Maintainers should verify
  before adopting this."
- A. El Gamal, A. Gohari, C. Nair, "A strengthened cutset upper bound on the capacity of the relay
  channel and applications," IEEE Trans. IT 68(7), 4247–4263, 2022; arXiv:2101.11139. Used:
  Corollary 1, Theorem 2, eqs. (50)–(53), Lemma 7, Fig. 4.
- A. Gohari, C. Nair, "Outer bounds for multiuser settings: the auxiliary receiver approach,"
  IEEE Trans. IT, 2022. Cited by EGN for eq. (52) (Remark 20); not read.
- A. El Gamal, M. Mohseni, S. Zahedi, "Bounds on capacity and minimum energy-per-bit for AWGN
  relay channels," IEEE Trans. IT 52(4), 1545–1561, 2006. Used: Thm. 1, Lemma 1, Table II,
  Example 1, Sec. V, Fig. 8.
- O. Kosut, M. Effros, M. Langberg, "Nobody expects a differential equation: minimum energy-per-bit
  for the Gaussian relay channel with rank-1 linear relaying," Proc. IEEE ISIT 2024,
  DOI 10.1109/ISIT57864.2024.10619129; arXiv:2401.15495. Used: eqs. (6)–(9), Fig. 1.
