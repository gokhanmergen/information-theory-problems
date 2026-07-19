---
problem: gaussian-interference-channel
date: 2026-07-19
attempter: claude-scheduled
model: claude-fable-5
type: numerical-evidence
status: unverified
---

## Summary

First attempt on this problem: a computational baseline for the **symmetric** real
channel ($P_1 = P_2 = P$, $a = b$, unit noise, $\mathrm{SNR} = P$,
$\mathrm{INR} = a^2 P$) on the grid $P \in \{1, 10\}$,
$a \in \{0.2,\ 0.5,\ \sqrt{1/2},\ 1.0,\ 1.5,\ 3.0\}$. Each point is classified into
the known regimes (noisy / weak-open / strong / very strong) by the exact finite-SNR
thresholds from the literature; inner bounds (TIN, power-controlled TDM, simple
Gaussian Han–Kobayashi over a power-split sweep including the Etkin–Tse–Wang split
$\eta = \min(1, 1/\mathrm{INR})$) are compared against the exact sum capacity where
it is known and the ETW outer bound where it is not. Result: capacity is exactly
known at 8 of the 12 grid points (gap $0$ to machine precision, i.e. the implemented
inner schemes attain the known sum capacity); at the 4 open weak-interference points
the inner/outer sum-rate gap is $0.076$ bits (both $P=1$ points — exactly
$\tfrac12\log_2\tfrac{10}{9}$ in closed form), $0.472$ bits at $(P,a)=(10,0.5)$, and
$0.241$ bits at $(10,\sqrt{1/2})$. No new theorem is claimed.

## Approach

The problem is open only in the weak-interference regime, so a useful baseline is to
quantify, at concrete parameter points, how far the standard achievable schemes sit
below the best known outer bounds — and to verify computationally that the known
exact results are reproduced by the same code. All quantities are closed-form
formulas from the cited literature evaluated in IEEE doubles
($C(x) = \tfrac12\log_2(1+x)$, bits per real channel use); the only optimization is
a 1-D sweep over the Han–Kobayashi power split $\eta$ (2001-point grid) with the
per-$\eta$ sum rate obtained by exact vertex enumeration of a 2-variable LP over the
Chong–Motani–Garg compact HK constraints. Code:
`attempts/gaussian-interference-channel/code/gic_symmetric_baseline.py`
(numpy + stdlib; single run, a few seconds).

## Claims

1. **[proved]** (Regime classification; thresholds from the literature.) With
   $\mathrm{INR} = a^2P$: *very strong* iff $a^2 \ge 1 + P$ (Carleial 1975; capacity
   = two interference-free links); *strong* iff $1 \le a^2 < 1+P$ (Sato 1981,
   Han–Kobayashi 1981; capacity = intersection of the two MAC regions); *noisy* iff
   $a^2 < 1$ and $2a(1 + a^2 P) \le 1$ (symmetric form of the
   Shang–Kramer–Chen / Motahari–Khandani / Annapureddy–Veeravalli 2008–09
   condition, often written $\sqrt{\mathrm{INR}}(1+\mathrm{INR}) \le
   \sqrt{\mathrm{SNR}}/2$; TIN is sum-capacity optimal); otherwise *weak (open)*.
   On the grid: $a=0.2$ is noisy at both powers; $a=0.5$ and $a=\sqrt{1/2}$ are
   weak-open at both powers; $a=1.0$ is strong at both; $a=1.5$ and $a=3.0$ are very
   strong at $P=1$ and strong at $P=10$.

2. **[proved]** (Exact sum capacities at the 8 solved points.) Noisy:
   $C_{\mathrm{sum}} = 2\,C\!\big(P/(1+\mathrm{INR})\big)$; strong:
   $C_{\mathrm{sum}} = \min\big(2\,C(P),\ C(P+\mathrm{INR})\big)$; very strong:
   $C_{\mathrm{sum}} = 2\,C(P)$. Values in the table below (column "outer", rows
   flagged "exact").

3. **[proved]** (Achievability of every inner-bound entry.) Each tabulated inner
   value is an achievable sum rate: TIN $= 2\,C(P/(1+\mathrm{INR}))$ with Gaussian
   inputs at full power; TDM $= C(2P)$ (half-duty bursts at power $2P$, average
   power $P$); and simple Han–Kobayashi with independent Gaussian common/private
   superposition (common power $(1-\eta)P$, private $\eta P$, same $\eta$ for both
   users, no time sharing), evaluated via the Chong–Motani–Garg compact region
   (El Gamal–Kim, *Network Information Theory*, Thm 6.4): with
   $N = 1 + a^2\eta P$,
   $$R_i \le C(P/N), \quad R_1{+}R_2 \le \min\{B_1, B_2\}, \quad
     2R_1{+}R_2,\ R_1{+}2R_2 \le B_1 + B_2/2,$$
   $$B_1 = C\!\Big(\tfrac{P + a^2(1-\eta)P}{N}\Big) + C\!\Big(\tfrac{\eta P}{N}\Big),
     \qquad B_2 = 2\,C\!\Big(\tfrac{\eta P + a^2(1-\eta)P}{N}\Big),$$
   maximized exactly (LP vertex enumeration) for each fixed $\eta$. $\eta = 1$
   recovers TIN; $\eta = 0$ (all-common) attains the exact strong/very-strong sum
   capacity, which the code checks.

4. **[proved]** (Outer bound at the 4 open points.) The ETW outer bound
   (Etkin–Tse–Wang 2008, symmetric real case) on the sum rate,
   $$R_1{+}R_2 \le \min\Big\{2C(\mathrm{SNR}),\ \
     C(\mathrm{SNR}) + C\!\big(\tfrac{\mathrm{SNR}}{1+\mathrm{INR}}\big),\ \
     2\,C\!\big(\mathrm{INR} + \tfrac{\mathrm{SNR}}{1+\mathrm{INR}}\big),$$
   $$\tfrac23\Big[C(\mathrm{SNR}{+}\mathrm{INR}) +
     C\!\big(\tfrac{\mathrm{SNR}}{1+\mathrm{INR}}\big) +
     C\!\big(\mathrm{INR} + \tfrac{\mathrm{SNR}}{1+\mathrm{INR}}\big)\Big]\Big\},$$
   where the second entry is the genie/Z-channel bound (remove one cross link after
   giving the interfering codeword to one receiver; the weak one-sided Gaussian IC
   sum capacity is $C(\mathrm{SNR}) + C(\mathrm{SNR}/(1+\mathrm{INR}))$), and the
   last is the symmetric consequence of ETW's $2R_1{+}R_2$ and $R_1{+}2R_2$ bounds.
   At all four open grid points the binding constraint is the Z-channel bound.
   *Caveat:* formulas were reproduced from the cited literature (and cross-checked
   against the generalized-degrees-of-freedom "W" curve, see Verification), not
   rederived here.

5. **[heuristic]** (Gap table; "best inner" is best over the *implemented* schemes
   only — Gaussian inputs, symmetric split, no time-sharing convexification, $\eta$
   on a grid — so gaps at open points are upper bounds on the true
   inner-vs-ETW-outer gap for this scheme family, and the true capacity gap could be
   smaller on both sides.) Rates in bits/real channel use; $\alpha =
   \log\mathrm{INR}/\log\mathrm{SNR}$ (descriptive GDoF parameter; undefined at
   $P=1$):

   | $P$ | $a$ | INR | regime | $\alpha$ | TIN | TDM | HK@$\eta_{\mathrm{ETW}}$ | HK best ($\eta^*$) | inner best | outer | gap | capacity |
   |---|---|---|---|---|---|---|---|---|---|---|---|---|
   | 1 | 0.2 | 0.04 | noisy | n/a | 0.9720 | 0.7925 | 0.9720 ($\eta$=1) | 0.9720 (1.000) | 0.9720 | 0.9720 | 0.0000 | exact |
   | 1 | 0.5 | 0.25 | weak | n/a | 0.8480 | 0.7925 | 0.8480 ($\eta$=1) | 0.8480 (1.000) | 0.8480 | 0.9240 | 0.0760 | OPEN |
   | 1 | $\sqrt{1/2}$ | 0.5 | weak | n/a | 0.7370 | 0.7925 | 0.7370 ($\eta$=1) | 0.7370 (1.000) | 0.7925 | 0.8685 | 0.0760 | OPEN |
   | 1 | 1.0 | 1 | strong | n/a | 0.5850 | 0.7925 | 0.5850 ($\eta$=1) | 0.7925 (0.000) | 0.7925 | 0.7925 | 0.0000 | exact |
   | 1 | 1.5 | 2.25 | very strong | n/a | 0.3870 | 0.7925 | 0.5850 (0.444) | 1.0000 (0.000) | 1.0000 | 1.0000 | 0.0000 | exact |
   | 1 | 3.0 | 9 | very strong | n/a | 0.1375 | 0.7925 | 0.5850 (0.111) | 1.0000 (0.000) | 1.0000 | 1.0000 | 0.0000 | exact |
   | 10 | 0.2 | 0.4 | noisy | $-0.398$ | 3.0255 | 2.1962 | 3.0255 ($\eta$=1) | 3.0255 (1.000) | 3.0255 | 3.0255 | 0.0000 | exact |
   | 10 | 0.5 | 2.5 | weak | 0.398 | 1.9475 | 2.1962 | 1.9069 (0.400) | 1.9475 (1.000) | 2.1962 | 2.6684 | 0.4722 | OPEN |
   | 10 | $\sqrt{1/2}$ | 5 | weak | 0.699 | 1.4150 | 2.1962 | 2.0000 (0.200) | 2.0850 (0.067) | 2.1962 | 2.4372 | 0.2411 | OPEN |
   | 10 | 1.0 | 10 | strong | 1.000 | 0.9329 | 2.1962 | 1.9886 (0.100) | 2.1962 (0.000) | 2.1962 | 2.1962 | 0.0000 | exact |
   | 10 | 1.5 | 22.5 | strong | 1.352 | 0.5115 | 2.1962 | 2.1778 (0.044) | 2.5330 (0.000) | 2.5330 | 2.5330 | 0.0000 | exact |
   | 10 | 3.0 | 90 | strong | 1.954 | 0.1504 | 2.1962 | 2.5850 (0.011) | 3.3291 (0.000) | 3.3291 | 3.3291 | 0.0000 | exact |

6. **[proved]** (Closed form of the two $P=1$ gaps — an arithmetic identity, not a
   structural theorem.) At $(1, 0.5)$: outer $= C(1) + C(0.8)$, inner (TIN)
   $= 2C(0.8)$, gap $= C(1) - C(0.8)$. At $(1, \sqrt{1/2})$: outer
   $= C(1) + C(2/3)$, inner (TDM) $= C(2)$, and since
   $(1{+}2)/(1{+}2/3) = 9/5 = 1{+}0.8$, i.e. $C(2) - C(2/3) = C(0.8)$, this gap is
   *also* $C(1) - C(0.8) = \tfrac12\log_2\tfrac{10}{9} \approx 0.07600$ bits. The
   agreement to all digits in the table is exact, not a numerical coincidence.

## Details

All formulas and thresholds are as stated in Claims 1–4; the script evaluates them
directly, with the only nontrivial step the per-$\eta$ LP (six constraints, two
variables, solved exactly by enumerating pairwise constraint intersections). The
ETW split $\eta_{\mathrm{ETW}} = \min(1, 1/\mathrm{INR})$ sets the private signal's
interference power at the other receiver to the noise floor ($a^2 \eta P = 1$).
Observations at the open points:

- At $P = 1$ (low SNR) the simple HK sweep is maximized at $\eta = 1$, i.e. **rate
  splitting buys nothing over TIN** within this scheme family at these two points;
  the binding obstruction is the $B_2$ constraint (cost of making both common
  messages decodable at both receivers), which at low SNR outweighs the benefit of
  interference cancellation.
- At $P = 10$ the best implemented scheme at both open points is **TDM** (2.1962),
  which beats both TIN and every simple-HK split on the grid — at $(10, 0.5)$ the
  best HK split is again $\eta^*=1$ (TIN, 1.9475), and at $(10, \sqrt{1/2})$
  interior splitting helps ($\eta^* \approx 0.067$ giving 2.0850) but still loses
  to TDM. Time-sharing-free simple HK is known to be weakest in exactly this
  moderately-weak band ($\alpha$ between $1/2$ and $1$), consistent with ETW's need
  for the $\mathsf{Q}$ time-sharing variable in their constant-gap proof.
- HK at $\eta_{\mathrm{ETW}}$ is within $1$ bit of the outer sum rate at every grid
  point (max deficit $0.762$ bits at $(10, 0.5)$), numerically consistent with the
  ETW one-bit program.

## Verification

- The script's built-in checks pass: inner $\le$ outer at all 12 points; at every
  point where capacity is exactly known, the implemented inner schemes attain the
  exact sum capacity to $<10^{-9}$ (TIN in noisy, HK with $\eta=0$ in
  strong/very strong); HK($\eta{=}1$) $\equiv$ TIN to $<10^{-9}$.
- The four ETW outer constraints were checked analytically to reproduce the correct
  GDoF ("W" curve) segments as $\mathrm{SNR}\to\infty$, $\mathrm{INR} =
  \mathrm{SNR}^\alpha$: per-user normalized limits $1$, $1-\alpha/2$,
  $\max(\alpha, 1-\alpha)$, and $\tfrac13(2-\alpha+\max(\alpha,1-\alpha))$
  respectively, whose minimum traces the known curve on $0\le\alpha\le1$.
- Spot values hand-checked: $(10,1.0)$ strong sum $= C(20) = \tfrac12\log_2 21 =
  2.1962$; $(10,3.0)$ strong sum $= C(100) = \tfrac12\log_2 101 = 3.3291$;
  $(1,0.2)$ noisy sum $= \log_2(1 + 1/1.04) = 0.9720$.
- Not independently verified: the exact statement of ETW Theorem 3 was reproduced
  from memory of the literature plus the GDoF cross-check above, without access to
  the paper text during this run. A reviewer with the paper should confirm the four
  constraints (this is the most valuable single check for this attempt).

## Dead ends

- **Rate splitting at low SNR.** The plan was to show the HK sweep strictly
  improving on max(TIN, TDM) at the open points. It does not, at any of the four:
  at $P=1$ the sweep collapses to $\eta^*=1$ (TIN), and at $P=10$ TDM wins. The
  precise obstruction at $P=1$: for all $\eta<1$ the LP optimum is pinned by
  $B_2 = 2C\big((\eta P + a^2(1-\eta)P)/(1+a^2\eta P)\big)$, which is monotone
  in the wrong direction — the common streams must be decoded at both receivers
  and at these SNRs the cross link ($a^2P \le 0.5$) is too weak to carry a common
  message at a useful rate. Conclusion: closing the 0.076/0.24/0.47-bit gaps needs
  either time sharing across HK operating points with power control, asymmetric
  splits, non-Gaussian inputs, or a tighter outer bound — not a finer $\eta$ grid
  (2001 points is already far past diminishing returns; the sweep is unimodal in
  practice).
- **GDoF-based classification at $P=1$.** $\alpha = \log\mathrm{INR}/\log
  \mathrm{SNR}$ is undefined at $\mathrm{SNR}=1$ ($\log P = 0$) and misleading at
  $P=10$ (e.g. $\alpha<0$ at $a=0.2$). Abandoned as a classification device in
  favor of the exact finite-SNR thresholds of Claim 1; $\alpha$ is reported as
  descriptive only.
- **Scope trims.** Full HK with time-sharing variable $Q$ and asymmetric splits
  (a higher-dimensional optimization) and the convex hull across schemes
  (TDM–HK mixing with power control would strictly improve the $(10,\sqrt{1/2})$
  inner bound) were deliberately left out to keep every reported number exactly
  reproducible from closed forms; they are the natural next attempt, and any
  improvement they give tightens only the OPEN rows.

## References

- No prior attempts existed in `attempts/gaussian-interference-channel/` (this is
  the first).
- A. B. Carleial, "A case where interference does not reduce capacity," IEEE
  Trans. Inf. Theory, 1975 (very strong interference).
- T. S. Han, K. Kobayashi, "A new achievable rate region for the interference
  channel," IEEE Trans. Inf. Theory, 1981; H. Sato, "The capacity of the Gaussian
  interference channel under strong interference," IEEE Trans. Inf. Theory, 1981
  (strong-interference capacity).
- H.-F. Chong, M. Motani, H. K. Garg, "On the Han–Kobayashi region for the
  interference channel," IEEE Trans. Inf. Theory, 2008; also A. El Gamal,
  Y.-H. Kim, *Network Information Theory*, Cambridge, 2011, Thm 6.4 (compact HK
  region used for the inner-bound LP).
- R. Etkin, D. Tse, H. Wang, "Gaussian interference channel capacity to within one
  bit," IEEE Trans. Inf. Theory, 2008 (outer bound, $\eta_{\mathrm{ETW}}$ split,
  GDoF "W" curve).
- X. Shang, G. Kramer, B. Chen, IEEE Trans. Inf. Theory 2009; A. S. Motahari,
  A. K. Khandani, IEEE Trans. Inf. Theory 2009; V. S. Annapureddy,
  V. V. Veeravalli, IEEE Trans. Inf. Theory 2009 (noisy-interference sum
  capacity and threshold).
- Code: `attempts/gaussian-interference-channel/code/gic_symmetric_baseline.py`.
