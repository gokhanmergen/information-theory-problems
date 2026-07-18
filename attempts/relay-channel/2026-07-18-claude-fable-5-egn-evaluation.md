---
problem: relay-channel
date: 2026-07-18
attempter: claude
model: claude-fable-5
type: numerical-evidence
status: unverified
---

## Summary

Numerical evaluation of the El Gamal–Gohari–Nair (EGN) strengthened cutset bound
(arXiv:2101.11139, Proposition 1) on the BSC primitive-relay testbed built in the
`bsc-baseline` attempt. The computation produces candidate objective values at six
parameter points. Because the EGN bound is defined by a maximization, these values
are lower estimates of the true converse value, not certified upper bounds on
capacity. They therefore do **not** establish that any portion of the
cutset–achievability gap is closed, or that compress-forward is near-optimal.

## Approach

EGN Proposition 1 for the primitive relay channel: capacity is at most
$$B = \max_{p(x)\,p(v|x,z)} \min\{\, I(X;Y,V) - I(V;X\mid Z),\;\; I(X;Y) + R_0 -
I(V;Z\mid X)\,\},$$
with $|\mathcal{V}| \leq |\mathcal{X}||\mathcal{Z}| + 1 = 5$ (the second term uses
$I(V;Z\mid X,Y) = I(V;Z\mid X)$, valid since $(V,Z) \perp Y \mid X$). Remark 9 of
the paper: this is exactly the compress-forward expression with the test channel
allowed to depend on $X$ — so the search space strictly contains CF's. Evaluated
by Nelder–Mead over softmax-parametrized $p(v|x,z)$ (21 parameters), 150 random
restarts per point.

**Direction-of-error caution:** $B$ is a *maximum*, so a numerical optimum is a
**lower estimate of $B$**. Algebraically, an exactly evaluated valid auxiliary would
give "$B\geq$ value"; the reported floating-point values are numerical candidates.
"$B\approx$ value" would require a global-optimality certificate not supplied here.

## Claims

1. **[proved]** Substituting $V=Z$, $V=X$, or $V=\text{const}$ into the EGN
   objective gives the three analytic special-case formulas listed in Verification.
   For any valid auxiliary evaluated exactly, its objective value is a lower bound
   on the maximized quantity $B$.

2. **[heuristic]** Nelder–Mead with 150 random restarts found the following candidate
   values of the EGN objective. The table compares them with the best evaluated
   DF/CF rate and the cutset bound only as numerical context:

   | $(\delta_1, \delta_2)$ | $R_0$ | best evaluated DF/CF | EGN candidate | cutset |
   |---|---|---|---|---|
   | (0.1, 0.2) | 0.3 | 0.5310 | 0.5486 | 0.5781 |
   | (0.1, 0.2) | 0.4 | 0.5310 | 0.5770 | 0.6358 |
   | (0.1, 0.2) | 0.5 | 0.5310 | 0.5982 | 0.6358 |
   | (0.1, 0.2) | 0.7 | 0.6012 | 0.6258 | 0.6358 |
   | (0.25, 0.1) | 0.1 | 0.5415 | 0.5471 | 0.6010 |
   | (0.25, 0.1) | 0.3 | 0.5610 | 0.5699 | 0.6010 |

   The best candidate's $p(x)$ is uniform to within $\pm0.005$ at every point, as
   symmetry suggests.

3. **[heuristic]** The optimizer repeatedly finds candidates between the evaluated
   achievable rate and the cutset bound. This is a useful regression target for a
   future certified optimizer, but it has no converse implication: the true maximum
   $B$ could be larger than the reported candidate at any of the six points.

4. **[proved]** Let $b_{\rm num}$ be any candidate found by the optimizer. The
   available inequalities are $b_{\rm num}\leq B$ and $C\leq B$. They imply no
   ordering between $b_{\rm num}$ and capacity $C$. Thus $b_{\rm num}$ cannot be
   used as a capacity upper bound, and the data do not quantify a closed fraction
   of the cutset–achievability gap.

## Details

Code: `attempts/relay-channel/code/egn_bound.py` (numpy + scipy Nelder–Mead; the
only scipy-dependent code in this repository so far). Baseline values from
`primitive_bsc.py` in the same directory.

## Verification

- Numerically evaluated special cases matched their analytic formulas to 6 decimals:
  $V=Z$ gives $(I(X;Y,Z),\, I(X;Y)+R_0-H(Z|X))$;
  $V=X$ gives $(I(X;Z),\, I(X;Y)+R_0)$; $V=\text{const}$ gives $(I(X;Y),\,
  I(X;Y)+R_0)$.
- At all six points the best candidate happened to lie between the evaluated DF/CF
  rate and cutset. This is a numerical sanity check, not a capacity sandwich.
- Restart concentration was low at some points: only 1–27 of 150 restarts were
  within $10^{-4}$ of the best candidate. This reinforces that global optimality
  was not established.

## Dead ends

- Nelder–Mead on the softmax parametrization has a rugged landscape (poor restart
  concentration at several points). A certified global upper bound on the
  maximization — for example via interval branch-and-bound, or a rigorous use of
  the paper's binary-symmetric evaluation strategy (Theorem 6) — is needed before
  drawing any capacity-gap conclusion. Not attempted here.
- The paper's auxiliary-receiver variant (which can be strictly tighter than
  Proposition 1) was not implemented.

## References

- A. El Gamal, A. Gohari, and C. Nair, "A strengthened cutset upper bound on the
  capacity of the relay channel and applications," IEEE Trans. Inf. Theory, 2022;
  arXiv:2101.11139 (Proposition 1, Remark 9).
- Prior attempt `2026-07-18-claude-fable-5-bsc-baseline.md` (testbed and baseline
  values).
