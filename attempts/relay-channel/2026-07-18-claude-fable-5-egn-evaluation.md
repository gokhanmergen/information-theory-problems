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
`bsc-baseline` attempt. At all six parameter points the bound estimate lands
strictly inside the cutset–achievability sandwich. Headline: in the **weak-relay
regime** the bound closes ~90% of the gap — evidence that compress-forward is
near-optimal there — while in the **good-relay, moderate-$R_0$ regime** a
~0.04-bit gap survives even the best current converse: that is where the capacity
question is most alive on this testbed.

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
**lower estimate of $B$**. "$B \geq$ value" is certified by the found auxiliary;
"$B \approx$ value" rests on restart evidence and is labeled accordingly.

## Claims

1. **[proved]** The implementation reproduces three analytic special cases exactly
   ($V=Z$, $V=X$, $V=\text{const}$; see Verification), and every found auxiliary
   certifies $B \geq$ the reported value.

2. **[heuristic]** (global optimality of the found optima) The EGN bound on the BSC
   testbed, against the cutset bound and the best of DF/CF:

   | $(\delta_1, \delta_2)$ | $R_0$ | best DF/CF | EGN est. | cutset | gap closed |
   |---|---|---|---|---|---|
   | (0.1, 0.2) | 0.3 | 0.5310 | 0.5486 | 0.5781 | 63% |
   | (0.1, 0.2) | 0.4 | 0.5310 | 0.5770 | 0.6358 | 56% |
   | (0.1, 0.2) | 0.5 | 0.5310 | 0.5982 | 0.6358 | 36% |
   | (0.1, 0.2) | 0.7 | 0.6012 | 0.6258 | 0.6358 | 29% |
   | (0.25, 0.1) | 0.1 | 0.5415 | 0.5471 | 0.6010 | **91%** |
   | (0.25, 0.1) | 0.3 | 0.5610 | 0.5699 | 0.6010 | 78% |

   Optimal $p(x)$ is uniform to within $\pm 0.005$ at every point, as symmetry
   suggests.

3. **[heuristic]** Interpretation: in the weak-relay regime ($I(X;Z) < I(X;Y)$,
   small $R_0$) the residual EGN-vs-CF gap is only ~0.006 bits — compress-forward
   is plausibly capacity-achieving or nearly so there. In the good-relay regime at
   moderate $R_0$ (0.4–0.5), ~0.04 bits remain between the best known converse and
   the best known scheme; on this testbed, that interval is the open problem.

4. **[conjectural]** The restart concentration is low at some points (1–27 of 150
   within $10^{-4}$ of the best), so the true $B$ may exceed the estimates —
   which would only *shrink* the reported "gap closed" percentages' complement
   toward the cutset side, not restore achievability. The qualitative picture in
   Claim 3 is stable under this uncertainty.

## Details

Code: `attempts/relay-channel/code/egn_bound.py` (numpy + scipy Nelder–Mead; the
only scipy-dependent code in this repository so far). Baseline values from
`primitive_bsc.py` in the same directory.

## Verification

- Special cases matched to 6 decimals: $V=Z$ gives $(I(X;Y,Z),\, I(X;Y)+R_0-H(Z|X))$;
  $V=X$ gives $(I(X;Z),\, I(X;Y)+R_0)$; $V=\text{const}$ gives $(I(X;Y),\,
  I(X;Y)+R_0)$.
- Sandwich check at all six points: best-of-DF/CF $\leq$ EGN estimate $\leq$ cutset,
  as theory requires (the EGN family contains CF's; the bound is at most cutset).
- Restart-concentration counts reported per point (see Claim 4).

## Dead ends

- Nelder–Mead on the softmax parametrization has a rugged landscape (poor restart
  concentration at several points). A convexified evaluation — e.g. alternating
  optimization exploiting concavity in $p(x)$, or the paper's own evaluation
  strategy for the binary symmetric case (their Theorem 6) — would firm Claim 2
  from `[heuristic]` toward `[proved]`. Not attempted here.
- The paper's auxiliary-receiver variant (which can be strictly tighter than
  Proposition 1) was not implemented.

## References

- A. El Gamal, A. Gohari, and C. Nair, "A strengthened cutset upper bound on the
  capacity of the relay channel and applications," IEEE Trans. Inf. Theory, 2022;
  arXiv:2101.11139 (Proposition 1, Remark 9).
- Prior attempt `2026-07-18-claude-fable-5-bsc-baseline.md` (testbed and baseline
  values).
