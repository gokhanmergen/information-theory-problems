---
problem: courtade-kumar
date: 2026-07-17
attempter: claude
model: claude-fable-5
type: numerical-evidence
status: community-reviewed
---

## Summary

Three results. (i) A one-line folklore lemma settling the conjecture trivially for all
sufficiently biased functions. (ii) An **exhaustive numerical verification at $n = 4$**: for ten
noise levels $\alpha \in \{0.01, 0.05, 0.10, \dots, 0.45\}$, the maximum of
$I(f(X);Y)$ over **all $2^{16} = 65{,}536$ Boolean functions** equals $1 - h(\alpha)$
exactly, attained by *precisely* the 8 dictators and anti-dictators — and the
runner-up class is exactly the 128 functions obtained by flipping a dictator's value
on a single input. (iii) $I(\mathrm{maj}_n(X); Y)$ is *decreasing* in $n$ at every
tested $\alpha$, converging from above to the Gaussian limit
$1 - \mathbb{E}\,h\big(\Phi\big(\rho G/\sqrt{1-\rho^2}\big)\big)$, $\rho = 1-2\alpha$,
$G \sim \mathcal{N}(0,1)$ — so majority moves *away* from the conjectured bound as
$n$ grows.

## Approach

Brute force where brute force is honest. At $n=4$ the full function space is
enumerable: a Gray-code sweep updates the joint law $P(f(X)=1, Y=y)$ in $O(2^n)$ per
function (each successive function differs on one input), so all $65{,}536$ functions
cost ~2 seconds per $\alpha$ in pure Python. For majority at large $n$, symmetry
reduces $Y$ to its Hamming weight, giving an $O(n^3)$ deterministic floating-point
evaluation.

## Claims

1. **[proved]** (folklore; no novelty claimed) $I(f(X);Y) \leq H(f(X)) = h(\mathbb{E}f)$.
   Hence the conjecture holds trivially for every $f$ with
   $h(\mathbb{P}(f=1)) \leq 1 - h(\alpha)$ — i.e. for all sufficiently biased
   functions; only the near-balanced regime is ever at stake.

2. **[proved]** (by exhaustive computation) For $n = 4$ and each
   $\alpha \in \{0.01, 0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.35, 0.40, 0.45\}$:
   $$\max_{f : \{0,1\}^4 \to \{0,1\}} I(f(X);Y) = 1 - h(\alpha),$$
   attained by exactly 8 functions — the dictators $x_i$ and anti-dictators
   $1 - x_i$ — verified by set equality against the full enumeration. **Caveat:**
   this proves the $n=4$ conjecture *on this grid of $\alpha$*, not for all
   $\alpha \in (0, 1/2)$ (see Claim 3).

3. **[heuristic]** The grid data are consistent with the $n=4$ statement for every
   $\alpha \in (0,1/2)$, but do not prove it. Although each of the finitely many
   functions has $I_f(\alpha)$ real-analytic on the open interval, a nonzero
   real-analytic difference can have infinitely many zeros accumulating at an
   endpoint. Moreover, the observed gap approaches zero as $\alpha\to1/2$.
   Extending Claim 2 therefore requires a certified interval calculation or
   symbolic inequalities on a compact interior interval together with explicit
   endpoint estimates. None was carried out here.

4. **[proved]** (by exhaustive computation) At $n=4$, at every grid $\alpha$, the
   second-highest MI value is attained by exactly the $8 \times 16 = 128$ functions at
   Hamming distance 1 (in function space) from an (anti-)dictator. Gap to the maximum:

   | $\alpha$ | 0.01 | 0.05 | 0.10 | 0.15 | 0.20 | 0.25 | 0.30 | 0.35 | 0.40 | 0.45 |
   |---|---|---|---|---|---|---|---|---|---|---|
   | gap | .0245 | .0449 | .0500 | .0459 | .0377 | .0281 | .0189 | .0110 | .0050 | .0013 |

   Dictators are strictly isolated maxima, most strongly at moderate noise
   $\alpha \approx 0.1$ — not near either endpoint.

5. **[heuristic]** (by deterministic floating-point evaluation, every odd
   $3\leq n\leq61$) $I(\mathrm{maj}_n(X);Y)$ decreases with $n$ at each of the five
   tested values $\alpha\in\{0.05,0.10,0.20,0.30,0.40\}$. For example, at
   $\alpha = 0.1$ (bound
   $0.5310$): $n{=}3$: $0.4572$, $n{=}9$: $0.4081$, $n{=}25$: $0.3924$,
   $n{=}61$: $0.3877$.

6. **[heuristic]** The $n \to \infty$ limit of majority's MI is
   $1 - \mathbb{E}_G\, h\big(\Phi(\rho G / \sqrt{1-\rho^2})\big)$ with
   $\rho = 1 - 2\alpha$ (CLT: the pair of normalized sums becomes jointly Gaussian and
   $Y$'s relevant statistic is its normalized sum). Numerically, at $\alpha = 0.1$ the
   formula gives $0.38460$ with the exact values decreasing toward it
   ($0.38771$ at $n=61$); agreement is similar at the other four tested $\alpha$.
   Consequence, if firmed up: majority is bounded away from the conjectured bound
   uniformly in $n$, so the conjecture's content lives entirely near dictators, not
   near "democratic" functions.

## Details

Code in `attempts/courtade-kumar/code/`:

- `exhaustive_n4.py` — Gray-code sweep over all $2^{16}$ functions; prints max,
  maximizer-set check against the dictator set, runner-up value, exact runner-up
  count, and set-equality check against the single-flip class. Runtime ≈ 2 s total,
  stdlib only.
- `majority_trend.py` — deterministic floating-point evaluation of
  $I(\mathrm{maj}_n)$ via the weight-enumerator reduction ($O(n^3)$), every odd
  $3\leq n\leq61$, at five noise levels; checks every adjacent pair.

The Gaussian-limit integral in Claim 6 was evaluated by direct quadrature
(trapezoid, $2 \times 10^5$ points on $[-10,10]$; script in the PR description's
verification log).

## Verification

- Internal consistency: the enumerated maximum matches the closed form
  $1 - h(\alpha)$ of the dictator (independent one-line proof, Claim 1 of the
  2026-07-17 example attempt) to 9 decimals at all ten $\alpha$.
- The maximizer set and runner-up set were checked by *set equality* against
  independently constructed families (dictators; single-flips), not by counting alone.
- The $n=5$ majority value at $\alpha = 0.1$ from `majority_trend.py` ($0.429234$)
  matches the independent brute-force enumeration in the earlier example attempt
  ($0.429234$), which used a different algorithm.
- **Review (claude-fable-5, 2026-07-20 — same-family review; flag for external
  re-review):** re-ran `exhaustive_n4.py` and `majority_trend.py`; every reported
  number reproduces exactly — max $=$ bound to 9 decimals at all ten $\alpha$ with
  maximizer set $=$ the 8 (anti-)dictators, runner-up bucket count 128 with set
  equality against the single-flip family and the Claim 4 gap table
  ($0.024465,\dots,0.001255$); all adjacent majority decreases at the five
  $\alpha$ with Claim 5's values; independent quadrature of the Claim 6 Gaussian
  limit gives $0.384596$ at $\alpha=0.1$, matching $0.38460$. Cross-check against
  `2026-07-18-claude-fable-5-n4-full-theorem.md`: the certified theorem proves
  the continuum statement on $(0,1/2)$ with dictator-only equality on
  $[0.001, 0.495] \supset$ this grid, so Claim 2's content is now independently
  certified and nothing here contradicts it; Claim 3's refusal to extrapolate is
  vindicated (the extension it declined to claim was done there with interval
  arithmetic). Claim 4's classification is floating-point-based but complete
  (bucket counts are exact; the 256-mask retention cap exceeds the 128-element
  class, so its set-equality check is not sampled), with class gaps
  $\geq 1.2\times10^{-3}$ against incremental drift $\lesssim 10^{-10}$;
  the `[proved]`-with-caveat labels on Claims 2 and 4 as amended by the
  2026-07-18 correction are judged accurate. Status set to `community-reviewed`.
  This is a same-family review (reviewer and attempter are both claude models);
  external re-review is requested before any move to `verified`.

## Dead ends

- **Exhaustive $n = 5$** ($2^{32}$ functions) is out of reach for plain Python
  (\~days); a C/bitset port of the Gray-code sweep (\~$10^{11}$ simple ops) looks
  feasible in minutes-to-hours and is the natural next computational step. Not
  attempted here.
- No new analytic attack was attempted beyond Claim 1; the Fourier/hypercontractivity
  routes and their known obstructions are covered in the problem file's references.

## References

- Problem file `problems/courtade-kumar.md` and references therein.
- Prior attempt `2026-07-17-claude-fable-5.md` (used as an independent cross-check
  for majority at $n=5$).
