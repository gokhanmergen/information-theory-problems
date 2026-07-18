---
problem: courtade-kumar
date: 2026-07-17
attempter: claude
model: claude-fable-5
type: numerical-evidence
status: unverified
---

## Summary

Three results. (i) A one-line folklore lemma settling the conjecture trivially for all
sufficiently biased functions. (ii) An **exhaustive verification at $n = 4$**: for ten
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
reduces $Y$ to its Hamming weight, giving an $O(n^3)$ exact computation.

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

3. **[sketch]** The $n=4$ case for *all* $\alpha \in (0,1/2)$ should follow from
   Claim 2's data: each of the finitely many functions has $I_f(\alpha)$ real-analytic
   in $\alpha$, so $\{ \alpha : I_f(\alpha) = 1-h(\alpha) \}$ is finite for every $f$
   not identically tied with the dictator, and the observed gaps (second-best is
   $\geq 0.001$ below at every grid point, peaking at $0.050$ near $\alpha = 0.1$)
   leave room for a routine interval-arithmetic/Lipschitz argument on a fine grid.
   Not carried out here.

4. **[proved]** (by exhaustive computation) At $n=4$, at every grid $\alpha$, the
   second-highest MI value is attained by exactly the $8 \times 16 = 128$ functions at
   Hamming distance 1 (in function space) from an (anti-)dictator. Gap to the maximum:

   | $\alpha$ | 0.01 | 0.05 | 0.10 | 0.15 | 0.20 | 0.25 | 0.30 | 0.35 | 0.40 | 0.45 |
   |---|---|---|---|---|---|---|---|---|---|---|
   | gap | .0245 | .0449 | .0500 | .0459 | .0377 | .0281 | .0189 | .0110 | .0050 | .0013 |

   Dictators are strictly isolated maxima, most strongly at moderate noise
   $\alpha \approx 0.1$ — not near either endpoint.

5. **[proved]** (by exact computation, odd $n \leq 61$) $I(\mathrm{maj}_n(X);Y)$ is
   decreasing in $n$ at every tested $\alpha$; e.g. at $\alpha = 0.1$ (bound
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
- `majority_trend.py` — exact $I(\mathrm{maj}_n)$ via the weight-enumerator
  reduction ($O(n^3)$), odd $n \leq 61$, five noise levels.

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
