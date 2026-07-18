---
problem: courtade-kumar
date: 2026-07-17
attempter: claude
model: claude-fable-5
type: numerical-evidence
status: unverified
---

## Summary

Exhaustive numerical evidence for the Courtade–Kumar conjecture at $n = 5$: for
$\alpha \in \{0.05, 0.10, 0.20\}$, the maximum of $I(f(X);Y)$ over **all
$2^{32} \approx 4.3\times 10^9$ Boolean functions** found no value exceeding
$1-h(\alpha)$ within the stated floating-point tolerance. The observed maximizers
are the 10 dictators and anti-dictators. Counts and sampled masks are consistent
with the runner-up class being the 320 single-input perturbations, but the program
did not retain enough masks to certify set equality. This executes the "next
computational step" proposed in the `n4-exhaustive` attempt while leaving explicit
roundoff and class-identification gaps.

## Approach

C port of the Gray-code sweep (`code/exhaustive_n5.c`): successive functions differ
on one input, so the joint law $P(f(X)=1, Y=y)$ updates in $O(2^n)$ per function.
The symmetry $I(f) = I(1-f)$ halves the search to the $2^{31}$ functions with
$f(11111) = 0$ (Gray indices $i < 2^{31}$ cover exactly this half). Sharded over 8
processes by index range (`code/run_n5.py`); ≈ 7 CPU-minutes per $\alpha$.

## Claims

1. **[heuristic]** (by exhaustive floating-point computation) For $n = 5$ and each
   $\alpha \in \{0.05, 0.10, 0.20\}$:
   $$\max_{f : \{0,1\}^5 \to \{0,1\}} I(f(X);Y) = 1 - h(\alpha),$$
   attained, within tolerance, by exactly 10 functions — the dictators and
   anti-dictators — with set equality checked on the complement-reduced half
   (5 anti-dictators) plus the
   $I(f) = I(1-f)$ symmetry (immediate, since $(f(X), Y) \mapsto (1-f(X), Y)$ is a
   relabeling). No outward-rounded or interval-arithmetic error bound was used, so
   this is numerical evidence rather than a proof. **Caveat:** these are only three
   grid values of $\alpha$; extension to all $\alpha\in(0,1/2)$ has the same
   `[heuristic]` status and endpoint obstruction as in the `n4-exhaustive` attempt.

2. **[heuristic]** The second-highest MI bucket has count 160 in the
   complement-reduced half, and every retained sample belongs to the independently
   constructed 160-element single-flip family. This is consistent with the full
   runner-up class being exactly the $10\times32=320$ single-input flips of
   (anti-)dictators, but is not a set-equality proof: the C kernel retains at most
   16 examples per shard, and the merge checks only those retained masks.

   | $\alpha$ | bound $1-h(\alpha)$ | second | gap |
   |---|---|---|---|
   | 0.05 | 0.713603 | 0.685742 | 0.027861 |
   | 0.10 | 0.531004 | 0.499412 | 0.031593 |
   | 0.20 | 0.278072 | 0.254774 | 0.023298 |

3. **[heuristic]** Comparing $n=4$ (gap $0.0500$ at $\alpha=0.1$) with $n=5$
   (gap $0.0316$): the isolation gap of the dictators shrinks as $n$ grows,
   consistent with a single flip carrying input mass $2^{-n}$. Any
   stability-based proof strategy must therefore be dimension-uniform in the right
   norm — the raw second-place gap vanishes as $n \to \infty$, even though (by the
   $n \to \infty$ majority analysis in the `n4-exhaustive` attempt) whole families
   far from dictators stay bounded away from the bound.

## Details

Code in `attempts/courtade-kumar/code/`: `exhaustive_n5.c` (kernel; build with
`cc -O3 -o exhaustive_n5 exhaustive_n5.c -lm`) and `run_n5.py` (sharding driver,
merging, and independent recheck). Throughput ≈ 5.2M functions/s/core; a range
benchmark on $[0, 2^{24})$ reproduced the expected leaders before the full run.

## Verification

- Every reported maximizer and a sample of runner-ups were **recomputed from scratch
  in Python** (independent code path, no incremental updates): max discrepancy
  $9.6\times 10^{-13}$ (best class) and $4.9\times 10^{-11}$ (second class) across
  all three $\alpha$. These sample checks detect some implementation errors but do
  not bound worst-case floating-point drift over $2^{31}$ incremental updates.
- The enumerated maximum matches the closed form $1-h(\alpha)$ (one-line proof in
  the earlier example attempt) to $\leq 5\times 10^{-11}$.
- Maximizer samples were checked by set equality against the five expected masks;
  the global count was also five. For the runner-up bucket, only the global count
  (160) and membership of the retained samples were checked; equality of the full
  sets was not checked.

## Dead ends

- Exhaustive $n = 6$ is $2^{64}$ functions — out of reach for this method by a
  factor of $\sim 10^{9}$; symmetry reduction (hyperoctahedral group, order
  $2^6 \cdot 6! = 46{,}080$) buys back at most $\sim 4.6\times 10^{4}$, leaving
  $\sim 4\times 10^{14}$ orbit evaluations. A fundamentally different idea
  (branch-and-bound with certified MI upper bounds per subcube of function space)
  would be needed; not attempted.
- A finer $\alpha$ grid at $n=5$ is pure compute (≈ 7 CPU-minutes per value) and was
  skipped only for time; the three values chosen bracket the peak-gap region
  identified at $n=4$.
- A rigorous version would retain all runner-up masks (or evaluate the independently
  generated 160-mask family and combine equality of values with the global count)
  and use interval or outward-rounded arithmetic to certify comparisons. Neither
  refinement was implemented.

## References

- Prior attempts `2026-07-17-claude-fable-5-n4-exhaustive.md` (structure being
  extended; cross-checks) and `2026-07-17-claude-fable-5.md`.
- Problem file `problems/courtade-kumar.md` and references therein.
