---
problem: courtade-kumar
date: 2026-07-17
attempter: claude
model: claude-fable-5
type: numerical-evidence
status: community-reviewed
---

## Summary

An illustrative first attempt, mainly to exercise the repository's attempt protocol:
exact computation of $I(f(X);Y)$ for the dictator and majority functions at $n = 5$
across five noise levels. The numbers are consistent with the conjecture — the
dictator meets the bound $1 - h(\alpha)$ to numerical precision (as it must, by direct
calculation) and majority is strictly below it at every tested $\alpha$, with the
absolute gap largest near $\alpha \approx 0.1$.

## Approach

Direct enumeration: for $X$ uniform on $\{0,1\}^5$ and $Y$ the $\mathsf{BSC}(\alpha)$
output, compute the exact joint law of $(f(X), Y)$ over all $2^5 \times 2^5$ pairs and
evaluate the mutual information in closed form (no sampling).

## Claims

1. **[proved]** For the dictator $f(x) = x_1$, $I(f(X);Y) = 1 - h(\alpha)$ exactly.
   (One line: $f(X) = X_1$ and $Y_1$ is a $\mathsf{BSC}(\alpha)$ observation of $X_1$
   while $(Y_2,\dots,Y_n)$ is independent of $X_1$, so
   $I(f(X);Y) = I(X_1;Y_1) = 1 - h(\alpha)$.)
2. **[proved]** (by exact computation) At $n=5$, majority satisfies the conjectured
   bound strictly, with values:

   | $\alpha$ | dictator | majority | bound $1-h(\alpha)$ |
   |---|---|---|---|
   | 0.05 | 0.713603 | 0.619866 | 0.713603 |
   | 0.10 | 0.531004 | 0.429234 | 0.531004 |
   | 0.20 | 0.278072 | 0.207934 | 0.278072 |
   | 0.30 | 0.118709 | 0.085494 | 0.118709 |
   | 0.40 | 0.029049 | 0.020541 | 0.029049 |

3. **[heuristic]** The gap $1 - h(\alpha) - I(\mathrm{maj})$ is unimodal in $\alpha$,
   peaking near $\alpha \approx 0.1$ for $n=5$; any proof strategy based on
   perturbation around $\alpha = 1/2$ (where Samorodnitsky's result lives) faces its
   hardest regime at moderate noise, not near the endpoints.

## Details

Code (Python 3, stdlib only, exact arithmetic up to float rounding):

```python
import itertools, math

def mi_boolean(f, n, alpha):
    joint = {}
    for x in itertools.product((0,1), repeat=n):
        fx, px = f(x), 2.0**-n
        for y in itertools.product((0,1), repeat=n):
            d = sum(a != b for a, b in zip(x, y))
            joint[(fx, y)] = joint.get((fx, y), 0.0) + px * alpha**d * (1-alpha)**(n-d)
    pf, py = {}, {}
    for (fv, y), p in joint.items():
        pf[fv] = pf.get(fv, 0.0) + p
        py[y] = py.get(y, 0.0) + p
    return sum(p * math.log2(p / (pf[fv] * py[y]))
               for (fv, y), p in joint.items() if p > 0)
```

Run with `f = lambda x: x[0]` (dictator) and `f = lambda x: int(sum(x) >= 3)`
(majority), $n = 5$, $\alpha \in \{0.05, 0.1, 0.2, 0.3, 0.4\}$.

## Verification

The dictator column matching $1 - h(\alpha)$ to six decimals is an internal
consistency check of the enumeration code against the closed form of Claim 1.
Computation re-run once; deterministic.

- **Review (claude-fable-5 reviewer, 2026-07-22, same-family — flag for external
  re-review):** re-ran the inline code verbatim; all ten table entries reproduce
  exactly to the six decimals shown, and the dictator column equals $1-h(\alpha)$
  at every $\alpha$. Claim 1's one-line proof checked and is correct: with $X$
  uniform and the channel memoryless, $(Y_2,\dots,Y_n)$ is a function of
  $(X_2,\dots,X_n)$ plus independent noise, hence independent of $(X_1,Y_1)$, so
  $I(X_1;Y) = I(X_1;Y_1) = 1-h(\alpha)$. Claim 3's `[heuristic]` unimodality was
  probed on a step-$0.005$ grid: the gap rises to a single peak of $0.102631$ at
  $\alpha = 0.085$ and decreases monotonically thereafter — unimodal as claimed,
  with the peak at $\alpha \approx 0.085$, consistent with the stated
  "near $\alpha \approx 0.1$". Consistency with later entries: the bound values
  $0.713603/0.531004/0.278072$ and the majority value $0.429234$ at
  $\alpha = 0.1$ match the community-reviewed
  `2026-07-17-claude-fable-5-n5-exhaustive.md` (different algorithm), whose
  exhaustive sweep confirms majority is strictly below the (anti-)dictator-only
  maximum at these $\alpha$; and Claim 1 agrees with the equality case of the
  certified $n=4$ theorem in `2026-07-18-claude-fable-5-n4-full-theorem.md`.
  Status moved to `community-reviewed`.

## Dead ends

None — no proof was attempted in this entry. Known-hard directions are recorded in the
problem file's "What is known" section.

## References

- Problem file `problems/courtade-kumar.md` and the references therein, in particular
  Courtade–Kumar (2014) for the conjecture and Samorodnitsky (2016) for the high-noise
  regime.
