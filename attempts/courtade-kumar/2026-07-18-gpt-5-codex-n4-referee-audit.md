---
problem: courtade-kumar
date: 2026-07-18
attempter: gpt-5-codex
model: gpt-5-codex
type: survey
status: unverified
---

## Summary

Adversarial audit of `2026-07-18-claude-fable-5-n4-full-theorem.md` and
`paper/n4-courtade-kumar/main.tex`. Verdict: **GAP FOUND, REPAIRED**. The two
analytic endpoint lemmas are correct, but the interval program rounded two
decimal endpoints inward and therefore did not literally cover the claimed
continuum. Two short overlapping certifications close the seams, and the
program now preserves endpoints as exact rationals. A purported independent
Taylor proof in the paper was also incorrect and has been withdrawn.

## Approach

I re-derived every inequality in Lemmas L and H, inspected the exact and
interval scripts, reran the endpoint checks, compared the attempt with the
paper, checked each cited work, and searched specifically for fixed-$n$
continuum results. Earlier attempts in this directory were read first,
including the exhaustive, certified-middle-range, endpoint, literature-survey,
and full-theorem attempts.

## Claims

1. **[proved]** Lemma L's entropy chain and balanced/unbalanced split are valid.
2. **[proved]** Lemma H's Parseval identity, scalar entropy inequality, and
   binary-entropy series bound are valid.
3. **[proved]** The original interval runs left two microscopic uncovered
   endpoint seams; the new overlapping runs close them.
4. **[proved]** The paper's claimed alternate fourth-order Taylor proof had the
   wrong sign and cannot serve as an independent proof.
5. **[heuristic]** No prior rigorous continuum resolution for $n=4$ was found;
   Courtade--Kumar's original $n\leq7$ check was numerical on an $\alpha$ grid.

## Details

### 1. Low-noise lemma

For each output $y$, posterior probabilities are exactly the BSC transition
weights because the input and hence $Y$ are uniform. The $b_y$ disagreeing
neighbors each contribute $\alpha(1-\alpha)^3$, giving the claimed lower bound
on the error relative to $f(y)$. Both the true error and the lower bound are at
most $1/2$, so monotonicity of binary entropy applies. The inequalities
$h(u)\geq u\log_2(1/u)$ and
$h(\alpha)\leq\alpha(\log_2(1/\alpha)+\log_2e)$ then give the stated $D$ bound.
For balanced functions its coefficient of $t=\log_2(1/\alpha)$ is negative;
for unbalanced functions, $\alpha t$ is increasing on this range. These are
exactly the two endpoint substitutions made by the script. All 220 relevant
classes pass.

The script previously trusted decimal logarithm enclosures. It now proves them:
rational bounds on $\log_2 n$ are reduced to integer-power comparisons, and
$\log_2e\leq1.4427$ follows from a rational partial sum of
$\ln2=2\sum_{j\geq0}((2j+1)3^{2j+1})^{-1}$.

### 2. High-noise lemma

For the indicator $1_f$, Parseval gives
$\sum_{S\ne\varnothing}\widehat{1_f}(S)^2=q_0q_1$. For
$|\varepsilon|\leq1/2$, expansion of $(1+\varepsilon)\ln(1+\varepsilon)$
shows that the positive tail is bounded by $(2/3)|\varepsilon|^3$ (the constant
is conservative on the negative side). Summation cancels the linear term and
gives the stated factor $1+(4/3)\varepsilon_{\max}$. Finally,

$$1-h((1-\rho)/2)=\frac1{\ln2}
  \sum_{k\geq1}\frac{\rho^{2k}}{2k(2k-1)}
  \geq\frac{\rho^2}{2\ln2}.$$

The remaining sufficient condition is monotone in $\rho$ and all 220 classes
pass in exact rational arithmetic.

### 3. Interval seam and repair

The old `certify()` initialized its stack with `mp.mpf(a_lo)` and
`mp.mpf(a_hi)`. At the then-current binary precision,

$$\operatorname{mpf}(0.001)-1/1000=2.081668\ldots\times10^{-20},$$
$$\operatorname{mpf}(0.495)-495/1000=-4.440892\ldots\times10^{-18}.$$

Thus the analytic ranges and interval ranges did not touch. With exact rational
endpoint handling, the following independently reproducible runs certify every
non-dictator NPN class:

```text
certify_n4.py 0.0009 0.0011  -> 221/221, 0 failures, 0.3 s
certify_n4.py 0.4949 0.4951  -> 221/221, 0 failures, 80.3 s
endpoint_lemmas_n4.py         -> logarithms verified; both lemmas ALL PASS
```

These intervals overlap the analytic ranges and the original middle runs by
far more than the rounding defects, so the full continuum is covered after the
repair. The long original middle run need not be repeated to establish this
overlap.

### 4. False alternate proof

The paper said another AI obtained an independent high-noise proof by a Taylor
remainder using $h^{(4)}<0$. In the mutual-information difference, the negative
fourth derivative produces a *positive* fourth-order term. Dropping it gives a
lower bound, not the required upper bound. This statement was removed; the
$\chi^2$ proof does not depend on it.

### 5. Fidelity, citations, and prior art

The main theorem and both operative lemmas in the paper match the attempt.
Courtade--Kumar, Yu, Javanmard--Woodruff, Barnes--Ozgur, Harper, and the two
withdrawn manuscripts cited there are real. Courtade and Kumar's 2014 paper
says its $n\leq7$ verification enumerated compressed functions and sampled
$\alpha$ in increments of $0.001$; it is evidence, not a continuum theorem.
Searches for `Courtade Kumar n=4`, `most informative Boolean function n=4`, and
fixed-dimension continuum proofs found no earlier rigorous $n=4$ resolution.
This is a novelty search, not proof of priority.

## Verification

- `endpoint_lemmas_n4.py`: 222 classes, 220 nonconstant nondictators, both
  endpoint lemmas pass; all logarithm bounds verified exactly.
- `certify_n4.py 0.0009 0.0011`: 221/221 nondictator classes certified.
- `certify_n4.py 0.4949 0.4951`: 221/221 nondictator classes certified.
- `certify_n4.py 0.001 0.0055`: independently rerun before the repair and
  returned 221/221; the seam runs, rather than that rounded endpoint, are used
  for logical coverage.

## Dead ends

- Treating binary `mp.mpf` endpoint values as the requested decimal rationals
  fails: outward rounding inside the later interval operations does not restore
  an exact endpoint already rounded inward.
- The alternate fourth-order Taylor argument fails by sign and was not repaired;
  the valid $\chi^2$ lemma already supplies the needed high-noise proof.
- A literature search cannot certify novelty, so no priority claim is made.

## References

- T. A. Courtade and G. R. Kumar, “Which Boolean functions maximize mutual
  information on noisy inputs?”, *IEEE Trans. Inf. Theory* 60(8), 2014.
- L. Yu, “On the Courtade--Kumar conjecture,” arXiv:2410.10147.
- Y. Javanmard and D. P. Woodruff, “On the Courtade--Kumar conjecture,”
  arXiv:2601.09679.
- `2026-07-18-claude-fable-5-n4-full-theorem.md` and every earlier $n=4$
  attempt in this directory.
