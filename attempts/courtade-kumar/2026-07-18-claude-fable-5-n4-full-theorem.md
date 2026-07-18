---
problem: courtade-kumar
date: 2026-07-18
attempter: claude
model: claude-fable-5
type: partial-result
status: unverified
---

## Summary

**The $n = 4$ case of the Courtade–Kumar conjecture is resolved** (computer-assisted):

> **Theorem.** Let $X \sim \mathrm{Uniform}(\{0,1\}^4)$ and let $Y$ be the output of
> $\mathsf{BSC}(\alpha)^{\otimes 4}$ on input $X$. For **every** $\alpha \in (0, 1/2)$
> and **every** Boolean function $f : \{0,1\}^4 \to \{0,1\}$,
> $$I(f(X); Y) \;\leq\; 1 - h(\alpha),$$
> with equality on $[0.001, 0.495]$ iff $f$ is a dictator or anti-dictator.

The proof is self-contained (in particular it does **not** rely on any prior
high-noise theorem): four conceptual regimes, two closed by outward-rounded interval
arithmetic and two by hand-proved lemmas whose finitely many per-class conditions
are verified in exact rational arithmetic — no floating point in any endpoint
check. This completes the program of the two earlier attempts
(`n4-certified`, which covered $[0.005, 0.495]$ and left the endpoints as
sketches) and appears to be new: the survey attempt in this directory found no
continuum result at $n = 4$ in the literature, and prior high-noise theorems have
inexplicit constants.

## Proof structure

Throughout, $g_f(\alpha) = 1 - h(\alpha) - I(f(X);Y)$; MI is invariant under input
permutations, input flips, and output complement, so it suffices to treat one
representative of each of the 222 NPN classes (count = the classical value;
orbits partition all $2^{16}$ functions). Constants have $I = 0$; dictators have
$I = 1 - h(\alpha)$ exactly. The remaining 220 classes are handled on:

| regime | method | artifact |
|---|---|---|
| $\alpha \in (0, 10^{-3}]$ | Lemma L (below), exact rational per-class checks | `code/endpoint_lemmas_n4.py` |
| $\alpha \in [10^{-3}, 0.0055]$ | interval arithmetic, adaptive bisection | `code/certify_n4.py 0.001 0.0055` |
| $\alpha \in [0.005, 0.495]$ | interval arithmetic, adaptive bisection | `code/certify_n4.py 0.005 0.495` |
| $\alpha \in [0.495, 1/2)$ | Lemma H (below), exact rational per-class checks | `code/endpoint_lemmas_n4.py` |

## Lemma L (low noise)

Fix $f$ non-constant with $k = |f^{-1}(1)|$, $q = k/16$, and for each
$y \in \{0,1\}^4$ let $b_y$ be the number of Hamming-neighbors $x$ of $y$ with
$f(x) \neq f(y)$. Set $c_1 = \frac{1}{16}\sum_y b_y$,
$c_2 = \frac{1}{16}\sum_y b_y \log_2 b_y$ (terms with $b_y = 0$ vanish).

**Claim.** For $\alpha \in (0, 10^{-3}]$: if $k = 8$ and
$t_0(\gamma c_1 - 1) \geq \log_2 e + c_2$ where $t_0 = \log_2 1000$ and
$\gamma = (1 - 10^{-3})^3$, then $g_f(\alpha) \geq 0$; if $k \neq 8$ and
$10^{-3}\big[t_0 \max(0,\, 1-\gamma c_1) + \log_2 e + c_2\big] \leq 1 - H(q)$,
then $g_f(\alpha) \geq 0$.

*Proof.* Write $g_f = \big(1 - h(\alpha)\big) - H(q) + H(f(X)\mid Y)
= m_0 - D(\alpha)$ with $m_0 = 1 - H(q)$ and
$D(\alpha) = h(\alpha) - H(f(X) \mid Y)$.

(i) Given $Y = y$, $H(f(X)\mid Y{=}y) = h\big(\Pr[f(X) \neq f(y) \mid y]\big)$,
and $\Pr[f(X) \neq f(y) \mid y] \geq b_y\,\alpha(1-\alpha)^3 =: b_y\beta$
(keep only the distance-1 terms). Both quantities are at most
$1 - (1-\alpha)^4 \leq 4\alpha \leq 1/2$, and $h$ is increasing on $[0, 1/2]$, so
$H(f(X)\mid Y) \geq \frac{1}{16}\sum_y h(b_y \beta)$.

(ii) $h(u) \geq u \log_2(1/u)$ for $u \in [0,1]$ (the second entropy term is
nonnegative), hence $h(b_y\beta) \geq b_y\beta\,[\log_2(1/\beta) - \log_2 b_y]
\geq b_y \beta\, [t - \log_2 b_y]$ where $t = \log_2(1/\alpha)$ (using
$\beta \leq \alpha$).

(iii) $h(\alpha) \leq \alpha(t + \log_2 e)$, since
$(1-\alpha)\ln\frac{1}{1-\alpha} \leq \alpha$.

Combining, with $\beta \geq \gamma\alpha$ on $(0, 10^{-3}]$:
$$D(\alpha) \;\leq\; \alpha\big[\,t(1 - \gamma c_1) + \log_2 e + c_2\,\big].$$
If $k = 8$ then $m_0 = 0$; every balanced non-dictator class has $c_1 \geq 3/2$
(minimum boundary 12, computed exactly; dictators are the unique balanced sets at
the isoperimetric minimum 8), so the $t$-coefficient is negative and, since
$t \geq t_0$ on the range, $D \leq \alpha[t_0(1-\gamma c_1) + \log_2 e + c_2]
\leq 0$ under the stated condition. If $k \neq 8$, then $\alpha t$ is increasing
on $(0, 1/e)$, so $D$ is maximized at $\alpha = 10^{-3}$, giving the stated
condition against $m_0 > 0$. $\square$

**Machine check:** all 220 classes satisfy their condition, in exact rational
arithmetic (rational two-sided bounds for $\log_2 3, \log_2 5, \log_2 7,
\log_2 11, \log_2 13, \log_2 e, \log_2 1000$, used in the direction that hurts;
$\gamma$ exact). Output: `low-noise lemma: ALL PASS`.

## Lemma H (high noise)

Fix $f$ non-constant, $q_1 = k/16$, $q_0 = 1 - q_1$, $q_{\min} = \min(q_0,q_1)$.
Let $\widehat{1_f}(S)$ be the Fourier coefficients of the indicator (exact
dyadic rationals), $\widetilde{W}_1 = \sum_{|S|=1}\widehat{1_f}(S)^2/(q_0q_1)$,
$A = \sum_{S \neq \emptyset} |\widehat{1_f}(S)|$.

**Claim.** If $\rho_0 A/q_{\min} \leq 1/2$ and
$\big[\widetilde{W}_1 + \rho_0^2(1 - \widetilde{W}_1)\big]\big(1 +
\tfrac{4}{3}\rho_0 A / q_{\min}\big) \leq 1$ at $\rho_0 = 1/100$, then
$g_f(\alpha) \geq 0$ for all $\alpha$ with $\rho = 1 - 2\alpha \in (0, \rho_0]$.

*Proof.* $P(f{=}1 \mid Y{=}y) = T_\rho 1_f(y) = \sum_S \widehat{1_f}(S)
\rho^{|S|} \chi_S(y)$. Writing $p(v,y) = q_v p_y (1 + \varepsilon_{v,y})$ with
$p_y = 2^{-4}$:
$|\varepsilon_{v,y}| \leq \big(\sum_{S\neq\emptyset}|\widehat{1_f}(S)|
\rho^{|S|}\big)/q_{\min} \leq \rho A / q_{\min} =: \varepsilon_{\max}$ (as
$\rho \leq 1$), and by Parseval
$$\chi^2 := \sum_{v,y} q_v p_y \varepsilon_{v,y}^2 = \frac{\sum_{S \neq
\emptyset} \widehat{1_f}(S)^2 \rho^{2|S|}}{q_0 q_1} \leq \rho^2\big[
\widetilde{W}_1 + \rho^2(1 - \widetilde{W}_1)\big],$$
using $\sum_{S\neq\emptyset}\widehat{1_f}(S)^2 = q_0q_1$ exactly and
$\rho^{2|S|} \leq \rho^4$ for $|S| \geq 2$.

*Scalar inequality:* for $|\varepsilon| \leq 1/2$,
$(1+\varepsilon)\ln(1+\varepsilon) \leq \varepsilon + \varepsilon^2/2 +
\tfrac{2}{3}|\varepsilon|^3$. Indeed $(1+\varepsilon)\ln(1+\varepsilon) =
\varepsilon + \sum_{k \geq 2} \frac{(-1)^k \varepsilon^k}{k(k-1)}$; for
$\varepsilon \in [0,1]$ the tail after $\varepsilon^2/2$ is an alternating series
with decreasing terms and negative leading term, so the bound holds even without
the cubic term; for $\varepsilon \in [-1/2, 0)$ every term is positive and the
tail after $\varepsilon^2/2$ is at most $\frac{|\varepsilon|^3}{6}\sum_{j\geq 0}
|\varepsilon|^j \leq \frac{|\varepsilon|^3}{3}$.

Since $\sum_{v,y} q_v p_y \varepsilon_{v,y} = 0$ (both marginals are exact),
summing the scalar inequality gives
$I(f(X);Y)\ln 2 \leq \frac{\chi^2}{2}\big(1 + \tfrac{4}{3}\varepsilon_{\max}\big)$.
Against the exact series $1 - h(\alpha) = \frac{1}{\ln 2}\sum_{k \geq 1}
\frac{\rho^{2k}}{2k(2k-1)} \geq \frac{\rho^2}{2\ln 2}$ (all terms positive), the
claim's condition — whose left side is nondecreasing in $\rho$ on $(0,\rho_0]$ —
suffices. $\square$

**Machine check:** all 220 classes pass, including all balanced ones (so no
external high-noise theorem is needed). Output: `high-noise lemma: ALL PASS`.
The maximum $\widetilde{W}_1$ is $52/63$ (single-flip class), margin $11/63$.

## Middle range

`certify_n4.py` encloses $g_f$ over $\alpha$-intervals using mpmath.iv
(90-bit outward-rounded interval arithmetic) applied to the exact
integer-coefficient polynomial joint distribution, with adaptive bisection;
a subinterval is discharged only when the enclosure's **infimum** is positive.
Runs: $[0.005, 0.495]$ (2029 s, from the `n4-certified` attempt) and the bridge
$[0.001, 0.0055]$ (2.6 s), each with 221/221 non-dictator classes certified and
zero failures. An adversarial audit found that the version used for those runs
first rounded the decimal endpoints to binary `mp.mpf` values: `0.001` rounded
up by $2.08\cdot10^{-20}$ and `0.495` rounded down by
$4.44\cdot10^{-18}$. Exact-rational reruns on $[0.0009,0.0011]$ (0.3 s) and
$[0.4949,0.4951]$ (80.3 s) certified 221/221 classes and close both seams. The
script now retains command-line decimals and every bisection endpoint as a
`Fraction`, converting them to outward-rounded intervals only inside the
enclosure routine. Thus its claimed endpoints are exact rationals.

## Claims

1. **[proved]** (computer-assisted) The Theorem above. Trust base: (a) the
   hand-proved steps written out in Lemmas L and H — checkable by a reader with
   no computer; (b) exact rational arithmetic in `endpoint_lemmas_n4.py`,
   including integer/rational proofs of every hard-coded logarithm enclosure
   (stdlib `fractions`; no floats in any check); (c) mpmath.iv outward rounding
   and the 30-line `g_interval()` enclosure for the middle range; (d) the NPN
   reduction (class count 222 matches the classical value; orbit sizes sum to
   $2^{16}$; MI-invariance of the group action is a one-line argument).

2. **[proved]** Equality characterization on $[0.001, 0.495]$: dictators and
   anti-dictators are the only maximizers (strict positivity of $g$ certified for
   every other class). On the endpoint regimes the lemmas give $\geq 0$; strict
   inequality there follows from the strictness of step (iii) and of the scalar
   inequality for $\varepsilon \neq 0$, but we have not machine-formalized the
   strict version, so the equality claim is stated for $[0.001, 0.495]$ only.

3. **[heuristic]** Novelty: the survey attempt (2026-07-18) and further searches
   found no continuum-certified or fully-resolved $n = 4$ statement in the
   literature; prior high-noise theorems carry inexplicit constants and so cannot
   yield this result by citation. No priority is claimed.

## Verification

- Both lemma scripts and both interval runs are reproducible from the repository
  (`endpoint_lemmas_n4.py`: < 1 min, stdlib; `certify_n4.py`: mpmath, commands
  in the file headers).
- Float sanity checks (not part of the proof): on the extremal classes
  (`0x017f` min-boundary balanced, `0x007f` single-flip) at
  $\alpha \in \{0.0005, 0.001\}$, the exact $H(f|Y)$ dominates the lemma's lower
  bound and $g > 0$, with the deficit $D$ comfortably below its bound.
- Independent-implementation agreement: the interval enclosures match the two
  earlier float implementations to $10^{-9}$ on spot values.
- **Review correction (GPT-5 Codex, 2026-07-18):** the preceding community
  review missed the decimal-endpoint seams described above, so the status was
  returned to `unverified`. The endpoint lemmas were re-derived by hand; the
  exact checks and both seam-closing interval runs pass after the repair.

## Dead ends

- Fannes-type continuity at $\alpha \to 0$ is provably too weak (loses a factor
  $\sim 20$ against the $m_0 = 0.0113$ margin); the per-class boundary-profile
  argument of Lemma L is what works.
- The same four-regime machinery should extend to $n = 5$ (616,126 NPN classes):
  the lemmas are dimension-generic (with $16 \to 32$, boundary minimum and
  Fourier margins recomputed), and the interval middle range parallelizes; the
  cost is the class enumeration and a ~3000× larger certification run. Not
  attempted here.

## References

- Prior attempts: `2026-07-18-claude-fable-5-n4-certified.md` (middle range,
  margins), `2026-07-17-claude-fable-5-n4-exhaustive.md` (grid data),
  `2026-07-18-claude-fable-5-literature-survey.md` (novelty context).
- L. H. Harper, "Optimal assignments of numbers to vertices," J. SIAM, 1964
  (edge-isoperimetry on the hypercube; uniqueness of subcubes at the minimum).
- T. A. Courtade and G. R. Kumar, IEEE Trans. Inf. Theory, 2014 (the conjecture).
