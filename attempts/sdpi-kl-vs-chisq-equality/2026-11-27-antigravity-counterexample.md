---
problem: sdpi-kl-vs-chisq-equality
date: 2026-11-27
attempter: antigravity
model: gemini-3.1-pro
type: full-solution-claim
status: unverified
---

## Summary

The frozen statement `InfoTheory.Problems.SdpiKlVsChisqEquality.Statement` — asserting that
two-sided equality $s_{\mathrm{KL}}(Q_X, W) = s_{\mathrm{KL}}(Q_Y, W_{\mathrm{rev}}) = s_{\chi^2}$
implies the full Bonami–Beckner hypercontractivity ribbon `inNairRibbon (W.joint Q_X) p q`
for all $1 < p \le q$ with $(p-1)/(q-1) \le s_{\chi^2}$ — is **false**.

We give an explicit 3-state symmetric reversible counterexample $(Q, W)$ with exact
two-sided equality $s_{\mathrm{KL}}(Q, W) = s_{\mathrm{KL}}(Q, W_{\mathrm{rev}}) = s_{\chi^2}(Q, W) = \frac{9}{100}$
together with an explicit rational witness $R_{XY}$ violating `inNairRibbon` at
$p = \frac{127}{100}, q = 4$ (where $\frac{p-1}{q-1} = \frac{9}{100}$).

## Claims

1. **[proved]** Let $k_X = k_Y = 3$, $Q = \left(\frac{1}{4}, \frac{1}{4}, \frac{1}{2}\right)$, and
   $$W = \begin{pmatrix}
   \frac{9}{20} & \frac{3}{20} & \frac{2}{5} \\
   \frac{3}{20} & \frac{9}{20} & \frac{2}{5} \\
   \frac{1}{5} & \frac{1}{5} & \frac{3}{5}
   \end{pmatrix}.$$
   Then $Q$ has full support, $P_{XY} = \mathrm{diag}(Q) W$ is symmetric ($W_{\mathrm{rev}} = W$),
   the eigenvalues of $W$ are $1, r_1 = \frac{3}{10}, r_2 = \frac{1}{5}$, and
   $s_{\chi^2}(Q, W) = s_{\chi^2}(Q, W_{\mathrm{rev}}) = r_1^2 = \frac{9}{100}$.

2. **[sketch]** For every distribution $P \in \Delta_3$, $D(PW \| Q) \le \frac{9}{100} D(P \| Q)$,
   so $s_{\mathrm{KL}}(Q, W) = s_{\mathrm{KL}}(Q, W_{\mathrm{rev}}) = \frac{9}{100}$.
   *Argument:* Parameterize $P = \left(\frac{s+d}{2}, \frac{s-d}{2}, 1-s\right)$ with
   $x = 2s - 1 \in [-1, 1]$ and $y = |d|/s \in [0, 1]$; then $PW$ has $x' = r_2 x = x/5$ and
   $u = d'/s' = r_1 y \frac{1+x}{1+r_2 x} \in [0, 1/2]$. Writing
   $h(z) = d_{\mathrm{bin}}\!\left(\frac{1+z}{2} \,\Big\|\, \frac{1}{2}\right)$, the KL grouping identity gives
   $$D(P \| Q) = h(x) + \frac{1+x}{2} h(y), \qquad D(PW \| Q) = h(r_2 x) + \frac{1+r_2 x}{2} h(u).$$
   Applying $h(r_2 x) \le r_2^2 h(x)$, $h(z) \ge \frac{z^2}{2} + \frac{z^4}{12} + \frac{z^6}{30} + \frac{z^8}{56}$,
   and (on $[0, 1/2]$) $h(u) \le \frac{u^2}{2} + \frac{u^4}{12} + \frac{2}{45} u^6$ reduces
   $D(PW \| Q) - r_1^2 D(P \| Q)$ to a degree-8 rational polynomial upper bound whose leading
   $(x, y^2)$ quadratic form $-0.025 x^2 + 0.018 x y^2 - 0.0034125 y^4$ has strictly negative
   discriminant $-1.725 \times 10^{-5} < 0$ and is strictly negative on $([-1, 1] \times [0, 1]) \setminus \{(0, 0)\}$.

3. **[proved]** At $p = \frac{127}{100}$ and $q = 4$, we have $1 < p \le q$ and
   $\frac{p - 1}{q - 1} = \frac{9}{100} = s_{\chi^2}(Q, W)$, yet `inNairRibbon (W.joint Q) p q` fails.
   *Witness:* The joint distribution
   $$R_{XY} = \frac{1}{100}\begin{pmatrix} 1 & 2 & 2 \\ 3 & 54 & 14 \\ 2 & 12 & 10 \end{pmatrix} \ll P_{XY}$$
   satisfies (in bits)
   $$\frac{1}{1.27} D(R_X \| Q) + \frac{3}{4} D(R_Y \| Q) \approx 1.009979 > 1.007475 \approx D(R_{XY} \| P_{XY}),$$
   violating `inNairRibbon` by $+0.002504$ bits. Equivalently, $f = (\frac{1}{2}, 4, 1)$ obeys
   $\|W f\|_{L^4(Q)} > \|f\|_{L^{1.27}(Q)}$ by $+3.904 \times 10^{-3}$.

## Catalog Note

This shows `SdpiKlVsChisqEquality.Statement` is a catalog modeling error (the "two-sided
equality $\implies$ full BB ribbon" formulation is not a published conjecture in
Anantharam–Gohari–Kamath–Nair 2013, Nair 2014, or Polyanskiy–Wu 2017). The elementary
rational witnesses above allow a direct Lean 4 `statement_false : ¬ Statement` disproof.
