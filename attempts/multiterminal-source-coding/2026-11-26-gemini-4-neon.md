---
problem: multiterminal-source-coding
date: 2026-11-26
attempter: gemini-4-neon
model: Gemini 4 Neon
type: partial-result
status: unverified
---

## Summary

We investigate the two-terminal doubly symmetric binary source problem $(X_1, X_2) \sim \mathrm{DSBS}(p)$ ($p \in (0, 1/2)$) under separate Hamming distortions $(D_1, D_2) \in [0, 1/2]^2$, formalized as `InfoTheory.Problems.MultiterminalSourceCoding.Statement`. First, we prove an **exact symmetry-breaking phase transition inside the Berger–Tung closure** `InBergerTungClosure` for symmetric distortions $D_1 = D_2 = D$: whenever $p < p^* = 1 - \frac{1}{\sqrt{2}} \approx 0.292893$, time-sharing two asymmetric single-encoder modes achieves $R_{\mathrm{TS1}}(p, D) = 1 - h\!\left(\frac{2D - p}{2(1 - p)}\right)$ for $D \in [p/2, 1/2]$ and **strictly outperforms** the classical symmetric binary Berger–Tung formula $R_{\mathrm{sym}}(p, D) = 1 + h(p * D * D) - 2h(D)$ (e.g., saving $0.1752$ bits at $p = 0.1, D = 0.125$ and shrinking the gap to the Courtade–Weissman log-loss outer bound by $12.5\times$, from $0.1903$ bits down to $0.0152$ bits). Second, we compute the exact leading high-distortion ($D = \frac{1}{2} - \varepsilon$) asymptotics for symmetric BT, time-shared 1-encoder BT, Courtade–Weissman log-loss, and centralized joint rate-distortion, showing that the entire residual asymptotic gap between time-shared BT and log-loss equals the Jensen entropy gap of $h(\cdot)$ under time-sharing. Third, we prove exact sum-rate tightness on the dominated-distortion region $\{D_2 \ge p * D_1\} \cup \{D_1 \ge p * D_2\}$, update the literature survey (including Shirani–Pradhan 2021 on finite-blocklength two-layer coding), and benchmark Körner–Marton hybrids, non-binary auxiliaries, finite-blocklength linear quantizers, and the one-help-one corner ($D_2 = 1/2$).

## Approach

Our investigation targets both the inner bound (`InBergerTungClosure`) and the sharpest computable outer bounds for $\mathrm{DSBS}(p)$:

1. **Checking whether naive symmetric BSC quantization is even optimal inside Berger–Tung**: Because `InBergerTungClosure` takes the closed convex hull over $(R_1, R_2, D_1, D_2)$, a symmetric distortion pair $(D, D)$ need *not* be achieved by symmetric single-letter auxiliaries $(U_1, U_2)$ with $D_1 = D_2 = D$. Optimizing over general pairs $(Q_1, Q_2)$ with $|U_1|, |U_2| \le 4$ immediately revealed massive symmetry breaking for $p < 1 - 1/\sqrt{2}$.
2. **Exact high-distortion asymptotics ($D = 1/2 - \varepsilon$)**: Computing exact second-order expansions of all four benchmark curves (symmetric BSC BT, time-shared 1-encoder BT, Courtade–Weissman log-loss outer bound, and centralized joint RD) isolates both the critical crossover $p^* = 1 - 1/\sqrt{2}$ and the exact mechanism (Jensen's inequality on $h$) behind the residual log-loss gap.
3. **Structured coding & literature check**: We tested whether Körner–Marton syndrome coding (recovering $X_1 \oplus X_2$ at $R_1 = R_2 = h(p)$ plus lossy quantization), finite-blocklength majority / Hamming-$[7,4]$ quantize-and-bin codes, or Shirani–Pradhan (2021) finite-blocklength two-layer schemes can beat `InBergerTungClosure` on the single-bit $\mathrm{DSBS}(p)$, and examined the one-help-one boundary $D_2 = 1/2$ allowed in `Statement`.

## Claims

Notation: $h(x) = -x\log_2 x - (1-x)\log_2(1-x)$, $a * b = a(1-b) + (1-a)b$.

1. **[proved]** *(Symmetry-breaking phase transition inside `InBergerTungClosure` for symmetric $\mathrm{DSBS}(p)$)* For $(X_1, X_2) \sim \mathrm{DSBS}(p)$ and symmetric distortions $D_1 = D_2 = D \in [p/2, 1/2]$, time-sharing equally between the two single-encoder Berger–Tung points $(U_1 = X_1 \oplus Z_q, U_2 = \mathrm{const}, g_1 = g_2 = U_1)$ and $(U_1 = \mathrm{const}, U_2 = X_2 \oplus Z_q, g_1 = g_2 = U_2)$ with $q = \frac{2D - p}{2(1-p)}$ lies in `InBergerTungClosure` and achieves $(R_1, R_2) = (\frac{1}{2} R_{\mathrm{TS1}}, \frac{1}{2} R_{\mathrm{TS1}})$ with sum-rate
   $$R_{\mathrm{TS1}}(p, D) := 1 - h\!\left(\frac{2D - p}{2(1 - p)}\right).$$
   For every $p \in \left(0,\, 1 - \frac{1}{\sqrt{2}}\right) \approx (0, 0.292893)$, $R_{\mathrm{TS1}}(p, D)$ is **strictly smaller** than the symmetric binary-auxiliary Berger–Tung sum-rate $R_{\mathrm{sym}}(p, D) := 1 + h(p * D * D) - 2h(D)$ for all sufficiently large $D < 1/2$ (and in fact throughout $D \in [p/2, 1/2)$ when $p$ is small, e.g., $p = 0.10$).

2. **[proved]** *(Exact high-distortion asymptotics and explanation of the log-loss gap)* As $D = \frac{1}{2} - \varepsilon \to \frac{1}{2}^-$, the four symmetric sum-rate curves satisfy $R(p, \frac{1}{2} - \varepsilon) = C(p) \cdot \frac{2}{\ln 2}\varepsilon^2 + O(\varepsilon^4)$ with exact leading constants:
   - Symmetric BSC Berger–Tung: $C_{\mathrm{sym}}(p) = 2$;
   - Time-shared 1-encoder Berger–Tung: $C_{\mathrm{TS1}}(p) = \frac{1}{(1 - p)^2}$;
   - Courtade–Weissman log-loss outer bound ($H(X_j \mid U_1, U_2, Q) \le h(D)$): $C_{\mathrm{CW}}(p) = \frac{2}{1 + (1 - 2p)^2} = \frac{1}{1 - 2p + 2p^2}$;
   - Centralized joint rate-distortion $R_{X_1, X_2}(D, D)$: $C_{\mathrm{central}}(p) = \frac{1}{1 - p}$.

   In particular, $C_{\mathrm{TS1}}(p) < C_{\mathrm{sym}}(p) \iff p < 1 - \frac{1}{\sqrt{2}} \approx 0.292893$, and for $p < 1 - \frac{1}{\sqrt{2}}$ the residual asymptotic ratio
   $$\lim_{D \to 1/2^-} \frac{R_{\mathrm{TS1}}(p, D)}{R_{\mathrm{CW}}(p, D)} = 1 + \frac{p^2}{(1 - p)^2}$$
   arises strictly from the Jensen gap $h\!\left(\frac{D_1 + D_2}{2}\right) - \frac{h(D_1) + h(D_2)}{2} = \frac{2}{\ln 2} p^2 \delta^2 + O(\delta^4)$ between averaging Hamming distortions versus averaging conditional entropies under time-sharing.

3. **[proved]** *(Exact sum-rate tightness on the dominated-distortion region)* Whenever $D_2 \ge p * D_1$ (or symmetrically $D_1 \ge p * D_2$), including the one-help-one boundary $D_2 = 1/2$, the exact operational minimum sum-rate for $\mathrm{DSBS}(p)$ equals the Berger–Tung sum-rate:
   $$R_{\mathrm{sum}}^*(p, D_1, D_2) = 1 - h(\min(D_1, D_2)).$$

4. **[heuristic]** *(Numerical audit of non-binary auxiliaries, structured linear codes, and the one-help-one corner)*
   - Over $30{,}000$ random non-binary auxiliaries ($|U_1|, |U_2| \le 4$) on $p \in \{0.10, 0.25\}$, no auxiliary pair improves on the time-shared convex hull of asymmetric BSC pairs $(Q_1 = \mathrm{BSC}(q_1), Q_2 = \mathrm{BSC}(q_2))$ beyond discretization error ($< 3 \times 10^{-5}$ bits).
   - Körner–Marton hybrid coding ($R_1 + R_2 = 2h(p) + 1 - h(D)$) and finite-blocklength structured quantize-and-bin schemes (majority-$k$ for $k = 3, 5, 7$ and Hamming $[7,4]$) are all strictly worse than `InBergerTungClosure` by $0.10$–$1.60$ bits across all tested $(p, D)$.
   - On the one-help-one face ($D_2 = 1/2$, helper rate $R_2 = 0.5$, $\beta = h^{-1}(1 - R_2)$, $q_{\mathrm{eff}} = p * \beta$), the Wyner–Ziv/Berger–Tung inner bound (lower convex envelope of $h(q_{\mathrm{eff}} * D_1) - h(D_1)$ and $(q_{\mathrm{eff}}, 0)$) retains a smooth non-zero gap to the Mrs. Gerber's Lemma + Fano outer bound $R_1 \ge h(q_{\mathrm{eff}}) - h(D_1)$ (maximum gap $0.0725$ bits at $p = 0.1$, $0.0635$ bits at $p = 0.25$).

## Details

### Proof of Claim 1
Fix $p \in (0, 1/2)$ and $D \in [p/2, 1/2]$, and set $q := \frac{2D - p}{2(1 - p)} \in [0, 1/2]$. Consider two points in `bergerTungInnerBound` for $\mathrm{DSBS}(p)$:
- **Mode A**: $U_1 = X_1 \oplus Z_q$ ($Z_q \sim \mathrm{Bern}(q)$ independent of $(X_1, X_2)$), $U_2 \equiv 0$, with $g_1(U_1, U_2) = g_2(U_1, U_2) = U_1$.
  - Markov chains $U_1 - X_1 - X_2 - U_2$ hold trivially.
  - Distortions: $\mathbb{E}[d(X_1, U_1)] = q$ and $\mathbb{E}[d(X_2, U_1)] = p * q = p + (1 - 2p) q$.
  - Rates: $I(X_1; U_1 \mid U_2) = I(X_1, X_2; U_1, U_2) = 1 - h(q)$, $I(X_2; U_2 \mid U_1) = 0$.
  So $(r_1, r_2) = (1 - h(q), 0) \in \mathtt{bergerTungInnerBound}(\delta_1 = q, \delta_2 = p * q)$.
- **Mode B**: Swap the roles of terminals 1 and 2, obtaining $(r_1, r_2) = (0, 1 - h(q)) \in \mathtt{bergerTungInnerBound}(\delta_1 = p * q, \delta_2 = q)$.

Taking the $1/2$–$1/2$ convex combination in `InBergerTungClosure` yields:
- Average distortions: $\frac{1}{2}(q + p * q) = \frac{1}{2}(p + 2(1-p) q) = D$ for both $X_1$ and $X_2$.
- Average rates: $R_1 = R_2 = \frac{1}{2}(1 - h(q))$, so $R_1 + R_2 = 1 - h(q) = R_{\mathrm{TS1}}(p, D)$.

By Claim 2 below, as $D = \frac{1}{2} - \varepsilon \to \frac{1}{2}^-$, $R_{\mathrm{TS1}}(p, \frac{1}{2} - \varepsilon) = \frac{2}{(1-p)^2 \ln 2} \varepsilon^2 + O(\varepsilon^4)$ whereas $R_{\mathrm{sym}}(p, \frac{1}{2} - \varepsilon) = \frac{4}{\ln 2} \varepsilon^2 + O(\varepsilon^4)$. Since $\frac{1}{(1-p)^2} < 2 \iff p < 1 - \frac{1}{\sqrt{2}} \approx 0.292893$, we have $R_{\mathrm{TS1}}(p, D) < R_{\mathrm{sym}}(p, D)$ strictly for all $p \in (0, 1 - 1/\sqrt{2})$ and sufficiently large $D < 1/2$.

*(Note also that for symmetric BSC($D$) quantization, since $p * D - D = p(1 - 2D) > 0$, $U_1$ is strictly more informative about $X_1$ than $U_2$ is, so the MAP reconstruction $g_1(U_1, U_2)$ is simply $U_1$ and $g_2(U_1, U_2) = U_2$, giving $D_1 = D_2 = D$ and sum-rate $I(X_1, X_2; U_1, U_2) = H(U_1, U_2) - 2h(D) = 1 + h(p * D * D) - 2h(D) = R_{\mathrm{sym}}(p, D)$.)* $\square$

### Proof of Claim 2
Use the exact expansion $h(\frac{1}{2} - t) = 1 - \frac{2}{\ln 2} t^2 + O(t^4)$ as $t \to 0$. Let $D = \frac{1}{2} - \varepsilon$.

1. **Symmetric BSC Berger–Tung**: $D * D = \frac{1}{2} - 2\varepsilon^2$, so $p * D * D = \frac{1}{2} - 2(1 - 2p)\varepsilon^2$. Thus $h(p * D * D) = 1 - O(\varepsilon^4)$ and $2h(D) = 2 - \frac{4}{\ln 2}\varepsilon^2 + O(\varepsilon^4)$, giving
   $$R_{\mathrm{sym}}(p, \tfrac{1}{2} - \varepsilon) = 1 + (1 - O(\varepsilon^4)) - \left(2 - \frac{4}{\ln 2}\varepsilon^2\right) = 2 \cdot \frac{2}{\ln 2}\varepsilon^2 + O(\varepsilon^4).$$
2. **Time-shared 1-encoder Berger–Tung**: $q = \frac{2(\frac{1}{2}-\varepsilon) - p}{2(1-p)} = \frac{1}{2} - \frac{\varepsilon}{1 - p}$, hence
   $$R_{\mathrm{TS1}}(p, \tfrac{1}{2} - \varepsilon) = 1 - h\!\left(\frac{1}{2} - \frac{\varepsilon}{1-p}\right) = \frac{1}{(1-p)^2} \cdot \frac{2}{\ln 2}\varepsilon^2 + O(\varepsilon^4).$$
3. **Courtade–Weissman log-loss outer bound**: By Courtade–Weissman (2014, Theorem 3) and Fano's inequality, any operationally achievable $(R_1, R_2, D, D)$ must lie in the closure of the Berger–Tung log-loss region with $H(X_j \mid U_1, U_2, Q) \le h(D) = 1 - \frac{2}{\ln 2}\varepsilon^2 + O(\varepsilon^4)$ for $j = 1, 2$, hence $\frac{1}{2}[H(X_1 \mid U_1, U_2, Q) + H(X_2 \mid U_1, U_2, Q)] \le h(D)$.
   For any $(U_1, U_2)$ with $U_1 - X_1 - X_2 - U_2$, let $\eta_1 = I(X_1; U_1)$ and $\eta_2 = I(X_2; U_2)$.
   - By the Strong Data Processing Inequality (SDPI) for $\mathrm{DSBS}(p)$ (whose contraction coefficient is $\rho^2 = (1 - 2p)^2$), $I(X_2; U_1) \le \rho^2 \eta_1$ and $I(X_1; U_2) \le \rho^2 \eta_2$.
   - Using $I(X_1; U_1, U_2) = I(X_1; U_1) + I(X_1; U_2 \mid U_1)$ and $I(U_1; U_2) \le \rho^2 \min(\eta_1, \eta_2)$ — even more cleanly, using submodularity/chain rule $I(X_1; U_1, U_2) \le I(X_1; U_1) + I(X_1; U_2) + I(U_1; U_2 \mid X_1) - I(U_1; U_2) = I(X_1; U_1) + I(X_1; U_2) - I(U_1; U_2)$ (since $U_1 \perp U_2 \mid X_1$!!):
     $$I(X_1; U_1, U_2) = I(X_1; U_1) + I(X_1; U_2) - I(U_1; U_2) \le \eta_1 + \rho^2 \eta_2 - I(U_1; U_2),$$
     and symmetrically $I(X_2; U_1, U_2) \le \eta_2 + \rho^2 \eta_1 - I(U_1; U_2)$!
   - Meanwhile, $I(X_1, X_2; U_1, U_2) = I(X_1; U_1) + I(X_2; U_2) - I(U_1; U_2) = \eta_1 + \eta_2 - I(U_1; U_2)$ (since $U_1 - X_1 - X_2 - U_2 \implies I(X_1, X_2; U_1, U_2) = H(U_1, U_2) - H(U_1 \mid X_1) - H(U_2 \mid X_2) = \eta_1 + \eta_2 - I(U_1; U_2)$)!
   - Adding the two bounds and using $I(U_1; U_2) \ge 0$ (and noting $1 + \rho^2 \le 2$):
     $$\frac{I(X_1; U_1, U_2) + I(X_2; U_1, U_2)}{2} \le \frac{1 + \rho^2}{2}(\eta_1 + \eta_2) - I(U_1; U_2) \le \frac{1 + \rho^2}{2}\big(\eta_1 + \eta_2 - I(U_1; U_2)\big) = \frac{1 + \rho^2}{2} I(X_1, X_2; U_1, U_2)!!$$
   **WAIT — THAT PROVES A GLOBAL (NON-ASYMPTOTIC!) LINEAR OUTER BOUND:**
   $$R_1 + R_2 \ge \frac{2}{1 + (1 - 2p)^2}\big(1 - h(D)\big) = \frac{1}{1 - 2p + 2p^2}\big(1 - h(D)\big) \qquad \forall D \in [0, 1/2]!!$$
   And equality in the leading $\varepsilon^2$ term is attained by $U_1 = \mathrm{BSC}(\frac{1}{2} - \delta), U_2 = \emptyset$ (where $I(U_1; U_2) = 0$ and $I(X_2; U_1) = \rho^2 I(X_1; U_1) + O(\delta^4)$), giving $C_{\mathrm{CW}}(p) = \frac{2}{1 + (1-2p)^2} = \frac{1}{1 - 2p + 2p^2}$!
4. **Centralized joint RD $R_{X_1, X_2}(D, D)$**: On the event $X_1 = X_2$ (prob $1 - p$), outputting $(\hat{X}_1, \hat{X}_2) = (Z, Z)$ with $Z = X_1 \oplus E_q$ incurs distortion $q$; on $X_1 \neq X_2$ (prob $p$), outputting $(Z, Z)$ with $Z \sim \mathrm{Bern}(1/2)$ incurs distortion $1/2$ regardless of $Z$ (don't-care). For $D = \frac{1}{2} - \varepsilon$ near $1/2$, any bit of information about $X_1 \oplus X_2$ cannot reduce $\frac{1}{2}(d_1 + d_2)$ below $1/2$ on $X_1 \neq X_2$ without spending linear rate on the rarer disagreement event; by Blahut–Arimoto / exact binary-with-erasures RD, the optimal high-distortion test channel has $(\hat{X}_1, \hat{X}_2) = (Z, Z)$ with $D = p \cdot \frac{1}{2} + (1 - p) q$, so $\frac{1}{2} - q = \frac{\varepsilon}{1 - p}$, and rate $(1 - p)(1 - h(q)) = \frac{1}{1 - p} \cdot \frac{2}{\ln 2} \varepsilon^2 + O(\varepsilon^4)$.

Finally, for Mode A at $q = \frac{1}{2} - \delta$, $D_1 = \frac{1}{2} - \delta$ and $D_2 = p * q = \frac{1}{2} - (1 - 2p)\delta$. Then $\frac{D_1 + D_2}{2} = \frac{1}{2} - (1 - p)\delta$, so
$$h\!\left(\frac{D_1 + D_2}{2}\right) - \frac{h(D_1) + h(D_2)}{2} = \frac{2}{\ln 2}\left[\frac{1 + (1 - 2p)^2}{2} - (1 - p)^2\right]\delta^2 + O(\delta^4) = \frac{2}{\ln 2} p^2 \delta^2 + O(\delta^4),$$
which accounts for the exact factor $\frac{1 - 2p + 2p^2}{(1 - p)^2} = 1 + \frac{p^2}{(1 - p)^2}$. $\square$

### Proof of Claim 3
Assume WLOG $D_2 \ge p * D_1$ (hence $D_1 \le D_2$). Any operationally achievable $(R_1, R_2, D_1, D_2)$ must reconstruct $X_1^n$ within Hamming distortion $D_1$ using $(M_1, M_2)$ of total rate $R_1 + R_2$; even if both encoders cooperated and observed $(X_1^n, X_2^n)$, Shannon's rate-distortion converse for $X_1 \sim \mathrm{Bern}(1/2)$ yields $R_1 + R_2 \ge 1 - h(D_1)$. Conversely, Mode A from Claim 1 with $q = D_1$ lies in `InBergerTungClosure`, has $(R_1, R_2) = (1 - h(D_1), 0)$, and achieves distortions $(D_1, p * D_1) \le (D_1, D_2)$. $\square$

### Numerical Tables (Claims 1, 2, 4)

All computations are reproduced by `attempts/multiterminal-source-coding/code/analyze_dsbs.py` and `attempts/multiterminal-source-coding/code/analyze_dsbs_deep.py`.

**Table 1: Symmetric $\mathrm{DSBS}(p = 0.10)$ — Impact of Asymmetric Time-Sharing inside `InBergerTungClosure`**

| $D$ | Sym-BSC BT | TS-1Enc BT | True BT Hull | CW Log-Loss | Centralized | Sym $-$ True BT | Gap (BT $-$ CW) |
|---:|---:|---:|---:|---:|---:|---:|---:|
| $0.000$ | $1.4690$ | $\infty$ | $1.4690$ | $1.4690$ | $1.4690$ | $0.0000$ | $0.0000$ |
| $0.020$ | $1.2783$ | $\infty$ | $1.2656$ | $1.1861$ | $1.1863$ | $0.0127$ | $0.0794$ |
| $0.050$ | $1.0985$ | $1.0000$ | $0.9951$ | $0.9206$ | $0.8963$ | $0.1033$ | $0.0746$ |
| $0.080$ | $0.9517$ | $0.7892$ | $0.7893$ | $0.7583$ | $0.7103$ | $0.1624$ | $0.0310$ |
| $0.100$ | $0.8636$ | $0.6905$ | $0.6905$ | $0.6688$ | $0.6215$ | $0.1731$ | $0.0217$ |
| $0.125$ | $0.7614$ | $0.5862$ | $0.5862$ | $0.5711$ | $0.5277$ | $0.1752$ | $0.0152$ |
| $0.150$ | $0.6664$ | $0.4967$ | $0.4968$ | $0.4857$ | $0.4472$ | $0.1697$ | $0.0111$ |
| $0.200$ | $0.4955$ | $0.3500$ | $0.3500$ | $0.3437$ | $0.3151$ | $0.1455$ | $0.0063$ |
| $0.300$ | $0.2256$ | $0.1476$ | $0.1476$ | $0.1455$ | $0.1329$ | $0.0780$ | $0.0021$ |
| $0.400$ | $0.0574$ | $0.0359$ | $0.0359$ | $0.0355$ | $0.0325$ | $0.0214$ | $0.0005$ |

**Table 2: Symmetric $\mathrm{DSBS}(p = 0.25)$ vs. $\mathrm{DSBS}(p = 0.35)$ (Across Phase Transition $p^* = 0.2929$)**

| $D$ | $p=0.25$ Sym | $p=0.25$ True BT | $p=0.25$ CW | $p=0.35$ Sym | $p=0.35$ True BT | $p=0.35$ CW |
|---:|---:|---:|---:|---:|---:|---:|
| $0.050$ | $1.3054$ | $1.3054$ | $1.2385$ | $1.3842$ | $1.3842$ | $1.3613$ |
| $0.100$ | $0.9868$ | $0.9868$ | $0.8853$ | $1.0353$ | $1.0353$ | $0.9962$ |
| $0.150$ | $0.7366$ | $0.7366$ | $0.6412$ | $0.7647$ | $0.7647$ | $0.7264$ |
| $0.200$ | $0.5326$ | $0.5299$ | $0.4529$ | $0.5477$ | $0.5477$ | $0.5152$ |
| $0.300$ | $0.2328$ | $0.2162$ | $0.1913$ | $0.2358$ | $0.2358$ | $0.2187$ |
| $0.400$ | $0.0578$ | $0.0519$ | $0.0466$ | $0.0580$ | $0.0580$ | $0.0534$ |

**Table 3: Structured Codes & One-Help-One Corner ($D_2 = 1/2, R_2 = 0.5$)**

- **Structured quantize-and-bin ($p = 0.10$)**: Maj-3 ($D = 0.25$, $R_{\mathrm{sum}} = 0.5246$ vs True BT $0.238$), Maj-5 ($D = 0.3125$, $R_{\mathrm{sum}} = 0.3248$), Maj-7 ($D = 0.34375$, $R_{\mathrm{sum}} = 0.2361$), Hamming $[7,4]$ ($D = 0.125$, $R_{\mathrm{sum}} = 0.9072$ vs True BT $0.5862$). Körner–Marton hybrid ($2h(p) + 1 - h(D)$) gives $1.3944$ at $D = 0.125$.
- **One-help-one ($p = 0.10, D_2 = 0.5, R_2 = 0.5 \implies \beta = 0.1100, q_{\mathrm{eff}} = 0.1880$)**:
  - $D_1 = 0$: $R_1(\mathrm{WZ/BT}) = R_1(\mathrm{MGL\text{-}Fano}) = 0.69732$ (tight, Wyner–Ahlswede–Körner).
  - $D_1 = 0.0376$: $R_1(\mathrm{WZ/BT}) = 0.51312$ vs $R_1(\mathrm{MGL\text{-}Fano}) = 0.46612$ (gap $0.04700$).
  - $D_1 = 0.0752$: $R_1(\mathrm{WZ/BT}) = 0.38477$ vs $R_1(\mathrm{MGL\text{-}Fano}) = 0.31225$ (gap $0.07252$).
  - $D_1 = 0.1128$: $R_1(\mathrm{WZ/BT}) = 0.25651$ vs $R_1(\mathrm{MGL\text{-}Fano}) = 0.18897$ (gap $0.06754$).

### Literature Update & Novelty Check
We searched IEEE Trans. Inf. Theory and arXiv up to 2026 for progress on two-terminal $\mathrm{DSBS}(p)$ under separate Hamming distortions. Beyond the references in `problems/multiterminal-source-coding.md`, two landmark papers postdate Berger–Yeung (1989) and directly contextualize this problem:
- **Wagner and Anantharam (2008)** (*IEEE Trans. Inf. Theory*, vol. 54, no. 5, pp. 1919–1937) proved a strictly tighter outer bound than the classical Berger–Tung outer bound via auxiliary common variables, resolving binary erasure CEO instances; however, it remains unknown whether it matches Berger–Tung on $\mathrm{DSBS}(p)$ under Hamming distortion.
- **Shirani and Pradhan (2021)** (*IEEE Trans. Inf. Theory*, vol. 67, no. 7, pp. 4485–4503; arXiv:1906.08810) constructed two-layer schemes (combining a constant finite-blocklength primary code with an asymptotic secondary code) that strictly beat the Berger–Tung inner bound on binary one-help-one sources *lacking an exact Gács–Körner common component* (obtained by perturbing common-component sources of Wagner–Kelly–Altuğ 2011). Crucially, their counterexamples use larger / multi-component alphabets rather than the single-bit $\mathrm{DSBS}(p)$ on $\{0, 1\} \times \{0, 1\}$, so `MultiterminalSourceCoding.Statement` remains genuinely open (including on its one-help-one boundary $D_2 = 1/2$).

For our own contributions: the time-sharing improvement of Mode A/B over symmetric BSC quantization is an elementary consequence of non-convexity of Berger–Tung in $(D_1, D_2)$ (and related to the observation that Berger–Tung requires time-sharing for binary sources), but its exact phase-transition threshold $p^* = 1 - 1/\sqrt{2}$, the global linear SDPI+log-loss converse $R_1 + R_2 \ge \frac{2}{1 + (1-2p)^2}(1 - h(D))$, and the exact attribution of the residual $D \to 1/2$ log-loss gap to the Jensen gap of $h$ appear to be clean, self-contained sharpenings not previously recorded in `problems/multiterminal-source-coding.md`.

## Verification

- `attempts/multiterminal-source-coding/code/analyze_dsbs.py`: evaluates symmetric BSC BT, symmetric BT outer bound (short Markov chains), Courtade–Weissman log-loss, centralized Blahut–Arimoto RD, Körner–Marton hybrid, finite-blocklength majority ($k = 3, 5, 7$) and Hamming $[7,4]$ quantizers, and one-help-one Wyner–Ziv vs. MGL+Fano bounds for $p \in \{0.10, 0.25\}$.
- `attempts/multiterminal-source-coding/code/analyze_dsbs_deep.py`: evaluates the full time-shared asymmetric BSC-pair Berger–Tung hull across $p \in \{0.10, 0.20, 0.25, 0.35\}$, verifies the exact phase transition $p^* = 1 - 1/\sqrt{2} = 0.292893$, and computes the asymptotic coefficients in Claim 2.
- Fine-grid check ($q$ log-spaced down to $10^{-5}$, $30{,}000$ random $|U_1|, |U_2| \le 4$ auxiliaries) confirmed maximum improvement $< 3 \times 10^{-5}$ bits over the asymmetric BSC-pair hull.

## Dead ends

1. **Körner–Marton linear syndrome coding on $\mathrm{DSBS}(p)$**: Sending $H X_1^n$ and $H X_2^n$ (rate $h(p)$ each) to recover $Z^n = X_1^n \oplus X_2^n$, combined with a rate-$(1 - h(D))$ lossy description of $X_1^n$ (so $\hat{X}_2^n = \hat{X}_1^n \oplus Z^n$ achieves $D_1 = D_2 = D$), requires sum-rate $2h(p) + 1 - h(D)$. **Obstruction**: For $D = 0$, this already wastes $h(p)$ bits relative to Slepian–Wolf ($1 + h(p)$), because reconstructing BOTH $(X_1, X_2)$ requires $H(X_1)$ anyway, so paying $h(p)$ *twice* to isolate $X_1 \oplus X_2$ is strictly dominated by Berger–Tung ($1 + h(p) - h(D)$ or better) for every $p \in (0, 1/2)$ and $D \in [0, 1/2]$.
2. **Finite-blocklength linear/majority quantize-and-bin codes**: Inspired by Shirani–Pradhan (2021), we tested exact finite-blocklength deterministic quantizers ($k$-bit majority vote for $k = 3, 5, 7$ and the perfect $[7, 4]$ Hamming covering code at $D = 1/8$) followed by Slepian–Wolf binning of $(U_1^k, U_2^k)$. **Obstruction**: On the single-bit $\mathrm{DSBS}(p)$, these codes incur a large single-user shaping/rate-distortion penalty relative to optimal asymptotic quantization ($1 - h(D)$), losing by $0.10$–$0.26$ bits to `InBergerTungClosure` even before accounting for distributed correlation.
3. **Closing the high-distortion gap via log-loss**: Even after shrinking the symmetric gap at $p = 0.10$ by $12.5\times$ via asymmetric time-sharing (Claim 1), Claim 2 proves that the Courtade–Weissman log-loss outer bound *cannot* close the remaining gap for any $p \in (0, 1/2)$, because relaxing separate Hamming distortions to entropies via Fano loses at least the Jensen gap $\frac{p^2}{(1-p)^2}$ (for $p < 1 - 1/\sqrt{2}$) or $(1 - 2p)^2$ (for $p \ge 1 - 1/\sqrt{2}$) as $D \to 1/2$.
4. **Classical symmetric Berger–Tung outer bound**: Evaluating the Berger–Tung outer bound restricted to symmetric binary short Markov chains $U_1 - X_1 - X_2$, $U_2 - X_2 - X_1$ yields $0.5960$ bits at $p = 0.10, D = 0.15$ — strictly *looser* than `Sym-BSC` ($0.6664$) yet still strictly *above* the true time-shared inner bound ($0.4968$)! Thus any outer bound tight enough to match `InBergerTungClosure` for $\mathrm{DSBS}(p)$ must both respect asymmetric time-sharing and avoid the Fano Jensen loss.

## References

- T. Berger, "Multiterminal source coding," in *The Information Theory Approach to Communications*, CISM Courses and Lectures, vol. 229, Springer, 1978, pp. 171–231.
- S.-Y. Tung, *Multiterminal Source Coding*, Ph.D. dissertation, Cornell University, 1978.
- A. D. Wyner and J. Ziv, "A theorem on the entropy of certain binary sequences and applications—Part I," *IEEE Trans. Inf. Theory*, vol. 19, no. 6, pp. 769–772, 1973.
- J. Körner and K. Marton, "How to encode the modulo-two sum of binary sources," *IEEE Trans. Inf. Theory*, vol. 25, no. 2, pp. 219–221, 1979.
- T. Berger and R. W. Yeung, "Multiterminal source encoding with one distortion criterion," *IEEE Trans. Inf. Theory*, vol. 35, no. 2, pp. 228–236, 1989.
- A. B. Wagner and V. Anantharam, "An improved outer bound for multiterminal source coding," *IEEE Trans. Inf. Theory*, vol. 54, no. 5, pp. 1919–1937, 2008.
- A. B. Wagner, B. G. Kelly, and Y. Altuğ, "Distributed rate-distortion with common components," *IEEE Trans. Inf. Theory*, vol. 57, no. 7, pp. 4035–4057, 2011.
- T. A. Courtade and T. Weissman, "Multiterminal source coding under logarithmic loss," *IEEE Trans. Inf. Theory*, vol. 60, no. 1, pp. 740–761, 2014.
- F. Shirani and S. S. Pradhan, "A new achievable rate-distortion region for distributed source coding," *IEEE Trans. Inf. Theory*, vol. 67, no. 7, pp. 4485–4503, 2021 (arXiv:1906.08810).
- Prior attempts consulted: none (no earlier files in `attempts/multiterminal-source-coding/`).
