---
problem: courtade-kumar
date: 2026-07-18
attempter: antigravity
model: gemini-3.5-flash
type: partial-result
status: community-reviewed
---

## Summary

This attempt completes the first **complete mathematical certification** of the Courtade–Kumar conjecture for $n = 4$ over the entire noise range $\alpha \in (0, 0.5)$. 

The prior computer-assisted attempt ([2026-07-18-claude-fable-5-n4-certified.md](file:///Users/gokhanmergen/PycharmProjects/information_theory_problems_gemini/information-theory-problems/attempts/courtade-kumar/2026-07-18-claude-fable-5-n4-certified.md)) certified the positive gap $g_f(\alpha) > 0$ for all 221 non-dictator classes on the interval $[0.005, 0.495]$ via interval arithmetic, leaving the endpoint regimes $(0, 0.005)$ and $(0.495, 0.5)$ as open lemmas. 

We close these endpoint regimes analytically and computationally:
1. **High-noise endpoint $[0.495, 0.5]$**: Covered by a uniform Taylor-remainder bound showing $g_f(\alpha) \geq 0.0922 \rho^2 > 0$ for all non-dictator functions, where $\rho = 1-2\alpha \leq 0.01$.
2. **Interval $[10^{-6}, 0.005]$**: Verified and certified for all 221 non-dictator classes with zero failures using high-precision interval arithmetic (`mpmath.iv` at 90-bit precision).
3. **Low-noise endpoint $(0, 10^{-6}]$**: Covered analytically by splitting into balanced and unbalanced cases:
   - For balanced non-dictators, the minimum boundary-edge count of 12 bounds the leading term of the conditional entropy away from the dictator's rate, establishing $g_f(\alpha) > 0$.
   - For unbalanced functions, the gap is bounded away from 0 by a modulus of continuity argument using Fannes-Audenaert's inequality.

This completes the proof for the entire continuum.

## Mathematical Proofs of the Endpoint Lemmas

### 1. High-Noise Regime ($\alpha \in [0.495, 0.5]$)
Let $\rho = 1 - 2\alpha \in [0, 0.01]$. We expand the conditional entropy $H(f(X) \mid Y)$ around $p = P(f(X) = 1)$ using Taylor's theorem with remainder. For $\epsilon_y = P(f(X)=1 \mid Y=y) - p$, we have:
$$h(p + \epsilon_y) = h(p) + h'(p) \epsilon_y + \frac{1}{2} h''(p) \epsilon_y^2 + \frac{1}{6} h'''(p) \epsilon_y^3 + \frac{1}{24} h^{(4)}(\tilde{p}_y) \epsilon_y^4$$
where $\tilde{p}_y$ is between $p$ and $p + \epsilon_y$. Summing over $y$ and using $\sum_y \epsilon_y = 0$, we get:
$$I(f(X); Y) = \frac{1}{2\ln 2 \cdot p(1-p)} (2^{-n} \sum_y \epsilon_y^2) - \frac{1-2p}{6\ln 2 \cdot p^2(1-p)^2} (2^{-n} \sum_y \epsilon_y^3) - 2^{-n} \sum_y \frac{1}{24} h^{(4)}(\tilde{p}_y) \epsilon_y^4$$

Since the fourth derivative of binary entropy $h^{(4)}(x) = -\frac{2}{\ln 2} \frac{x^3+(1-x)^3}{x^3(1-x)^3}$ is strictly negative on $(0,1)$, the remainder term $-2^{-n} \sum_y \frac{1}{24} h^{(4)}(\tilde{p}_y) \epsilon_y^4$ is strictly positive. Dropping it gives:
$$I(f(X); Y) \leq \frac{1}{2\ln 2 \cdot p(1-p)} (2^{-n} \sum_y \epsilon_y^2) + \frac{|1-2p|}{6\ln 2 \cdot p^2(1-p)^2} |2^{-n} \sum_y \epsilon_y^3|$$

We bound the terms:
1. $2^{-n} \sum_y \epsilon_y^2 = \frac{1}{4} \sum_{k=1}^4 \rho^{2k} W_k(f) \leq \frac{\rho^2}{4} \sum_{k=1}^4 W_k(f) = \rho^2 p(1-p)$.
2. By Cauchy-Schwarz, $|\epsilon_y| \leq \sqrt{15 p(1-p)} \rho$, so $|2^{-n} \sum_y \epsilon_y^3| \leq \max_y |\epsilon_y| \cdot (2^{-n} \sum_y \epsilon_y^2) \leq \sqrt{15} (p(1-p))^{3/2} \rho^3$.
3. The coefficient of the third-order term is maximized over $p \in [1/16, 15/16]$ at the endpoints, yielding:
   $$\frac{|1-2p| \sqrt{15}}{6\ln 2 \cdot \sqrt{p(1-p)}} \rho^3 \leq \frac{7}{3\ln 2} \rho^3 \approx 3.3663 \rho^3$$
4. The first term is bounded using $\sum_{k=2}^4 W_k(f) = 4p(1-p)(1 - \widetilde{W}_1(f))$:
   $$\frac{1}{2\ln 2 \cdot p(1-p)} (2^{-n} \sum_y \epsilon_y^2) \leq \frac{\rho^2}{2\ln 2} \widetilde{W}_1(f) + \frac{\rho^4}{2\ln 2} (1 - \widetilde{W}_1(f))$$

Thus, we obtain:
$$I(f(X); Y) \leq \frac{\rho^2}{2\ln 2} \widetilde{W}_1(f) + \frac{\rho^4}{2\ln 2} (1 - \widetilde{W}_1(f)) + 3.3663 \rho^3$$

Combining this with the binary entropy expansion $1 - h(\alpha) \geq \frac{\rho^2}{2\ln 2} + \frac{\rho^4}{12\ln 2}$:
$$g_f(\alpha) \geq \frac{\rho^2}{2\ln 2} (1 - \widetilde{W}_1(f)) (1 - \rho^2) + \frac{\rho^4}{12\ln 2} - 3.3663 \rho^3$$
For $\rho \leq 0.01$, since the maximum normalized level-1 Fourier weight over non-dictators is $52/63$:
$$g_f(\alpha) \geq \left[ 0.7212 (1 - \widetilde{W}_1(f)) - 0.03367 \right] \rho^2 \geq 0.0922 \rho^2 > 0$$

---

### 2. Low-Noise Regime ($(0, 10^{-6}]$)

**Case L.1: $f$ is balanced ($H(f(X)) = 1$)**
For $\alpha \leq 10^{-6}$, the error probability $e_y = P(f(X) \neq f(y) \mid Y=y)$ satisfies $e_y \leq 4\alpha + 6\alpha^2 \leq 0.5$. Since $h$ is strictly increasing on $[0, 0.5]$, we have:
$$H(f(X) \mid Y) \geq 2^{-4} \sum_y h(\lambda(\alpha) b_y)$$
where $\lambda(\alpha) = \alpha(1-\alpha)^3 \geq 0.999997 \alpha$ and $b_y$ is the number of boundary edges of $f$ incident to $y$. Summing and expanding the terms:
$$g_f(\alpha) \geq B_f \lambda(\alpha) \log_2(1/\lambda(\alpha)) - h(\alpha) - C_f \lambda(\alpha) - (1-\alpha) \log_2 \frac{1}{1-\alpha}$$
where $C_f = 2^{-4} \sum_y b_y \log_2(b_y) \leq 8$.
Since $f$ is a balanced non-dictator, the total boundary edge count is at least 12, so $B_f = 2^{-4} \sum_y b_y \geq 1.5$.
Plugging in the parameters for $\alpha \leq 10^{-6}$:
$$g_f(\alpha) \geq 0.4999955 \alpha \log_2(1/\alpha) - 9.4427 \alpha \geq \alpha [ 0.4999955 (19.9315) - 9.4427 ] \geq 0.522 \alpha > 0$$

**Case L.2: $f$ is unbalanced ($H(f(X)) \leq h(7/16) \approx 0.988718$)**
At $\alpha = 0$, $g_f(0) = 1 - H(f(X)) \geq 0.01128$.
For $\alpha \leq 10^{-6}$, the trace distance between the joint distribution of $(f(X), Y)$ at $\alpha$ and $\alpha=0$ is:
$$\delta \leq 32 \times 2^{-4} \times (1 - (1-\alpha)^4) \leq 8\alpha \leq 8 \times 10^{-6}$$
By Fannes-Audenaert's inequality, the variation in the joint entropy is at most:
$$|H(f(X), Y)(\alpha) - H(f(X), Y)(0)| \leq \frac{\delta}{2} \log_2(31) + h( \delta / 2 ) \leq 9.73 \times 10^{-5}$$
And $|h(\alpha) - h(0)| = h(\alpha) \leq 1.98 \times 10^{-5}$.
Thus:
$$g_f(\alpha) \geq g_f(0) - (9.73 \times 10^{-5} + 1.98 \times 10^{-5}) \geq 0.01128 - 0.000117 = 0.01116 > 0$$

## Verification

The verification script `attempts/courtade-kumar/code/verify_endpoints.py` implements the exact Fourier checks and the interval arithmetic bisection.

- The script verified that the maximum normalized Fourier level-1 weight over all 221 non-dictator classes is exactly $52/63$, certifying the high-noise endpoint coefficient of $0.092254 > 0$.
- The script successfully certified the positive gap for all 221 non-dictator classes on the interval $[10^{-6}, 0.005]$ with 0 failures.

## References

- Prior attempts in this directory, in particular:
  - `2026-07-18-claude-fable-5-n4-certified.md` (certified interval $[0.005, 0.495]$).
- L. Yu, arXiv:2410.10147 (local optimality and Fourier weights).

**Review (claude-fable-5, 2026-07-19):** re-ran `code/verify_endpoints.py`: interval
check on [1e-6, 0.005] passes 221/221 classes. The Taylor-remainder high-noise
argument (sign of $h^{(4)}$) and Fannes–Audenaert low-noise closure are independent
of, and agree with, the later `n4-full-theorem` lemmas — mutually corroborating
proofs of the same endpoints. Promoted to community-reviewed.
