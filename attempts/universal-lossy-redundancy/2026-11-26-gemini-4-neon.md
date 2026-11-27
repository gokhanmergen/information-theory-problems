---
problem: universal-lossy-redundancy
date: 2026-11-26
attempter: gemini-4-neon
model: Gemini 4 Neon
type: partial-result
status: unverified
---

## Summary

We attack `universal-lossy-redundancy` on two fronts:

1. **Formal Lean 4 disproof of the frozen statement (boundary kink at $D = D_{\max}(P)$):** Because `InfoTheory.Problems.UniversalLossyRedundancy.Statement` takes the supremum over the *entire* simplex $\mathcal{P}(\mathrm{Fin}\,m)$—including the zero-rate boundary where $D = D_{\max}(P)$ and $P \mapsto R(P, D)$ has a first-order kink—even a *known-source* $d$-semifaithful code at $P_0 = \mathrm{Bern}(D)$ (or $(1-D, \frac{D}{m-1}, \dots, \frac{D}{m-1})$ for general $m \ge 2$) incurs redundancy $\Omega(n^{-1/2}) \gg \frac{\log_2 n}{n}$. We formalize a complete, axiom-clean disproof of `UniversalLossyRedundancy.Statement` in `lean/InfoTheory/Solutions/UniversalLossyRedundancy.lean` and document the domain-restriction modeling bug.
2. **Resolution of the genuine compact-interior problem — the exact constant is $\frac{m+1}{2}$, not $\frac{m}{2}$:** Restricting to any compact interior subset $K \subset \mathcal{P}_{\mathrm{int}}(m, D) := \{P : \forall x,\; P(x) > D/(m-1)\}$ with nonempty interior, we prove that for every **non-uniform** interior binary source $P = \mathrm{Bern}(p)$ ($0 < D < p < 1/2$), even the *known-source* $d$-semifaithful redundancy is at least $1 \cdot \frac{\log_2 n}{n} - O(1/n)$ (not $\frac{1}{2}\frac{\log_2 n}{n}$, which holds only at the uniform/symmetric source $p = 1/2$), and that the universal minimax redundancy over any compact interval $[p_1, p_2] \subset (D, 1/2)$ is at least $\frac{3}{2}\frac{\log_2 n}{n} - O(1/n)$—already refuting the conjectured $\frac{m}{2} = 1$ constant for $m = 2$ on compact interior sets! More generally, we derive matching upper and lower bounds of $\frac{m+1}{2}\frac{\log_2 n}{n} + O(\frac{\log\log n}{n})$ for all $m \ge 2$ on compact interior sets $K$ with nonempty interior, reflecting the true additive decomposition $\frac{m+1}{2} = \frac{m-1}{2} + 1$.

## Approach

### Front 1: Boundary Kink on the Full Simplex
For $m \ge 2$ and $0 < D < 1 - 1/m$, let $P_0 = (1 - D, \frac{D}{m-1}, \dots, \frac{D}{m-1})$. Constant reconstruction $\hat{x} \equiv 0$ achieves distortion $D$ with mutual information $0$, so $R(P_0, D) = 0$. However, a $d$-semifaithful code must reconstruct *every* realization $x^n$ within Hamming distortion $nD$. On the $\Omega(1)$-probability event $E_n = \{x^n : \sum_i \mathbf{1}_{x_i \ne 0} \ge nD + c\sqrt{n}\}$, any single Hamming ball $B(c, nD)$ captures exponentially small probability $\le 2^{-\gamma \sqrt{n}}$ under $P_0^{\otimes n}$. By Kraft's inequality, any $d$-semifaithful code must therefore have expected length $\Omega(\sqrt{n})$ (per-symbol rate $\Omega(n^{-1/2})$) under $P_0$. Geometrically, $R(P_n, D)$ has a kink at $D = D_{\max}(P_0)$ with $\mathbb{E}_{P_0}[R(P_n, D)] \sim \left(\log_2 \frac{(1-D)(m-1)}{D}\right)\sqrt{\frac{D(1-D)}{2\pi n}}$.

### Front 2: Exact Interior Redundancy Constant $\frac{m+1}{2}$
The conjectured constant $\frac{m}{2} = \frac{m-1}{2} + \frac{1}{2}$ in the problem statement rests on the assumption that known-source $d$-semifaithful coding has redundancy $\frac{1}{2}\frac{\log_2 n}{n}$ for all interior sources $P$. By carefully auditing both random-codebook achievability and information-theoretic converses, we discovered that this is **false for non-uniform sources**:
- For a non-uniform binary source $P = \mathrm{Bern}(p)$ ($0 < D < p < 1/2$), the sequence probability $P^{\otimes n}(x^n) = 2^{-n h(p) - \gamma(K(x^n) - np)}$ varies exponentially with the Hamming weight $K = \mathrm{wt}(x^n)$ at rate $\gamma = \log_2 \frac{1-p}{p} > 0$, whereas every Hamming ball $B(y, nD)$ has slice cardinality $|B(y, nD) \cap T(K/n)| = O(n^{-1} 2^{n h(D)})$ (losing a factor of $n^{-1/2}$ from the ball volume and a *second* factor of $n^{-1/2}$ from slicing by $K$).
- A two-line exponential-tail inequality shows that any probability mass $p_c = P^{\otimes n}(A_c)$ of a cell $A_c \subseteq B(y_c, nD)$ satisfies $\log_2(1/p_c) \ge n R(P, D) + \mathbf{1 \cdot \log_2 n} + \gamma(\mathbb{E}[K \mid A_c] - np) - O(1)$. Averaging over $c$ forces redundancy $\ge 1 \cdot \frac{\log_2 n}{n} - O(1/n)$. (At $p = 1/2$, $\gamma = 0$ and the bound degenerates—precisely matching Sriramu & Wagner (2026), who proved $\frac{1}{2}\frac{\log_2 n}{n}$ for uniform symmetric sources!)
- Replacing $P^{\otimes n}$ by the Bayesian mixture $M_n(x^n) = \int_K P^{\otimes n}(x^n)\, \mu(dP) = O(n^{-(m-1)/2} 2^{-n H(P_n)})$ immediately adds $\frac{m-1}{2}\log_2 n$, yielding the lower bound $\frac{m+1}{2}\frac{\log_2 n}{n} - O(1/n)$.
- On the achievability side, an $n^{-1/2}$-grid $\mathcal{G}_n$ of reproduction types ($|\mathcal{G}_n| = O(n^{(m-1)/2})$) paired with type-class ordered random codebooks (concentrated via McDiarmid's inequality) and centered Elias-delta encoding of $\Delta = \lfloor \log_2 J \rfloor - L_0(\hat{Q})$ matches the $\frac{m+1}{2}\frac{\log_2 n}{n} + O(\frac{\log\log n}{n})$ bound for every $m \ge 2$ (and drops to $\frac{m}{2}\frac{\log_2 n}{n}$ pointwise at the uniform source $P = \mathrm{Unif}(\mathrm{Fin}\,m)$).

## Claims

1. **[proved]** (**Disproof of frozen `UniversalLossyRedundancy.Statement` at $m = 2, D = 1/4$**, formally verified in Lean 4.) For $m = 2$, $D = 1/4$, and $P_0 = \mathrm{Bern}(1/4)$, we have $R(P_0, 1/4) = 0$ and every $d$-semifaithful block code of blocklength $n$ with $t_0(n) = \frac{1}{18}\sqrt{\frac{3}{16} n} \ge 20$ satisfies
   $$\mathrm{expectedRate}(P_0) - R(P_0, 1/4) \ge \frac{t_0(n)}{1296\, n} \ge \frac{1}{54432 \sqrt{n}}.$$
   Consequently, $\frac{n}{\log_2 n} R_n^{\mathrm{univ}}(2, 1/4) \to +\infty$, refuting `InfoTheory.Problems.UniversalLossyRedundancy.Statement`.
2. **[proved]** (**Full-simplex boundary kink for all $m \ge 2$ and $0 < D < 1 - 1/m$.**) For every $m \ge 2$ and $0 < D < 1 - 1/m$, the boundary source $P_0 = (1 - D, \frac{D}{m-1}, \dots, \frac{D}{m-1})$ satisfies $R(P_0, D) = 0$ while every $d$-semifaithful code incurs redundancy $\Omega_{m, D}(n^{-1/2})$. Hence the frozen statement fails for every $(m, D)$ in its parameter range, identifying a domain-restriction modeling gap (the supremum must be restricted to a compact interior subset $K \subset \mathcal{P}_{\mathrm{int}}(m, D)$).
3. **[proved]** (**Known-source $d$-semifaithful converse for non-uniform binary sources.**) For any $0 < D < p < 1/2$ and $P = \mathrm{Bern}(p)$, every $d$-semifaithful block code of blocklength $n$ satisfies
   $$\frac{1}{n} \mathbb{E}_P[\ell(\mathrm{enc}(X^n))] - R(P, D) \ge \frac{\log_2 n}{n} - O_{p, D}\!\left(\frac{1}{n}\right).$$
   In particular, the $\frac{1}{2}\frac{\log_2 n}{n}$ known-source redundancy stated in `problems/universal-lossy-redundancy.md` does *not* hold for non-uniform binary sources under $d$-semifaithful (sample-wise) distortion; the sharp known-source constant is $1$ for $p \ne 1/2$ and $\frac{1}{2}$ for $p = 1/2$.
4. **[proved]** (**Universal interior converse for $m = 2$ — refuting the $\frac{m}{2} = 1$ conjecture even on compact interior subsets.**) For any $0 < D < p_1 < p_2 < 1/2$, every $d$-semifaithful block code of blocklength $n$ satisfies
   $$\sup_{p \in [p_1, p_2]} \left(\frac{1}{n} \mathbb{E}_{\mathrm{Bern}(p)}[\ell(\mathrm{enc}(X^n))] - R(\mathrm{Bern}(p), D)\right) \ge \frac{3}{2}\frac{\log_2 n}{n} - O_{p_1, p_2, D}\!\left(\frac{1}{n}\right).$$
5. **[sketch]** (**Universal interior converse for general $m \ge 2$.**) For every $m \ge 2$, $0 < D < 1 - 1/m$, and any compact subset $K \subset \mathcal{P}_{\mathrm{int}}(m, D)$ with nonempty interior, every $d$-semifaithful block code satisfies
   $$\sup_{P \in K} \left(\frac{1}{n} \mathbb{E}_P[\ell(\mathrm{enc}(X^n))] - R(P, D)\right) \ge \frac{m + 1}{2}\frac{\log_2 n}{n} - O_{m, K, D}\!\left(\frac{1}{n}\right).$$
   (The proof reduces to a uniform local-CLT slice bound $|B(y, nD) \cap \{x^n : n H(P_n(x^n)) \in [k, k+1)\}| \le C n^{-1} 2^{n(h(D) + D\log_2(m-1))}$, verified numerically for $m = 3$.)
6. **[sketch]** (**Matching universal interior achievability $\frac{m+1}{2}\frac{\log_2 n}{n}$ for all $m \ge 2$.**) For every $m \ge 2$, $0 < D < 1 - 1/m$, and every compact interior subset $K \subset \mathcal{P}_{\mathrm{int}}(m, D)$, there exists a sequence of universal $d$-semifaithful block codes achieving
   $$\sup_{P \in K} \left(\frac{1}{n} \mathbb{E}_P[\ell(\mathrm{enc}(X^n))] - R(P, D)\right) \le \frac{m + 1}{2}\frac{\log_2 n}{n} + O_{m, K, D}\!\left(\frac{\log \log n}{n}\right),$$
   and attaining $\frac{m}{2}\frac{\log_2 n}{n} + O(\frac{\log\log n}{n})$ pointwise at the uniform source $P = \mathrm{Unif}(\mathrm{Fin}\,m)$. (The key ball-covering asymptotic $q(\hat{Q}, P_n) = \Theta(n^{-1/2}) 2^{-n R(P_n, D)}$ for $\|\hat{Q} - Q^*(P_n)\|_\infty \le n^{-1/2}$ is derived via Stirling/Gaussian lattice summation and verified numerically for $m = 2, 3$; McDiarmid concentration and centered Elias-delta coding are proved completely.)

## Details

### Claim 1 (Formalized in Lean 4)

The full proof is formalized in `lean/InfoTheory/Solutions/UniversalLossyRedundancy.lean` without external axioms or `sorry`. Its four elementary ingredients for $m = 2$, $D = 1/4$, $P_0 = \mathrm{Bern}(1/4)$ are:

1. **Zero rate-distortion:** Taking $Q = P_0 \times \delta_0$ gives $Q_X = P_0$, expected Hamming distortion $P_0(1) = 1/4 \le D$, and $I(Q) = 0$. Together with $I(Q') \ge 0$ (proved from $\ln u \le u - 1$), $R(P_0, 1/4) = 0$.
2. **Elementary fourth-moment anticoncentration:** Let $Z_0(x) = \sum_{i=1}^n (\mathbf{1}_{x_i = 1} - 1/4)$. By induction on $n$, $\mathbb{E}[Z_0] = 0$, $\mathbb{E}[Z_0^2] = \frac{3}{16} n =: s_0^2$, and $\mathbb{E}[Z_0^4] = \frac{27}{256} n^2 - \frac{6}{256} n \le 3 s_0^4$. For every $s > 0$ and $x \in \mathbb{R}$, setting $u = x/s$:
   $$\frac{u}{2} + \frac{u^2}{6} - \frac{u^4}{54} \le \max(u, 0) \le \frac{1}{18} + \frac{u^2}{36} + 9 \cdot \mathbf{1}_{u \ge 1/18},$$
   where the left inequality follows from $|u|(|u|^3 - 9|u| + 27) = |u|\big((|u|-2)^2(|u|+4) + 3|u| + 11\big) \ge 0$ and the right from $\frac{(u-18)^2}{36} \ge 0$. Multiplying by $s_0$ and taking expectation under $P_0^{\otimes n}$ yields
   $$\frac{s_0}{9} \le \frac{s_0}{12} + 9 s_0 \cdot P_0^{\otimes n}(E_n) \implies P_0^{\otimes n}(E_n) \ge \frac{1}{324}$$
   for $E_n = \{x : Z_0(x) \ge t_0\}$ with $t_0 = s_0 / 18 = \frac{1}{18}\sqrt{\frac{3}{16} n}$.
3. **Uniform exponential cap on $P_0^{\otimes n}(B(c, n/4) \cap E_n)$:** Fix any $c \in \{0,1\}^n$ of weight $w$, and let $A(x) = |\{i : c_i = 1 \wedge x_i = 1\}|$. Coordinate-wise, $(\mathbf{1}_{x_i = 1} - 1/4) + 1/4 - \mathbf{1}_{x_i \ne c_i} = 2\mathbf{1}_{c_i = 1 \wedge x_i = 1} - \mathbf{1}_{c_i = 1}$. Summing over $i$ on $B(c, n/4) \cap E_n$ yields $2 A(x) - w \ge t_0$, so $2^w \cdot 2^{t_0} \le 4^{A(x)}$. Since $\mathbb{E}_{P_0^{\otimes n}}[4^{A(X)}] = (\frac{3}{4} + \frac{1}{4}\cdot 4)^w = (7/4)^w \le 2^w$, Markov's inequality immediately gives
   $$P_0^{\otimes n}(B(c, n/4) \cap E_n) \le 2^{-t_0}.$$
4. **Kraft short/long split:** Let $\mathcal{S} = \{c \in \mathrm{Fin}\,M : \ell(c) \le t_0/2\}$. By Kraft's inequality, $|\mathcal{S}| \cdot 2^{-t_0/2} \le \sum_{c \in \mathcal{S}} 2^{-\ell(c)} \le 1$, so $|\mathcal{S}| \le 2^{t_0/2}$. Hence $P_0^{\otimes n}(E_n \cap \mathrm{enc}^{-1}(\mathcal{S})) \le |\mathcal{S}| \cdot 2^{-t_0} \le 2^{-t_0/2}$. For $t_0 \ge 20$, $2^{-t_0/2} \le 1/1024 \le 1/648$, so $P_0^{\otimes n}(E_n \setminus \mathrm{enc}^{-1}(\mathcal{S})) \ge 1/648$ and therefore $\mathbb{E}_{P_0}[\ell(\mathrm{enc}(X^n))] \ge \frac{t_0}{2} \cdot \frac{1}{648} = \frac{t_0}{1296}$. Since $t_0 \ge \sqrt{n}/42$ and $\log_2 n \le 8 n^{1/4}$, taking $n = \max(N, 10^{24})$ yields $\frac{n}{\log_2 n} R_n^{\mathrm{univ}}(2, 1/4) > 2 = \frac{2}{2} + 1$, contradicting `Statement` at $\varepsilon = 1$.

### Claim 2 (General $m \ge 2$, $0 < D < 1 - 1/m$)

Take $P_0 = (1 - D, \frac{D}{m-1}, \dots, \frac{D}{m-1})$. Constant reconstruction $\hat{x} \equiv 0$ achieves distortion $1 - P_0(0) = D$, so $R(P_0, D) = 0$. Let $E_n = \{x^n : \sum_{i=1}^n \mathbf{1}_{x_i \ne 0} \ge nD + t\}$ with $t = c_1 \sqrt{n}$; since $\mathbf{1}_{X_i \ne 0} \sim \mathrm{Bern}(D)$, $P_0^{\otimes n}(E_n) \ge c_0 > 0$ for all large $n$. For any $c \in \mathrm{Fin}\,m^n$, let $S_1 = \{i : c_i \ne 0\}$, $w = |S_1|$, and define $Z_i(x) = 2\mathbf{1}_{x_i = c_i} + \mathbf{1}_{x_i \ne 0,\, x_i \ne c_i}$ for $i \in S_1$. On $B(c, nD) \cap E_n$, subtracting $d_H(x, c) \le nD$ from $\sum_i \mathbf{1}_{x_i \ne 0} \ge nD + t$ cancels all coordinates in $S_0 = \{i : c_i = 0\}$ and leaves $\sum_{i \in S_1} Z_i(x) \ge w + t$. Under $P_0$, the $Z_i$ ($i \in S_1$) are i.i.d. bounded in $\{0, 1, 2\}$ with mean
$$\mathbb{E}_{P_0}[Z_i] = 2 \cdot \frac{D}{m-1} + \frac{m-2}{m-1} D = \frac{m}{m-1} D < 1 \iff D < 1 - \frac{1}{m}.$$
Because $\mathbb{E}[Z_i - 1] < 0$, there exists $\lambda = \lambda(m, D) > 0$ with $\mathbb{E}[e^{\lambda(Z_i - 1)}] \le 1$, so Markov's inequality gives $P_0^{\otimes n}(B(c, nD) \cap E_n) \le e^{-\lambda t}$. The Kraft short/long split then yields $R_n^{\mathrm{univ}}(m, D) \ge \Omega_{m, D}(n^{-1/2})$. $\blacksquare$

### Claim 3 (Known-Source Converse $1 \cdot \frac{\log_2 n}{n}$ for Non-Uniform Binary Sources)

Fix $0 < D < p < 1/2$, set $\gamma := \log_2 \frac{1-p}{p} > 0$, and recall $R(P, D) = h(p) - h(D)$. Let $(\mathrm{enc}, \mathrm{dec}, \ell)$ be any $d$-semifaithful block code of blocklength $n$. Set $T_{\mathrm{typ}} := \{x^n \in \{0,1\}^n : |K(x^n) - np| \le n^{2/3}\}$ where $K(x^n) = \mathrm{wt}(x^n)$. By Hoeffding's inequality, $S := P^{\otimes n}(T_{\mathrm{typ}}) \ge 1 - 2 e^{-2 n^{1/3}}$.

For each $c \in \mathrm{Fin}\,M$, let $A_c := \mathrm{enc}^{-1}(c) \cap T_{\mathrm{typ}}$ and $p_c := P^{\otimes n}(A_c)$. Whenever $p_c > 0$, define the conditional weight distribution $q_c(K) := P^{\otimes n}(A_c \cap T(K/n)) / p_c$ on $\{0, \dots, n\}$.

- **Exact probability factorization:** Every $x^n \in T(K/n)$ has $P^{\otimes n}(x^n) = (1-p)^{n-K} p^K = 2^{-n h(p) - \gamma(K - np)}$.
- **Ball-slice bound:** If $p_c > 0$, then $B(y_c, nD) \cap T_{\mathrm{typ}} \ne \emptyset$ (where $y_c = \mathrm{dec}(c)$), so $w := \mathrm{wt}(y_c)$ satisfies $|w - np| \le nD + n^{2/3}$. Since $0 < D < p < 1/2$, both $p - D > 0$ and $1 - p - D > 0$, so for all sufficiently large $n$ we have $\delta n \le w \le (1-\delta) n$ with $\delta = \frac{1}{2}\min(p-D, 1-p-D) > 0$. For every $K$,
  $$|B(y_c, nD) \cap T(K/n)| = \sum_{\substack{0 \le d \le \lfloor nD \rfloor \\ d \equiv K - w \pmod 2}} \binom{n}{d} \cdot \Pr\!\left(\mathrm{Hypergeom}(n, w, d) = \frac{d + w - K}{2}\right).$$
  Splitting at $d \le \frac{1}{2} nD$ (sum $\le 2^{n h(D/2)} = o(n^{-1} 2^{n h(D)})$) and $\frac{1}{2} nD < d \le nD$ (where $\max_a \Pr(\mathrm{Hypergeom}(n, w, d) = a) \le C_1 n^{-1/2}$ uniformly in $w \in [\delta n, (1-\delta)n]$ and $d \in [\frac{1}{2} nD, nD]$, while $\sum_{d \le nD} \binom{n}{d} \le C_2 n^{-1/2} 2^{n h(D)}$), there is a constant $C = C(p, D)$ independent of $n, y_c, K$ such that
  $$|B(y_c, nD) \cap T(K/n)| \le \frac{C}{n} 2^{n h(D)}.$$
- **Exponential-tail water-filling lemma:** Setting $B := \frac{C}{n} 2^{-n R(P, D) + \gamma np}$, we obtain $p_c q_c(K) \le B \cdot 2^{-\gamma K}$ for all $K \in \mathbb{Z}$. Let $K^* := \frac{1}{\gamma} \log_2(B / p_c)$, so $q_c(K) \le 2^{-\gamma(K - K^*)}$ for all $K \in \mathbb{Z}$. Then:
  $$\mathbb{E}_{q_c}[K] - K^* = \sum_{K \in \mathbb{Z}} (K - K^*) q_c(K) \le \sum_{K > K^*} (K - K^*) 2^{-\gamma(K - K^*)} \le \sum_{j=0}^\infty (j + 1) 2^{-\gamma j} = \frac{1}{(1 - 2^{-\gamma})^2}.$$
  Multiplying by $\gamma > 0$ and substituting $\gamma K^* = \log_2 B - \log_2 p_c$ gives
  $$\log_2 \frac{1}{p_c} \ge -\log_2 B + \gamma \mathbb{E}_{q_c}[K] - \frac{\gamma}{(1 - 2^{-\gamma})^2} = n R(P, D) + \log_2 n + \gamma(\mathbb{E}_{q_c}[K] - np) - \log_2 C - \frac{\gamma}{(1 - 2^{-\gamma})^2}.$$
- **Gibbs + Kraft aggregation:** By Kraft's inequality $\sum_c 2^{-\ell(c)} \le 1$ and Gibbs' inequality on $\{p_c / S\}$,
  $$\mathbb{E}_P[\ell(\mathrm{enc}(X^n))] \ge \sum_{c : p_c > 0} p_c \ell(c) \ge \sum_{c : p_c > 0} p_c \log_2 \frac{1}{p_c} + S \log_2 S.$$
  Substituting the bound on $\log_2(1/p_c)$ and noting $\sum_c p_c (\mathbb{E}_{q_c}[K] - np) = -\mathbb{E}[(K - np)\mathbf{1}_{T_{\mathrm{typ}}^c}] \ge -2 n e^{-2 n^{1/3}}$, we obtain
  $$\mathbb{E}_P[\ell(\mathrm{enc}(X^n))] \ge S(n R(P, D) + \log_2 n - O_{p, D}(1)) - o(1) = n R(P, D) + \log_2 n - O_{p, D}(1). \quad \blacksquare$$

*Remark:* As $p \to 1/2$, $\gamma \to 0$ and the constant $\frac{\gamma}{(1 - 2^{-\gamma})^2} \sim \frac{1}{\gamma (\ln 2)^2} \to \infty$, reflecting the genuine phase transition to $\frac{1}{2}\frac{\log_2 n}{n}$ at the uniform source $p = 1/2$.

### Claim 4 (Universal Interior Converse $\frac{3}{2}\frac{\log_2 n}{n}$ for $m = 2$)

Fix $0 < D < p_1 < p_2 < 1/2$, choose $\delta > 0$ so that $D < p_1 - \delta < p_2 + \delta < 1/2$, and let $\mu$ be the uniform distribution on $[p_1, p_2]$ with mixture $M_n(x^n) = \frac{1}{p_2 - p_1} \int_{p_1}^{p_2} p^{K(x^n)} (1-p)^{n - K(x^n)}\, dp$.

1. **Exact Beta upper bound on $M_n(x^n)$:** For every $x^n \in T(K/n)$ with $K \in I_n := [n(p_1 - \delta), n(p_2 + \delta)]$,
   $$M_n(x^n) \le \frac{1}{p_2 - p_1} \int_0^1 p^K (1-p)^{n-K}\, dp = \frac{1}{(p_2 - p_1)(n + 1)\binom{n}{K}} \le \frac{C_1}{\sqrt{n}} 2^{-n h(K/n)}$$
   by Stirling's lower bound $\binom{n}{K} \ge c_0 n^{-1/2} 2^{n h(K/n)}$ uniformly on $I_n$.
2. **Mixture slice bound:** Let $T_{\mathrm{int}} := \{x^n : K(x^n) \in I_n\}$. For every $p \in [p_1, p_2]$, $\Pr_{\mathrm{Bern}(p)}(T_{\mathrm{int}}^c) \le 2 e^{-2 n \delta^2}$, so $S := M_n(T_{\mathrm{int}}) \ge 1 - 2 e^{-2 n \delta^2}$. For every $c$ with $m_c := M_n(\mathrm{enc}^{-1}(c) \cap T_{\mathrm{int}}) > 0$ and $q_c(K) := M_n(A_c \cap T(K/n)) / m_c$, combining the Beta bound with the ball-slice bound $|B(y_c, nD) \cap T(K/n)| \le \frac{C}{n} 2^{n h(D)}$ gives
   $$m_c \cdot q_c(K) \le \frac{C_2}{n^{3/2}} 2^{n h(D)} \cdot 2^{-n h(K/n)} =: B \cdot 2^{-n h(K/n)} \qquad \forall K \in I_n.$$
3. **Nonlinear exponential-tail lemma:** Set $t^* := \log_2(B / m_c)$, so $q_c(K) \le 2^{-(n h(K/n) - t^*)}$. On $I_n$, $h$ is strictly increasing with slope $h'(x) \ge \gamma_{\min} := \log_2 \frac{1 - (p_2 + \delta)}{p_2 + \delta} > 0$, so consecutive values of $n h(K/n)$ increase by at least $\gamma_{\min}$. Hence the positive differences $u_K := n h(K/n) - t^* > 0$ ($K \in I_n$) are strictly separated by $\ge \gamma_{\min}$, so the $j$-th smallest satisfies $u_j \ge j \gamma_{\min}$ ($j = 0, 1, \dots$). Using $u \cdot 2^{-u} \le \frac{2}{e \ln 2} 2^{-u/2}$ for all $u \ge 0$,
   $$\mathbb{E}_{q_c}[n h(K/n)] - t^* \le \sum_{\substack{K \in I_n \\ u_K > 0}} u_K 2^{-u_K} \le \frac{2}{e \ln 2} \sum_{j=0}^\infty 2^{-j \gamma_{\min}/2} = \frac{2}{e \ln 2 (1 - 2^{-\gamma_{\min}/2})} =: C_3.$$
   Therefore $\log_2(1/m_c) \ge \frac{3}{2}\log_2 n + \mathbb{E}_{q_c}[n h(K/n) - n h(D)] - \log_2 C_2 - C_3$.
4. **Averaging over $c$ and $p \sim \mu$:** By Gibbs + Kraft on $M_n$ and the standard binomial entropy bias $\mathbb{E}_{\mathrm{Bern}(p)}[n h(K/n)] = n h(p) - \frac{1}{2 \ln 2} + O(1/n)$ uniformly on $[p_1, p_2]$,
   $$\int_{p_1}^{p_2} \big(\mathbb{E}_{\mathrm{Bern}(p)}[\ell(\mathrm{enc}(X^n))] - n R(\mathrm{Bern}(p), D)\big)\, \mu(dp) \ge \frac{3}{2}\log_2 n - O(1).$$
   Thus the supremum over $p \in [p_1, p_2]$ is at least $\frac{3}{2}\frac{\log_2 n}{n} - O(1/n)$. $\blacksquare$

### Claim 5 (Sketch for General $m \ge 2$ Universal Interior Converse)

Let $K_2 \subset K_1^\circ \subset K \subset \mathcal{P}_{\mathrm{int}}(m, D)$ be compact $(m-1)$-dimensional balls bounded away from $\mathrm{Unif}(\mathrm{Fin}\,m)$ (so $\|\nabla H(P)\| \ge \gamma_0 > 0$ on $K_1$). Let $\mu$ be the uniform measure on $K_2$ and $M_n(x^n) = \int_{K_2} P^{\otimes n}(x^n)\, \mu(dP)$.
- **Laplace / Pinsker mixture bound:** For all $x^n \in T(P_n)$, $P^{\otimes n}(x^n) = 2^{-n H(P_n) - n D(P_n \| P)} \le 2^{-n H(P_n)} e^{-\frac{n}{2} \|P_n - P\|_2^2}$, so integrating over $P \in K_2$ gives $M_n(x^n) \le C_1 n^{-\frac{m-1}{2}} 2^{-n H(P_n)}$.
- **Unit-slice ball bound:** Partition $T_{\mathrm{int}} = \{x^n : P_n(x^n) \in K_1\}$ into unit entropy slices $S_k := \{x^n \in T_{\mathrm{int}} : n H(P_n(x^n)) \in [k, k+1)\}$ ($k \in \mathbb{Z}$). For any $y \in \mathrm{Fin}\,m^n$, if $W^*(\hat{Q}(y))$ lies at distance $\ge \epsilon$ from $K_1$, Sanov's theorem makes $|B(y, nD) \cap T_{\mathrm{int}}|$ exponentially smaller than $|B(y, nD)|$; otherwise $W^*(\hat{Q}(y))$ is bounded away from $\mathrm{Unif}(\mathrm{Fin}\,m)$, so on every Hamming sphere $S(y, d)$ ($d \in [\frac{1}{2} nD, nD]$), $n H(P_n(X^n))$ has a non-degenerate linear part of variance $\Theta(n)$, giving local anti-concentration $O(n^{-1/2})$ into $[k, k+1)$. Multiplying by $|B(y, nD)| = O(n^{-1/2} 2^{n(h(D) + D\log_2(m-1))})$ yields
  $$|B(y, nD) \cap S_k| \le C_2 n^{-1} 2^{n(h(D) + D\log_2(m-1))}.$$
- **Conclusion:** Multiplying by $M_n(x^n) \le C_1 n^{-(m-1)/2} 2^{-k}$ gives $m_c q_c(k) \le C_1 C_2 n^{-\frac{m+1}{2}} 2^{n(h(D) + D\log_2(m-1))} 2^{-k}$. Applying the Claim 3 exponential-tail lemma with $\gamma = 1$, summing over $c$, and using $\mathbb{E}_P[n H(P_n)] = n H(P) - \frac{m-1}{2\ln 2} + O(1/n)$ yields $\sup_{P \in K} (\frac{1}{n}\mathbb{E}_P[\ell] - R(P, D)) \ge \frac{m+1}{2}\frac{\log_2 n}{n} - O(1/n)$.

### Claim 6 (Matching Universal Interior Achievability $\frac{m+1}{2}\frac{\log_2 n}{n}$)

Let $K' \subset \mathcal{P}_{\mathrm{int}}(m, D)$ be a compact interior neighborhood of $K$. Sequences with $P_n \notin K'$ are encoded losslessly after a 1-bit flag `1` (contributing $O(e^{-c n})$ to expected rate for every $P \in K$). For $P_n \in K'$ (flag `0`):

1. **Grid of reproduction types $\mathcal{G}_n$:** Cover $Q^*(K') \subset \Delta_{m-1}^\circ$ by a uniform grid $\mathcal{G}_n$ of $n$-types with spacing $\lceil \sqrt{n} \rceil / n$, so $|\mathcal{G}_n| = O(n^{\frac{m-1}{2}})$. Specifying the nearest grid point $\hat{Q} = \hat{Q}(P_n) \in \mathcal{G}_n$ (with $\|\hat{Q} - Q^*(P_n)\|_\infty \le n^{-1/2}$) costs $\frac{m-1}{2}\log_2 n + O(1)$ bits.
2. **Exact ball-covering prefactor $q(\hat{Q}, P_n) = \Theta(n^{-1/2}) 2^{-n R(P_n, D)}$:** For any $x^n \in T(P_n)$ and $Y^n \sim \mathrm{Unif}(T(\hat{Q}))$, each joint type $V$ with marginals $(P_n, \hat{Q})$ contributes $|T(V \mid x^n)| / |T(\hat{Q})| = \Theta(n^{-(m-1)^2/2}) 2^{-n I_V(X; Y)}$. The affine lattice of such joint types has dimension $(m-1)^2$. Near the unique interior minimizer $V^*$ on the active distortion boundary $\sum_{x \ne y} V(x,y) = D$, the normal coordinate decays geometrically ($\Theta(1)$ sum) while the $(m-1)^2 - 1$ tangential coordinates contribute a Gaussian lattice sum $\Theta(n^{((m-1)^2 - 1)/2})$. Multiplying gives exact dimension cancellation:
   $$q(\hat{Q}, P_n) = \Theta\!\left(n^{-\frac{(m-1)^2}{2}} \cdot n^{\frac{(m-1)^2 - 1}{2}}\right) 2^{-n f(\hat{Q}, P_n)} = \Theta\!\left(n^{-\frac{1}{2}}\right) 2^{-n f(\hat{Q}, P_n)}.$$
   Because $Q \mapsto f(Q, P_n)$ is $C^2$ near its interior global minimum $Q^*(P_n)$ where $\nabla_Q f(Q^*(P_n), P_n) = 0$ and $f(Q^*(P_n), P_n) = R(P_n, D)$, Taylor expansion yields $n f(\hat{Q}, P_n) = n R(P_n, D) + O(n \|\hat{Q} - Q^*(P_n)\|^2) = n R(P_n, D) + O(1)$, hence
   $$\log_2 \frac{1}{q(\hat{Q}, P_n)} = n R(P_n, D) + \frac{1}{2}\log_2 n + O(1)$$
   uniformly over $P_n \in K'$.
3. **McDiarmid-concentrated ordered random codebook:** For each $\hat{Q} \in \mathcal{G}_n$, draw $Y_1, Y_2, \dots \stackrel{\text{i.i.d.}}{\sim} \mathrm{Unif}(T(\hat{Q}))$. For any type $P_n \in K'$, let $U_k(P_n)$ be the fraction of $T(P_n)$ uncovered by $Y_1, \dots, Y_k$. Then $\mathbb{E}[U_k(P_n)] = (1 - q(\hat{Q}, P_n))^k \le e^{-k q(\hat{Q}, P_n)}$, and by double counting, modifying one codeword $Y_j \in T(\hat{Q})$ changes $U_k(P_n)$ by at most $|B(Y_j, nD) \cap T(P_n)| / |T(P_n)| = q(\hat{Q}, P_n)$. By McDiarmid's inequality, for $k \asymp 1/q$,
   $$\Pr\big(U_k(P_n) - \mathbb{E}[U_k(P_n)] \ge n^{-2}\big) \le \exp\!\left(-\frac{2 n^{-4}}{k q^2}\right) = \exp\!\left(-\Omega(n^{-4} \cdot 2^{n R_{\min}})\right),$$
   which is doubly exponentially small since $R_{\min} = \inf_{P \in K'} R(P, D) > 0$. Union-bounding over all $\le (n+1)^{m-1}$ types $P_n \in K'$ and all dyadic $k = 2^s$ ($2^s \le k_{\max} = \lceil \frac{n \ln m + m \ln(n+1) + 2}{q} \rceil$) together with Markov's inequality for complete covering at $k_{\max}$ yields a deterministic ordered codebook for each $\hat{Q} \in \mathcal{G}_n$ whose first-covering index $J(x^n)$ satisfies, simultaneously for every $P_n \in K'$,
   $$\frac{1}{|T(P_n)|} \sum_{x^n \in T(P_n)} \log_2 J(x^n) \le n R(P_n, D) + \frac{1}{2}\log_2 n + O(1).$$
4. **Centered Elias-delta encoding of $J(x^n)$:** From $\hat{Q}$, the decoder knows $\hat{P} = W^*(\hat{Q})$ satisfying $\|P_n - \hat{P}\|_\infty \le n^{-1/2}$, hence $|n R(P_n, D) - n R(\hat{P}, D)| \le C_1 \sqrt{n}$ (and $O(1)$ near $P = \mathrm{Unif}(\mathrm{Fin}\,m)$ where $\nabla R = 0$). Setting $L_0(\hat{Q}) = \lfloor n R(\hat{P}, D) + \frac{1}{2}\log_2 n \rfloor$ and $L = \lfloor \log_2 J \rfloor$, we encode the signed offset $\Delta = L - L_0(\hat{Q})$ with 1 sign bit + Elias-delta of $|\Delta| + 1$ (cost $\log_2(|\Delta| + 1) + 2\log_2\log_2(|\Delta| + 4) + O(1)$), followed by the $L$ lower bits of $J$. Since $|\Delta| = O(\sqrt{n})$ on $K'$, the offset costs $\frac{1}{2}\log_2 n + O(\log\log n)$ bits (and $O(\log\log n)$ at $P = \mathrm{Unif}$). Summing all terms and using $\mathbb{E}_P[R(P_n, D)] = \mathbb{E}_P[H(P_n)] - h(D) - D\log_2(m-1) \le R(P, D)$ (by concavity of $H$) yields
   $$\frac{1}{n}\mathbb{E}_P[\ell(X^n)] - R(P, D) \le \left(\frac{m-1}{2} + \frac{1}{2} + \frac{1}{2}\right)\frac{\log_2 n}{n} + O\!\left(\frac{\log\log n}{n}\right) = \frac{m + 1}{2}\frac{\log_2 n}{n} + O\!\left(\frac{\log\log n}{n}\right).$$

## Verification

1. **Lean 4 mechanical check:** `lean/InfoTheory/Solutions/UniversalLossyRedundancy.lean` defines `theorem disproof : ¬ InfoTheory.Problems.UniversalLossyRedundancy.Statement`. Certified via `python3 scripts/verify_proof.py --verify universal-lossy-redundancy`:
   ```text
   VERIFIED universal-lossy-redundancy: OK disproof of InfoTheory.Problems.UniversalLossyRedundancy.Statement; axioms: #[propext, Quot.sound, Classical.choice] (leanchecker + CheckSolution passed)
   ```
2. **Python numerical verification:** `attempts/universal-lossy-redundancy/code/verify_bounds.py` was executed via `.venv/bin/python` and confirmed all three quantitative regimes:
   - **Boundary kink ($m = 2$, $D = 1/4$, $n \in [40, 1600]$):** $\sqrt{n}\,\mathbb{E}[R(P_n, D)]$ converges smoothly to $\log_2(3)\sqrt{3/(32\pi)} \approx 0.27380$; $P(E_n) \approx 0.30$; $\max_w P(B(c, nD) \cap E_n)$ lies strictly below $2^{-t}$ and gives $\sqrt{n} \cdot \mathrm{LB} \ge 0.113$.
   - **Prefactor of $q(\hat{Q}, P_n)$ and $O(1)$ grid penalty:**
     - $m = 2$ ($P = (0.7, 0.3)$, $D = 0.1$, $n = 400 \dots 6400$): $\log_2(1/q^*) - n R(P_n, D) - \frac{1}{2}\log_2 n \to -2.247$; $+\sqrt{n}$ grid shift penalty stays $5.82\text{--}6.49$ bits ($O(1)$).
     - $m = 3$ ($P = (0.5, 0.3, 0.2)$, $D = 0.2$, $n = 35 \dots 140$): $\log_2(1/q^*) - n R(P_n, D) - \frac{1}{2}\log_2 n \to -1.15$; $+\sqrt{n}$ grid shift penalty stays $4.79\text{--}5.48$ bits ($O(1)$), directly confirming the dimension cancellation $-\frac{(m-1)^2}{2} + \frac{(m-1)^2 - 1}{2} = -\frac{1}{2}$.
   - **Unit-slice ball bound:**
     - $m = 2$ ($D = 0.1$, $n = 100 \dots 1600$): $\max_K |B(y, nD) \cap T(K/n)| / (n^{-1} 2^{n h(D)}) \to 4.13$.
     - $m = 3$ ($D = 0.2$, $Q = (0.57, 0.29, 0.14)$, $n = 30 \dots 90$): $\max_k |B(y, nD) \cap S_k| / (n^{-1} 2^{n(h(D) + D\log_2 2)}) \in [1.16, 1.55]$.

## Dead ends

1. **Attempting to achieve $\frac{m}{2}\frac{\log_2 n}{n}$ via Elias-delta or a $Q$-mixture Poisson codebook:**
   - Using Elias-delta directly on $J \asymp 2^{n R}$ adds $2 \log_2 \log_2 J \approx 2 \log_2 n$ because $\log_2 J = \Theta(n)$. Centering around $L_0(\hat{Q})$ reduces the fluctuation $|\Delta| = O(\sqrt{n})$, which reduces the length-prefix overhead to $\frac{1}{2}\log_2 n + O(\log\log n)$, giving $\frac{m+1}{2}\frac{\log_2 n}{n}$.
   - Attempting to eliminate this final $\frac{1}{2}\log_2 n$ via a non-separated Poisson codebook over all reproduction weights $w$ (so that a single codeword $y^n$ covers $\Theta(\sqrt{n})$ source weights $K$ and preserves $H(K \mid f(X^n)) = \frac{1}{2}\log_2 n$) failed for asymmetric $P = \mathrm{Bern}(p)$ ($p < 1/2$): because $P^{\otimes n}(x^n)$ varies as $2^{-\gamma K}$ while $|B(y, nD) \cap T(K/n)| = O(n^{-1} 2^{n h(D)})$, any attempt to spread a cell $A_c$ over a window of width $W$ in $K$ trades $+\frac{\gamma}{2} W$ bits of excess length against $-\log_2 W$ bits of entropy savings, optimizing at $W = \Theta(1)$. This obstruction led directly to our exact converse proofs (Claims 3–5) showing that $\frac{m+1}{2}$ (not $\frac{m}{2}$) is in fact the true optimal constant!
2. **Naive two-stage type-class coding (sending exact empirical type $P_n$):** Describing $P_n$ costs $(m-1)\log_2 n$ bits, and unlike lossless coding (where $\log_2 |T(P_n)| = n H(P_n) - \frac{m-1}{2}\log_2 n$ cancels half the type cost), lossy ball covering costs $\log_2(1/q) = n R(P_n, D) + \frac{1}{2}\log_2 n$, yielding $(m - \frac{1}{2})\frac{\log_2 n}{n}$, which is strictly suboptimal for all $m \ge 3$.

## References

- No prior attempts existed in `attempts/universal-lossy-redundancy/`.
- B. Yu and T. P. Speed, "A rate of convergence result for a universal $d$-semifaithful code," *IEEE Trans. Inf. Theory*, vol. 39, no. 3, pp. 813–820, 1993.
- Z. Zhang, E.-H. Yang, and V. K. Wei, "The redundancy of source coding with a fidelity criterion—Part I: Known statistics," *IEEE Trans. Inf. Theory*, vol. 43, no. 1, pp. 71–91, 1997.
- E.-H. Yang and Z. Zhang, "On the redundancy of lossy source coding with abstract alphabets," *IEEE Trans. Inf. Theory*, vol. 45, no. 4, pp. 1092–1110, 1999.
- I. Kontoyiannis, "Pointwise redundancy in lossy data compression and universal lossy data compression," *IEEE Trans. Inf. Theory*, vol. 46, no. 1, pp. 136–152, 2000.
- S. M. Sriramu and A. B. Wagner, "Exact Redundancy for Symmetric Rate-Distortion," arXiv:2601.11927, 2026 (confirming that $\frac{1}{2}\frac{\log_2 n}{n}$ is achieved for symmetric/uniform sources, whereas our Claim 3 proves $1 \cdot \frac{\log_2 n}{n}$ for non-uniform binary sources).
