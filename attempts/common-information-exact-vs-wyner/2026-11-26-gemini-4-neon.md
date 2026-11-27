---
problem: common-information-exact-vs-wyner
date: 2026-11-26
attempter: gemini-4-neon
model: Gemini 4 Neon
type: full-solution-claim
status: verified
---

## Summary

We formally **disprove** the finite-letter attainment statement `InfoTheory.Problems.CommonInformationExactVsWyner.Statement` in Lean 4 (`lean/InfoTheory/Solutions/CommonInformationExactVsWyner.lean`, theorem `disproof`). Taking $P$ to be the Symmetric Binary Erasure Source $\mathrm{SBES}(3/4)$ on $\mathrm{Fin}\,2 \times \mathrm{Fin}\,3$, we prove both:
1. a strict finite-$n$ lower bound $G_1(X^n; Y^n)/n > h(3/4)$ for **every** $n \ge 1$, and
2. an elementary asymptotic upper bound $G(X; Y) \le h(3/4)$.

Hence $G(X; Y) \le h(3/4) < G_1(X^n; Y^n)/n$ for every $n \ge 1$, so the infimum defining $G(X; Y)$ is never attained at any finite blocklength $n \ge 1$. The entire proof is self-contained and kernel-verified in Lean 4 against the frozen statement with only the standard axioms (`propext`, `Quot.sound`, `Classical.choice`).

## Approach

Kumar, Li, and El Gamal (2014) established that for $\mathrm{SBES}(e)$ with $e > 1/2$, the asymptotic exact common information equals Wyner's common information $G(X; Y) = C_W(X; Y) = h(e)$ while the one-shot exact common information satisfies $G_1(X; Y) > h(e)$. However, Wyner's lower bound $G_1(X^n; Y^n)/n \ge C_W(X; Y) = h(e)$ only gives a non-strict inequality for general $n \ge 1$.

To obtain a **strict** separation for every finite $n \ge 1$ on $P = \mathrm{SBES}(3/4)$ ($P(0,0)=P(1,1)=1/8$, $P(0,2)=P(1,2)=3/8$, $P(0,1)=P(1,0)=0$):
- **Finite-$n$ strict lower bound (stability around $0^n$ vs. $2^n$):** Any exact common-randomness coupling $(X^n, Y^n, W)$ with $X^n \perp Y^n \mid W$ obeys the exact identity
  $$H(W) - n h(3/4) = \bigl(n - H(X^n, Y^n \mid W)\bigr) + H(W \mid X^n, Y^n).$$
  Because $X^n \perp Y^n \mid W = w$ and the SBES support forbids $(0,1)$ and $(1,0)$, every atom $w$ satisfies $H(X^n, Y^n \mid W = w) \le n$. Moreover, on the set $A = \{w : Q(W = w) > 0 \wedge Q(0^n, 0^n, w) > 0\}$, conditioning on $W = w$ forces $X^n = 0^n$ almost surely and $\mathrm{supp}(Y^n \mid W = w) \subseteq \{0, 2\}^n$, so the local deficit $n - H(X^n, Y^n \mid W = w)$ equals $D_{\mathrm{KL}}(Q_{Y^n \mid w} \,\|\, \mathrm{Unif}(\{0, 2\}^n))$. Applying Pinsker's inequality and Cauchy–Schwarz forces $Q(W \in A, X^n = 0^n, Y^n = 2^n)$ to be close to $Q(X^n = 0^n, Y^n = 0^n) = (1/8)^n$ whenever $n - H(X^n, Y^n \mid W)$ is small. Because $Q(X^n = 0^n, Y^n = 2^n) = (3/8)^n > (1/8)^n$, this forces the conditional probability $Q(W \in A \mid X^n = 0^n, Y^n = 2^n)$ away from $\{0, 1\}$, which by data processing lower-bounds $H(W \mid X^n, Y^n)$ uniformly away from $0$.
- **Asymptotic upper bound ($G(X; Y) \le h(3/4)$):** Decompose $\mathrm{supp}(P^{\otimes n})$ into constant-erasure shells $S_k$ (exact number $k$ of non-erased coordinates). For $2k \le n$, cover $S_k$ using a deterministic list of $M_k$ product rectangles $A_w \times B_w$ (indexed by $(T, u)$ with $|T| = 2k$), whose existence follows from a one-sided Chernoff / MGF finite-sum argument; place the remaining $\delta / (1 + \delta)$ mass on singleton atoms. For $2k > n$, use singleton atoms (total probability $\le (7/8)^n$ by Markov's inequality on $4^K$). The one-line inequality $\binom{n}{k}(1/4)^k(3/4)^{n-k} \le 1$ immediately yields $\mathbb{E}[\log_2 \binom{n}{K}] \le n h(3/4)$.

### Novelty Check

- **Sources checked:** Web searches on Kumar–Li–El Gamal (2014, arXiv:1402.0062), Yu–Tan (2020, arXiv:1810.13246), and queries for `"exact common information" "symmetric binary erasure" finite blocklength / attainment / G_1(X^n; Y^n)`. Also inspected `problems/common-information-exact-vs-wyner.md` (no prior attempts existed in `attempts/common-information-exact-vs-wyner/`).
- **Assessment:** The asymptotic equality $G(X; Y) = h(e)$ for $\mathrm{SBES}(e)$ with $e > 1/2$ and the one-shot gap $G_1(X; Y) > h(e)$ are known from Kumar–Li–El Gamal (2014). Our literature search did not locate an explicit published proof of strict non-attainment $G_1(X^n; Y^n)/n > h(3/4)$ for *every* finite $n \ge 1$ on $\mathrm{SBES}(3/4)$, nor a prior formalization resolving `InfoTheory.Problems.CommonInformationExactVsWyner.Statement`. Regardless of whether a folklore argument existed for SBES, this resolves the cataloged Lean 4 formal statement completely. Note that the broader informal question in the problem description—whether $G(X; Y)$ admits a computable single-letter formula for arbitrary finite sources—is not addressed by this disproof of finite-letter attainment.

## Claims

1. **[proved]** For $P = \mathrm{SBES}(3/4)$ on $\mathrm{Fin}\,2 \times \mathrm{Fin}\,3$, $H(P) = 1 + h(3/4)$ and $H(P^{\otimes n}) = n(1 + h(3/4))$ for all $n \ge 0$. (`shannonEntropy_sbes`, `shannonEntropy_bipartitePower`)
2. **[proved]** For every $n \ge 1$ and every finite-alphabet coupling $Q$ on $(\mathrm{Fin}\,n \to \mathrm{Fin}\,2) \times (\mathrm{Fin}\,n \to \mathrm{Fin}\,3) \times \mathrm{Fin}\,k_W$ with $(X^n, Y^n)$-marginal $P^{\otimes n}$ and $I(X^n; Y^n \mid W) = 0$, every $w$ with $Q_W(w) > 0$ satisfies $H(X^n, Y^n \mid W = w) \le n$. (`sbes_cond_entropy_le_n`)
3. **[proved]** For every $n \ge 1$, letting $p_0 = (1/8)^n$, $p_e = (3/8)^n$, $m = \min(p_0/2, (p_e - p_0)/2)$, $\varepsilon_0 = m / p_e$, and
   $$c(n) = \min\!\left(\frac{m^2}{2 \ln 2},\; p_e \cdot (-\log_2(1 - \varepsilon_0))\right) > 0,$$
   every feasible finite coupling $Q$ satisfies $H(W) \ge n h(3/4) + c(n)$, and hence $G_1(X^n; Y^n)/n > h(3/4)$. (`sbes_finite_n_strict_lower_bound`)
4. **[proved]** For every $n \ge 1$ and $\delta \in (0, 1/2]$, there exists a finite coupling $(X^n, Y^n, W)$ with marginal $P^{\otimes n}$ and $I(X^n; Y^n \mid W) = 0$ such that
   $$\frac{G_1(X^n; Y^n)}{n} \le h(3/4) + 2\delta + \frac{\log_2(n + 1) + 1 + \log_2\!\bigl(12(2n + 1)(n + 1)/\delta^2\bigr)}{n} + 2\left(\frac{7}{8}\right)^n.$$
   Consequently $G(X; Y) \le h(3/4)$. (`sbes_exactCommonInfoSingle_le`, `sbes_exactCommonInfo_le`)
5. **[proved]** `¬ InfoTheory.Problems.CommonInformationExactVsWyner.Statement`. (`disproof`)

## Details

All proofs are fully formalized in `lean/InfoTheory/Solutions/CommonInformationExactVsWyner.lean`:

1. **Source entropy (Claim 1):** Direct evaluation of `shannonEntropy sbes` using $\log_2(1/8) = \log_2(1/4) - 1$ and $\log_2(3/8) = \log_2(3/4) - 1$ yields $H(\mathrm{SBES}(3/4)) = 1 + h(3/4)$. Induction on $n$ via `Fin.cons` equivalence and `shannonEntropy_prod` gives $H(P^{\otimes n}) = n H(P)$.
2. **Per-atom conditional entropy bound (Claim 2):** By `condMutualInfo_eq_zero_iff`, conditioned on $W = w$ with $Q_W(w) > 0$, the conditional law $R_w$ factors as $R_w = R_{w, X} \times R_{w, Y}$. Define $S_w = \{i \in \mathrm{Fin}\,n : \exists y,\, R_{w, Y}(y) > 0 \wedge y_i \ne 2\}$. Pick any $x_0$ with $R_{w, X}(x_0) > 0$:
   - For every $i \in S_w$ and $x$ with $R_{w, X}(x) > 0$, compatibility with $\mathrm{SBES}$ forces $x_i = (x_0)_i$, so $|\mathrm{supp}(R_{w, X})| \le 2^{n - |S_w|}$ and $H(R_{w, X}) \le n - |S_w|$.
   - For every $y$ with $R_{w, Y}(y) > 0$, $y_i = 2$ for $i \notin S_w$ and $y_i \in \{2, (x_0)_i\}$ for $i \in S_w$, so $|\mathrm{supp}(R_{w, Y})| \le 2^{|S_w|}$ and $H(R_{w, Y}) \le |S_w|$.
   - Summing gives $H(R_w) = H(R_{w, X}) + H(R_{w, Y}) \le n$.
3. **Uniform strict finite-$n$ lower bound (Claim 3):** Let $x_0 = 0^n$, $y_0 = 0^n$, $y_e = 2^n$, and $A = \{w : Q_W(w) > 0 \wedge Q(x_0, y_0, w) > 0\}$. For $w \in A$, $R_{w, Y}(y_0) > 0$ forces $R_{w, X} = \delta_{x_0}$ (so $H(R_{w, X}) = 0$) and $\mathrm{supp}(R_{w, Y}) \subseteq \{0, 2\}^n \cong \mathrm{Fin}\,n \to \mathrm{Bool}$. Since $n \ge 1$, $y_0 \ne y_e$, so by `klDivergence_uniform` and `pinsker_inequality`,
   $$(R_{w, Y}(y_0) - R_{w, Y}(y_e))^2 \le 4\,\mathrm{TV}(R_{w, Y}, \mathrm{Unif}(\{0, 2\}^n))^2 \le 2\ln 2 \cdot (n - H(R_w)).$$
   Summing over $w \in A$ weighted by $Q_W(w)$ and applying Cauchy–Schwarz (`Finset.sum_mul_sq_le_sq_mul_sq`) gives
   $$(p_0 - S_{Ae})^2 \le 2 \ln 2 \cdot \bigl(n - H(X^n, Y^n \mid W)\bigr), \qquad S_{Ae} := \sum_{w \in A} Q(x_0, y_e, w).$$
   - If $|p_0 - S_{Ae}| \ge m$, then $n - H(X^n, Y^n \mid W) \ge m^2 / (2\ln 2) = c_1$.
   - If $|p_0 - S_{Ae}| < m$, then $q := S_{Ae} / p_e \in [\varepsilon_0, 1 - \varepsilon_0]$, and applying data processing (`shannonEntropy_map_le`) to the indicator $\mathbf{1}[W \in A]$ conditioned on $(X^n, Y^n) = (x_0, y_e)$ gives
     $$H(W \mid X^n, Y^n) \ge p_e \cdot h(q) \ge p_e \cdot (-\log_2(1 - \varepsilon_0)) = c_2.$$
   Combined with the identity $H(W) - n h(3/4) = (n - H(X^n, Y^n \mid W)) + H(W \mid X^n, Y^n)$ and nonnegativity of both terms, $H(W) \ge n h(3/4) + \min(c_1, c_2)$. Taking `le_csInf` (after exhibiting a feasible coupling via $W = X^n \times Y^n$) proves $G_1(X^n; Y^n)/n > h(3/4)$.
4. **Asymptotic upper bound (Claim 4):** Partition $\mathrm{supp}(P^{\otimes n})$ into shells $S_k = \{(x, y) : \forall i,\, y_i = 2 \vee y_i = x_i,\; |\{i : y_i \ne 2\}| = k\}$ of size $|S_k| = \binom{n}{k} 2^n$ and shell probabilities $p_{\mathrm{bin}}(n, k) = \binom{n}{k}(1/4)^k(3/4)^{n-k}$.
   - For $2k \le n$, let $W_k = \{(T, u) : |T| = 2k,\; u|_{T^c} = 0\}$ ($|W_k| = \binom{n}{2k} 2^{2k}$) with rectangles $A_w \times B_w \subseteq S_k$ of size $2^{n-2k} \binom{2k}{k}$. Every $(x, y) \in S_k$ belongs to $\binom{n-k}{k}$ rectangles, a fraction $p_k = \binom{2k}{k}/(\binom{n}{k} 2^{2k}) \ge 1 / ((n+1)\binom{n}{k})$.
   - Choosing $M_k = \lceil 6(2n + 1)/(\delta^2 p_k) \rceil$ and $t = \delta/2$, the elementary bound $1 - t \le e^{-t}$ gives $e^t - 1 - t(1 + \delta) \le -\delta^2/6$, so averaging $\exp(t(N(x, y) - (1+\delta) M_k p_k))$ over all $f : \mathrm{Fin}\,M_k \to W_k$ yields a deterministic list covering every $(x, y) \in S_k$ at most $(1+\delta) M_k p_k$ times.
   - Assigning weight $1/((1+\delta)M_k)$ to each $\mathrm{Unif}(A_{f(j)}) \times \mathrm{Unif}(B_{f(j)})$ and the remaining $\delta/(1+\delta)$ mass to singleton atoms reproduces $\mathrm{Unif}(S_k)$ with entropy $\le 1 + \log_2 M_k + 2\delta n$.
   - For $2k > n$, singletons on $S_k$ have entropy $\le 2n$, and $\sum_{2k > n} p_{\mathrm{bin}}(n, k) \le 2^{-n} \sum_{k=0}^n p_{\mathrm{bin}}(n, k) 4^k = (7/8)^n$.
   - Combining shells via `sigmaDist` and `prodMixDist`, and bounding $\log_2 \binom{n}{k} \le -k \log_2(1/4) - (n-k)\log_2(3/4)$ (from $p_{\mathrm{bin}}(n, k) \le 1$) yields $\mathbb{E}[\log_2 \binom{n}{K}] \le n h(3/4)$. Sending $n \to \infty$ and $\delta \to 0$ gives $G(X; Y) \le h(3/4)$.
5. **Disproof (Claim 5):** Instantiating `Statement` at $k_X = 2$, $k_Y = 3$, $P = \mathrm{SBES}(3/4)$ yields $n > 0$ with $G(X; Y) = G_1(X^n; Y^n)/n$, contradicting Claims 3 and 4.

## Verification

Verified on 2026-11-26 using the repository's two-gate Lean 4 verification harness (`lake build` + `leanchecker` kernel replay + `CheckSolution.lean` with `trustLevel := 0`) and lockfile integrity check:

```text
$ export PATH="$HOME/.elan/bin:$PATH" && python3 scripts/verify_proof.py --verify common-information-exact-vs-wyner && python3 scripts/verify_proof.py --check-lock
VERIFIED common-information-exact-vs-wyner: OK disproof of InfoTheory.Problems.CommonInformationExactVsWyner.Statement; axioms: #[propext, Quot.sound, Classical.choice] (leanchecker + CheckSolution passed)
STATEMENT LOCK CHECK PASSED: 127 frozen files match SHA-256 hashes.
```

### Referee Audit (2026-11-27)
Independently audited by a fresh-context referee agent (Gemini 4 Neon): re-ran `verify_proof.py --verify common-information-exact-vs-wyner`, `leanchecker`, `CheckSolution`, and `--check-lock` (all passed, standard axioms only), confirmed zero modeling loopholes in `bipartitePower`/`exactCommonInfoSingle`/`Statement` (the finite-$n$ gap $c(n) > 0$ is independent of $k_W$ and extends to countable $W$), verified all 5 claims against their Lean theorems, and corrected the inherited arXiv ID typo for Yu–Tan (2020) from `arXiv:1810.00807` to `arXiv:1810.13246`. Status moved to `verified`.

## Dead ends

- **Direct Wyner-bound comparison:** The inequality $G_1(X^n; Y^n) \ge n C_W(X; Y) = n h(3/4)$ is non-strict and cannot by itself rule out finite-$n$ attainment. Establishing strictness required the quantitative stability bound (Pinsker's inequality + Cauchy–Schwarz on the event $A$) linking the conditional entropy deficit $n - H(X^n, Y^n \mid W)$ to the conditional entropy $H(W \mid X^n, Y^n)$ at $(0^n, 2^n)$.
- **Two-sided Chernoff covering:** A two-sided concentration bound requiring both $(1 - \delta) \mu \le N(x, y) \le (1 + \delta) \mu$ is unnecessary; the one-sided upper tail $N(x, y) \le (1 + \delta) \mu$ already guarantees nonnegative residual mass summing to exactly $\delta / (1 + \delta)$ on singleton atoms, significantly simplifying the formal proof.

## References

- Prior attempts consulted: none (no files in `attempts/common-information-exact-vs-wyner/`).
- Problem specification: `problems/common-information-exact-vs-wyner.md`, `lean/InfoTheory/Problems/CommonInformationExactVsWyner.lean`.
- Formal solution: `lean/InfoTheory/Solutions/CommonInformationExactVsWyner.lean`.
- G. R. Kumar, C. T. Li, and A. El Gamal, "Exact common information," Proc. IEEE ISIT, 2014; arXiv:1402.0062.
- L. Yu and V. Y. F. Tan, "Exact channel synthesis," IEEE Trans. Inf. Theory, 2020; arXiv:1810.13246.
- A. D. Wyner, "The common information of two dependent random variables," IEEE Trans. Inf. Theory, 1975.
