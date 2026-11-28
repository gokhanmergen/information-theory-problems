---
id: ldp-minimax-kl-sharp
title: Sharp Asymptotic Minimax KL Risk for Locally Differentially Private Distribution Estimation
status: open
category: security-privacy
posed_by: John C. Duchi, Michael I. Jordan, and Martin J. Wainwright
posed_year: 2013
tags: [local-differential-privacy, minimax-risk, kl-divergence, distribution-estimation]
lean_module: InfoTheory.Problems.LdpMinimaxKlSharp
lean_file: lean/InfoTheory/Problems/LdpMinimaxKlSharp.lean
---

## Statement

Consider estimating an unknown discrete probability distribution $P \in \Delta_k$ on $[k] = \{1, \dots, k\}$ from $n$ i.i.d. samples $X_1, \dots, X_n \sim P$ passed through a non-interactive **$\varepsilon$-locally differentially private ($\varepsilon$-LDP)** channel $Q : [k] \to \mathcal{Y}$, meaning
$$
Q(y \mid x) \le e^\varepsilon \, Q(y \mid x') \qquad \text{for all } x, x' \in [k], \; y \in \mathcal{Y}.
$$
Let $R_{\mathrm{KL}}^{\mathrm{LDP}}(k, n, \varepsilon)$ denote the minimax expected Kullback–Leibler risk
$$
R_{\mathrm{KL}}^{\mathrm{LDP}}(k, n, \varepsilon) := \inf_{Q \in \mathcal{Q}_\varepsilon} \inf_{\hat{P}} \sup_{P \in \Delta_k} \mathbb{E}_{Y^n \sim (QP)^{\otimes n}} \big[ D_{\mathrm{KL}}(P \mathbin{\|} \hat{P}(Y^n)) \big].
$$

**Determine the exact asymptotic leading constant of $R_{\mathrm{KL}}^{\mathrm{LDP}}(k, n, \varepsilon)$ across all regimes of $(k, n, \varepsilon)$, and characterize the exact asymptotically minimax-optimal $\varepsilon$-LDP mechanism $Q$.**

In particular, the accompanying Lean statement formalizes whether the **Subset Selection** family of $\varepsilon$-LDP mechanisms (which outputs a uniform $s$-subset $S \subset [k]$ containing $x$ with probability proportional to $e^\varepsilon$ and not containing $x$ with probability proportional to $1$, interpolating between $k$-ary Randomized Response at $s = 1$ and RAPPOR-like half-subsets at $s = \lfloor k/2 \rfloor$) achieves the **exact** asymptotic minimax KL risk (with multiplicative factor $1 + o(1)$ as $n \to \infty$) for every $k \ge 2$ and $\varepsilon > 0$.

**Provenance: catalog formulation (checked 2026-11-27).** The Subset Selection question
(and the "exact KL constant" question above it) was **posed in this catalog**, motivated by
Ye–Barg (2018), who proved exact asymptotic optimality of Subset Selection for the
$\ell_2^2$ loss in some regimes, and by Duchi–Jordan–Wainwright (2013/2018). We found it stated
nowhere in the literature. We searched:
- the full texts of Duchi–Jordan–Wainwright (arXiv:1305.6000, NeurIPS 2013 probability-estimation paper), Kairouz–Bonawitz–Ramage
  (arXiv:1602.07387, whose only forward-looking remarks concern nonstationary distributions) and
  Ye–Barg (arXiv:1702.00610, which uses KL only as a proof device in its lower bounds);
- recent KL-loss work under privacy: Sima et al., AISTATS 2024 (arXiv:2402.00315, online KL
  risk under LDP, whose open remark concerns pure versus approximate LDP), and the
  instance-optimal KL estimation paper arXiv:2505.23620 (central DP);
- web searches for "KL divergence", "locally differentially private", "distribution estimation",
  "minimax", combined with "open"/"conjecture".

None poses exact $(1+o(1))$-minimaxity of Subset Selection, or of any mechanism, under KL loss.
The `posed_by` field credits the LDP minimax framework, not this specific question. Read the
Lean `Statement` as a precise catalog conjecture, not a literature problem.

## Background

Local differential privacy eliminates the need for a trusted data curator by privatizing each user's observation before collection. Duchi, Jordan, and Wainwright (2013, 2018) initiated the minimax statistical theory of LDP, establishing order-optimal rates for discrete distribution estimation under $\ell_1$, $\ell_2^2$, and related losses via strong data-processing and Assouad inequalities.

Under KL divergence loss $D_{\mathrm{KL}}(P \mathbin{\|} \hat{P})$, local privacy causes a dramatic qualitative change compared to non-private estimation: whereas non-private minimax KL risk decays as $\frac{k-1}{2n}$ for fixed $k$, under $\varepsilon$-LDP boundary distributions (where $P(x) \approx 0$ is masked by constant-rate privacy noise) force the minimax KL risk to decay only as $\Theta(1/\sqrt{n})$! Determining the exact minimax constant and exact optimal privacy mechanism under KL loss across all privacy levels $\varepsilon$ and alphabet sizes $k$ remains open.

## What is known

- **Binary alphabet ($k = 2$):** Kairouz, Oh, and Viswanath (2016) proved that binary Randomized Response ($s = 1$) Blackwell-dominates all other $\varepsilon$-LDP channels for $k = 2$, hence is universally optimal for every convex loss including KL divergence; however, even for $k = 2$ the exact asymptotic constant $\lim_{n \to \infty} \sqrt{n} \, R_{\mathrm{KL}}^{\mathrm{LDP}}(2, n, \varepsilon)$ is not known in closed form.
- **Order-optimal rates for $\ell_2^2$ and $\ell_1$ losses:** Duchi–Jordan–Wainwright (2013, 2018), Kairouz–Bonawitz–Ramage (2016), Ye–Barg (2018), and Acharya–Sun–Zhang (2019) established tight order-optimal minimax rates across all privacy regimes ($\varepsilon \lesssim 1$, $1 \lesssim \varepsilon \lesssim \log k$, $\varepsilon \gtrsim \log k$): $\Theta\big(\frac{k}{n (e^\varepsilon - 1)^2}\big)$ for $\ell_2^2$ (for small $\varepsilon$) and $\Theta\big(\frac{k}{\sqrt{n}(e^\varepsilon - 1)}\big)$ for $\ell_1$.
- **Exact optimality of Subset Selection under $\ell_2^2$ risk:** Ye and Barg (2018) proved that Subset Selection with optimal subset size $s \approx \lceil k / (e^\varepsilon + 1) \rceil$ achieves order-optimal $\ell_2^2$ and $\ell_1$ risks across all regimes and exact asymptotic optimality for $\ell_2^2$ risk in specific regimes; Wang, Blocki, Li, and Jha (2017) analyzed exact variance tradeoffs across mechanisms.
- **KL risk and exact constants remain open:** Neither the exact asymptotic constant of $R_{\mathrm{KL}}^{\mathrm{LDP}}(k, n, \varepsilon)$ nor exact $(1 + o(1))$-minimax optimality of Subset Selection under KL loss is proved for general $k \ge 3$ and $\varepsilon > 0$.

## Formal statement and certificate

Adversarial audit (2026-11-27): the Lean `Statement` matches the slice described above, and no junk
value was found: both minimax risks are infima over non-empty sets bounded below, lying in
`[0, log₂ k]`, and estimators must have full support. Two caveats:

- **No literature source** (see **Provenance** above). "Subset Selection is exactly
  `(1+o(1))`-minimax under KL for every `k, ε`" is this catalog's own formulation. Ye–Barg (2018) proved exact optimality for the
  $\ell_2^2$ loss in some regimes; no cited paper conjectures it for KL. Because the KL risk under LDP is
  dominated by distributions near the boundary ($\Theta(n^{-1/2})$), the $\ell_2^2$/Fisher-information
  heuristics behind SS do not obviously carry over.
- **The `k = 2` slice is a known theorem** (Kairouz–Oh–Viswanath 2016: binary randomized response
  Blackwell-dominates every `ε`-LDP channel; averaging the estimator is allowed because KL is
  convex in its second argument). The open content is `k ≥ 3`.

Certificate `lean/InfoTheory/Known/Certificates/LdpMinimaxKlSharp.lean` proves the following:
- `k`-ary randomized response is a Subset Selection channel.
- Every SS channel is `ε`-LDP, so `ldpMinimaxKLRisk ≤ subsetSelectionMinimaxKLRisk`.
- Both risks lie in `[0, log₂ k]`.

## References

- J. C. Duchi, M. I. Jordan, and M. J. Wainwright, "Local privacy and statistical minimax rates," *Proc. 54th IEEE FOCS*, 429–438 (2013); full version *J. Amer. Statist. Assoc.* **113**(521), 182–201 (2018).
- P. Kairouz, S. Oh, and P. Viswanath, "Extremal mechanisms for local differential privacy," *J. Mach. Learn. Res.* **17**(17), 1–51 (2016).
- P. Kairouz, K. Bonawitz, and D. Ramage, "Discrete distribution estimation under local privacy," *Proc. 33rd ICML*, 2436–2444 (2016).
- M. Ye and A. Barg, "Optimal schemes for discrete distribution estimation under locally differential privacy," *IEEE Trans. Inf. Theory* **64**(8), 5662–5676 (2018).
- J. Acharya, Z. Sun, and H. Zhang, "Hadamard response: Estimating distributions privately, efficiently, and with little communication," *Proc. AISTATS*, 1120–1129 (2019).
