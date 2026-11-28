---
id: sdpi-kl-vs-chisq-equality
title: Equality Conditions Between KL and Chi-Squared Strong Data Processing Constants
status: solved
category: statistical-info-theory
posed_by: Rudolf Ahlswede and Péter Gács; Venkat Anantharam, Amin Gohari, Sudeep Kamath, and Chandra Nair
posed_year: 1976
tags: [strong-data-processing, kl-divergence, chi-squared, hypercontractivity]
lean_module: InfoTheory.Problems.SdpiKlVsChisqEquality
lean_file: lean/InfoTheory/Problems/SdpiKlVsChisqEquality.lean
formal_status: disproved
formal_status_note: "Kernel-checked Lean disproof (Solutions/SdpiKlVsChisqEquality.lean, verify_proof OK): explicit 3-letter reversible channel with s_KL = s_chi2 = 9/100 whose ribbon fails at (1.27, 4)"
---

## Statement

Given a discrete memoryless channel $W : \mathcal{X} \to \mathcal{Y}$ and a full-support input distribution $Q \in \Delta(\mathcal{X})$, define the **input-dependent** Kullback–Leibler and Pearson $\chi^2$ strong data processing inequality (SDPI) constants:
$$
s_{\mathrm{KL}}(Q, W) := \sup_{P \ll Q,\; P \ne Q} \frac{D_{\mathrm{KL}}(PW \mathbin{\|} QW)}{D_{\mathrm{KL}}(P \mathbin{\|} Q)},
\qquad
s_{\chi^2}(Q, W) := \sup_{P \ll Q,\; P \ne Q} \frac{\chi^2(PW \mathbin{\|} QW)}{\chi^2(P \mathbin{\|} Q)} = \rho_m^2(X; Y),
$$
where $\rho_m(X; Y)$ is the Hirschfeld–Gebelein–Rényi maximal correlation of $(X, Y) \sim Q \times W$.

At the **channel** level (taking the supremum over all input distributions $Q$), it is a known theorem that $\eta_{\mathrm{KL}}(W) := \sup_Q s_{\mathrm{KL}}(Q, W) = \sup_Q s_{\chi^2}(Q, W) =: \eta_{\chi^2}(W)$ for every DMC $W$ (Raginsky 2016; Polyanskiy–Wu 2017). At the **input-dependent (bipartite-source)** level, however, $s_{\chi^2}(Q, W) \le s_{\mathrm{KL}}(Q, W)$ always holds and strict inequality is generic (occurring even for the binary symmetric channel with biased input $Q \ne \mathrm{Unif}$, and for the $q$-ary symmetric channel with $q \ge 4$ even at uniform input!).

**Characterize the exact set of bipartite sources $(Q, W)$ for which $s_{\mathrm{KL}}(Q, W) = s_{\chi^2}(Q, W)$ — and specifically resolve the hypercontractivity-extremality question formalized in Lean:**

If a finite full-support bipartite source $(X, Y) \sim Q \times W$ satisfies **two-sided** KL/$\chi^2$ SDPI equality — namely, $s_{\mathrm{KL}}(Q, W) = s_{\chi^2}(Q, W)$ and $s_{\mathrm{KL}}(Q_Y, W^*) = s_{\chi^2}(Q_Y, W^*)$ (where $W^*$ is the reverse channel $Y \to X$) — does its entire hypercontractivity ribbon $\mathcal{R}(P_{XY})$ necessarily coincide with the Bonami–Beckner hyperbola $\frac{p - 1}{q - 1} \ge \rho_m^2(X; Y)$?

**Provenance: catalog formulation (checked 2026-11-27).** The "two-sided equality ⇒
Bonami–Beckner ribbon" implication formalized in Lean was **posed in this catalog**. The
literature does contain its ingredients: $s^* = s_{\mathrm{KL}} \ge \rho_m^2$, the ribbon
characterizations of $s^*$ and $\rho_m^2$, and channel-level equality
$\eta_{\mathrm{KL}} = \eta_{\chi^2}$. We found neither this implication nor an explicit
call to "characterize all $(Q, W)$ with $s_{\mathrm{KL}} = s_{\chi^2}$" posed as an open
problem. We searched:
- the full texts of Anantharam–Gohari–Kamath–Nair (arXiv:1304.6133), whose conclusion only
  asks for "other connections";
- Raginsky (arXiv:1411.3575);
- Polyanskiy–Wu (arXiv:1508.06025);
- Makur–Zheng, "Linear bounds between contraction coefficients for $f$-divergences"
  (arXiv:1510.01844, Problems Inf. Transm. 2020). Its §III "leading questions" and §VII future
  directions concern linear bounds $\eta_{\mathrm{KL}}(P_X, W) \le C\,\eta_{\chi^2}(P_X, W)$,
  their tensorization, and the Gaussian equality case, not an equality characterization;
- web searches.

The `posed_by` field credits the originators of the quantities, not this question. Read the
Lean `Statement` as a catalog conjecture.

**Status warning.** The attempt
`attempts/sdpi-kl-vs-chisq-equality/2026-11-27-antigravity-counterexample.md` claims a
disproof. It uses a 3-state symmetric source with
$s_{\mathrm{KL}} = s_{\chi^2} = 9/100$ on both sides (only `[sketch]`) and an explicit ribbon
violation at $(p, q) = (1.27, 4)$. An independent numerical check on 2026-11-27 reproduced:
- the violation, $+0.002504$ bits;
- the singular values $1, 0.3, 0.2$, so $s_{\chi^2} = 0.09$;
- a grid search giving $\sup_P D(PW\|Q)/D(P\|Q) \approx 0.0900$, attained as $P \to Q$.

So the formalized implication is very likely **false**, pending a kernel-checked `disproof`. The
broader characterization question in the first paragraph above remains a catalog formulation.

## Background

Ahlswede and Gács (1976) initiated the study of strong data processing inequalities by introducing $s^*(X; Y) = \sup_{U - X - Y} \frac{I(U; Y)}{I(U; X)}$ and comparing it against maximal correlation squared $\rho_m^2(X; Y)$. Anantharam, Gohari, Kamath, and Nair (2013) proved the identity $s^*(X; Y) = s_{\mathrm{KL}}(Q, W)$ and demonstrated that $s_{\mathrm{KL}}(Q, W)$ governs the slope of the hypercontractivity ribbon at $(p, q) = (1, 1)$, while $s_{\chi^2}(Q, W) = \rho_m^2(X; Y)$ governs the local second-order (Hessian) behavior at $P = Q$.

Understanding precisely when global KL contraction matches local $\chi^2$ contraction — and how this governs the global shape of the hypercontractivity ribbon — is central to non-asymptotic information theory, Markov chain mixing (log-Sobolev vs. spectral gap), and distributed inference.

## What is known

- **Channel-level equality (solved):** For every DMC $W$, $\eta_{\mathrm{KL}}(W) = \eta_{\chi^2}(W)$ (Cohen–Kemperman–Zbăganu 1998; Raginsky 2016; Polyanskiy–Wu 2017, Theorem 4), proved by applying Cauchy's mean value theorem twice along the mixture segment $P_t = (1-t)Q + tP$.
- **Input-dependent inequality:** Always $s_{\chi^2}(Q, W) \le s_{\mathrm{KL}}(Q, W) \le \eta_{\chi^2}(W)$ (Ahlswede–Gács 1976; Anantharam–Gohari–Kamath–Nair 2013).
- **Binary-input channels:** For any strictly positive binary-input channel $W : \{0, 1\} \to \mathcal{Y}$ (including $\mathrm{BSC}(p)$), $s_{\mathrm{KL}}(Q, W) = s_{\chi^2}(Q, W)$ holds if and only if $Q$ maximizes $Q' \mapsto s_{\chi^2}(Q', W)$ (for $\mathrm{BSC}(p)$, uniquely $Q = \mathrm{Unif}\{0, 1\}$, Ahlswede–Gács 1976).
- **Symmetric $q$-ary channels ($q \ge 4$):** For the $q$-ary symmetric channel $W = (1-\lambda)I + \frac{\lambda}{q} J$ at uniform input $Q = \mathrm{Unif}_q$, $s_{\chi^2}(\mathrm{Unif}_q, W) = (1 - \lambda)^2$, whereas for $q \ge 4$ and $\lambda$ near $1$, $D(e_1 W \| \mathrm{Unif}_q) / D(e_1 \| \mathrm{Unif}_q) \approx \frac{q - 1}{2 \ln q}(1 - \lambda)^2 > (1 - \lambda)^2$, so $s_{\mathrm{KL}}(\mathrm{Unif}_q, W) > s_{\chi^2}(\mathrm{Unif}_q, W)$ (Polyanskiy–Wu 2017).
- **General characterization open:** For general discrete sources $(X, Y)$ with $|\mathcal{X}|, |\mathcal{Y}| \ge 3$, no necessary and sufficient algebraic or structural characterization of $s_{\mathrm{KL}}(Q, W) = s_{\chi^2}(Q, W)$ is known, nor is it known whether two-sided equality $s_{\mathrm{KL}}(X \to Y) = s_{\mathrm{KL}}(Y \to X) = \rho_m^2(X; Y)$ forces the full hypercontractivity ribbon to equal the Bonami–Beckner hyperbola.

## Formal statement and certificate

- **Adversarial check (2026-11-27): Statement is faithful.** The condition `inNairRibbon` is the Carlen–Cordero-Erausquin/Nair dual of `E[f(X)g(Y)] ≤ ‖f‖_p ‖g‖_{q'}`. The hypotheses force full support, so the two SDPI constants are `sSup`s of bounded sets in `[0, 1]`. Ribbon ⊆ hyperbola always holds, so the implication in `Statement` is exactly the "coincides" question. Degenerate cases (`kX = 1`, `p = q`) are true and harmless. A literature search (2026-11) found no resolution, and no source posing it (see **Provenance**).
- **Certificate** `lean/InfoTheory/Known/Certificates/SdpiKlVsChisqEquality.lean` (kernel-checked, standard axioms only) proves:
  - `0 ≤ s_KL ≤ 1` (KL data processing);
  - `χ²` data processing (`chiSq_channel_le`, via Cauchy–Schwarz) and `0 ≤ s_{χ²} ≤ 1`;
  - **regressions:**
    - `s_{χ²}(Unif, BSC(p)) = (1-2p)²`;
    - for the noiseless channel on `Fin k`, both constants equal `1`;
    - for a channel with identical rows, both constants equal `0`;
    - for the noiseless source, the Nair ribbon is exactly `p = q` (the Bonami–Beckner region with `ρ = 1`);
    - the noiseless source satisfies all the hypotheses of `Statement` and its conclusion.
- Not certified: `s_KL(Unif, BSC(p)) = (1-2p)²` for `0 < p < 1/2`, and the general inequality `s_{χ²} ≤ s_KL`.

## References

- R. Ahlswede and P. Gács, "Spreading of sets in product spaces and hypercontraction of the Markov operator," *Ann. Probab.* **4**(6), 925–939 (1976).
- J. E. Cohen, J. H. B. Kemperman, and G. Zbăganu, *Comparisons of Stochastic Matrices with Applications in Information Theory, Statistics, Economics and Population Sciences*, Birkhäuser (1998).
- V. Anantharam, A. Gohari, S. Kamath, and C. Nair, "On maximal correlation, hypercontractivity, and the data processing inequality studied by Erkip and Cover," *arXiv:1304.6133* (2013). (Earlier versions of this file cited arXiv:1304.2333, which is an unrelated paper.)
- C. Nair, "Equivalent formulations of hypercontractivity using information measures," *Proc. Int. Zurich Seminar on Communications (IZS)* (2014).
- M. Raginsky, "Strong data processing inequalities and $\Phi$-Sobolev inequalities for discrete channels," *IEEE Trans. Inf. Theory* **62**(6), 3355–3389 (2016).
- Y. Polyanskiy and Y. Wu, "Strong data-processing inequalities for channels and Bayesian networks," *Convexity and Concentration*, IMA Vol. **161**, Springer, 211–249 (2017).
- A. Makur and L. Zheng, "Linear bounds between contraction coefficients for $f$-divergences," *Problems of Information Transmission* **56**, 103–156 (2020); arXiv:1510.01844.

## Resolution (2026-11-27): formally disproved

The frozen statement (a catalog formulation, see Provenance) is **false**, and the Lean kernel has checked this:
`lean/InfoTheory/Solutions/SdpiKlVsChisqEquality.lean` proves `¬ Statement`, and
`python3 scripts/verify_proof.py --verify sdpi-kl-vs-chisq-equality` reports
`OK disproof … axioms: [propext, Quot.sound, Classical.choice]`.

- **Witness:** the symmetric source Q = (1/4, 1/4, 1/2) with the reversible channel of the antigravity attempt (singular values 1, 3/10, 1/5).
- **Equality hypothesis:** exact, s_KL = s_χ² = 9/100. The global inequality D(PW‖Q) ≤ (9/100)·D(P‖Q) is proved by:
  - a grouping identity;
  - the power series of the symmetric binary divergence;
  - a degree-7 polynomial positivity certificate (exact rational, checked by `linear_combination`).
- **Failed conclusion:** the Bonami–Beckner ribbon fails at (p, q) = (127/100, 4), by about 0.003 bits, with certified log bounds.

Proof notes: `attempts/sdpi-kl-vs-chisq-equality/2026-11-27-claude-known-lean-disproof-feasibility.md`. The LP and exact-rational generator scripts are in `attempts/sdpi-kl-vs-chisq-equality/code/claude-known/`; the proof does not depend on them.
