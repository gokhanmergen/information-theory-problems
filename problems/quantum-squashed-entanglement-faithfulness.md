---
id: quantum-squashed-entanglement-faithfulness
title: Optimal Dimension Dependence for Faithfulness of Squashed Entanglement
status: open
category: quantum-info
posed_by: Fernando G. S. L. Brandão, Matthias Christandl, and Jon Yard
posed_year: 2011
tags: [quantum-information, squashed-entanglement, faithfulness, separability]
lean_module: InfoTheory.Problems.QuantumSquashedEntanglementFaithfulness
lean_file: lean/InfoTheory/Problems/QuantumSquashedEntanglementFaithfulness.lean
---

## Statement

For a bipartite quantum state $\rho_{AB} \in \mathcal{D}(\mathbb{C}^{d_A} \otimes \mathbb{C}^{d_B})$, the **squashed entanglement** (Christandl–Winter 2004) is defined by
$$
E_{\mathrm{sq}}(\rho_{AB}) := \frac{1}{2} \inf_{\rho_{ABE}} I(A; B \mid E)_\rho,
$$
where the infimum ranges over all finite-dimensional extensions $\rho_{ABE}$ with $\operatorname{Tr}_E \rho_{ABE} = \rho_{AB}$. Let
$$
\operatorname{dist}_1(\rho_{AB}, \mathrm{SEP}) := \inf_{\sigma_{AB} \in \mathrm{SEP}} \frac{1}{2} \|\rho_{AB} - \sigma_{AB}\|_1
$$
denote the trace distance from $\rho_{AB}$ to the set $\mathrm{SEP}$ of separable bipartite states.

**Determine the optimal dimension dependence in the faithfulness lower bound for squashed entanglement in trace distance.** Specifically, determine the smallest exponent $\alpha \ge 1$ for which there exists a universal constant $c > 0$ such that
$$
E_{\mathrm{sq}}(\rho_{AB}) \ge \frac{c}{\min(d_A, d_B)^\alpha} \, \operatorname{dist}_1(\rho_{AB}, \mathrm{SEP})^2
$$
holds for all $d_A, d_B \ge 1$ and all bipartite states $\rho_{AB}$. The accompanying Lean statement formalizes the sharp conjectured exponent $\alpha = 1$, matching the scaling of the $d \times d$ antisymmetric state.

## Background

Squashed entanglement is one of the most well-behaved entanglement measures known: it is convex, additive on tensor products, monotone under LOCC, asymptotically continuous, and sandwiched between distillable entanglement and entanglement cost ($E_D \le E_{\mathrm{sq}} \le E_C$). A key foundational question was whether $E_{\mathrm{sq}}$ is *faithful* — i.e., whether $E_{\mathrm{sq}}(\rho_{AB}) = 0$ implies that $\rho_{AB}$ is separable.

Brandão, Christandl, and Yard (2011) resolved faithfulness in the affirmative via a breakthrough quantum de Finetti theorem, establishing a quantitative lower bound in terms of the one-way LOCC norm. However, converting from the one-way LOCC norm to the standard trace distance introduces a polynomial dimension penalty, and closing the gap between the known upper and lower bounds in dimension remains open.

## What is known

- **Dimension-independent lower bound in the $\mathrm{LOCC}_1$ norm:** Brandão, Christandl, and Yard (2011) proved
  $$
  E_{\mathrm{sq}}(\rho_{AB}) \ge \frac{1}{16 \ln 2} \, \inf_{\sigma \in \mathrm{SEP}} \|\rho_{AB} - \sigma\|_{\mathrm{LOCC}_1}^2
  $$
  (later tightened in constant by Li and Winter 2014/2018 to $\frac{1}{4 \ln 2}$ via relative entropy and quantum recovery maps).
- **Trace-distance lower bound ($\alpha = 2$):** Using the comparison $\|\Delta\|_{\mathrm{LOCC}_1} \ge \frac{c_0}{\min(d_A, d_B)} \|\Delta\|_1$ (Matthews–Wehner–Winter 2009; Lancien–Winter 2013), the BCY/Li–Winter bound yields
  $$
  E_{\mathrm{sq}}(\rho_{AB}) \ge \frac{c}{\min(d_A, d_B)^2} \, \operatorname{dist}_1(\rho_{AB}, \mathrm{SEP})^2.
  $$
- **No dimension-independent trace-distance bound ($\alpha \ge 1$ required):** Christandl, Schuch, and Winter (2012) showed that the $d \times d$ antisymmetric state $\alpha_d$ satisfies $E_{\mathrm{sq}}(\alpha_d) = O(1/d)$ while $\operatorname{dist}_1(\alpha_d, \mathrm{SEP}) \ge 1/2$, ruling out any universal bound with $\alpha < 1$.
- **Open gap ($\alpha \in [1, 2]$):** Whether the true optimal trace-distance scaling is $\alpha = 1$ (matching the antisymmetric state, i.e. $E_{\mathrm{sq}}(\rho_{AB}) \ge \frac{c}{\min(d_A, d_B)} \operatorname{dist}_1(\rho_{AB}, \mathrm{SEP})^2$), or whether there exist states with $E_{\mathrm{sq}}(\rho_{AB}) = o(1/d)$ and constant trace distance to $\mathrm{SEP}$, remains open.

## Formal statement and certificate

The Lean `Statement` asks for the sharp exponent `α = 1` (a universal `c > 0` and, for each `ρ`, a separable `σ` with `(c / min(d_A, d_B)) · T(ρ, σ)² ≤ E_sq(ρ)`). It does **not** ask for qualitative faithfulness, which is the Brandão–Christandl–Yard theorem. Adversarial re-check (2026-11-27): the marginals inside `squashedEntanglement` were checked index by index; the existential `σ` matches `dist₁(ρ, SEP)` because SEP is compact; still open. The certificate `InfoTheory.Known.Certificates.QuantumSquashedEntanglementFaithfulness` proves `kron_isSeparable` (product states are separable), `traceDistance_self`, `traceDistance_nonneg`, `matEntropy_cast`, `cmi_dim_one`, and `squashedEntanglement_dim_one` (`E_sq = 0` on `ℂ¹ ⊗ ℂ¹`, which checks the index juggling and rules out `sInf` junk).

## References

- M. Christandl and A. Winter, "'Squashed entanglement': An additive entanglement measure," *J. Math. Phys.* **45**, 829–840 (2004).
- W. Matthews, S. Wehner, and A. Winter, "Distinguishability of quantum states under restricted families of measurements with an application to quantum data hiding," *Commun. Math. Phys.* **291**, 813–843 (2009).
- F. G. S. L. Brandão, M. Christandl, and J. Yard, "Faithful squashed entanglement," *Commun. Math. Phys.* **306**, 805–830 (2011).
- M. Christandl, N. Schuch, and A. Winter, "Entanglement of the antisymmetric state," *Commun. Math. Phys.* **311**, 397–422 (2012).
- K. Li and A. Winter, "Relative entropy and squashed entanglement," *Commun. Math. Phys.* **326**, 63–80 (2014).
- K. Li and A. Winter, "Squashed entanglement, $k$-extendibility, quantum Markov chains, and recovery maps," *Found. Phys.* **48**, 910–924 (2018).
