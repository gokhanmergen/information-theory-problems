---
id: zero-error-broadcast-channel
title: Zero-Error Broadcasting over the Pentagon: Is the Free-Lunch Point of C₅ Positive?
status: open
category: zero-error
posed_by: Sihuang Hu, Ofer Shayevitz
posed_year: 2017
tags: [zero-error, broadcast-channel, graph-capacity, rho-capacity, pentagon, shannon-capacity]
lean_module: InfoTheory.Problems.ZeroErrorBroadcastChannel
lean_file: lean/InfoTheory/Problems/ZeroErrorBroadcastChannel.lean
---

> **Statement-fix (2026-11-27).** This entry used to ask whether the zero-error *feedback sum
> capacity* of a general two-receiver broadcast channel is computable by a register machine
> to precision $1/m$. No source poses that question. The cited references (Körner–Orlitsky
> 1998; Shayevitz–Wigger 2013) do not discuss it, and two independent provenance checks and
> a web search found no other source. It was a catalog invention. The entry now asks a
> zero-error broadcast question that the literature states as open: an instance of
> Hu–Shayevitz (2017), Problems 1(ii) and 2.

## Statement

A two-receiver zero-error broadcast channel with private messages is described by a pair of
confusability graphs $(G_1, G_2)$ on the input alphabet. Its zero-error capacity region
$\mathcal{C}(G_1, G_2)$ is the closure of the set of rate pairs
$(\tfrac1n\log M_1, \tfrac1n\log M_2)$ of codes in which receiver $i$ recovers its message
$w_i$ with certainty. Let receiver 1 be noiseless ($G_1 = \overline{K}_m$, the empty graph)
and let receiver 2 have confusability graph $G$. Hu and Shayevitz define the
**ρ-capacity**
$$C_\rho(G) = \sup\{R : (\rho, R) \in \mathcal{C}(\overline{K}_m, G)\}
= \lim_{n\to\infty} \tfrac1n \log \alpha_{2^{\rho n}}(G^{\boxtimes n}),$$
where $\alpha_k$ is the largest number of pairwise non-adjacent disjoint vertex subsets, each
of size at least $k$. $C_\rho(G)$ is concave and non-increasing in $\rho$, and
$C_0(G) = \log \Theta(G)$. The **free-lunch point** $\rho^*(G)$ is the largest $\rho$ with
$C_\rho(G) = C_0(G)$. Up to that point the noiseless receiver gets rate $\rho$ at no cost to
the noisy receiver.

**Question.** For the pentagon $G = C_5$, is $\rho^*(C_5) > 0$? Equivalently, is there a
$\rho > 0$ such that $(\rho, \tfrac12 \log_2 5) \in \mathcal{C}(\overline{K}_5, C_5)$? Here
$\tfrac12 \log_2 5 = \log_2 \Theta(C_5)$ by Lovász (1979).

Hu–Shayevitz (2017) state the relevant open problems verbatim:

- "Find the ρ-capacity of the Pentagon $C_5$" (Problem 1(ii));
- "Characterize the free-lunch point $\rho^*(G)$. Specifically, give a necessary and
  sufficient condition for $\rho^*(G) > 0$" (Problem 2).

## Background

Shannon's pentagon code $\{(i, 2i \bmod 5)\}$ achieves $\Theta(C_5) = \sqrt5$, and Lovász's
$\vartheta$ shows this is optimal. In the broadcast setting the question is whether the
optimal $C_5$-codes have enough slack to carry an extra private stream of positive rate to a
second, noiseless receiver. This requires grouping codewords into clusters: codewords with
different $w_2$ must be distinguishable in $C_5^{\boxtimes n}$, while codewords with the
same $w_2$ only need to be distinct. The number of clusters must stay at $5^{n/2 - o(n)}$
while each cluster has size $2^{\rho n}$.

## What is known

- **Shape of $C_\rho$** (Hu–Shayevitz 2017, Prop. 4–5): concave and non-increasing, with
  $\frac{C(G)}{\log m}(\log m - \rho) \le C_\rho(G) \le \min\{C(G), \log m - \rho\}$.
- **Disjoint unions of cliques**: $C_\rho$ is determined exactly. For these graphs the
  free-lunch point equals the packing point iff $G = sK_n$ (Theorems 3, 10, 11).
- **A free lunch can exist**: the pentagon with one extra edge has $\rho^* \ge 1/2$
  (Example 4). For $C_5$ itself, Example 6 gives only bounds. The Lovász-type bound for
  regular graphs (Theorem 4) applies only for $\rho$ in roughly $(0.58, 1.55)$ bits and does
  not decide whether $\rho^*(C_5) > 0$.
- Single-letter: $\alpha_2(C_5) = 1$ (Example 6).
- No later work that settles $\rho^*(C_5)$ was found (searched 2026-11-27).

## Formal statement (Lean)

`InfoTheory.Problems.ZeroErrorBroadcastChannel.Statement` imports only `InfoTheory.Core`:

- `Distinguishable n x y := x ≠ y ∧ ¬ (strongPower (cycleGraph 5) n).Adj x y`. Two words of
  `ZMod 5` letters can never produce a common output at the $C_5$ receiver.
- `IsPentagonBroadcastCode n M₁ M₂ enc`, for `enc : Fin M₁ → Fin M₂ → (Fin n → ZMod 5)`:
  equal codewords force equal `w₁` (noiseless receiver), and codewords with different `w₂`
  are `Distinguishable`.
- `InPentagonRegion R₁ R₂`: for every `δ > 0` there is a code with `0 < n`, `0 < M₁`,
  `0 < M₂`, `(R₁ - δ) n ≤ log₂ M₁` and `(R₂ - δ) n ≤ log₂ M₂`. This is the closed region
  $\mathcal{C}(\overline K_5, C_5)$, written without `sSup` or limits. The nonempty message
  sets rule out vacuous codes.
- `Statement := ∃ ρ : ℝ, 0 < ρ ∧ InPentagonRegion ρ (log2 5 / 2)`.

**Certificate** (`lean/InfoTheory/Known/Certificates/ZeroErrorBroadcastChannel.lean`):

- At `ρ = 0` the condition holds, by Shannon's `(2, 1, 5)` code (`decide`). The question is
  therefore exactly whether $\rho^* > 0$.
- The corner `(log₂ 5, 0)` is achievable.
- Every code has `M₂ ≤ α(C₅^{⊠n}) ≤ √5ⁿ`, so every point of the region has
  `R₂ ≤ ½ log₂ 5`. The $C_5$ receiver alone sees exactly the single-user problem.
- Every code has `M₁ M₂ ≤ 5ⁿ`, so any witness has `ρ ≤ ½ log₂ 5`.

## References

- S. Hu and O. Shayevitz, "The ρ-capacity of a graph," *IEEE Trans. Inf. Theory* 63(4),
  2017; arXiv:1607.07263.
- C. E. Shannon, "The zero error capacity of a noisy channel," *IRE Trans. Inf. Theory*, 1956.
- L. Lovász, "On the Shannon capacity of a graph," *IEEE Trans. Inf. Theory* 25(1), 1979.
- J. Körner and A. Orlitsky, "Zero-error information theory," *IEEE Trans. Inf. Theory*
  44(6), 1998.
- L. Gargano, J. Körner and U. Vaccaro, "Capacities: from information theory to extremal set
  theory," *J. Combin. Theory Ser. A* 68, 1994.
- Q. Cao, Z. Wu, G. Niu and Y. Geng, "Zero-error capacity of broadcast channels with two
  binary outputs," *Proc. IEEE ITW*, 2024.
