---
id: log-sobolev-hypercube-sharp
title: The Fourier Entropy–Influence Conjecture on the Boolean Hypercube
status: open
category: entropy-inequalities
posed_by: Michel Talagrand; Ehud Friedgut and Gil Kalai
posed_year: 1996
tags: [entropy-inequalities, boolean-functions, discrete-fourier, log-sobolev, hypercube]
lean_module: InfoTheory.Problems.LogSobolevHypercubeSharp
lean_file: lean/InfoTheory/Problems/LogSobolevHypercubeSharp.lean
---

## Statement

For a Boolean function $f : \{0,1\}^n \to \{-1, 1\}$, its Walsh–Fourier expansion is
$$f(x) = \sum_{S \subseteq [n]} \hat{f}(S) \chi_S(x), \qquad \chi_S(x) = \prod_{i \in S} (-1)^{x_i}, \qquad \hat{f}(S) = \frac{1}{2^n} \sum_{x \in \{0,1\}^n} f(x) \chi_S(x).$$
By Parseval's identity, $\sum_{S \subseteq [n]} \hat{f}(S)^2 = 1$, so the squared Fourier coefficients $\{\hat{f}(S)^2\}_{S \subseteq [n]}$ form a probability distribution on $2^{[n]}$. Define the **Fourier entropy** of $f$ as the Shannon entropy of its spectral distribution (in bits),
$$H(\hat{f}^2) := -\sum_{S \subseteq [n]} \hat{f}(S)^2 \log_2 \hat{f}(S)^2,$$
and the **total influence** (average sensitivity) of $f$ as
$$\mathbf{I}(f) := \sum_{i=1}^n \mathrm{Inf}_i(f) = \sum_{S \subseteq [n]} |S|\, \hat{f}(S)^2.$$

**Conjecture (Fourier Entropy–Influence Conjecture; Friedgut–Kalai, 1996).** There exists a universal constant $C > 0$, independent of $n$, such that for every $n \ge 1$ and every Boolean function $f : \{0,1\}^n \to \{-1, 1\}$,
$$H(\hat{f}^2) \;\le\; C \cdot \mathbf{I}(f).$$

## Background

The interplay between entropy, variance, and influence on the Boolean hypercube $\{0,1\}^n$ is governed by logarithmic Sobolev inequalities (Gross 1975; Bonami–Beckner hypercontractivity) and Talagrand's (1994) sharp $L^1$–$L^2$ and variance–influence inequalities. While the classical hypercube log-Sobolev inequality bounds the *physical-space* entropy $\mathrm{Ent}(f^2)$ by the Dirichlet energy (total influence), the **Fourier Entropy–Influence (FEI) Conjecture** of Friedgut and Kalai (1996) asks for the *dual* statement in Fourier space: the Shannon entropy of the spectral weights $\hat{f}(S)^2$ is at most a constant multiple of the average Fourier degree $\mathbf{I}(f)$.

The FEI conjecture is one of the central open problems in the analysis of Boolean functions and theoretical computer science. It implies the Mansour conjecture on sparse Fourier approximations of DNFs, strengthens the Kahn–Kalai–Linial (KKL) and Friedgut junta theorems, and is intimately connected to Talagrand's sharp boundary-influence inequalities on the cube.

## What is known

- **Talagrand's variance and boundary-influence inequalities (Talagrand, 1994, 1997; Eldan–Gross, 2022):** Talagrand established the sharp $L^1$–$L^2$ inequality $\mathrm{Var}(f) \le C \sum_i \frac{\mathrm{Inf}_i(f)}{1 + \log(1/\mathrm{Inf}_i(f))}$ and posed his boundary-influence conjecture $\mathbb{E}[\sqrt{h_f}] \ge c\,\mathrm{Var}(f)\sqrt{\log(1/\sum_i \mathrm{Inf}_i(f)^2)}$, which was resolved by Eldan and Gross (2022) via pathwise stochastic calculus on the hypercube. The FEI conjecture remains open.
- **Min-entropy version (Kahn–Kalai–Linial / Friedgut–Kalai):** The weaker Fourier *min-entropy*–influence inequality $H_\infty(\hat{f}^2) \le C\,\mathbf{I}(f)$ is also open in general, though implied by FEI.
- **General upper bounds:** Using elementary bounds on the entropy of a distribution with fixed mean $\mathbf{I}(f)$ on $2^{[n]}$, one trivially has $H(\hat{f}^2) \le \mathbf{I}(f) \log_2 n + O(\mathbf{I}(f))$; removing the $\log n$ factor in full generality remains open.
- **Resolved special classes:** FEI holds with explicit constants for symmetric Boolean functions, read-once formulas, random DNFs, linear threshold functions (up to $\log \mathbf{I}(f)$ or for regular LTFs), monotone functions with small influence, and functions computed by small decision trees (O'Donnell–Wright–Zhou 2011; Wan–Wright–Wu 2014; Chakraborty et al. 2016; Kelman–Kindler–Lifshitz–Minzer–Safra 2020).
- **Lower bounds on the optimal constant $C$:** For the 2-bit $\mathrm{AND}$ function, $H(\hat{f}^2)/\mathbf{I}(f) = 2$. Via iterated compositions and recursive threshold functions, Hod (2018) proved that any universal constant must satisfy $C \ge 6.278\dots$ (improving earlier bounds of O'Donnell–Tan).

## References

- E. Friedgut and G. Kalai, "Every monotone graph property has a sharp threshold," *Proc. Amer. Math. Soc.*, 124(10):2993–3002, 1996.
- M. Talagrand, "On Russo's approximate zero-one law," *Ann. Probab.*, 22(3):1576–1587, 1994.
- M. Talagrand, "On boundaries and influences," *Combinatorica*, 17(2):275–285, 1997.
- R. Eldan and R. Gross, "Concentration on the Boolean hypercube via pathwise stochastic analysis," *Invent. Math.*, 230:935–994, 2022.
- R. O'Donnell, J. Wright, and Y. Zhou, "The Fourier entropy–influence conjecture for certain classes of Boolean functions," *Proc. ICALP*, pp. 330–341, 2011.
- R. Hod, "Improved lower bounds for the Fourier entropy/influence conjecture via lexicographic functions," *J. Comb. Theory Ser. A*, 160:177–199, 2018.
- R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014.

## Formal statement and certificate

- **Adversarial check (2026-11-27): Statement is faithful and still open.** It is the FEI
  conjecture word for word (`±1` encoded as `Bool`, entropy in bits, `I(f) = ∑ |S| f̂(S)²`);
  no junk values (finite sums, `negPLogP 0 = 0`). The module name (`LogSobolevHypercubeSharp`)
  is historical; the statement is FEI. No proof had appeared by November 2026: recent work is
  partial, e.g. arXiv:2606.00246 ("Further evidence towards the Fourier Entropy-Influence
  conjecture", June 2026) and X. Han's bound `H ≤ O(I(f) + ∑_k I_k(f) log(1/I_k(f)))`
  (Combinatorica 2025).
- **Certificate** `lean/InfoTheory/Known/Certificates/LogSobolevHypercubeSharp.lean`:
  `abs_fourierCoeff_le_one`, `fourierEntropy_nonneg`, `totalInfluence_nonneg` (both sides are
  genuine nonnegative reals); the regression for the 2-bit AND, `fourierCoeff_and2`
  (`f̂(S)² = 1/4` for all four `S`), `fourierEntropy_and2 = 2` and `totalInfluence_and2 = 1`,
  so any valid constant needs `C ≥ 2` (`two_le_of_FEI`); and the 1-bit dictator, with `H = 0`
  and `I = 1`.
