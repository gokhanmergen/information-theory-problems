---
id: courtade-kumar
title: The Courtade–Kumar Most-Informative-Boolean-Function Conjecture
status: open
posed_by: Courtade and Kumar
posed_year: 2013
tags: [entropy-inequalities, boolean-functions, discrete-fourier]
---

## Statement

Let $X \sim \mathrm{Uniform}(\{0,1\}^n)$ and let $Y$ be the output of a memoryless
binary symmetric channel $\mathsf{BSC}(\alpha)$ with input $X$, $\alpha \in (0, 1/2)$.

**Conjecture.** For every Boolean function $f : \{0,1\}^n \to \{0,1\}$,
$$I(f(X); Y) \;\leq\; 1 - h(\alpha),$$
where $h$ is the binary entropy function — i.e. no one-bit summary of $X$ is more
informative about the noisy observation $Y$ than a single coordinate ("dictator")
function $f(x) = x_i$, which achieves equality.

## Background

A disarmingly simple statement — one line, finite-dimensional, checkable for small $n$
— that has become a benchmark for the interaction of information theory with the
analysis of Boolean functions. It sits at the junction of hypercontractivity,
isoperimetry, and mutual information, and its resistance to standard Fourier-analytic
attacks is part of its fame. A natural warm-up for AI attempts: everything needed to
state and explore it fits on a page, and numerical exploration is genuinely useful.

## What is known

- Verified exhaustively for $n \leq 5$ on grids of $\alpha$ (all $2^{2^n}$ functions;
  see this repository's attempt log), and for structured families (symmetric,
  low-degree, lex) at larger $n$; full exhaustion is infeasible for $n \geq 6$
  ($2^{64}$ functions).
- True in the **high-noise regime**: Samorodnitsky (2016) proved the conjecture for
  $\alpha$ in a neighborhood of $1/2$, via a strengthened hypercontractive/entropy
  approach. Ordentlich–Shayevitz–Weinstein gave improved bounds for all $\alpha$ short
  of the conjecture.
- Weaker global bounds: $I(f(X);Y) \leq (1-2\alpha)^2$ follows from standard
  hypercontractivity-type arguments and is weaker than the conjecture for all
  $\alpha$.
- The analogous "complementary" conjecture of Courtade–Kumar on $H(f(X) \mid Y)$ and
  several Gaussian analogues have been resolved (e.g. the Gaussian isoperimetric
  version by Kindler–O'Donnell–Witmer and, for the "mean" version, Eldan's and
  others' work) — the original discrete conjecture remains open in the general-noise
  regime.
- Equality analysis: dictators are conjectured to be the unique maximizers up to
  symmetry; any proof must fail gracefully for functions correlated with dictators
  (lex functions, majorities are strictly worse — verified numerically).

## References

- T. A. Courtade and G. R. Kumar, "Which Boolean functions maximize mutual information
  on noisy inputs?" IEEE Trans. Inf. Theory, 2014.
- A. Samorodnitsky, "On the entropy of a noisy function," IEEE Trans. Inf. Theory,
  2016.
- O. Ordentlich, O. Shayevitz, and O. Weinstein, "An improved upper bound for the most
  informative Boolean function conjecture," Proc. IEEE ISIT, 2016.
- R. O'Donnell, *Analysis of Boolean Functions*, Cambridge Univ. Press, 2014
  (background).
