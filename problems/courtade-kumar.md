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
- At $n = 4$, **certified for the continuum** $\alpha \in [0.005, 0.495]$ by
  outward-rounded interval arithmetic over the 222 NPN classes (computer-assisted;
  see attempt log), with the two endpoint regimes reduced to explicit finite-margin
  lemmas (max non-dictator normalized level-1 weight $52/63$; min balanced
  non-dictator boundary $12$ vs. the dictator's isoperimetric $8$).
- True in the **high-noise regime**: Samorodnitsky (2016) proved the conjecture for
  $\alpha$ in a neighborhood of $1/2$, via a strengthened hypercontractive/entropy
  approach; explicit thresholds have improved steadily since
  (Ordentlich–Shayevitz–Weinstein 2016; Javanmard–Woodruff 2026, who also prove the
  coordinate-wise bound $\sum_i I(f(X);Y_i) \leq 1-h(\alpha)$ for *all* Boolean
  functions).
- **Local optimality of dictators is a theorem**: Yu (2024) proved dictators locally
  optimal among balanced functions, confirming the local version of the conjecture
  for $\rho = 1-2\alpha \in [0, 0.914]$ (partly computer-assisted). Globally,
  dictators are conjectured to be the unique maximizers up to symmetry; exhaustive
  computation at $n \leq 5$ finds the runner-ups are exactly their single-input
  perturbations (see attempt log).
- The conjecture is **equivalent** to a symmetrized Li–Médard conjecture
  (Barnes–Özgür 2020). A differential-equation reformulation reduces the balanced
  case to a finite-dimensional functional inequality, established modulo four
  explicit numerically-supported inequalities (Chen–Gohari–Nair 2025).
- Two claimed full proofs on arXiv were later **withdrawn** by their authors with
  acknowledged flaws (Kesal 2015, arXiv:1511.01828; Sârbu 2016, arXiv:1604.05113) —
  a caution for attempters.
- The analogous "complementary" conjecture on $H(f(X) \mid Y)$ and several Gaussian
  analogues have been resolved (Kindler–O'Donnell–Witmer; fixed-mean versions by
  Eldan and others) — the original discrete conjecture remains open at general noise.

## References

- T. A. Courtade and G. R. Kumar, "Which Boolean functions maximize mutual information
  on noisy inputs?" IEEE Trans. Inf. Theory, 2014.
- A. Samorodnitsky, "On the entropy of a noisy function," IEEE Trans. Inf. Theory,
  2016.
- O. Ordentlich, O. Shayevitz, and O. Weinstein, "An improved upper bound for the most
  informative Boolean function conjecture," Proc. IEEE ISIT, 2016.
- L. Barnes and A. Özgür, "The Courtade–Kumar most informative Boolean function
  conjecture and a symmetrized Li–Médard conjecture are equivalent," ISIT 2020;
  arXiv:2004.01277.
- L. Yu, "Local optimality of dictator functions with applications to Courtade–Kumar
  and Li–Médard conjectures," arXiv:2410.10147, 2024.
- Z. Chen, A. Gohari, and C. Nair, "A differential equation approach to the
  most-informative Boolean function conjecture," arXiv:2502.10019, 2025.
- A. Javanmard and D. P. Woodruff, "Progress on the Courtade–Kumar conjecture,"
  arXiv:2601.09679, 2026.
- R. O'Donnell, *Analysis of Boolean Functions*, Cambridge Univ. Press, 2014
  (background).
