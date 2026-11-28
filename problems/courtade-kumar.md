---
id: courtade-kumar
title: The Courtade–Kumar Most-Informative-Boolean-Function Conjecture
status: solved
category: entropy-inequalities
posed_by: Courtade and Kumar
posed_year: 2013
tags: [entropy-inequalities, boolean-functions, discrete-fourier]
lean_module: InfoTheory.Problems.CourtadeKumar
lean_file: lean/InfoTheory/Problems/CourtadeKumar.lean
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

- **RESOLVED IN FULL (September 2026, formally verified in Lean 4):** The
  Courtade–Kumar conjecture is **true** for all $n \ge 1$, all $\alpha \in (0, 1/2)$,
  and all (possibly unbalanced) Boolean functions $f : \{0,1\}^n \to \{0,1\}$.
  - **Chen, Gohari, Javanmard, Lin, Mirrokni, Nair, and Woodruff** (Sept 21, 2026,
    `arXiv:2609.24931`) proved the general Courtade–Kumar conjecture (including
    unbalanced functions) and **formally verified the entire proof end-to-end in
    Lean 4** (`dpwoodru/general-courtade-kumar-lean`).
  - Independent analytical proofs also appeared immediately afterwards: **Vu Khac Ky
    and Tuan Tran** (Sept 21, 2026, `arXiv:2609.24184`), **Hessam Mahdavifar and
    Ahmad Beirami** (Sept 22, 2026, `arXiv:2609.26444`), and **Dimiter Kramer and
    Mert Sağlam** (Nov 3, 2026, `arXiv:2611.05430`).
  - **Bridge to the frozen statement (Lean, in this repository):**
    `lean/InfoTheory/External/CourtadeKumar.lean` proves
    `GeneralCK.GeneralCourtadeKumar → InfoTheory.Problems.CourtadeKumar.Statement` against a
    byte-identical copy of the upstream target statement. It also shows the two formalisations
    of $I(f(X);Y)$ are equal. The upstream theorem itself is checked in its own repository
    (Lean `v4.33.1`) and is not replayed here, so there is still no unconditional
    `Solutions/CourtadeKumar.lean`. See
    `attempts/courtade-kumar/2026-11-27-claude-opus-5-5-lean-bridge.md`.

### Prior milestones before the September 2026 resolution

- Verified exhaustively for $n \leq 5$ on grids of $\alpha$ (all $2^{2^n}$ functions;
  see this repository's attempt log), and for structured families (symmetric,
  low-degree, lex) at larger $n$; full exhaustion is infeasible for $n \geq 6$
  ($2^{64}$ functions).
- **The $n = 4$ case** (computer-assisted, status `unverified` pending
  review): $I(f(X);Y) \leq 1-h(\alpha)$ for **all** $\alpha \in (0, 1/2)$ and all
  $f$ on 4 variables, with dictators the unique maximizers on $[0.001, 0.495]$.
  Proof: interval arithmetic over the 222 NPN classes on the middle range, plus
  two hand-proved endpoint lemmas (boundary-profile at low noise, $\chi^2$-vs-
  exact-entropy-series at high noise) whose per-class conditions are verified in
  exact rational arithmetic. Self-contained — no reliance on prior high-noise
  theorems. See attempt log (`n4-full-theorem`).
- True in the **high-noise regime**: Samorodnitsky (2016) proved the conjecture for
  $\alpha$ in a neighborhood of $1/2$, via a strengthened hypercontractive/entropy
  approach; explicit thresholds have improved steadily since
  (Ordentlich–Shayevitz–Weinstein 2016; Javanmard–Woodruff 2026, who also prove the
  coordinate-wise bound $\sum_i I(f(X);Y_i) \leq 1-h(\alpha)$ for *all* Boolean
  functions).
- Yu (2024, revised 2026) proved a general **local optimality theorem** for dictators
  among balanced Boolean functions for $\Phi$-stability, and combined it with
  computer-assisted estimates to prove the **global balanced Courtade–Kumar
  conjecture** for $\rho=1-2\alpha\in[0,0.914]$.
- The conjecture is **equivalent** to a symmetrized Li–Médard conjecture
  (Barnes–Özgür 2020). A differential-equation reformulation reduced the balanced
  case to a finite-dimensional functional inequality, established modulo four
  explicit numerically-supported inequalities (Chen–Gohari–Nair 2025).
- Two earlier claimed full proofs on arXiv were **withdrawn** by their authors with
  acknowledged flaws (Kesal 2015, arXiv:1511.01828; Sârbu 2016, arXiv:1604.05113).
- The analogous "complementary" conjecture on $H(f(X) \mid Y)$ and several Gaussian
  analogues had been resolved earlier (Kindler–O'Donnell–Witmer; fixed-mean versions
  by Eldan and others).

## References

- Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, and D. P. Woodruff,
  "Proof of the general Courtade–Kumar conjecture," arXiv:2609.24931, Sept. 2026
  (with end-to-end Lean 4 formalization at `github.com/dpwoodru/general-courtade-kumar-lean`).
- V. K. Ky and T. Tran, "A proof of the Courtade–Kumar conjecture," arXiv:2609.24184,
  Sept. 2026.
- H. Mahdavifar and A. Beirami, "Proof of the Courtade–Kumar conjecture,"
  arXiv:2609.26444, Sept. 2026.
- D. Kramer and M. Sağlam, "On the Courtade–Kumar conjecture," arXiv:2611.05430,
  Nov. 2026.
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
