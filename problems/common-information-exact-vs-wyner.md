---
id: common-information-exact-vs-wyner
title: Finite-Letter Attainment and Single-Letter Characterization of Exact Common Information
status: open
category: source-coding
posed_by: Gowtham R. Kumar, Cheuk Ting Li, and Abbas El Gamal; Lei Yu and Vincent Y. F. Tan
posed_year: 2014
tags: [source-coding, common-information, simulation, single-letter]
lean_module: InfoTheory.Problems.CommonInformationExactVsWyner
lean_file: lean/InfoTheory/Problems/CommonInformationExactVsWyner.lean
---

## Statement

For a finite-alphabet bipartite source $(X, Y) \sim P_{XY}$, let
$$G_1(X; Y) := \inf_{X - W - Y} H(W)$$
be the one-shot exact common information and
$$G(X; Y) := \inf_{n \ge 1} \frac{1}{n} G_1(X^n; Y^n)$$
be the asymptotic **exact common information** (Kumar–Li–El Gamal 2014) — the minimum rate of shared randomness required to generate $(X^n, Y^n)$ with *exact* joint distribution $P_{XY}^{\otimes n}$ via independent local processing.

**Open Problem.** Does $G(X; Y)$ admit a computable single-letter characterization for all finite-alphabet bipartite sources $P_{XY}$? In particular, is the infimum in $G(X; Y) = \inf_{n \ge 1} \frac{1}{n} G_1(X^n; Y^n)$ attained at some finite blocklength $n \ge 1$ for every finite source $P_{XY}$?

## Background

Wyner's common information $C_W(X; Y) = \inf_{X - W - Y} I(X, Y; W)$ characterizes the minimum common randomness rate for *asymptotically vanishing* KL-divergence simulation of $P_{XY}^{\otimes n}$. Kumar, Li, and El Gamal (2014) introduced the exact-simulation counterpart $G(X; Y)$, proving $C_W(X; Y) \le G(X; Y) \le G_1(X; Y)$ and showing that $G(X; Y) = C_W(X; Y)$ can hold strictly below $G_1(X; Y)$ (e.g., for the symmetric binary erasure source with $e > 1/2$).

## What is known

- **Strict separation from Wyner's common information:** Yu and Tan (2020) proved that $G(X; Y)$ equals the unnormalized $\infty$-Rényi common information and showed $G(X; Y) > C_W(X; Y)$ strictly for the doubly symmetric binary source (DSBS), resolving Kumar–Li–El Gamal's separation question.
- **One-shot vs. asymptotic gap:** Kumar–Li–El Gamal (2014) showed that for the symmetric binary erasure source with erasure probability $e > 1/2$, $G(X; Y) = C_W(X; Y) < G_1(X; Y)$, so $n = 1$ does not suffice in general.
- **General characterization:** Beyond symmetric binary and bivariate Gaussian sources (characterized by Yu–Tan 2020), no general single-letter formula is known, and whether $G(X; Y)$ is attained at finite $n$ for arbitrary discrete sources remains open.

## References

- G. R. Kumar, C. T. Li, and A. El Gamal, "Exact common information," Proc. IEEE ISIT, 2014; arXiv:1402.0062.
- L. Yu and V. Y. F. Tan, "Exact channel synthesis," IEEE Trans. Inf. Theory, 2020; arXiv:1810.00807.
- A. D. Wyner, "The common information of two dependent random variables," IEEE Trans. Inf. Theory, 1975.
