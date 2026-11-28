---
id: entropic-doubling-constant
title: Sharp Constant in the Entropic Polynomial Freiman–Ruzsa Inequality
status: partially-solved
category: entropy-inequalities
posed_by: Katalin Marton; Terence Tao
posed_year: 2023
tags: [entropy-inequalities, additive-combinatorics, pfr, ruzsa-distance]
lean_module: InfoTheory.Problems.EntropicDoublingConstant
lean_file: lean/InfoTheory/Problems/EntropicDoublingConstant.lean
---

## Statement

For independent random variables $X, Y$ taking values in $\mathbb{F}_2^n$, define the **entropic Ruzsa distance**
$$d[X; Y] := H(X + Y) - \frac{1}{2} H(X) - \frac{1}{2} H(Y),$$
where $H(\cdot)$ is Shannon entropy in bits and addition is in $\mathbb{F}_2^n$. For a linear subspace $H \le \mathbb{F}_2^n$, let $U_H$ denote the uniform distribution on $H$.

The breakthrough proof of Marton's Polynomial Freiman–Ruzsa (PFR) conjecture by Gowers, Green, Manners, and Tao (2023) established that there exists an absolute constant $C > 0$ such that for all $n \ge 1$ and all $\mathbb{F}_2^n$-valued random variables $X, Y$, there exists a subspace $H \le \mathbb{F}_2^n$ satisfying
$$d[X; U_H] + d[Y; U_H] \;\le\; C \cdot d[X; Y]$$
(and in particular, taking $X = Y$, $d[X; U_H] \le \frac{C}{2}\, d[X; X]$).

**Conjecture (Sharp Entropic PFR Constant).** For every $n \ge 1$ and every $\mathbb{F}_2^n$-valued random variable $X$, there exists a subspace $H \le \mathbb{F}_2^n$ such that
$$d[X; U_H] \;\le\; 2 \cdot d[X; X],$$
and more generally determine the infimum $C_*$ of all constants $C$ for which $\min_{H \le \mathbb{F}_2^n} d[X; U_H] \le C \cdot d[X; X]$ holds universally over all $n$ and $X$.

## Background

In late 2023, Gowers, Green, Manners, and Tao resolved Marton's long-standing Polynomial Freiman–Ruzsa conjecture over $\mathbb{F}_2^n$ (and subsequently over all bounded-torsion abelian groups) by translating the combinatorial doubling problem into an entropic descent argument on the Ruzsa distance $d[X; Y]$. While the existence of an absolute constant $C$ is now settled (and formally verified in Lean 4), the optimal value of the exponent/constant remains wide open. Sharpening the entropic constant immediately improves the polynomial exponent in the combinatorial PFR theorem (covering a set $A \subset \mathbb{F}_2^n$ with $|A + A| \le K|A|$ by at most $2 K^c$ cosets of a subspace $H$ of size $|H| \le |A|$), with direct applications in coding theory, communication complexity, and property testing.

## What is known

- **Initial breakthrough (Gowers–Green–Manners–Tao, 2023):** Proved the entropic PFR inequality with $d[X; U_H] + d[Y; U_H] \le 11\, d[X; Y]$ (giving $d[X; U_H] \le 6\, d[X; X]$ in the symmetric case and combinatorial coset exponent $c = 12$).
- **Refined descent (Liao, 2024):** Jyun-Jie Liao improved the entropic descent analysis, reducing the combinatorial exponent from $12$ to $11$ and then to $9$ (with corresponding improvements to the entropic Ruzsa-distance constant, formalized in the Lean 4 PFR project).
- **Lower bounds on the optimal constant:** Simple examples (such as $X$ supported on a subspace plus a small perturbation, or $X$ uniform on three non-collinear points in $\mathbb{F}_2^2$) give lower bounds on $C_*$. Already $X\sim\mathrm{Bern}(p)$ on $\mathbb{F}_2$ with $h(p)=1/2$ ($p\approx0.110028$) gives $\min_H d[X;U_H]=1/4$ against $d[X;X]=h(2p(1-p))-h(p)\approx0.21354$, so $C_*\ge 1.1707$ (numerical, verified by an exhaustive subspace search for $n\le4$, claude-known triage 2026-11-27; earlier text said "around 1/2 to 1"); in the combinatorial PFR setting, subsets of $\mathbb{F}_2^n$ of size $2^k + 1$ and random subsets show the combinatorial exponent must be at least $2$ (up to lower-order factors).
- **Sharp constant $C = 2$ (and exact $C_*$):** Closing the gap between the known upper bounds (around $4.5$–$5.5$ for $d[X; U_H] / d[X; X]$, and $9$ for the two-variable/combinatorial constant) and the conjectured sharp constant remains open.

## References

- W. T. Gowers, B. Green, F. Manners, and T. Tao, "On a conjecture of Marton," arXiv:2311.05762, 2023.
- W. T. Gowers, B. Green, F. Manners, and T. Tao, "Marton's conjecture in abelian groups with bounded torsion," arXiv:2404.02244, 2024.
- J.-J. Liao, "Improved exponent for Marton's conjecture in $\mathbb{F}_2^n$," arXiv:2404.09639, 2024.
- T. Tao, "Sumset and inverse sumset theory for Shannon entropy," *Combin. Probab. Comput.*, 19(4):603–639, 2010.
- B. Green, "Notes on PFR," expository notes, 2023.
