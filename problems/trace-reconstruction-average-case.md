---
id: trace-reconstruction-average-case
title: Sample Complexity of Average-Case Binary Trace Reconstruction
status: open
category: coding-theory
posed_by: Tugkan Batu, Sampath Kannan, Sanjeev Khanna, and Andrew McGregor
posed_year: 2004
tags: [coding-theory, trace-reconstruction, average-case, deletion-channel]
lean_module: InfoTheory.Problems.TraceReconstructionAverageCase
lean_file: lean/InfoTheory/Problems/TraceReconstructionAverageCase.lean
---

## Statement

Let $X \sim \mathrm{Unif}(\{0, 1\}^n)$ be a uniformly random binary string of length $n$, and let $Y^{(1)}, \dots, Y^{(T)}$ be $T$ independent traces obtained by passing $X$ through the i.i.d. binary deletion channel $\mathrm{Del}_{1/2}$ with deletion probability $d = 1/2$. Let $T_{\mathrm{avg}}(n, 1/2)$ be the minimum number of traces $T$ for which there exists a reconstruction algorithm $\hat{X}(Y^{(1)}, \dots, Y^{(T)})$ satisfying
$$\Pr[\hat{X}(Y^{(1)}, \dots, Y^{(T)}) = X] \ge \frac{2}{3}.$$

**Open Problem:** Does average-case binary trace reconstruction at deletion probability $d = 1/2$ have **polylogarithmic** sample complexity, i.e., does there exist a constant $c \in \mathbb{N}$ such that
$$T_{\mathrm{avg}}(n, 1/2) = O((\log n)^c),$$
or is $T_{\mathrm{avg}}(n, 1/2)$ super-polylogarithmic in $n$?

## Background

In average-case trace reconstruction, the unknown string $X$ is drawn uniformly at random rather than adversarially. Random strings exhibit abundant local uniqueness—short substrings of length $O(\log n)$ occur uniquely with high probability—allowing alignment algorithms to reduce a length-$n$ average-case instance to worst-case instances of length $O(\log n)$.

Historically, researchers asked whether $O(\log n)$ traces suffice in the average case; Holden and Lyons (2020) and Chase (2021) ruled out $O(\log n)$ by proving lower bounds of $\tilde{\Omega}(\log^{9/4} n)$ and $\tilde{\Omega}(\log^{5/2} n)$, respectively. On the upper-bound side, Holden, Pemantle, Peres, and Zhai (2020) broke the polynomial barrier with $\exp(O(\log^{1/3} n))$ traces, and Rubinstein (2023) improved this to $\exp(\tilde{O}(\log^{1/5} n))$ using Chase's worst-case breakthrough. Whether the true average-case complexity is $\mathrm{polylog}(n)$ or super-polylogarithmic remains wide open.

## What is known

- **Upper bounds:**
  - Peres and Zhai (2017): $\exp(O(\log^{1/2} n))$ traces for $d < 1/2$.
  - Holden, Pemantle, Peres, and Zhai (2020, Ann. Probab. / COLT 2018): $\exp(O(\log^{1/3} n))$ traces for every constant $d < 1$, by aligning traces locally and invoking the $\exp(O(m^{1/3}))$ mean-based worst-case algorithm on blocks of length $m = O(\log n)$.
  - Rubinstein (2023): $\exp(\tilde{O}(\log^{1/5} n))$ traces for every constant $d < 1$, via a general average-to-shifted-worst-case reduction combined with Chase's (2021) $\exp(\tilde{O}(m^{1/5}))$ worst-case algorithm.
- **Lower bounds:**
  - McGregor, Price, and Vorotnikova (2014): $\Omega(\log n / \log \log n)$.
  - Holden and Lyons (2020): $\tilde{\Omega}(\log^{9/4} n)$ traces (disproving $O(\log n)$).
  - Chase (2021): $\tilde{\Omega}(\log^{5/2} n)$ traces, currently the best known lower bound for average-case binary trace reconstruction at $d = 1/2$.
- **Connection to worst-case:** A polynomial upper bound $T_{\mathrm{wc}}(m, 1/2) = \mathrm{poly}(m)$ for shifted worst-case trace reconstruction would immediately imply $T_{\mathrm{avg}}(n, 1/2) = \mathrm{polylog}(n)$ via Rubinstein's reduction; conversely, any super-polylogarithmic lower bound for $T_{\mathrm{avg}}(n, 1/2)$ would imply a super-polynomial lower bound for $T_{\mathrm{wc}}(m, 1/2)$.

## Formal statement and certificate

Adversarial audit (2026-11-27): the Lean `Statement` is faithful and open. The best upper bound is
`exp(Õ(log^{1/5} n))`, and a search found no polylogarithmic upper bound as of 2026-11.

Certificate `lean/InfoTheory/Known/Certificates/TraceReconstructionAverageCase.lean` proves the following:
- `Pr[Del_d(x) = x] = (1-d)^n`.
- A one-trace decoder succeeds with probability `≥ (1-d)^n`.
- **Regression check:** `T_avg(n, d) = 1` whenever `(1-d)^n ≥ 2/3`. In particular this holds for
  the noiseless channel `d = 0`, for every `n`.

Not certified: that the defining set is non-empty at `d = 1/2`, which is needed so that `sInf` is
not the junk value 0. It is true: with `T` traces, the probability that some trace has full length
is `1 - (1-2^{-n})^T → 1`. The proof needs the deletion-channel normalisation lemma.

## References

- T. Batu, S. Kannan, S. Khanna, and A. McGregor, "Reconstructing strings from random traces," *Proc. 15th ACM–SIAM SODA*, pp. 910–918, 2004.
- Y. Peres and A. Zhai, "Average-case reconstruction for the deletion channel: Subpolynomially many traces suffice," *Proc. 58th IEEE FOCS*, pp. 228–239, 2017.
- N. Holden, R. Pemantle, Y. Peres, and A. Zhai, "Subpolynomial trace reconstruction for random strings and arbitrary deletion probability," *Mathematical Statistics and Learning*, 2(3):275–309, 2020 (COLT 2018).
- N. Holden and R. Lyons, "Lower bounds for trace reconstruction," *Annals of Applied Probability*, 30(2):503–525, 2020.
- Z. Chase, "New lower bounds for trace reconstruction," *Annales de l'Institut Henri Poincaré, Probabilités et Statistiques*, 57(2):627–643, 2021.
- Z. Chase, "Separating words and trace reconstruction," *Proc. 53rd ACM STOC*, pp. 21–31, 2021.
- I. Rubinstein, "Average-case to (shifted) worst-case reduction for the trace reconstruction problem," *Proc. 50th ICALP*, 2023 (arXiv:2202.07577).
