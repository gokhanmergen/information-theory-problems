---
id: gilbert-varshamov-binary
title: Asymptotic Tightness of the Binary Gilbert–Varshamov Bound
status: open
category: coding-theory
posed_by: E. N. Gilbert; R. R. Varshamov (folklore)
posed_year: 1952
tags: [coding-theory, gilbert-varshamov, binary-codes, rate-distance-tradeoff]
lean_module: InfoTheory.Problems.GilbertVarshamovBinary
lean_file: lean/InfoTheory/Problems/GilbertVarshamovBinary.lean
---

## Statement

For integers $n, d \ge 1$, let $A_2(n, d)$ denote the maximum cardinality of a binary code $C \subseteq \{0, 1\}^n$ with minimum Hamming distance at least $d$. For any relative minimum distance $\delta \in (0, 1/2)$, define the asymptotic maximum binary code rate
$$R_2(\delta) = \limsup_{n \to \infty} \frac{1}{n} \log_2 A_2(n, \lceil \delta n \rceil).$$
Let $h(\delta) = -\delta \log_2 \delta - (1 - \delta) \log_2(1 - \delta)$ be the binary entropy function. The Gilbert–Varshamov bound establishes $R_2(\delta) \ge 1 - h(\delta)$ for every $\delta \in (0, 1/2)$.

**Conjecture / Open Problem:** Does equality
$$R_2(\delta) = 1 - h(\delta)$$
hold for all $\delta \in (0, 1/2)$, or does there exist some $\delta \in (0, 1/2)$ with $R_2(\delta) > 1 - h(\delta)$?

## Background

Determining the optimal asymptotic rate–distance tradeoff $R_q(\delta)$ of $q$-ary error-correcting codes is the central extremal problem of algebraic and combinatorial coding theory. Gilbert (1952) proved via a greedy sphere-packing argument that $R_q(\delta) \ge 1 - h_q(\delta)$, and Varshamov (1957) proved the same bound is achieved by random linear codes.

For large prime-power alphabets—specifically all squares $q \ge 49$—Tsfasman, Vlăduţ, and Zink (1982) dramatically disproved the optimality of the Gilbert–Varshamov bound using algebraic geometry (Goppa) codes constructed from modular curves, achieving $R_q(\delta) \ge 1 - \delta - (\sqrt{q} - 1)^{-1} > 1 - h_q(\delta)$ on a non-empty subinterval of $\delta$. In stark contrast, for the binary alphabet $q = 2$ (and indeed for all $q < 49$), no code family—linear or nonlinear—has ever beaten the exponential growth rate $1 - h(\delta)$, even by an arbitrarily small additive constant at any single $\delta \in (0, 1/2)$.

## What is known

- **Lower bounds (Gilbert–Varshamov and subexponential improvements):**
  - Gilbert (1952) and Varshamov (1957) established $R_2(\delta) \ge 1 - h(\delta)$ for all $\delta \in (0, 1/2)$.
  - Jiang and Vardy (2004) improved the finite-length Gilbert–Varshamov bound by a logarithmic factor, showing $A_2(n, d) = \Omega(n \cdot 2^n / V_2(n, d-1))$ via an independent-set bound in the Hamming graph, and Vu and Wu (2005) generalized this to $q$-ary codes. However, polynomial prefactors vanish in the asymptotic rate $\frac{1}{n} \log_2 A_2(n, \lceil \delta n \rceil)$.
- **Upper bounds (Linear Programming / MRRW bounds):**
  - Delsarte (1973) introduced the linear programming (LP) framework based on Krawtchouk polynomials.
  - McEliece, Rodemich, Rumsey, and Welch (1977) proved the first and second MRRW upper bounds, giving the best known asymptotic upper bound on $R_2(\delta)$ for every $\delta \in (0, 1/2)$:
    - First MRRW bound: $R_2(\delta) \le h\!\left(\frac{1}{2} - \sqrt{\delta(1 - \delta)}\right)$.
    - Second MRRW bound (strictly tighter for $\delta \lesssim 0.273$): $R_2(\delta) \le \min_{0 \le u \le 1 - 2\delta} \left\{ 1 + g(u^2) - g(u^2 + 2\delta u + 2\delta) \right\}$ where $g(x) = h\!\left(\frac{1 - \sqrt{1 - x}}{2}\right)$.
  - Barg and Jaffe (1998) and Navon and Samorodnitsky (2009) gave alternative proofs and studied the limits of Delsarte's LP bound; Samorodnitsky (2001) proved that the LP bound itself cannot match $1 - h(\delta)$ for any $\delta \in (0, 1/2)$ unless strengthened beyond degree-1 Krawtchouk inequalities.
- **Large alphabets:** Tsfasman–Vlăduţ–Zink (1982) proved $R_q(\delta) > 1 - h_q(\delta)$ for every square prime power $q \ge 49$ and a non-empty range of $\delta$.

## References

- E. N. Gilbert, "A comparison of signalling alphabets," *Bell System Technical Journal*, 31(3):504–522, 1952.
- R. R. Varshamov, "Estimate of the number of signals in error correcting codes," *Doklady Akademii Nauk SSSR*, 117:739–741, 1957.
- P. Delsarte, "An algebraic approach to the association schemes of coding theory," *Philips Research Reports Supplements*, 10:1–97, 1973.
- R. J. McEliece, E. R. Rodemich, H. Rumsey Jr., and L. R. Welch, "New upper bounds on the rate of a code via the Delsarte–MacWilliams inequalities," *IEEE Trans. Inf. Theory*, 23(2):157–166, 1977.
- M. A. Tsfasman, S. G. Vlăduţ, and Th. Zink, "Modular curves, Shimura curves, and Goppa codes, better than Varshamov–Gilbert bound," *Mathematische Nachrichten*, 109(1):21–28, 1982.
- T. Jiang and A. Vardy, "Asymptotic improvement of the Gilbert–Varshamov bound on the size of binary codes," *IEEE Trans. Inf. Theory*, 50(8):1655–1664, 2004.
- M. Navon and A. Samorodnitsky, "Linear programming bounds for codes via a covering argument," *Discrete & Computational Geometry*, 41(2):199–207, 2009.
