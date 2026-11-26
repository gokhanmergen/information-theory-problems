---
id: zero-error-mac-adder
title: Zero-Error Sum Capacity of the Two-User Binary Adder Multiple-Access Channel
status: open
category: zero-error
posed_by: Bernt Lindström; Tadao Kasami, Shu Lin
posed_year: 1969
tags: [zero-error, multiple-access, adder-channel, uniquely-decodable-codes, combinatorics]
lean_module: InfoTheory.Problems.ZeroErrorMacAdder
lean_file: lean/InfoTheory/Problems/ZeroErrorMacAdder.lean
---

## Statement

In the two-user synchronous binary adder multiple-access channel (BAC), two transmitters
independently send binary vectors $a \in A \subseteq \{0, 1\}^n$ and $b \in B \subseteq \{0, 1\}^n$,
and the receiver observes their coordinatewise real sum $a + b \in \{0, 1, 2\}^n$. The code pair
$(A, B)$ is **uniquely decodable** (zero-error) if $a_1 + b_1 = a_2 + b_2$ implies
$a_1 = a_2$ and $b_1 = b_2$ for all $a_1, a_2 \in A$ and $b_1, b_2 \in B$.

The **zero-error sum capacity** of the binary adder MAC is
$$C_{0,\mathrm{sum}}^{\mathrm{BAC}} = \sup \left\{ \frac{\log_2 |A| + \log_2 |B|}{n} : n \ge 1, \; (A, B) \text{ uniquely decodable in } \{0, 1\}^n \right\} .$$

**Determine $C_{0,\mathrm{sum}}^{\mathrm{BAC}}$.** Current bounds bracket the sum capacity in
$$1.3186 \lesssim C_{0,\mathrm{sum}}^{\mathrm{BAC}} \lesssim 1.480 < 1.5 .$$
In particular, the accompanying Lean statement formalizes whether $C_{0,\mathrm{sum}}^{\mathrm{BAC}}$ is attained at some finite blocklength $n \ge 1$.

## Background

With vanishing error probability, the two-user binary adder MAC is one of the simplest solved
multiuser channels: its capacity region is the pentagon $R_1 \le 1$, $R_2 \le 1$,
$R_1 + R_2 \le 1.5$ bits per channel use. Requiring **zero error** transforms the problem into
a notoriously difficult question in additive combinatorics: maximizing $|A| \cdot |B|$ over
subsets $A, B \subseteq \{0, 1\}^n$ whose Minkowski sum $A + B \subseteq \{0, 1, 2\}^n$ has
no collisions ($|A + B| = |A| \cdot |B|$).

Unlike the vanishing-error case, Urbanke and Li (1998) proved that $C_{0,\mathrm{sum}}^{\mathrm{BAC}}$
is strictly smaller than $1.5$, establishing a genuine zero-error penalty for the binary adder
channel. Closing the gap between explicit finite-blocklength uniquely decodable code pairs
($\approx 1.3178$) and information-theoretic / Fourier-analytic / combinatorial upper bounds
($\approx 1.428$) has resisted fifty years of research.

## What is known

- **Vanishing-error sum capacity:** $1.5$ bits per channel use.
- **Best lower bounds (explicit uniquely decodable code pairs):**
  - Kasami and Lin (1976): $\frac{\log_2 6}{2} \approx 1.2925$ ($n = 2$).
  - van Tilborg (1978): $\frac{\log_2 96}{5} \approx 1.3170$ ($n = 5$).
  - Mattas and Östergård (2005): $\frac{\log_2 240}{6} \approx 1.3178$ ($n = 6$, via a code pair
    with $|A| \cdot |B| = 240$).
- **Best upper bounds:**
  - Urbanke and Li (1998): $C_{0,\mathrm{sum}}^{\mathrm{BAC}} \le 1.4500$ (first proof of strict
    separation from $1.5$).
  - Ordentlich and Shayevitz (2016): $C_{0,\mathrm{sum}}^{\mathrm{BAC}} \le 1.441$ (via
    VC-dimension and hypercontractivity / entropy arguments).
  - Austrin, Kaski, Koivisto, and Nederlof (2017): $C_{0,\mathrm{sum}}^{\mathrm{BAC}} \le 1.428$
    (via refined subset-sum / Fourier-entropy inequalities).
- **Equal-rate and asymmetric cases:** When one user sends at rate $R_1 = 1$ ($A = \{0, 1\}^n$),
  the problem reduces to Lindström's (1969) coin-weighing / Sidon-type bound, giving $R_2 = 0$;
  the maximum sum rate occurs near symmetric or mildly asymmetric rate pairs.

## References

- B. Lindström, "Determination of two vectors from the sum,"
  J. Combin. Theory, 1969.
- T. Kasami and S. Lin, "Coding for a multiple-access channel,"
  IEEE Trans. Inf. Theory, 1976.
- H. C. A. van Tilborg, "An upper bound for codes in a two-access binary erasure channel,"
  IEEE Trans. Inf. Theory, 1978.
- R. Urbanke and Q. Li, "The zero-error capacity region of the 2-user synchronous BAC is
  strictly smaller than its Shannon capacity region," Proc. Information Theory Workshop, 1998.
- M. Mattas and P. R. J. Östergård, "A new bound for the zero-error capacity region of the
  two-user binary adder channel," IEEE Trans. Inf. Theory, 2005.
- O. Ordentlich and O. Shayevitz, "A VC-dimension-based outer bound on the zero-error
  capacity of the binary adder channel," Proc. IEEE ISIT, 2016.
- P. Austrin, P. Kaski, M. Koivisto, and J. Nederlof, "Dense subset sum may be the hardest,"
  STACS / arXiv, 2017.
