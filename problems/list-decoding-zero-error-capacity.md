---
id: list-decoding-zero-error-capacity
title: Zero-Error List-Decoding Capacity of the 3/2 Channel (Trifferent Codes)
status: open
category: zero-error
posed_by: Peter Elias; János Körner, Katalin Marton
posed_year: 1988
tags: [zero-error, list-decoding, trifferent-codes, perfect-hashing, combinatorics]
lean_module: InfoTheory.Problems.ListDecodingZeroErrorCapacity
lean_file: lean/InfoTheory/Problems/ListDecodingZeroErrorCapacity.lean
---

## Statement

In Elias's (1988) **$3/2$-channel**, both the input and output alphabets are $\{0, 1, 2\}$,
and on input $x \in \{0, 1, 2\}$ the channel can output either symbol $y \in \{0, 1, 2\} \setminus \{x\}$.
Its ordinary zero-error capacity (list size $L = 1$) is $0$. Under **zero-error list decoding
with list size $L = 2$**, a codebook $C \subseteq \{0, 1, 2\}^n$ is valid if and only if no
three distinct codewords can produce a common output sequence — equivalently, for every three
distinct codewords $x, y, z \in C$, there exists a coordinate $i \in \{1, \dots, n\}$ where
$x_i, y_i, z_i$ are pairwise distinct ($\{x_i, y_i, z_i\} = \{0, 1, 2\}$). Such a codebook is
called a **trifferent code** (or $3$-hash family).

The **zero-error list-of-2 capacity of the $3/2$-channel** is
$$C_{3/2, 2} = \sup \left\{ \frac{\log_2 |C|}{n} : n \ge 1, \; C \subseteq \{0, 1, 2\}^n \text{ is a trifferent code} \right\} .$$

**Determine $C_{3/2, 2}$** — and as the flagship benchmark problem, **prove whether $C_{3/2, 2}$
is strictly smaller than the elementary Fredman–Komlós / Körner upper bound $\log_2(3/2)$**:
$$C_{3/2, 2} < \log_2\!\left(\frac{3}{2}\right) \approx 0.5850 .$$

## Background

Peter Elias (1988) introduced zero-error list-decoding capacity for general discrete memoryless
channels and singled out the $q/(q-1)$ channel (which outputs any symbol other than the input)
as the simplest non-trivial benchmark. For list size $L = q - 1$, zero-error list-decoding codes
for the $q/(q-1)$ channel are in exact bijection with **$q$-perfect hash families** — subsets of
$\{0, \dots, q-1\}^n$ in which every $q$ distinct words take all $q$ distinct values in at least
one coordinate.

For $q = 3$, this is the **trifference problem** studied by Körner (1973), Fredman and Komlós
(1984), Körner and Marton (1988), and Elias (1988). An elementary pigeonhole/double-counting
argument gives $|C| \le 2 \cdot (3/2)^n$, i.e. $C_{3/2, 2} \le \log_2(3/2) \approx 0.5850$.
Despite forty years of effort — including graph-entropy bounds, linear programming, and modern
algebraic tensor methods such as slice rank (which solved the cap set problem!) — **not a single
exponential improvement** over $(3/2)^n$ has been achieved, leaving a dramatic gap to the best
known lower bound $\frac{1}{4}\log_2(9/5) \approx 0.2120$ (Körner–Marton 1988).

## What is known

- **Best asymptotic rate lower bound:** Körner and Marton (1988) achieved
  $C_{3/2, 2} \ge \frac{1}{4} \log_2(9/5) \approx 0.2120$ bits via random coding concatenated
  with a small inner trifferent code.
- **Best asymptotic rate upper bound:** $C_{3/2, 2} \le \log_2(3/2) \approx 0.5850$ bits
  (elementary; Fredman–Komlós 1984; Körner 1986).
- **Subexponential improvements:** Bhandari and Khetan (2022) improved the upper bound on
  maximum trifferent code size to $T(n) = O(n^{-2/5} (3/2)^n)$ (improving earlier $O((3/2)^n)$
  constants), which still leaves the asymptotic rate upper bound at $\log_2(3/2)$.
- **Barriers to polynomial/slice-rank methods:** Costa and Dalai (2021) proved structural
  limitations showing that straightforward applications of the slice-rank method cannot beat
  $\log_2(3/2)$ for trifferent codes.
- **Larger $q$ and list sizes:** For $q \ge 4$, Fredman–Komlós (1984), Körner–Marton (1988),
  Dalai–Guruswami–Radhakrishnan (2020), and Bhandari–Radhakrishnan (2021) obtained tighter
  bounds for $q$-hashing and the $q/(q-1)$ channel, while the exact zero-error list-decoding
  capacity remains open for all $q \ge 3$ and $L = q - 1$.

## References

- P. Elias, "Zero error capacity under list decoding,"
  IEEE Trans. Inf. Theory, 1988.
- M. L. Fredman and J. Komlós, "On the size of separating systems and families of perfect hash
  functions," SIAM J. Algebraic Discrete Methods, 1984.
- J. Körner and K. Marton, "New bounds for perfect hashing via information theory,"
  Eur. J. Combin., 1988.
- S. Costa and M. Dalai, "New bounds for perfect $k$-hashing,"
  Discrete Appl. Math., 2021.
- M. Dalai, V. Guruswami, and J. Radhakrishnan, "An improved bound for zero-error list decoding
  of the 4/3 channel," IEEE Trans. Inf. Theory, 2020.
- S. Bhandari and A. Khetan, "Improved upper bound for the size of trifferent codes,"
  arXiv:2204.06498, 2022.
