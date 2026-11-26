---
id: mds-conjecture
title: The MDS Conjecture
status: partially-solved
category: coding-theory
posed_by: Beniamino Segre
posed_year: 1955
tags: [coding-theory, mds-codes, finite-geometry, arcs]
lean_module: InfoTheory.Problems.MdsConjecture
lean_file: lean/InfoTheory/Problems/MdsConjecture.lean
---

## Statement

Let $\mathbb{F}_q$ be a finite field of order $q$. A linear $[n, k, d]_q$ code $C \subseteq \mathbb{F}_q^n$ is called **Maximum Distance Separable (MDS)** if its minimum Hamming distance meets the Singleton bound with equality: $d = n - k + 1$.

**MDS Conjecture (Segre 1955):** For every finite field $\mathbb{F}_q$ and every linear $[n, k, n - k + 1]_q$ MDS code with $2 \le k \le q - 1$,
$$n \le \begin{cases} q + 2 & \text{if } q \text{ is even and } k \in \{3, q - 1\}, \\ q + 1 & \text{otherwise.} \end{cases}$$

Equivalently, in projective geometry over $\mathbb{F}_q$, the maximum size of an arc (a set of points in $\mathrm{PG}(k - 1, q)$ with no $k$ points lying in a common hyperplane) is at most $q + 1$, except for hyperovals and their duals when $q$ is even and $k \in \{3, q - 1\}$, where $q + 2$ points are achievable.

## Background

MDS codes achieve the optimal tradeoff between redundancy and minimum distance allowed by the Singleton bound, making them foundational across storage systems, communication protocols, and secret sharing. Doubly extended Reed–Solomon codes provide linear $[q + 1, k, q - k + 2]_q$ MDS codes for all $1 \le k \le q$, and when $q$ is even, hyperovals in $\mathrm{PG}(2, q)$ (and their duals) yield $[q + 2, 3, q]_q$ and $[q + 2, q - 1, 4]_q$ MDS codes.

Segre posed the problem in 1955 in the language of arcs in finite projective spaces. Beyond its intrinsic interest in coding theory and Galois geometry, the MDS conjecture determines the maximum blocklength of optimal erasure-correcting codes over a fixed finite alphabet and connects deeply to algebraic hypersurfaces, Segre's lemma of tangents, and polynomial methods over finite fields.

## What is known

- **Prime fields (Ball 2012):** Simeon Ball proved the MDS conjecture completely whenever $q = p$ is prime, for all $2 \le k \le p - 1$. This is the most celebrated breakthrough on the conjecture since Segre's work.
- **Small dimensions and co-dimensions:**
  - $k = 2$: elementary ($n \le q + 1$, as $|\mathrm{PG}(1, q)| = q + 1$).
  - $k = 3$: Bose (1947) proved $n \le q + 1$ for $q$ odd and $n \le q + 2$ for $q$ even.
  - $k = 4, 5$: Segre (1955) and Casse–Glynn (1982, 1984) proved the conjecture for $k \in \{4, 5\}$ (and by duality for $k \in \{q - 2, q - 3\}$).
  - By MDS duality (the dual of an $[n, k, n - k + 1]_q$ MDS code is an $[n, n - k, k + 1]_q$ MDS code), if the conjecture holds for $(q, k)$ up to $n = q + 1$, it holds for $(q, q + 2 - k)$ as well.
- **Non-prime powers $q = p^h$ ($h \ge 2$):**
  - Ball (2012) and Ball–De Beule (2012) proved the conjecture for $q = p^h$ whenever $k \le p$ (and when $k \le 2p - 2$ for $h = 2$, and $k \le \sqrt{q}/2 + \dots$ in various regimes).
  - For $q = p^2$ (squares), Ball and De Beule (2012) proved $n \le q + 1$ for $k \le 2\sqrt{q} - 2$.
  - For general non-prime $q = p^h$ ($h \ge 2$) and intermediate dimensions $p < k < q - p$, the conjecture remains **open**.
- **Nonlinear MDS codes:** Notice the conjecture above is specifically for *linear* MDS codes; for general (nonlinear) MDS codes over a $q$-ary alphabet, the analogous bound also remains open in general (settled for small $q$ and small $k$).

## References

- R. C. Bose, "Mathematical theory of the symmetrical factorial design," *Sankhyā*, 8(2):107–166, 1947.
- B. Segre, "Curve razionali normali e $k$-archi negli spazi finiti," *Annali di Matematica Pura ed Applicata*, 39:357–379, 1955.
- L. R. A. Casse and D. G. Glynn, "The solution to Beniamino Segre's problem $I_{r,q}$, $r = 3$, $q = 2^h$," *Geometriae Dedicata*, 13:157–163, 1982.
- L. R. A. Casse and D. G. Glynn, "On the uniqueness of $(q+1)_4$-arcs of $\mathrm{PG}(4,q)$, $q = 2^h$, $h \ge 3$," *Discrete Mathematics*, 48:173–186, 1984.
- S. Ball, "On sets of vectors of a finite vector space in which every subset of basis size is a basis," *Journal of the European Mathematical Society*, 14(3):733–748, 2012.
- S. Ball and J. De Beule, "On sets of vectors of a finite vector space in which every subset of basis size is a basis II," *Designs, Codes and Cryptography*, 65:5–14, 2012.
