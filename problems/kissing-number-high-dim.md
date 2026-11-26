---
id: kissing-number-high-dim
title: Asymptotic Exponential Growth Rate of the High-Dimensional Kissing Number
status: open
category: coding-theory
posed_by: Claude E. Shannon; Aaron D. Wyner; Grigorii A. Kabatiansky and Vladimir I. Levenshtein
posed_year: 1959
tags: [coding-theory, spherical-codes, kissing-number, sphere-packing]
lean_module: InfoTheory.Problems.KissingNumberHighDim
lean_file: lean/InfoTheory/Problems/KissingNumberHighDim.lean
---

## Statement

The **kissing number** $\tau(d)$ in $\mathbb{R}^d$ is the maximum number of non-overlapping unit spheres that can simultaneously touch a central unit sphere in $\mathbb{R}^d$; equivalently, it is the maximum size of a spherical code $X \subseteq S^{d-1}$ with minimum angular separation at least $\pi/3$, i.e., $\langle x, y \rangle \le 1/2$ for all distinct $x, y \in X$.

It is known that $\tau(d)$ grows exponentially in $d$, with
$$\log_2\!\left(\frac{2}{\sqrt{3}}\right) \approx 0.207519 \le \liminf_{d \to \infty} \frac{1}{d} \log_2 \tau(d) \le \limsup_{d \to \infty} \frac{1}{d} \log_2 \tau(d) \le 0.401414.$$

**Open Problem:** Determine the exact asymptotic exponential growth rate $\lim_{d \to \infty} \frac{1}{d} \log_2 \tau(d)$ of the Euclidean kissing number. In particular, **does the exponential growth rate strictly exceed the Chabauty–Shannon–Wyner lower bound $\log_2(2/\sqrt{3})$**, i.e., does there exist $\varepsilon > 0$ such that $\frac{1}{d} \log_2 \tau(d) \ge \log_2(2/\sqrt{3}) + \varepsilon$ for infinitely many dimensions $d$?

## Background

The kissing number problem is the spherical-code analogue of the binary Gilbert–Varshamov problem and is intimately linked to high-dimensional sphere packing and the capacity of the additive white Gaussian noise (AWGN) channel at low signal-to-noise ratio (Shannon 1959; Wyner 1965). Just as no binary code has beaten the Gilbert–Varshamov exponential rate since 1952, no spherical code of angular separation $\pi/3$ has improved the exponential base $2/\sqrt{3}$ since Chabauty (1953), Shannon (1959), and Wyner (1965), and no upper bound has improved the exponential constant $0.401414$ since Kabatiansky and Levenshtein (1978).

Either proving $\limsup_{d \to \infty} \frac{1}{d} \log_2 \tau(d) > \log_2(2/\sqrt{3})$ or disproving it (which would settle the exact asymptotic growth rate at $\log_2(2/\sqrt{3})$) would represent a major breakthrough in discrete geometry and coding theory.

## What is known

- **Exact low-dimensional values:** $\tau(1) = 2$, $\tau(2) = 6$, $\tau(3) = 12$ (Schütte–van der Waerden 1953), $\tau(4) = 24$ (Musin 2008), $\tau(8) = 240$ ($E_8$ lattice, Odlyzko–Sloane 1979; Levenshtein 1979), $\tau(24) = 196560$ (Leech lattice, Odlyzko–Sloane 1979; Levenshtein 1979). All other dimensions $d \ge 5$ ($d \neq 8, 24$) remain open.
- **Asymptotic lower bounds:**
  - Chabauty (1953), Shannon (1959), and Wyner (1965): greedy sphere covering gives $\tau(d) \ge \Omega\!\left(\sqrt{d}\,(2/\sqrt{3})^d\right)$, yielding exponential rate $\log_2(2/\sqrt{3}) = 1 - \frac{1}{2}\log_2 3 \approx 0.207519$.
  - Jenssen, Joos, and Perkins (2018) improved the polynomial prefactor by a linear factor in $d$, proving $\tau(d) \ge \Omega\!\left(d^{3/2} (2/\sqrt{3})^d\right)$ using the hard-sphere model from statistical mechanics.
  - Fernández, Kim, Liu, and Pikhurko (2024) further improved the leading constant in front of $d^{3/2}(2/\sqrt{3})^d$, without changing the exponential base $2/\sqrt{3}$.
- **Asymptotic upper bounds:**
  - Rankin (1955): $\frac{1}{d}\log_2 \tau(d) \le 0.5 + o(1)$.
  - Kabatiansky and Levenshtein (1978): using Delsarte's linear programming method with Gegenbauer polynomials, proved
    $$\limsup_{d \to \infty} \frac{1}{d} \log_2 \tau(d) \le \frac{1 + \sin \theta^*}{2 \sin \theta^*} \log_2 \frac{1 + \sin \theta^*}{2 \sin \theta^*} - \frac{1 - \sin \theta^*}{2 \sin \theta^*} \log_2 \frac{1 - \sin \theta^*}{2 \sin \theta^*} \approx 0.401414$$
    (evaluated at $\theta^* = \pi/3$, i.e., $\sin \theta^* = \sqrt{3}/2$? More precisely, Kabatiansky–Levenshtein's first bound for angle $\phi = \pi/3$ gives $\approx 0.401414$ via $\beta(\phi)$). This upper bound has stood unimproved for nearly five decades.
  - Cohn and Zhao (2014) showed that the Kabatiansky–Levenshtein kissing-number bound also implies the best known asymptotic upper bound on Euclidean sphere-packing density (up to a factor of $2$ in the linear programming framework).

## References

- C. Chabauty, "Résultats sur l'empilement de calottes égales sur une périsphère de $\mathbb{R}^n$ et correction à un travail antérieur," *C. R. Acad. Sci. Paris*, 236:1462–1464, 1953.
- C. E. Shannon, "Probability of error for optimal codes in a Gaussian channel," *Bell System Technical Journal*, 38(3):611–656, 1959.
- A. D. Wyner, "Capabilities of bounded discrepancy decoding," *Bell System Technical Journal*, 44(6):1061–1122, 1965.
- G. A. Kabatiansky and V. I. Levenshtein, "Bounds for packings on a sphere and in space," *Problems of Information Transmission*, 14(1):1–17, 1978.
- O. R. Musin, "The kissing number in four dimensions," *Annals of Mathematics*, 168(1):1–32, 2008.
- H. Cohn and Y. Zhao, "Sphere packing bounds via spherical codes," *Duke Mathematical Journal*, 163(10):1965–2002, 2014.
- M. Jenssen, F. Joos, and W. Perkins, "On kissing numbers and spherical codes in high dimensions," *Advances in Mathematics*, 335:307–321, 2018.
- I. Gil Fernández, J. Kim, H. Liu, and O. Pikhurko, "New lower bound on kissing numbers in high dimensions," *arXiv:2311.04058*, 2023.
