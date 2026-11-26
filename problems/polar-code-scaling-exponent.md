---
id: polar-code-scaling-exponent
title: Optimal Scaling Exponent of Binary Polar Codes with Finite Kernels on the BSC
status: partially-solved
category: coding-theory
posed_by: Erdal Arıkan; S. Hamed Hassani, Kasra Alishahi, and Rüdiger L. Urbanke
posed_year: 2014
tags: [coding-theory, polar-codes, scaling-exponent, finite-blocklength]
lean_module: InfoTheory.Problems.PolarCodeScalingExponent
lean_file: lean/InfoTheory/Problems/PolarCodeScalingExponent.lean
---

## Statement

Let $G \in \mathrm{GL}_\ell(\mathbb{F}_2)$ be an invertible $\ell \times \ell$ binary polarization kernel. For $m \ge 1$, the polar transform $G^{\otimes m}$ maps $u \in \mathbb{F}_2^{\ell^m}$ to $x = u G^{\otimes m} \in \mathbb{F}_2^{\ell^m}$ of blocklength $N = \ell^m$. A polar code of dimension $|A|$ is specified by an information set $A \subseteq \{0, \dots, \ell - 1\}^m$ (with frozen bits outside $A$ fixed to $0$) and decoded sequentially by **successive cancellation (SC) decoding** in the natural lexicographic order.

For a binary-input memoryless symmetric channel $W$ with capacity $C(W)$ and target block error probability $\eta \in (0, 1)$, the **scaling exponent** $\mu(G, W)$ is the infimum of all $\mu > 0$ such that polar codes with kernel $G$ achieve block error probability $\le \eta$ at rate $R \ge C(W) - O(N^{-1/\mu})$ (equivalently, blocklength $N = O((C(W) - R)^{-\mu})$). By Strassen's (1962) and Polyanskiy–Poor–Verdú's (2010) finite-blocklength dispersion theorem, no code family over any non-trivial channel can beat $\mu = 2$.

**Open Problem (Hassani–Alishahi–Urbanke 2014):** On the binary symmetric channel $\mathrm{BSC}(p)$ for any $p \in (0, 1/2)$, can binary polar codes with a **single fixed finite-size binary kernel** $G \in \mathrm{GL}_\ell(\mathbb{F}_2)$ under successive cancellation decoding achieve scaling exponent $\mu(G, \mathrm{BSC}(p))$ arbitrarily close to the optimal value $\mu = 2$? That is, for every $p \in (0, 1/2)$, $\varepsilon > 0$, and $\eta \in (0, 1)$, does there exist a finite binary kernel $G \in \mathrm{GL}_\ell(\mathbb{F}_2)$ achieving SC block error $\le \eta$ at rate $1 - h(p) - O(N^{-1/(2+\varepsilon)})$ for all sufficiently large $N = \ell^m$?

## Background

Polar codes (Arıkan 2009) were the first explicit family of error-correcting codes provably achieving the Shannon capacity of every BMS channel with $O(N \log N)$ encoding and SC decoding complexity. However, for Arıkan's original $2 \times 2$ kernel $G_2 = \begin{pmatrix} 1 & 0 \\ 1 & 1 \end{pmatrix}$, the convergence of rate to capacity as a function of blocklength $N$ is significantly slower than the optimal random-coding scaling $N = O((C - R)^{-2})$: on the BEC, $\mu(G_2, \mathrm{BEC}) \approx 3.627$, and on general BMS channels $\mu(G_2, W)$ can be larger still.

Understanding whether large fixed binary kernels $G \in \mathrm{GL}_\ell(\mathbb{F}_2)$ drive the scaling exponent all the way down to $\mu \to 2$ on the BSC (and general BMS channels) bridges the gap between explicit $O(N \log N)$-decodable codes and the fundamental second-order dispersion limit of information theory.

## What is known

- **Universal lower bound:** For any channel with positive dispersion $V(W) > 0$, every code family has scaling exponent $\mu \ge 2$ (Strassen 1962; Polyanskiy–Poor–Verdú 2010).
- **Arıkan's $2 \times 2$ kernel:**
  - Hassani, Alishahi, and Urbanke (2014) proved that for $G_2$ on any BMS channel, $3.579 \le \mu(G_2, W) \le 6$, and showed $\mu(G_2, \mathrm{BEC}) \approx 3.627$.
  - Mondelli, Hassani, and Urbanke (2016) improved the upper bound for $G_2$ on all BMS channels to $\mu(G_2, W) \le 4.714$, and later Wang, Duursma, and Riazanov tightened it further to $\mu \le 4.63$.
- **Erasure channels (solved):**
  - Pfister and Urbanke (2016) proved that over large $q$-ary alphabets, Reed–Solomon kernels achieve $\mu \to 2$ on the $q$-ary erasure channel.
  - Fazeli, Hassani, Mondelli, and Vardy (2021) proved that **binary** polar codes with large fixed binary kernels $G \in \mathrm{GL}_\ell(\mathbb{F}_2)$ achieve scaling exponent arbitrarily close to $2$ on the **BEC**.
- **General BMS / BSC channels (dynamic / non-binary / multiple kernels vs fixed single binary kernel):**
  - Guruswami, Riazanov, and Ye (2020) and Wang and Duursma (2021) constructed polar-type codes achieving $\mu \to 2$ on general BMS channels (including the BSC) using **dynamic / varying sequences of binary kernels** (or growing alphabets) combined with channel polarization analysis.
  - Achieving $\mu \to 2$ on the $\mathrm{BSC}(p)$ using a **single fixed static binary kernel** $G \in \mathrm{GL}_\ell(\mathbb{F}_2)$ (Hassani's conjecture for static binary kernels on BSC) remains open.

## References

- E. Arıkan, "Channel polarization: A method for constructing capacity-achieving codes for symmetric binary-input memoryless channels," *IEEE Trans. Inf. Theory*, 55(7):3051–3073, 2009.
- Y. Polyanskiy, H. V. Poor, and S. Verdú, "Channel coding rate in the finite blocklength regime," *IEEE Trans. Inf. Theory*, 56(5):2307–2359, 2010.
- S. H. Hassani, K. Alishahi, and R. L. Urbanke, "Finite-length scaling for polar codes," *IEEE Trans. Inf. Theory*, 60(10):5875–5898, 2014.
- M. Mondelli, S. H. Hassani, and R. L. Urbanke, "Unified scaling of polar codes: Error exponent, scaling exponent, moderate deviations, and error floors," *IEEE Trans. Inf. Theory*, 62(12):6698–6712, 2016.
- H. D. Pfister and R. Urbanke, "Near-optimal finite-length scaling for polar codes over large alphabets," *Proc. IEEE ISIT*, pp. 215–219, 2016.
- V. Guruswami, A. Riazanov, and M. Ye, "Arikan meets Shannon: Polar codes with near-optimal convergence to channel capacity," *Proc. 52nd ACM STOC*, pp. 552–564, 2020.
- A. Fazeli, H. Hassani, M. Mondelli, and A. Vardy, "Binary linear codes with optimal scaling: Polar codes with large kernels," *IEEE Trans. Inf. Theory*, 67(9):5693–5710, 2021.
