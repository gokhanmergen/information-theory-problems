---
id: quantum-ldpc-rate-distance
title: Optimal Rate–Distance Tradeoff for Constant-Weight Quantum LDPC Codes
status: partially-solved
formal_status: claimed-resolved
formal_status_note: 2026 preprints (Mittal–Srivastava–Tulsiani–Wootters arXiv:2610.02648; Kasai arXiv:2603.24588) construct constant-check-weight qLDPC codes approaching the quantum GV bound; CSS-specific verification pending.
category: coding-theory
posed_by: Pavel Panteleev and Gleb Kalachev; Anthony Leverrier and Gilles Zémor (folklore)
posed_year: 2022
tags: [coding-theory, quantum-ldpc, css-codes, gilbert-varshamov]
lean_module: InfoTheory.Problems.QuantumLdpcRateDistance
lean_file: lean/InfoTheory/Problems/QuantumLdpcRateDistance.lean
---

## Statement

A **Calderbank–Shor–Steane (CSS) quantum code** on $n$ physical qubits is defined by a pair of binary parity-check matrices $H_X \in \mathbb{F}_2^{m_X \times n}$ and $H_Z \in \mathbb{F}_2^{m_Z \times n}$ satisfying the orthogonality (commutativity) condition $H_X H_Z^T = 0$. The number of encoded logical qubits is $k = n - \mathrm{rank}(H_X) - \mathrm{rank}(H_Z)$, the rate is $R = k/n$, and the CSS minimum distance is $d = \min(d_X, d_Z)$, where
$$d_Z = \min \{ \mathrm{wt}(v) \mid v \in \ker(H_X) \setminus \mathrm{row}(H_Z) \}, \qquad d_X = \min \{ \mathrm{wt}(v) \mid v \in \ker(H_Z) \setminus \mathrm{row}(H_X) \}.$$
A CSS code is **$w$-LDPC** if every row and every column of both $H_X$ and $H_Z$ has Hamming weight at most $w$.

For dense (non-LDPC) random CSS codes, Calderbank and Shor (1996) established the **CSS Gilbert–Varshamov bound**: for every relative distance $\delta \in (0, h^{-1}(1/2))$ (where $h^{-1}(1/2) \approx 0.110028$), there exist CSS codes achieving asymptotic rate $R = 1 - 2 h(\delta)$.

**Open Problem:** Can constant-check-weight **quantum LDPC (CSS)** codes achieve the CSS Gilbert–Varshamov rate–distance tradeoff $R = 1 - 2 h(\delta)$? That is, for every $\delta \in (0, 1/2)$ with $1 - 2 h(\delta) > 0$ and every $\varepsilon > 0$, does there exist a constant check weight $w \in \mathbb{N}$ such that for infinitely many blocklengths $n$, there exists a $w$-LDPC CSS code of blocklength $n$ with rate $k/n \ge 1 - 2 h(\delta) - \varepsilon$ and CSS distance $d \ge \delta n$?

## Background

For over two decades following Kitaev's toric code and Gottesman's stabilizer formalism, the central open problem in quantum coding theory was the **qLDPC conjecture**: whether *asymptotically good* quantum LDPC codes (constant check weight $w = O(1)$, linear dimension $k = \Theta(n)$, and linear distance $d = \Theta(n)$) exist at all. Classical LDPC codes achieve $k = \Theta(n), d = \Theta(n)$—and even approach the classical Gilbert–Varshamov bound $1 - h(\delta)$ as $w \to \infty$ (Gallager 1962)—but the CSS commutativity constraint $H_X H_Z^T = 0$ defeated random sparse constructions.

In 2021–2022, Panteleev and Kalachev (STOC 2022), followed closely by Leverrier and Zémor (FOCS 2022) and Dinur, Hsieh, Lin, and Vidick (STOC 2023), famously resolved the qLDPC conjecture by constructing explicit families of asymptotically good qLDPC codes via lifted products / balanced products of classical Tanner codes on left–right Cayley complexes. However, the resulting rate–distance curves lie far below the CSS Gilbert–Varshamov bound $1 - 2 h(\delta)$ (and even further below the general non-CSS quantum GV bound $1 - h(\delta) - \delta \log_2 3$). Determining the optimal rate–distance tradeoff of constant-weight qLDPC codes—and in particular whether they can reach $1 - 2 h(\delta)$ as $w$ grows—is the premier post-breakthrough open problem in quantum coding theory.

## What is known

- **Existence of asymptotically good qLDPC codes (solved 2022):**
  - Tillich and Zémor (2014): hypergraph product codes with $k = \Theta(n)$, $d = \Theta(\sqrt{n})$, $w = O(1)$.
  - Hastings, Haah, and O'Donnell (2021), Panteleev and Kalachev (2021), and Breuckmann and Eberhardt (2021): broke the $\sqrt{n}$ distance barrier via fiber bundle and balanced product codes.
  - Panteleev and Kalachev (STOC 2022): first proof of asymptotically good qLDPC codes ($k = \Theta(n)$, $d = \Theta(n)$, $w = O(1)$) using lifted products over non-abelian groups.
  - Leverrier and Zémor (FOCS 2022) and Dinur, Hsieh, Lin, and Vidick (STOC 2023): Quantum Tanner codes with simpler analysis and linear-time decoders.
- **Rate–distance tradeoffs for qLDPC codes:**
  - The explicit constants in Panteleev–Kalachev and Quantum Tanner codes yield very small relative distances $\delta$ for a given rate $R$ (orders of magnitude below $1 - 2 h(\delta)$) and require large check weights $w$.
  - For classical LDPC codes, Gallager (1962) proved that regular $w$-LDPC codes approach the classical Gilbert–Varshamov bound $1 - h(\delta)$ as $w \to \infty$.
  - Recent work (e.g., distance-amplification and concatenated/random-product qLDPC constructions, such as Bergamaschi–Golowich–Gunn 2024 and related works) has improved rate–distance tradeoffs in specific regimes (such as near $R \to 1$ or near $R \to 0$), but achieving the full CSS Gilbert–Varshamov curve $R = 1 - 2 h(\delta)$ with constant check weight $w = O_{\delta, \varepsilon}(1)$ remains open.
  - **2026 preprints claiming resolution:** T. Mittal, S. Srivastava, M. Tulsiani, and M. Wootters (`arXiv:2610.02648`, Oct. 2026) construct random constant-check-weight $p$-ary qLDPC ensembles (for every prime $p \ge 2$) approaching the quantum Gilbert–Varshamov bound via expander-based distance amplification and quantum Thommesen concatenation; K. Kasai (`arXiv:2603.24588`, Mar. 2026) also claims finite-degree nested CSS qLDPC codes reaching the CSS GV bound. Independent peer review and verification of the exact CSS $1 - 2h(\delta)$ statement remain pending.
- **Upper bounds:** The quantum Singleton bound gives $R \le 1 - 2\delta$ (Rains 1999), and quantum LP bounds (Ashikhmin–Litsyn 1999) tighten this further for general (not necessarily LDPC) quantum codes.

## References

- A. R. Calderbank and P. W. Shor, "Good quantum error-correcting codes exist," *Physical Review A*, 54(2):1098–1105, 1996.
- A. Ashikhmin and S. Litsyn, "Upper bounds on the size of quantum codes," *IEEE Trans. Inf. Theory*, 45(4):1206–1215, 1999.
- J.-P. Tillich and G. Zémor, "Quantum LDPC codes with positive rate and minimum distance proportional to the square root of the blocklength," *IEEE Trans. Inf. Theory*, 60(2):1193–1202, 2014.
- M. B. Hastings, J. Haah, and R. O'Donnell, "Fiber bundle codes: Breaking the $N^{1/2}\operatorname{polylog}(N)$ barrier for quantum LDPC codes," *Proc. 53rd ACM STOC*, pp. 1276–1288, 2021.
- P. Panteleev and G. Kalachev, "Asymptotically good quantum and locally testable classical LDPC codes," *Proc. 54th ACM STOC*, pp. 375–388, 2022.
- A. Leverrier and G. Zémor, "Quantum Tanner codes," *Proc. 63rd IEEE FOCS*, pp. 872–883, 2022.
- I. Dinur, M.-H. Hsieh, T.-C. Lin, and T. Vidick, "Good quantum LDPC codes with linear time decoders," *Proc. 55th ACM STOC*, pp. 905–918, 2023.
