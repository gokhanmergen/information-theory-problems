---
id: quantum-capacity-two-pauli
title: Exact Quantum Capacity and Positivity Threshold of the Qubit Two-Pauli Channel
status: open
category: quantum-info
posed_by: David P. DiVincenzo, Peter W. Shor, and John A. Smolin
posed_year: 1998
tags: [quantum-information, quantum-capacity, pauli-channel, superadditivity]
lean_module: InfoTheory.Problems.QuantumCapacityTwoPauli
lean_file: lean/InfoTheory/Problems/QuantumCapacityTwoPauli.lean
---

## Statement

The qubit **two-Pauli channel** $\mathcal{N}_p : \mathcal{M}_2(\mathbb{C}) \to \mathcal{M}_2(\mathbb{C})$ with noise parameter $p \in [0, 1]$ acts on a $2 \times 2$ density matrix $\rho$ by
$$
\mathcal{N}_p(\rho) = (1 - p)\rho + \frac{p}{2}(X \rho X + Z \rho Z),
$$
applying a bit-flip ($X$) or phase-flip ($Z$) error each with probability $p/2$ and no $Y$ error.

**Determine the exact quantum capacity $Q(\mathcal{N}_p)$ for all $p \in [0, 1]$, and in particular determine the exact zero-capacity threshold**
$$
p_0 := \inf \{ p \in [0, 1] : Q(\mathcal{N}_p) = 0 \}.
$$

The accompanying Lean statement formalizes the central threshold question: whether $p_0$ is strictly smaller than the no-cloning (anti-degradability) threshold $1/3$, i.e., whether there exists $p \in (0, 1/3)$ with $Q(\mathcal{N}_p) = 0$.

## Background

Alongside the depolarizing channel, the qubit two-Pauli channel is the simplest non-degradable Pauli channel for which single-letter coherent information is strictly suboptimal. Because it has only three Kraus operators (versus four for the depolarizing channel), its complementary channel has a smaller environment dimension ($d_E = 3$), making it a favorite testing ground for degenerate quantum error-correcting codes, neural quantum codes, and upper-bound techniques.

Yet just as for the depolarizing channel, neither the exact quantum capacity curve $p \mapsto Q(\mathcal{N}_p)$ nor the zero-capacity noise threshold $p_0$ is known.

## What is known

- **Single-letter hashing bound:** For maximally mixed input $\rho = I/2$, the single-letter coherent information is $I_c(I/2, \mathcal{N}_p) = 1 - H(1 - p, p/2, p/2) = 1 - h(p) - p$, which vanishes at $p_1 \approx 0.22709$.
- **Superadditivity and lower bounds on $p_0$:** DiVincenzo, Shor, and Smolin (1998), Smith and Smolin (2007), and Fern and Whaley (2008) showed that degenerate repetition codes achieve strictly positive coherent information per channel use beyond $p_1$, proving $p_0 > 0.22709$ (with concatenated / degenerate codes pushing $p_0$ slightly higher, above $0.2272$).
- **No-cloning / anti-degradability upper bound ($p_0 \le 1/3$):** For $p \ge 1/3$, the Choi state of $\mathcal{N}_p$ is symmetrically $2$-extendible (Cerf 2000; Smith–Smolin 2008; Myhr–Lütkenhaus 2009), so $\mathcal{N}_p$ is anti-degradable and hence $Q(\mathcal{N}_p) = 0$ for all $p \ge 1/3$.
- **Entanglement-breaking threshold:** $\mathcal{N}_p$ is entanglement-breaking (separable Choi state) for $p \ge 1/2$.
- **Open gap:** For $p \in (0.2272, 1/3)$, upper bounds via degradable extensions (Smith–Smolin 2008), approximate degradability (Sutter et al. 2017), and quantum flags improve the quantitative upper bound on $Q(\mathcal{N}_p)$, but none vanish strictly below $p = 1/3$. Determining whether $p_0 < 1/3$ or $p_0 = 1/3$ remains completely open.

## References

- D. P. DiVincenzo, P. W. Shor, and J. A. Smolin, "Quantum-channel capacity of very noisy channels," *Phys. Rev. A* **57**, 830–839 (1998).
- N. J. Cerf, "Pauli cloning of a quantum bit," *Phys. Rev. Lett.* **84**, 4497–4500 (2000).
- G. Smith and J. A. Smolin, "Degenerate quantum codes for Pauli channels," *Phys. Rev. Lett.* **98**, 030501 (2007).
- J. Fern and K. B. Whaley, "Lower bounds on the nonzero capacity for Pauli channels," *Phys. Rev. A* **78**, 062335 (2008).
- G. Smith and J. A. Smolin, "Additive extensions of a quantum channel," *IEEE Inf. Theory Workshop (ITW)*, 368–372 (2008).
- G. O. Myhr and N. Lütkenhaus, "Spectrum conditions for symmetric extendible states," *Phys. Rev. A* **79**, 062307 (2009).
- D. Sutter, V. B. Scholz, A. Winter, and R. Renner, "Approximate degradable quantum channels," *IEEE Trans. Inf. Theory* **63**(12), 7832–7844 (2017).
