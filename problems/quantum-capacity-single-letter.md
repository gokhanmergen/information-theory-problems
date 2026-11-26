---
id: quantum-capacity-single-letter
title: Bounded-Letter Regularization and Computability of Quantum Capacity
status: open
category: quantum-info
posed_by: David P. DiVincenzo, Peter W. Shor, and John A. Smolin
posed_year: 1998
tags: [quantum-information, quantum-capacity, single-letterization, computability]
lean_module: InfoTheory.Problems.QuantumCapacitySingleLetter
lean_file: lean/InfoTheory/Problems/QuantumCapacitySingleLetter.lean
---

## Statement

For a finite-dimensional CPTP quantum channel $\mathcal{N} : \mathcal{M}_{d_1}(\mathbb{C}) \to \mathcal{M}_{d_2}(\mathbb{C})$, let
$$
Q^{(n)}(\mathcal{N}) := \max_{\rho \in \mathcal{D}(\mathbb{C}^{d_1^n})} I_c(\rho, \mathcal{N}^{\otimes n})
$$
denote its $n$-letter coherent information, so that the quantum capacity is $Q(\mathcal{N}) = \sup_{n \ge 1} \frac{1}{n} Q^{(n)}(\mathcal{N})$.

**Determine whether for every fixed pair of finite dimensions $(d_1, d_2)$ there exists a uniform finite regularization horizon $k = k(d_1, d_2) \ge 1$ such that**
$$
Q(\mathcal{N}) = \frac{1}{k} Q^{(k)}(\mathcal{N})
$$
**for all quantum channels $\mathcal{N} : \mathcal{M}_{d_1}(\mathbb{C}) \to \mathcal{M}_{d_2}(\mathbb{C})$.** More broadly, determine whether $Q(\mathcal{N})$ is algorithmically computable (to arbitrary additive precision) given a description of $\mathcal{N}$.

## Background

In classical information theory, Shannon's channel capacity $C(W) = \max_{P_X} I(X; Y)$ is a single-letter convex optimization problem and is therefore efficiently computable. In quantum Shannon theory, the Lloyd–Shor–Devetak theorem expresses the quantum capacity $Q(\mathcal{N})$ only as an infinite regularization $\lim_{n \to \infty} \frac{1}{n} Q^{(n)}(\mathcal{N})$. Because coherent information is non-additive in general, no finite-letter formula is known even for qubit channels ($d_1 = d_2 = 2$).

Whether there exists a bounded-letter characterization $k(d_1, d_2) < \infty$ — or even whether the decision problem "$Q(\mathcal{N}) > 0$?" is decidable — is one of the deepest foundational questions in quantum information theory.

## What is known

- **Single-letter special cases:** For **degradable** channels (Devetak–Shor 2005), coherent information is additive and $Q(\mathcal{N}) = Q^{(1)}(\mathcal{N})$. For **anti-degradable** and **PPT (entanglement-binding)** channels, $Q(\mathcal{N}) = 0$.
- **Non-additivity ($k = 1$ fails):** DiVincenzo–Shor–Smolin (1998) proved $Q^{(5)}(\mathcal{D}_p)/5 > Q^{(1)}(\mathcal{D}_p)$ for the qubit depolarizing channel. Smith–Smolin (2007) and Leditzky–Leung–Smith (2018) gave simpler low-dimensional examples (such as the qubit dephrasure channel, where $Q^{(2)}/2 > Q^{(1)}$).
- **Unbounded regularization across growing dimensions:** Cubitt, Elkouss, Matthews, Ozols, Pérez-García, and Strelchuk (2015) proved that for every integer $n \ge 1$ there exists a quantum channel $\mathcal{N}_n$ (whose Hilbert space dimension grows with $n$) such that $Q^{(n)}(\mathcal{N}_n) = 0$ while $Q(\mathcal{N}_n) > 0$. Consequently, no single dimension-independent $k$ works for all channels simultaneously.
- **Fixed dimension remains open:** For any fixed finite dimensions $(d_1, d_2)$ — and in particular for qubit-to-qubit channels $(d_1, d_2) = (2, 2)$ — it remains open whether a uniform finite $k(d_1, d_2)$ exists, or whether $Q(\mathcal{N})$ can require arbitrarily large blocklengths $n$ within fixed dimension.
- **Computability:** Because no general computable upper bound converging to $Q(\mathcal{N})$ is known, it is not even known whether $Q(\mathcal{N})$ is Turing-computable, nor whether testing $Q(\mathcal{N}) > 0$ is decidable (Wolf–Pérez-García 2007; Cubitt et al. 2015).

## References

- D. P. DiVincenzo, P. W. Shor, and J. A. Smolin, "Quantum-channel capacity of very noisy channels," *Phys. Rev. A* **57**, 830–839 (1998).
- I. Devetak and P. W. Shor, "The capacity of a quantum channel for simultaneous transmission of classical and quantum information," *Commun. Math. Phys.* **256**, 287–303 (2005).
- G. Smith and J. A. Smolin, "Degenerate quantum codes for Pauli channels," *Phys. Rev. Lett.* **98**, 030501 (2007).
- T. Cubitt, D. Elkouss, W. Matthews, M. Ozols, D. Pérez-García, and S. Strelchuk, "Unbounded number of channel uses may be required to detect quantum capacity," *Nature Commun.* **6**, 6739 (2015).
- F. Leditzky, D. Leung, and G. Smith, "Dephrasure channel and superadditivity of coherent information," *Phys. Rev. Lett.* **121**, 160501 (2018).
- F. Leditzky, D. Leung, V. Siddhu, G. Smith, and J. A. Smolin, "Generic nonadditivity of quantum capacity in simple channels," *IEEE Trans. Inf. Theory* **69**(6), 3825–3849 (2023).
