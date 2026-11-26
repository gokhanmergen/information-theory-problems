---
id: private-vs-quantum-capacity-gap
title: Zero-Quantum-Capacity Qubit Channels with Positive Private Capacity
status: open
category: quantum-info
posed_by: Karol Horodecki, Michał Horodecki, Paweł Horodecki, and Jonathan Oppenheim
posed_year: 2005
tags: [quantum-information, private-capacity, quantum-capacity, qubit-channels]
lean_module: InfoTheory.Problems.PrivateVsQuantumCapacityGap
lean_file: lean/InfoTheory/Problems/PrivateVsQuantumCapacityGap.lean
---

## Statement

For a finite-dimensional quantum channel $\mathcal{N} : \mathcal{M}_{d_1}(\mathbb{C}) \to \mathcal{M}_{d_2}(\mathbb{C})$, its quantum capacity $Q(\mathcal{N})$ and private classical capacity $P(\mathcal{N})$ always satisfy $0 \le Q(\mathcal{N}) \le P(\mathcal{N})$.

**Determine whether there exists a qubit-to-qubit quantum channel $\mathcal{N} : \mathcal{M}_2(\mathbb{C}) \to \mathcal{M}_2(\mathbb{C})$ having zero quantum capacity yet strictly positive private capacity:**
$$
Q(\mathcal{N}) = 0 \qquad \text{and} \qquad P(\mathcal{N}) > 0.
$$
More broadly, determine the maximum possible separation $P(\mathcal{N}) - Q(\mathcal{N})$ (and maximum ratio when $Q(\mathcal{N}) > 0$) as a function of channel dimension $d$.

## Background

Because maximally entangled states yield secret keys upon local measurement, every quantum communication protocol also yields a private classical communication protocol, so $Q(\mathcal{N}) \le P(\mathcal{N})$. For several years it was speculated that privacy and quantum coherence were operationally equivalent ($Q(\mathcal{N}) > 0 \iff P(\mathcal{N}) > 0$). Horodecki, Horodecki, Horodecki, and Oppenheim (2005) refuted this intuition by constructing *private states* (pbits) with bound (PPT) entanglement, inducing quantum channels of dimension $d \ge 4$ with $Q(\mathcal{N}) = 0$ and $P(\mathcal{N}) > 0$.

For qubit-to-qubit channels ($d_1 = d_2 = 2$), however, all PPT bipartite states are separable, so Horodecki-type PPT constructions cannot produce a $Q = 0, P > 0$ qubit channel. Resolving the qubit case would clarify whether private capacity can strictly outlive quantum capacity in the smallest non-trivial quantum system.

## What is known

- **Separation in higher dimensions ($d \ge 4$):**
  - Horodecki, Horodecki, Horodecki, and Oppenheim (2005, 2008) constructed PPT channels (acting on $d \ge 4$) with $Q(\mathcal{N}) = 0$ and $P(\mathcal{N}) > 0$.
  - Smith and Smolin (2009) and Li, Winter, Zou, and Guo (2009) showed that private capacity is extensively non-additive and can greatly exceed quantum capacity.
  - Leung, Li, Smith, and Smolin (2014) constructed channels in dimension $d$ with $Q(\mathcal{N}) \le 1$ (or $Q(\mathcal{N}) = 0$ via PPT constructions) and $P(\mathcal{N}) = \Omega(\log d)$ (up to $\frac{1}{2}\log_2 d - O(1)$), establishing near-maximal separation in high dimension.
- **Qubit channels ($d_1 = d_2 = 2$):**
  - If $\mathcal{N}$ is degradable, $Q(\mathcal{N}) = P(\mathcal{N})$ (Smith 2008).
  - If $\mathcal{N}$ is anti-degradable or entanglement-breaking, $Q(\mathcal{N}) = P(\mathcal{N}) = 0$.
  - For the qubit depolarizing channel $\mathcal{D}_p$, it is known that $P(\mathcal{D}_p) > Q^{(1)}(\mathcal{D}_p)$ in certain regimes, and $P(\mathcal{D}_p) = 0$ for $p \ge 1/4$ (anti-degradable). Whether there is a noise interval $p \in (p_0, 1/4)$ where $Q(\mathcal{D}_p) = 0$ while $P(\mathcal{D}_p) > 0$, or whether *any* qubit channel satisfies $Q(\mathcal{N}) = 0 < P(\mathcal{N})$, remains completely open.

## References

- K. Horodecki, M. Horodecki, P. Horodecki, and J. Oppenheim, "Secure key from bound entanglement," *Phys. Rev. Lett.* **94**, 160502 (2005).
- K. Horodecki, M. Horodecki, P. Horodecki, D. Leung, and J. Oppenheim, "Quantum key distribution based on private states: Unconditional security over untrusted channels with zero quantum capacity," *IEEE Trans. Inf. Theory* **54**(6), 2604–2620 (2008).
- G. Smith, "Private classical capacity with a symmetric side channel and its application to quantum cryptography," *Phys. Rev. A* **78**, 022306 (2008).
- G. Smith and J. A. Smolin, "Extensive nonadditivity of privacy," *Phys. Rev. Lett.* **103**, 120503 (2009).
- K. Li, A. Winter, X. Zou, and G. Guo, "Private capacity of quantum channels is not additive," *Phys. Rev. Lett.* **103**, 120501 (2009).
- D. Leung, K. Li, G. Smith, and J. A. Smolin, "Maximal privacy without coherence," *Phys. Rev. Lett.* **113**, 030502 (2014).
