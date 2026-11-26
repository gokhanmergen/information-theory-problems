---
id: quantum-capacity-depolarizing
title: Exact Quantum Capacity and Zero-Capacity Threshold of the Qubit Depolarizing Channel
status: open
category: quantum-info
posed_by: Charles H. Bennett, David P. DiVincenzo, John A. Smolin, and William K. Wootters
posed_year: 1996
tags: [quantum-information, quantum-capacity, depolarizing-channel, superadditivity]
lean_module: InfoTheory.Problems.QuantumCapacityDepolarizing
lean_file: lean/InfoTheory/Problems/QuantumCapacityDepolarizing.lean
---

## Statement

The qubit depolarizing channel $\mathcal{D}_p : \mathcal{M}_2(\mathbb{C}) \to \mathcal{M}_2(\mathbb{C})$ with noise parameter $p \in [0, 1]$ acts on a $2 \times 2$ density matrix $\rho$ by
$$
\mathcal{D}_p(\rho) = (1 - p)\rho + \frac{p}{3}(X \rho X + Y \rho Y + Z \rho Z),
$$
where $X, Y, Z$ are the Pauli matrices. By the Lloyd–Shor–Devetak coding theorem, its quantum capacity is given by the regularized coherent information
$$
Q(\mathcal{D}_p) = \sup_{n \ge 1} \frac{1}{n} \max_{\rho \in \mathcal{D}((\mathbb{C}^2)^{\otimes n})} I_c(\rho, \mathcal{D}_p^{\otimes n}),
$$
where $I_c(\rho, \mathcal{N}) = S(\mathcal{N}(\rho)) - S(\mathcal{N}^c(\rho))$.

**Determine $Q(\mathcal{D}_p)$ for all $p \in [0, 1]$, and in particular determine the exact zero-capacity threshold**
$$
p_0 := \inf \{ p \in [0, 1] : Q(\mathcal{D}_p) = 0 \}.
$$

A flagship concrete milestone — formalized in the accompanying Lean statement — is to determine whether $p_0$ lies strictly below the no-cloning (anti-degradability) threshold $1/4$, i.e., whether there exists $p \in (0, 1/4)$ such that $Q(\mathcal{D}_p) = 0$.

## Background

The qubit depolarizing channel is the quantum analogue of the binary symmetric channel: it is the simplest non-trivial, unitarily covariant noise model for a single qubit. While the classical capacity $C(\mathcal{D}_p)$ was determined in closed form by King (2003) and the entanglement-assisted capacity $C_E(\mathcal{D}_p)$ is elementary, the unassisted quantum capacity $Q(\mathcal{D}_p)$ has resisted exact evaluation for three decades.

The core obstruction is the **superadditivity of coherent information**: DiVincenzo, Shor, and Smolin (1998) discovered that entangled multi-qubit inputs (specifically quantum repetition codes) can achieve strictly higher coherent information per channel use than any single-letter input, showing that $Q(\mathcal{D}_p)$ cannot be evaluated from single-letter optimization alone. Resolving $Q(\mathcal{D}_p)$ and its threshold $p_0$ is widely regarded as the benchmark problem of quantum Shannon theory.

## What is known

- **Single-letter hashing bound:** For a maximally mixed input $\rho = I/2$, the single-letter coherent information is $I_c(I/2, \mathcal{D}_p) = 1 - H(1 - p, p/3, p/3, p/3)$, which is positive for $p < p_1 \approx 0.18929$.
- **Lower bounds on $p_0$ via superadditive codes:**
  - DiVincenzo, Shor, and Smolin (1998) used a 5-qubit repetition code to show $Q(\mathcal{D}_p) > 0$ beyond $p_1$, pushing the threshold above $0.19036$.
  - Fern and Whaley (2008) analyzed concatenated repetition codes and improved the lower bound to $p_0 \ge 0.19086$.
  - Bausch and Leditzky (2020) used neural-network-assisted code search to push the positive-capacity region slightly further to $p_0 \gtrsim 0.1912$.
  - Leditzky, Leung, and Smith (2018) and Siddhu and Griffiths (2021) illuminated structural mechanisms behind superadditivity of coherent information in low-noise and high-noise regimes.
- **Upper bounds on $Q(\mathcal{D}_p)$ and $p_0$:**
  - **No-cloning / anti-degradability bound:** For $p \ge 1/4$, $\mathcal{D}_p$ is anti-degradable (its Choi state is symmetrically 2-extendible; Bruß et al. 1998; Cerf 2000), which proves $Q(\mathcal{D}_p) = 0$ for all $p \ge 1/4$, hence $p_0 \le 0.25$.
  - Tighter upper bounds on $Q(\mathcal{D}_p)$ for $p \in (0, 1/4)$ have been obtained via degradable extensions (Smith–Smolin 2008), approximate degradability (Sutter–Scholz–Winter–Renner 2017), semidefinite programming / Rains information (Wang–Fang–Duan 2019), and quantum flag extensions (Fanizza–Kianvash–Giovannetti 2020; Kianvash–Fanizza–Giovannetti 2022). However, **none of the known upper bounds vanish strictly below $p = 1/4$**, leaving the entire interval $p_0 \in [0.1912, 0.25]$ open.

## References

- C. H. Bennett, D. P. DiVincenzo, J. A. Smolin, and W. K. Wootters, "Mixed-state entanglement and quantum error correction," *Phys. Rev. A* **54**, 3824–3851 (1996).
- D. P. DiVincenzo, P. W. Shor, and J. A. Smolin, "Quantum-channel capacity of very noisy channels," *Phys. Rev. A* **57**, 830–839 (1998).
- N. J. Cerf, "Pauli cloning of a quantum bit," *Phys. Rev. Lett.* **84**, 4497–4500 (2000).
- C. King, "The capacity of the quantum depolarizing channel," *IEEE Trans. Inf. Theory* **49**(1), 221–229 (2003).
- J. Fern and K. B. Whaley, "Lower bounds on the nonzero capacity for Pauli channels," *Phys. Rev. A* **78**, 062335 (2008).
- G. Smith and J. A. Smolin, "Additive extensions of a quantum channel," *IEEE Inf. Theory Workshop (ITW)*, 368–372 (2008).
- D. Sutter, V. B. Scholz, A. Winter, and R. Renner, "Approximate degradable quantum channels," *IEEE Trans. Inf. Theory* **63**(12), 7832–7844 (2017).
- F. Leditzky, D. Leung, and G. Smith, "Dephrasure channel and superadditivity of coherent information," *Phys. Rev. Lett.* **121**, 160501 (2018).
- J. Bausch and F. Leditzky, "Quantum codes from neural networks," *New J. Phys.* **22**, 023005 (2020).
- M. Fanizza, F. Kianvash, and V. Giovannetti, "Quantum flags and new bounds on the quantum capacity of the depolarizing channel," *Phys. Rev. Lett.* **125**, 020503 (2020).
- V. Siddhu and R. B. Griffiths, "Positivity and nonadditivity of quantum capacities using generalized erasure channels," *IEEE Trans. Inf. Theory* **67**(7), 4533–4545 (2021).
