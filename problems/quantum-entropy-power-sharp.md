---
id: quantum-entropy-power-sharp
title: The Bosonic Entropy Photon-Number Inequality (EPnI)
status: open
category: quantum-info
posed_by: Saikat Guha, Jeffrey H. Shapiro, and Baris I. Erkmen
posed_year: 2008
tags: [quantum-information, entropy-power-inequality, bosonic-channels]
lean_module: InfoTheory.Problems.QuantumEntropyPowerSharp
lean_file: lean/InfoTheory/Problems/QuantumEntropyPowerSharp.lean
---

## Statement

Let $g(x) = (x+1)\log_2(x+1) - x\log_2 x$ ($x \ge 0$) be the von Neumann entropy of a single-mode bosonic thermal state with mean photon number $x$, and define the **entropy photon number** of a state $\rho$ by $N(\rho) := g^{-1}(S(\rho))$.

Let $U_\lambda$ be a passive beam splitter of transmissivity $\lambda \in (0, 1)$ combining two independent single-mode bosonic states $\rho_A$ and $\rho_B$, with output mode $\sigma_C = \operatorname{Tr}_D[U_\lambda (\rho_A \otimes \rho_B) U_\lambda^\dagger]$.

**Conjecture (Entropy Photon-Number Inequality, Guha–Erkmen–Shapiro 2008).** For all single-mode bosonic states $\rho_A, \rho_B$ (in particular, all states supported on finite Fock cutoffs $M \ge 1$) and all $\lambda \in (0, 1)$,
$$N(\sigma_C) \;\ge\; \lambda\, N(\rho_A) + (1 - \lambda)\, N(\rho_B).$$

## Background

The bosonic quantum entropy power inequality $2^{S(\sigma_C)} \ge \lambda 2^{S(\rho_A)} + (1-\lambda) 2^{S(\rho_B)}$ was proved by König–Smith (2014), De Palma–Mari–Giovannetti (2014), and extended to the conditional setting by De Palma–Trevisan (2018). However, the strictly stronger **Entropy Photon-Number Inequality (EPnI)**—which replaces the classical entropy power $2^S$ with the thermal photon number $g^{-1}(S)$ and is tight for thermal Gaussian states—remains open for general non-Gaussian states. Establishing the EPnI would resolve several central capacity region conjectures for bosonic Gaussian broadcast and wiretap channels.

## What is known

- **Weaker qEPI proved:** König–Smith (2014) and De Palma–Mari–Giovannetti (2014) proved the quantum EPI $e^{S(\sigma_C)} \ge \lambda e^{S(\rho_A)} + (1-\lambda) e^{S(\rho_B)}$, and De Palma–Trevisan (2018, Theorem 6) proved the conditional bosonic qEPI $e^{S(C\mid E)} \ge \lambda e^{S(A\mid E)} + (1-\lambda) e^{S(B\mid E)}$.
- **Gaussian and passive states:** Equality holds for all thermal Gaussian states. De Palma–Mari–Giovannetti–Holevo (2015) proved the EPnI when one input is Gaussian and established strong partial results for Fock-diagonal (passive) states.
- **General non-Gaussian states:** Open in full generality even for single-mode finite-Fock-cutoff states.

## References

- S. Guha, B. I. Erkmen, and J. H. Shapiro, "The entropy photon-number inequality and its consequences," Proc. ITA Workshop, 2008; arXiv:0710.5666.
- R. König and G. Smith, "The entropy power inequality for quantum systems," IEEE Trans. Inf. Theory, 2014.
- G. De Palma, A. Mari, and V. Giovannetti, "A generalization of the entropy power inequality to bosonic quantum systems," Nature Photonics, 2014.
- G. De Palma, A. Mari, S. Lloyd, and V. Giovannetti, "Passive states as optimal inputs for single-jump lossy quantum channels," Phys. Rev. A, 2015.
- G. De Palma and D. Trevisan, "The conditional entropy power inequality for bosonic quantum systems," Comm. Math. Phys., 2018; arXiv:1706.00440.
