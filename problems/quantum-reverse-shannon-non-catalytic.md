---
id: quantum-reverse-shannon-non-catalytic
title: Single-Letterization of Quantum Channel Entanglement Cost and Channel Simulation
status: open
category: quantum-info
posed_by: Mario Berta, Fernando G. S. L. Brandão, Matthias Christandl, and Stephanie Wehner
posed_year: 2013
tags: [quantum-information, channel-simulation, entanglement-cost, additivity]
lean_module: InfoTheory.Problems.QuantumReverseShannonNonCatalytic
lean_file: lean/InfoTheory/Problems/QuantumReverseShannonNonCatalytic.lean
---

## Statement

For a quantum channel $\mathcal{N} : \mathcal{L}(\mathbb{C}^{d_1}) \to \mathcal{L}(\mathbb{C}^{d_2})$, define its single-letter channel entanglement of formation by
$$E_F(\mathcal{N}) := \sup_{\rho_{RA}} E_F\big((\mathrm{id}_R \otimes \mathcal{N})(\rho_{RA})\big),$$
and its **entanglement cost** (the minimum asymptotic rate of entanglement required to simulate $\mathcal{N}^{\otimes n}$ using free classical communication, Berta–Brandão–Christandl–Wehner 2013) by the regularized limit
$$E_C(\mathcal{N}) := \lim_{n \to \infty} \frac{1}{n} E_F(\mathcal{N}^{\otimes n}) = \inf_{n \ge 1} \frac{1}{n} E_F(\mathcal{N}^{\otimes n}).$$

**Open Problem.** Does the entanglement cost $E_C(\mathcal{N})$ single-letterize to $E_F(\mathcal{N})$ for every qubit quantum channel ($d_1 = d_2 = 2$)?

## Background

Quantum channel simulation is the operational dual to channel coding. For universal diamond-norm simulation via classical communication and shared entanglement (the Quantum Reverse Shannon Theorem), Bennett, Devetak, Harrow, Shor, and Winter (2014, §IV) showed that standard maximally entangled ebits are insufficient for general correlated sources without catalytic entanglement-embezzling states or backward communication. When classical communication is free and entanglement is the scarce resource, Berta, Brandão, Christandl, and Wehner (2013) proved that the exact entanglement cost of simulating $\mathcal{N}$ is given by the regularized quantity $E_C(\mathcal{N})$.

## What is known

- **Regularized theorem:** Berta–Brandão–Christandl–Wehner (2013) proved that the operational entanglement cost of simulating a quantum channel with free classical communication equals $E_C(\mathcal{N}) = \lim_{n \to \infty} \frac{1}{n} E_F(\mathcal{N}^{\otimes n})$.
- **High-dimensional non-additivity:** By Shor's equivalence and Hastings' (2009) counterexample to additivity of entanglement of formation in high dimensions, $E_C(\mathcal{N}) < E_F(\mathcal{N})$ can occur for sufficiently high-dimensional channels.
- **Qubit channels:** Whether $E_C(\mathcal{N}) = E_F(\mathcal{N})$ holds for all qubit channels ($d_1 = d_2 = 2$) remains open, paralleling the open additivity question for qubit minimum output entropy.

## References

- M. Berta, F. G. S. L. Brandão, M. Christandl, and S. Wehner, "Entanglement cost of quantum channels," IEEE Trans. Inf. Theory, 2013; arXiv:1108.5357.
- C. H. Bennett, I. Devetak, A. W. Harrow, P. W. Shor, and A. Winter, "The quantum reverse Shannon theorem and resource tradeoffs for simulating quantum channels," IEEE Trans. Inf. Theory, 2014; arXiv:0912.5537.
- M. B. Hastings, "Superadditivity of communication capacity using entangled inputs," Nature Physics, 2009.
