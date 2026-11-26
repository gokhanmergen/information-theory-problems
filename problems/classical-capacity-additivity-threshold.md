---
id: classical-capacity-additivity-threshold
title: Minimum Output Dimension for Non-Additivity of Minimum Output Entropy
status: open
category: quantum-info
posed_by: Matthew B. Hastings
posed_year: 2009
tags: [quantum-information, classical-capacity, minimum-output-entropy, additivity]
lean_module: InfoTheory.Problems.ClassicalCapacityAdditivityThreshold
lean_file: lean/InfoTheory/Problems/ClassicalCapacityAdditivityThreshold.lean
---

## Statement

For a CPTP quantum channel $\mathcal{N} : \mathcal{M}_{d_1}(\mathbb{C}) \to \mathcal{M}_{d_2}(\mathbb{C})$, its minimum output von Neumann entropy is
$$
S_{\min}(\mathcal{N}) := \inf_{\rho \in \mathcal{D}(\mathbb{C}^{d_1})} S(\mathcal{N}(\rho)).
$$
Shor (2004) proved that global additivity of $S_{\min}$ across all quantum channels is equivalent to global additivity of the Holevo capacity $\chi(\mathcal{N})$ and of the entanglement of formation. Hastings (2009) disproved global additivity by showing that there exist high-dimensional channels $\mathcal{N}_1, \mathcal{N}_2$ with
$$
S_{\min}(\mathcal{N}_1 \otimes \mathcal{N}_2) < S_{\min}(\mathcal{N}_1) + S_{\min}(\mathcal{N}_2).
$$

**Determine the exact minimum output dimension $d \ge 2$ for which non-additivity of minimum output entropy occurs** — i.e., the smallest $d$ for which there exist channels $\mathcal{N}_1 : \mathcal{M}_{d_1}(\mathbb{C}) \to \mathcal{M}_d(\mathbb{C})$ and $\mathcal{N}_2 : \mathcal{M}_{e_1}(\mathbb{C}) \to \mathcal{M}_d(\mathbb{C})$ with $S_{\min}(\mathcal{N}_1 \otimes \mathcal{N}_2) < S_{\min}(\mathcal{N}_1) + S_{\min}(\mathcal{N}_2)$. In particular, the Lean formalization poses the sharp $d = 2$ threshold question: does non-additivity already occur for qubit-output channels?

## Background

The Holevo–Schumacher–Westmoreland (HSW) theorem expresses the classical capacity of a quantum channel as the regularized Holevo information $C(\mathcal{N}) = \lim_{n \to \infty} \frac{1}{n} \chi(\mathcal{N}^{\otimes n})$. For nearly a decade it was conjectured that $\chi$ and $S_{\min}$ are additive, which would make $C(\mathcal{N})$ single-letter. Hastings's celebrated probabilistic counterexample refuted this conjecture in high dimension, establishing that entangled inputs can strictly increase classical communication rates.

Despite substantial simplifications of Hastings's construction via random subspaces and free probability, all known counterexamples live in relatively large dimensions (and have tiny violations), leaving open whether non-additivity is a purely high-dimensional phenomenon or already occurs for qubits ($d = 2$) or qutrits ($d = 3$).

## What is known

- **Solved low-dimensional and structured classes:**
  - **Entanglement-breaking channels:** $S_{\min}$ and $\chi$ are additive when one channel is entanglement-breaking (Shor 2002).
  - **Unital qubit channels and depolarizing channels:** King (2002, 2003) proved additivity of $S_{\min}$ (and of all $p$-norms) whenever one of the channels is a unital qubit channel or a depolarizing channel in any dimension.
  - **Covariant / Werner–Holevo channels:** Additivity of $S_{\min}$ holds for several symmetric families (e.g., certain Werner–Holevo channels), although Rényi $p$-entropy additivity fails for $p > 4.79$ already in dimension $d = 3$ (Werner–Holevo 2002) and for all $p > 1$ in high dimension (Hayden–Winter 2008).
- **Upper bounds on the minimum dimension $d$ for von Neumann ($p = 1$) violations:**
  - Hastings (2009) proved existence of violations for random unitary channels in sufficiently large dimension (explicitly $\sim 10^8$ or larger).
  - Brandão and Horodecki (2010), Fukuda, King, and Moser (2010), and Aubrun, Szarek, and Werner (2010) simplified the proof and lowered the dimension estimates (to $\sim 10^4$ and below).
  - Belinschi, Collins, and Nechita (2016) used free probability and random quantum channels to prove violations exist at output dimension $d \le 183$ (and with conjugate channels $\mathcal{N} \otimes \bar{\mathcal{N}}$).
- **Qubit and qutrit output channels remain open:** For general (non-unital) qubit-output channels ($d = 2$) and qutrit-output channels ($d = 3$), it is unknown whether $S_{\min}(\mathcal{N}_1 \otimes \mathcal{N}_2) = S_{\min}(\mathcal{N}_1) + S_{\min}(\mathcal{N}_2)$ always holds.

## References

- P. W. Shor, "Additivity of the classical capacity of entanglement-breaking quantum channels," *J. Math. Phys.* **43**, 4334–4340 (2002).
- C. King, "Additivity for unital qubit channels," *J. Math. Phys.* **43**, 4641–4653 (2002).
- P. W. Shor, "Equivalence of additivity questions in quantum information theory," *Commun. Math. Phys.* **246**, 453–472 (2004).
- P. Hayden and A. Winter, "Counterexamples to the maximal $p$-norm multiplicativity conjecture for all $p > 1$," *Commun. Math. Phys.* **284**, 263–280 (2008).
- M. B. Hastings, "Superadditivity of communication capacity using entangled inputs," *Nature Phys.* **5**, 255–257 (2009).
- M. Fukuda, C. King, and D. K. Moser, "Comments on Hastings' additivity counterexamples," *Commun. Math. Phys.* **296**, 111–143 (2010).
- F. G. S. L. Brandão and M. Horodecki, "On Hastings' counterexamples to the minimum output entropy additivity conjecture," *Open Syst. Inf. Dyn.* **17**, 31–52 (2010).
- G. Aubrun, S. Szarek, and E. Werner, "Hastings's additivity counterexample via Dvoretzky's theorem," *Commun. Math. Phys.* **305**, 85–97 (2011).
- S. T. Belinschi, B. Collins, and I. Nechita, "Almost one bit violation for the additivity of the minimum output entropy," *Commun. Math. Phys.* **341**, 885–909 (2016).
