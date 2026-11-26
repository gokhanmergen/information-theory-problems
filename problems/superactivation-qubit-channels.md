---
id: superactivation-qubit-channels
title: Superactivation of Quantum Capacity for Qubit Channels
status: open
category: quantum-info
posed_by: Graeme Smith and Jon Yard
posed_year: 2008
tags: [quantum-information, quantum-capacity, superactivation, qubit-channels]
lean_module: InfoTheory.Problems.SuperactivationQubitChannels
lean_file: lean/InfoTheory/Problems/SuperactivationQubitChannels.lean
---

## Statement

Two quantum channels $\mathcal{N}_1, \mathcal{N}_2$ exhibit **superactivation** of quantum capacity if each individually has zero quantum capacity, yet their tensor product has strictly positive quantum capacity:
$$
Q(\mathcal{N}_1) = 0, \qquad Q(\mathcal{N}_2) = 0, \qquad Q(\mathcal{N}_1 \otimes \mathcal{N}_2) > 0.
$$

**Determine whether superactivation of quantum capacity can occur for a pair of qubit-to-qubit channels $\mathcal{N}_1, \mathcal{N}_2 : \mathcal{M}_2(\mathbb{C}) \to \mathcal{M}_2(\mathbb{C})$.**

## Background

In classical information theory, Shannon capacity is strictly additive: two channels of capacity zero can never transmit information when used in parallel. Smith and Yard (2008) stunned the field by demonstrating that quantum capacity can be *superactivated*: combining a zero-capacity PPT (Horodecki) channel with a zero-capacity 50% erasure channel yields strictly positive quantum capacity.

However, the Smith–Yard construction requires PPT-entangled (bound entangled) states, which do not exist in $2 \times 2$ or $2 \times 3$ systems by the Peres–Horodecki criterion. Thus all known mechanisms for superactivation fail for qubit-to-qubit channels, making the qubit superactivation problem closely linked to the characterization of zero-capacity qubit channels and the existence of NPT bound entanglement.

## What is known

- **Higher-dimensional superactivation:** Smith and Yard (2008) constructed superactivating pairs by tensoring a 4-dimensional Horodecki PPT channel (which has $Q = 0$ and private capacity $P > 0$) with a 50%-erasure channel (which is anti-degradable, hence $Q = 0$).
- **Further constructions:** Brandão, Oppenheim, and Strelchuk (2012) proved that superactivation occurs even with channels whose coherent information is zero for all single-letter inputs using random constructions; Smith, Smolin, and Yard (2011) demonstrated superactivation for Gaussian (bosonic) quantum channels.
- **Obstructions for qubit channels ($d_1 = d_2 = 2$):**
  - Every PPT bipartite state on $\mathbb{C}^2 \otimes \mathbb{C}^2$ is separable (Horodecki–Horodecki–Horodecki 1996), so every PPT qubit channel is entanglement-breaking.
  - Tensoring an entanglement-breaking channel with any other channel cannot increase quantum capacity ($Q(\mathcal{N}_{\text{EB}} \otimes \mathcal{N}) = Q(\mathcal{N})$), so entanglement-breaking channels cannot participate in superactivation.
  - Tensoring two anti-degradable channels is again anti-degradable, hence has $Q = 0$.
  - Therefore, superactivation of qubit channels can occur **only if** there exists a qubit channel with $Q(\mathcal{N}) = 0$ that is *neither* entanglement-breaking *nor* anti-degradable (for instance, a depolarizing channel $\mathcal{D}_p$ with $p < 1/4$ if $p_0 < 1/4$, or a non-degradable qubit channel with $Q = 0$ and $P > 0$). Whether any such zero-capacity qubit channel exists — let alone superactivates — remains completely open.

## References

- M. Horodecki, P. Horodecki, and R. Horodecki, "Separability of mixed states: necessary and sufficient conditions," *Phys. Lett. A* **223**, 1–8 (1996).
- G. Smith and J. Yard, "Quantum communication with zero-capacity channels," *Science* **321**, 1812–1815 (2008).
- G. Smith, J. A. Smolin, and J. Yard, "Quantum communication with Gaussian channels of zero quantum capacity," *Nature Photonics* **5**, 624–627 (2011).
- F. G. S. L. Brandão, J. Oppenheim, and S. Strelchuk, "When does noise increase the quantum capacity?," *Phys. Rev. Lett.* **108**, 040501 (2012).
- G. Smith and J. A. Smolin, "Detecting incapacity of a quantum channel," *Phys. Rev. Lett.* **108**, 230507 (2012).
