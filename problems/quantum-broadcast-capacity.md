---
id: quantum-broadcast-capacity
title: Capacity Region of the Classical-Quantum Two-Receiver Broadcast Channel
status: open
category: quantum-info
posed_by: Jon Yard, Patrick Hayden, and Igor Devetak
posed_year: 2011
tags: [quantum-information, broadcast-channel, marton-bound, network-information-theory]
lean_module: InfoTheory.Problems.QuantumBroadcastCapacity
lean_file: lean/InfoTheory/Problems/QuantumBroadcastCapacity.lean
---

## Statement

A two-receiver classical-quantum (c-q) broadcast channel maps each classical input symbol $x \in \mathcal{X}$ to a bipartite quantum state $\rho_x^{B_1 B_2} \in \mathcal{D}(\mathbb{C}^{d_1} \otimes \mathbb{C}^{d_2})$, with reduced marginal states $\rho_x^{B_1} = \operatorname{Tr}_{B_2}(\rho_x^{B_1 B_2})$ and $\rho_x^{B_2} = \operatorname{Tr}_{B_1}(\rho_x^{B_1 B_2})$. A rate pair $(R_1, R_2)$ is operationally achievable if there exist block encoders $x^n(m_1, m_2)$ and POVM decoders $\{\Lambda^{(1)}_{m_1}\}$ on $B_1^{\otimes n}$ and $\{\Lambda^{(2)}_{m_2}\}$ on $B_2^{\otimes n}$ whose average decoding errors vanish as $n \to \infty$.

The single-letter **quantum Marton inner bound** $\mathcal{M}(\mathcal{N})$ consists of all pairs $(R_1, R_2) \ge (0, 0)$ for which there exist finite auxiliary alphabets $\mathcal{U}, \mathcal{V}$ and a joint distribution $P_{UVX}$ such that
$$
R_1 \le I(U; B_1)_\sigma, \qquad R_2 \le I(V; B_2)_\sigma, \qquad R_1 + R_2 \le I(U; B_1)_\sigma + I(V; B_2)_\sigma - I(U; V),
$$
where $I(U; B_1)_\sigma = S(\sum_u P_U(u) \sigma_u^{B_1}) - \sum_u P_U(u) S(\sigma_u^{B_1})$ and $I(V; B_2)_\sigma$ are the Holevo informations of the induced c-q states.

**Determine a single-letter characterization of the capacity region $\mathcal{C}(\mathcal{N})$ for general two-receiver classical-quantum broadcast channels — and specifically determine whether the quantum Marton inner bound $\mathcal{M}(\mathcal{N})$ equals $\mathcal{C}(\mathcal{N})$ for all c-q broadcast channels.**

## Background

The two-receiver broadcast channel is the flagship open problem of classical network information theory (Cover 1972). Yard, Hayden, and Devetak (2011) initiated quantum network Shannon theory for broadcast channels, showing that quantum superposition coding and degraded c-q broadcast channels mirror classical theory, while non-commuting output states introduce fundamentally new decoding challenges (such as simultaneous non-commuting sequential decoding and convex splitting).

Because classical discrete memoryless broadcast channels embed as diagonal c-q broadcast channels, resolving the general c-q broadcast channel encompasses the classical Marton tightness problem while additionally testing whether entangled / collective quantum decoding creates new phenomena beyond single-letter Marton coding.

## What is known

- **Degraded c-q broadcast channels:** Yard, Hayden, and Devetak (2011) established a single-letter capacity region for degraded classical-quantum broadcast channels (and for quantum-input degraded broadcast channels with a classical and a quantum message).
- **Achievability of the quantum Marton inner bound:**
  - Savov and Wilde (2015) proved achievability of a Marton-type inner bound for general c-q broadcast channels using classical-quantum polar/random coding and sequential decoding.
  - Radhakrishnan, Sen, and Warsi (2016) and Sen (2018) used the quantum union bound / convex splitting to prove full one-shot and asymptotic achievability of the exact single-letter quantum Marton inner bound $\mathcal{M}(\mathcal{N}) \subseteq \mathcal{C}(\mathcal{N})$ (including common messages).
- **Outer bounds and tightness open:** Quantum generalizations of the Nair–El Gamal UV outer bound exist, but as in the classical setting, there is a gap between the quantum Marton inner bound and the best known outer bounds, and it remains open whether $\mathcal{M}(\mathcal{N}) = \mathcal{C}(\mathcal{N})$ for all c-q broadcast channels (and even more generally for fully quantum-input broadcast channels, where non-additivity of Holevo information already prevents single-letterization).

## References

- T. M. Cover, "Broadcast channels," *IEEE Trans. Inf. Theory* **18**(1), 2–14 (1972).
- K. Marton, "A coding theorem for the discrete memoryless broadcast channel," *IEEE Trans. Inf. Theory* **25**(3), 306–311 (1979).
- J. Yard, P. Hayden, and I. Devetak, "Quantum broadcast channels," *IEEE Trans. Inf. Theory* **57**(10), 7147–7162 (2011).
- I. Savov and M. M. Wilde, "Classical codes for quantum broadcast channels," *IEEE Trans. Inf. Theory* **61**(12), 7017–7028 (2015).
- J. Radhakrishnan, P. Sen, and N. Warsi, "One-shot Marton inner bound for classical-quantum broadcast channel," *IEEE Trans. Inf. Theory* **62**(5), 2836–2848 (2016).
- P. Sen, "Inner bounds via simultaneous decoding in quantum network information theory," *arXiv:1806.07276* (2018).
