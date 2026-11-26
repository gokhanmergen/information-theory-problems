---
id: npt-bound-entanglement
title: Existence of NPT Bound Entangled Quantum States
status: open
category: quantum-info
posed_by: David P. DiVincenzo, Peter W. Shor, John A. Smolin, Barbara M. Terhal, and Ashish V. Thapliyal
posed_year: 2000
tags: [quantum-information, entanglement, bound-entanglement, distillation, npt]
lean_module: InfoTheory.Problems.NptBoundEntanglement
lean_file: lean/InfoTheory/Problems/NptBoundEntanglement.lean
---

## Statement

A bipartite density matrix $\rho \in \mathcal{D}(\mathbb{C}^{d_A} \otimes \mathbb{C}^{d_B})$ is **Positive Partial Transpose (PPT)** if its partial transpose $\rho^{T_B}$ is positive semidefinite, and **Non-Positive Partial Transpose (NPT)** otherwise. By the Horodecki distillation criterion, $\rho$ is **distillable** under local operations and classical communication (LOCC) if and only if there exists $n \ge 1$ and a Schmidt-rank-2 vector $|\psi\rangle \in \mathbb{C}^{d_A^n} \otimes \mathbb{C}^{d_B^n}$ such that
$$
\langle \psi | (\rho^{\otimes n})^{T_B} | \psi \rangle < 0.
$$
Every PPT state is undistillable, and entangled PPT states (which exist for $d_A d_B > 6$) are called PPT bound entangled states.

**Determine whether there exist NPT bound entangled states — that is, finite dimensions $d_A, d_B \ge 1$ and a bipartite state $\rho \in \mathcal{D}(\mathbb{C}^{d_A} \otimes \mathbb{C}^{d_B})$ that is simultaneously NPT ($\rho^{T_B} \not\succeq 0$) and undistillable.**

## Background

Entanglement distillation — converting many noisy entangled states into pure Bell pairs via LOCC — is the operational foundation of quantum repeaters, quantum key distribution, and two-way quantum capacities. The Horodeckis (1998) proved that PPT states can never be distilled, uncovering the phenomenon of *bound entanglement* (entanglement that requires pure entanglement to create but from which zero pure entanglement can be distilled).

Whether the PPT condition is *exact* for undistillability — or whether there exist NPT states that are nevertheless completely undistillable — is arguably the single most famous open problem in entanglement theory.

## What is known

- **Reduction to Werner states:** DiVincenzo, Shor, Smolin, Terhal, and Thapliyal (2000) and Dür, Cirac, Lewenstein, and Bruß (2000) independently proved that NPT bound entanglement exists if and only if there exists an undistillable NPT **Werner state** $\rho_W(\alpha)$ on $\mathbb{C}^d \otimes \mathbb{C}^d$ (in particular, it suffices to consider a single one-parameter family of Werner states with $d \ge 3$ and parameter in the range where $\rho_W$ is $1$-copy undistillable).
- **Low-dimensional results:** Every NPT state in $2 \times 2$ or $2 \times 3$ dimensions is distillable (Horodecki–Horodecki–Horodecki 1997; Horodecki–Horodecki 1999). Every NPT state of rank $\le \max(d_A, d_B)$ is distillable (Chen–Đoković 2011).
- **$n$-copy undistillability:** Watrous (2004) proved that for every integer $n \ge 1$ there exist NPT states (in sufficiently high dimension $d(n)$) that are $n$-copy undistillable yet distillable at larger copy numbers. Strong analytical and numerical evidence (DiVincenzo et al. 2000; Dür et al. 2000; Pankowski–Piani–Horodecki–Horodecki 2010) suggests that Werner states with $\alpha = -1/2$ in dimension $d = 3$ (or $d \ge 4$) are $n$-copy undistillable for all $n \ge 1$, but a proof for all $n$ simultaneously remains elusive.
- **Implications:** If NPT bound entanglement exists, then the set of undistillable states is non-convex (Shor–Smolin–Terhal 2001), and distillable entanglement $E_D$ is non-additive even on states of zero distillable entanglement.

## References

- M. Horodecki, P. Horodecki, and R. Horodecki, "Mixed-state entanglement and distillation: Is there a 'bound' entanglement in nature?," *Phys. Rev. Lett.* **80**, 5239–5242 (1998).
- D. P. DiVincenzo, P. W. Shor, J. A. Smolin, B. M. Terhal, and A. V. Thapliyal, "Evidence for bound entangled states with negative partial transpose," *Phys. Rev. A* **61**, 062312 (2000).
- W. Dür, J. I. Cirac, M. Lewenstein, and D. Bruß, "Distillability and partial transposition in bipartite systems," *Phys. Rev. A* **61**, 062313 (2000).
- P. W. Shor, J. A. Smolin, and B. M. Terhal, "Nonadditivity of bipartite distillable entanglement follows from a conjecture on bound entangled Werner states," *Phys. Rev. Lett.* **86**, 2681–2684 (2001).
- J. Watrous, "Many copies may be required for entanglement distillation," *Phys. Rev. Lett.* **93**, 010502 (2004).
- Ł. Pankowski, M. Piani, M. Horodecki, and P. Horodecki, "A few steps more towards NPT bound entanglement," *IEEE Trans. Inf. Theory* **56**(8), 4085–4100 (2010).
- L. Chen and D. Ž. Đoković, "Distillability and PPT entanglement of low-rank quantum states," *J. Phys. A: Math. Theor.* **44**, 285303 (2011).
