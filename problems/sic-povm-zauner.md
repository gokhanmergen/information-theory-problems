---
id: sic-povm-zauner
title: Zauner's Conjecture on the Existence of SIC-POVMs in Every Dimension
status: open
category: quantum-info
posed_by: Gerhard Zauner
posed_year: 1999
tags: [quantum-information, sic-povm, equiangular-lines, quantum-measurements]
lean_module: InfoTheory.Problems.SicPovmZauner
lean_file: lean/InfoTheory/Problems/SicPovmZauner.lean
---

## Statement

A **Symmetric Informationally Complete Positive Operator-Valued Measure (SIC-POVM)** in dimension $d \ge 2$ is a collection of $d^2$ unit vectors $|\psi_1\rangle, \dots, |\psi_{d^2}\rangle \in \mathbb{C}^d$ satisfying the maximal equiangular tight-frame condition
$$
|\langle \psi_j \mid \psi_k \rangle|^2 = \frac{1}{d + 1} \qquad \text{for all } 1 \le j \ne k \le d^2.
$$
The corresponding rank-one operators $E_k = \frac{1}{d} |\psi_k\rangle\langle\psi_k|$ form a POVM ($\sum_{k=1}^{d^2} E_k = I_d$) that spans $\mathcal{M}_d(\mathbb{C})$ symmetrically.

**Zauner's Conjecture:** Prove (or disprove) that for **every** integer $d \ge 2$, there exists a SIC-POVM in $\mathbb{C}^d$.

## Background

A set of equiangular lines in $\mathbb{C}^d$ can have cardinality at most $d^2$ (the absolute Gerzon bound). Achieving $d^2$ equiangular lines in $\mathbb{C}^d$ is equivalent to the existence of a SIC-POVM, which provides an optimal symmetric quantum state tomography measurement, a minimal projective $2$-design, and a canonical reference measurement in quantum Bayesianism (QBism).

Remarkably, the existence problem for SIC-POVMs has turned out to have deep, unexpected links to algebraic number theory — specifically Hilbert's 12th problem (explicit class field theory) for real quadratic fields $\mathbb{Q}(\sqrt{(d-3)(d+1)})$ via Stark units and ray class fields (Appleby–Flammia–McConnell–Yard 2017; Kopp 2021).

## What is known

- **Zauner's stronger covariant conjecture:** Zauner (1999) and Renes, Blume-Kohout, Scott, and Caves (2004) conjectured that in every dimension $d \ge 2$, a SIC-POVM exists as the orbit of a single fiducial vector under the Weyl–Heisenberg group, with the fiducial vector lying in a specific eigenspace of the order-3 Zauner unitary.
- **Exact analytical solutions:** Exact algebraic SIC-POVMs have been constructed for all dimensions $d \le 53$ and for numerous higher dimensions (including $d = 57, 61, 67, 73, 78, 84, 91, 93, 97, 99, 103, 109, 111, 120, 124, 127, 129, 139, 143, 147, 151, 163, 168, 172, 195, 199, 228, 259, 323, 399, 844, 1299, \dots$, Scott–Grassl 2010; Grassl–Scott 2017; Appleby et al. 2017, 2022).
- **High-precision numerical solutions:** High-precision numerical SIC-POVMs are known for every dimension $d \le 193$ and many higher dimensions up to $d > 2000$ (Scott–Grassl 2010; Scott 2017; Bengtsson–Grassl).
- **Number-theoretic conditional constructions:** Appleby, Flammia, McConnell, and Yard (2017, 2020) and Kopp (2021) linked Weyl–Heisenberg SIC fiducials to Stark units in ray class fields of $\mathbb{Q}(\sqrt{(d-3)(d+1)})$, yielding explicit recipes for infinite families conditional on the Stark conjectures.
- **No unconditional infinite family:** Despite overwhelming numerical and algebraic evidence, **not even a single infinite sequence of dimensions $d$** is unconditionally proved to admit SIC-POVMs.

## Formal statement and certificate

The Lean `Statement` (`InfoTheory.Problems.SicPovmZauner`) asks exactly for `d²` unit vectors in `ℂ^d` with pairwise `|⟨ψ_j|ψ_k⟩|² = 1/(d+1)` for every `d ≥ 2` (plain existence, not the Weyl–Heisenberg-covariant version). Adversarial re-check (2026-11-27): faithful, still open (exact SICs only in finitely many dimensions; infinite families only conditional on the Stark conjectures). The certificate `InfoTheory.Known.Certificates.SicPovmZauner` proves `sic_dim_two` (the tetrahedral qubit SIC satisfies `IsSICPOVM 2`), `sic_dim_one`, and `not_sic_two_real` (no real-amplitude family is a SIC in `ℂ²`), so `IsSICPOVM` is neither junk-true nor junk-false.

## References

- G. Zauner, *Quantendesigns: Grundzüge einer nichtkommutativen Designtheorie*, Ph.D. thesis, University of Vienna (1999); English translation in *Int. J. Quantum Inf.* **9**(1), 445–507 (2011).
- J. M. Renes, R. Blume-Kohout, A. J. Scott, and C. M. Caves, "Symmetric informationally complete quantum measurements," *J. Math. Phys.* **45**, 2171–2180 (2004).
- A. J. Scott and M. Grassl, "Symmetric informationally complete positive-operator-valued measures: A new computer study," *J. Math. Phys.* **51**, 042203 (2010).
- C. A. Fuchs, M. C. Hoang, and B. C. Stacey, "The SIC question: History and state of play," *Axioms* **6**(3), 21 (2017).
- M. Appleby, S. Flammia, G. McConnell, and J. Yard, "SICs and algebraic number theory," *Found. Phys.* **47**, 1042–1059 (2017).
- G. S. Kopp, "SIC-POVMs and the Stark conjectures," *Int. Math. Res. Not.* **2021**(18), 13812–13838 (2021).
