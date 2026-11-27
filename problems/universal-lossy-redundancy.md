---
id: universal-lossy-redundancy
title: Exact Minimax Redundancy Constant for Universal d-Semifaithful Lossy Source Coding
status: open
category: source-coding
posed_by: Bin Yu, T. P. Speed; Zhen Zhang, En-Hui Yang, Victor K. Wei
posed_year: 1993
tags: [source-coding, universal-coding, rate-distortion, redundancy]
lean_module: InfoTheory.Problems.UniversalLossyRedundancy
lean_file: lean/InfoTheory/Problems/UniversalLossyRedundancy.lean
---

## Statement

Consider a finite source alphabet $\mathcal{X} = \{0, \dots, m - 1\}$ with $m \ge 2$ and the
Hamming distortion measure $d(x, \hat{x}) = \mathbf{1}_{x \ne \hat{x}}$. A variable-length
prefix-free block code of blocklength $n$ is **$d$-semifaithful** at distortion level $D$ if
every source sequence $x^n \in \mathcal{X}^n$ is mapped to a reproduction sequence
$\hat{x}^n \in \mathcal{X}^n$ satisfying $\frac{1}{n}\sum_{i=1}^n d(x_i, \hat{x}_i) \le D$,
and the codeword lengths $\ell(c)$ satisfy Kraft's inequality $\sum_c 2^{-\ell(c)} \le 1$.

The **minimax universal lossy redundancy** over the simplex $\mathcal{P}(\mathcal{X})$ of all
i.i.d. sources on $\mathcal{X}$ is
$$R_n^{\mathrm{univ}}(m, D) = \inf_{\mathcal{C}_n \text{ $d$-semifaithful}} \sup_{P \in \mathcal{P}(\mathcal{X})} \left( \frac{1}{n} \mathbb{E}_P[\ell(\mathcal{C}_n(X^n))] - R(P, D) \right) ,$$
where $R(P, D)$ is Shannon's rate-distortion function for source $P$.

**Determine the exact leading coefficient of $\frac{\log_2 n}{n}$ in $R_n^{\mathrm{univ}}(m, D)$**
for every alphabet size $m \ge 2$ and interior distortion $0 < D < 1 - 1/m$; in particular,
whether
$$\lim_{n \to \infty} \frac{n}{\log_2 n} \, R_n^{\mathrm{univ}}(m, D) = \frac{m}{2} ,$$
reflecting the exact sum of the $(m-1)/2$ universal parameter-estimation penalty and the $1/2$
known-source lossy covering penalty.

## Background

In lossless universal compression ($D = 0$), Krichevsky–Trofimov (1981), Rissanen (1984), and
Shtarkov (1987) established the exact minimax redundancy $\frac{m-1}{2}\frac{\log_2 n}{n} + O(1/n)$
over all i.i.d. sources on an $m$-letter alphabet, whereas for a *known* source the lossless
redundancy drops to $O(1/n)$.

Lossy compression behaves fundamentally differently: Zhang, Yang, and Wei (1997) proved the
Yu–Speed conjecture that even when the source distribution $P$ is *known*, $d$-semifaithful
lossy source coding still incurs an unavoidable $\Theta(\frac{\log n}{n})$ redundancy
(specifically $\frac{1}{2}\frac{\log_2 n}{n} + o(\frac{\log n}{n})$ under regularity
conditions), driven by the geometry of covering type classes with distortion balls. When $P$
is *unknown*, combining universal source estimation with lossy covering gives
$R_n^{\mathrm{univ}}(m, D) = \Theta(\frac{\log n}{n})$, but pinning down the exact sharp
leading constant for general $m \ge 2$ and general distortion measures remains open.

## What is known

- **Known statistics ($d$-semifaithful):** Zhang, Yang, and Wei (1997) proved that for a known
  i.i.d. source $P$ at an interior distortion level $D$, the optimal $d$-semifaithful redundancy
  lies between $\frac{1}{2}\frac{\log_2 n}{n}$ and $\frac{\log_2 n}{n}$ (up to lower-order terms),
  leaving a factor-of-2 gap. Sriramu and Wagner (2026) resolved this gap at
  $\frac{1}{2}\frac{\log_2 n}{n}$ for uniform sources with symmetric distortion measures. By
  contrast, for non-uniform interior binary sources $P = \mathrm{Bern}(p)$ ($0 < D < p < 1/2$),
  every $d$-semifaithful code incurs redundancy at least $1 \cdot \frac{\log_2 n}{n} - O(1/n)$
  (`attempts/universal-lossy-redundancy/2026-11-26-gemini-4-neon.md`).
- **Universal upper bounds:** Yu and Speed (1993) constructed a two-stage universal
  $d$-semifaithful code achieving $O(\frac{\log n}{n})$ redundancy on compact interior subsets.
  Yang and Zhang (1999) refined the universal redundancy bounds for finite and abstract alphabets.
- **Pointwise and fixed-slope theory:** Kontoyiannis (2000) established pointwise redundancy
  central limit theorems and laws of the iterated logarithm (order $O(n^{-1/2})$ pointwise,
  $\Theta(\frac{\log n}{n})$ in expectation) for both known-source and universal lossy codes.
- **Exact universal constant & Formalization note (2026-11):**
  1. *Frozen Lean statement (`statement_false`):* Both `problems/universal-lossy-redundancy.md`
     and `lean/InfoTheory/Problems/UniversalLossyRedundancy.lean` take the supremum over the
     *entire* simplex $\mathcal{P}(\mathrm{Fin}\,m)$, which includes the zero-rate boundary kink
     $P_0 = \mathrm{Bern}(D)$ ($R(P_0, D) = 0$) where even a known-source $d$-semifaithful code
     incurs $\Omega(n^{-1/2}) \gg \frac{\log_2 n}{n}$ redundancy. Thus the frozen Lean statement
     is false as written (certified in `InfoTheory.Known.Certificates.UniversalLossyRedundancy.statement_false`)
     and needs a statement-fix PR restricting $P$ to compact interior subsets $K \subset \mathcal{P}_{\mathrm{int}}(m, D)$.
  2. *Compact-interior constant:* Even on compact interior intervals $[p_1, p_2] \subset (D, 1/2)$
     for $m = 2$, the conjectured constant $\frac{m}{2} = 1$ is refuted by a proved minimax lower
     bound of $\frac{3}{2}\frac{\log_2 n}{n} - O(1/n)$ (with matching $\frac{m+1}{2}\frac{\log_2 n}{n}$
     upper/lower sketches for general $m \ge 2$; see `attempts/universal-lossy-redundancy/2026-11-26-gemini-4-neon.md`).

## References

- B. Yu and T. P. Speed, "A rate of convergence result for a universal $d$-semifaithful code,"
  IEEE Trans. Inf. Theory, 1993.
- Z. Zhang, E.-H. Yang, and V. K. Wei, "The redundancy of source coding with a fidelity
  criterion — Part I: Known statistics," IEEE Trans. Inf. Theory, 1997.
- E.-H. Yang and Z. Zhang, "The redundancy of source coding with a fidelity criterion — Part II:
  Coding at a fixed rate level with unknown statistics," IEEE Trans. Inf. Theory, 1999.
- E.-H. Yang and Z. Zhang, "On the redundancy of lossy source coding with abstract alphabets,"
  IEEE Trans. Inf. Theory, 1999.
- I. Kontoyiannis, "Pointwise redundancy in lossy data compression and universal lossy data
  compression," IEEE Trans. Inf. Theory, 2000.
- S. M. Sriramu and A. B. Wagner, "Exact Redundancy for Symmetric Rate-Distortion,"
  arXiv:2601.11927, 2026.
