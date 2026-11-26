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
  is $\frac{1}{2}\frac{\log_2 n}{n} + O(\frac{\log \log n}{n})$ (with matching lower bound
  resolving the Yu–Speed conjecture).
- **Universal upper bounds:** Yu and Speed (1993) constructed a two-stage universal
  $d$-semifaithful code achieving $O(\frac{\log n}{n})$ redundancy. Yang and Zhang (1999)
  refined the universal redundancy bounds for finite and abstract alphabets, showing
  $R_n^{\mathrm{univ}}(m, D) = \Theta(\frac{\log n}{n})$ with upper constants exceeding
  $\frac{m}{2}$ for general $m \ge 2$.
- **Pointwise and fixed-slope theory:** Kontoyiannis (2000) established pointwise redundancy
  central limit theorems and laws of the iterated logarithm (order $O(n^{-1/2})$ pointwise,
  $\Theta(\frac{\log n}{n})$ in expectation) for both known-source and universal lossy codes.
- **Exact universal constant:** Whether the minimax universal $d$-semifaithful redundancy over
  all $m$-ary memoryless sources achieves the exact additive constant $\frac{m-1}{2} + \frac{1}{2} = \frac{m}{2}$
  remains open.

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
