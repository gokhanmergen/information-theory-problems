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
$\hat{x}^n \in \mathcal{X}^n$ with $\frac{1}{n}\sum_{i=1}^n d(x_i, \hat{x}_i) \le D$, and the
codeword lengths $\ell(c)$ satisfy Kraft's inequality $\sum_c 2^{-\ell(c)} \le 1$.

Fix $0 < D < 1 - 1/m$ and $0 < \delta < \frac{1}{m} - \frac{D}{m-1}$. Let the **interior
source class** be
$$\mathcal{P}_\delta(m, D) = \Bigl\{P : P(x) \ge \tfrac{D}{m-1} + \delta \text{ for all } x\Bigr\}.$$
This is a compact set of i.i.d. sources. It contains the uniform source in its relative
interior and lies strictly inside the regular region $\{P : (m-1)\min_x P(x) > D\}$. There
$R(P, D) = H(P) - h(D) - D\log_2(m-1) > 0$ and the optimal reproduction law has full support.
Every compact subset of the regular region lies in some $\mathcal{P}_\delta(m, D)$. The
**minimax universal lossy redundancy** is
$$R_n(m, D, \delta) = \inf_{\mathcal{C}_n \text{ $d$-semifaithful}} \sup_{P \in \mathcal{P}_\delta(m, D)} \left( \frac{1}{n} \mathbb{E}_P[\ell(\mathcal{C}_n(X^n))] - R(P, D) \right).$$

**Determine the exact leading coefficient of $\frac{\log_2 n}{n}$ in $R_n(m, D, \delta)$.** The
formal statement asks the robust first step: for all such $m, D, \delta$, does the limit
$$L(m, D, \delta) = \lim_{n \to \infty} \frac{n}{\log_2 n} \, R_n(m, D, \delta)$$
exist as a real number? The conjectured value is $L = \frac{m+1}{2} = \frac{m-1}{2} + 1$: the
universal parameter-estimation penalty $(m-1)/2$ plus the known-source $d$-semifaithful
penalty of a non-uniform source, $1$. That conjecture comes from an unrefereed attempt (see below),
so the frozen statement does not use it.

## Background

In lossless universal compression ($D = 0$), Krichevsky–Trofimov (1981), Rissanen (1984) and
Shtarkov (1987) showed that the minimax redundancy over all i.i.d. sources on an $m$-letter
alphabet is $\frac{m-1}{2}\frac{\log_2 n}{n} + O(1/n)$. For a *known* source the lossless
redundancy is only $O(1/n)$.

Lossy compression behaves differently. Even when $P$ is *known*, $d$-semifaithful coding pays a
$\Theta(\frac{\log n}{n})$ redundancy (Zhang–Yang–Wei 1997, proving a conjecture of Yu–Speed),
driven by the geometry of covering type classes with distortion balls. When $P$ is unknown,
universal estimation adds to this. The exact constant is open in both settings.

## What is known

- **Known statistics.** Zhang, Yang and Wei (1997) proved that the optimal $d$-semifaithful
  redundancy of a known memoryless source is at most $\frac{\log n}{n}$ and, in most cases, at
  least $\frac{\log n}{2n}$, up to lower-order terms. Sriramu and Wagner (arXiv:2601.11927,
  2026) showed $\frac{\log n}{2n}$ is exact for a uniform source with a suitably symmetric
  distortion measure. A repository attempt proves that for non-uniform interior binary
  sources $\mathrm{Bern}(p)$, $0 < D < p < 1/2$, every $d$-semifaithful code has redundancy at
  least $\frac{\log_2 n}{n} - O(1/n)$, so the upper bound $1$ is the right constant there
  (`attempts/universal-lossy-redundancy/2026-11-26-gemini-4-neon.md`, Claim 3).
- **Weakly universal (pointwise) bounds.** Yu and Speed (1993) built a universal
  $d$-semifaithful code with redundancy $O(\frac{\log n}{n})$ under regularity conditions.
  Yang and Zhang (unpublished, as reported by Mahmood–Wagner) improved the pre-log to
  $\frac{K+2}{2}\frac{\ln n}{n}$ and gave a lower bound of $\frac{K}{2}\frac{\ln n}{n}$ for most
  sources. Here $K$ is the reproduction alphabet size, $K = m$ in this problem. The earlier
  catalog constant $m/2$ equals that lower bound.
- **Minimax and the boundary.** Mahmood and Wagner (*Minimax rate-distortion*, ISIT 2022 and
  journal version) showed the following.
  - Without regularity conditions the optimal redundancy is $\tilde{\Theta}(1/\sqrt{n})$, even
    for a known source (Cor. 5).
  - Minimax over *all* regular sources is also $\Omega(1/\sqrt{n})$, because such sources
    approach the zero-rate boundary (App. D, Lemma 11).

  Hence the source class must stay a fixed distance inside the regular region, as
  $\mathcal{P}_\delta$ does.
- **Minimax over interior classes.** For $m = 2$ and an interval $[p_1, p_2] \subset (D, 1/2)$, a
  repository attempt proves a minimax lower bound of $\frac{3}{2}\frac{\log_2 n}{n} - O(1/n)$, so
  the constant is not $m/2 = 1$. For general $m$ it gives matching
  $\frac{m+1}{2}\frac{\log_2 n}{n}$ upper and lower bounds at sketch level only
  (`attempts/universal-lossy-redundancy/2026-11-26-gemini-4-neon.md`, Claims 4–6). These have
  not been refereed.
- **Pointwise theory.** Kontoyiannis (2000) proved pointwise redundancy central limit theorems
  and laws of the iterated logarithm for known-source and universal lossy codes.
- **Statement-fix (2026-11-27).** The earlier Lean statement had two problems.
  - *Wrong class.* It took the supremum over the *entire* simplex. That includes zero-rate
    boundary sources such as $\mathrm{Bern}(1/4)$ at $D = 1/4$, where every
    $d$-semifaithful code has redundancy $\Omega(n^{-1/2})$. This is machine-checked as
    `fullSimplex_version_false` in
    `InfoTheory.Known.Certificates.UniversalLossyRedundancy`, on the old proposition spelled
    out as `FullSimplexStatement`.
  - *Wrong constant.* It asked for the upper bound $m/2$, which the $m = 2$ interior lower
    bound above contradicts.

  The statement now uses the interior class $\mathcal{P}_\delta(m, D)$ and asks whether the
  pre-log limit exists. A same-day version froze the constant $(m+1)/2$, but no published source
  poses it; it comes from the gemini-4-neon attempt, which only AI referees have checked. It was
  replaced by the existence question (Statement-fix 2, claude-known). The certificate proves the following.
  - The class is nonempty: it contains the uniform source.
  - Every source in it satisfies $D < (m-1)P(x)$, and it excludes $\mathrm{Bern}(1/4)$.
  - $R_n$ is a genuine finite infimum:
    $-R(\mathrm{unif}, D) \le R_n \le \lceil n\log_2 m\rceil / n$.
  - $R_n$ is at most the full-simplex value.

## References

- B. Yu and T. P. Speed, "A rate of convergence result for a universal $d$-semifaithful code,"
  IEEE Trans. Inf. Theory 39(3):813–820, 1993.
- Z. Zhang, E.-H. Yang, and V. K. Wei, "The redundancy of source coding with a fidelity
  criterion — Part I: Known statistics," IEEE Trans. Inf. Theory 43(1):71–91, 1997.
- E.-H. Yang and Z. Zhang, "The redundancy of source coding with a fidelity criterion — Part II:
  Coding at a fixed rate level with unknown statistics," IEEE Trans. Inf. Theory, 2001.
- E.-H. Yang and Z. Zhang, "On the redundancy of lossy source coding with abstract alphabets,"
  IEEE Trans. Inf. Theory 45(4):1092–1110, 1999.
- I. Kontoyiannis, "Pointwise redundancy in lossy data compression and universal lossy data
  compression," IEEE Trans. Inf. Theory 46(1):136–152, 2000.
- A. Mahmood and A. B. Wagner, "Minimax rate-distortion," presented in part at ISIT 2022;
  journal version at NSF PAR 10589419 (https://par.nsf.gov/servlets/purl/10589419).
- S. M. Sriramu and A. B. Wagner, "Exact Redundancy for Symmetric Rate-Distortion,"
  arXiv:2601.11927, 2026.
