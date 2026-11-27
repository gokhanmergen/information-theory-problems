---
id: binary-multiplier-two-way-channel
title: Symmetric Capacity of Blackwell's Binary Multiplying Channel
status: open
category: network-info-theory
posed_by: David Blackwell (via Claude E. Shannon)
posed_year: 1961
tags: [network-information-theory, two-way-channel, binary-multiplying-channel, dependence-balance]
lean_module: InfoTheory.Problems.BinaryMultiplierTwoWayChannel
lean_file: lean/InfoTheory/Problems/BinaryMultiplierTwoWayChannel.lean
---

## Statement

**Blackwell's binary multiplying channel (BMC)** is the deterministic single-output
discrete memoryless two-way channel with binary inputs $X_1, X_2 \in \{0, 1\}$ and common
binary output
$$
Y_1 = Y_2 = Y = X_1 \cdot X_2.
$$
Let $C_{\mathrm{sym}}(\mathrm{BMC}) = \sup \{ R \ge 0 : (R, R) \in \mathcal{C}_{\mathrm{TWC}}(\mathrm{BMC}) \}$
denote its symmetric (equal-rate) capacity.

The **Hekstra–Willems dependence-balance outer bound** (1989) for the symmetric capacity of
the BMC is
$$
C_{\mathrm{DB}}(\mathrm{BMC}) = \sup_{p(z, x_1, x_2)} \min\!\big(I(X_1; Y \mid X_2, Z),\; I(X_2; Y \mid X_1, Z)\big),
$$
where the supremum ranges over all finite-alphabet auxiliaries $Z$ and joint distributions
$p(z, x_1, x_2)$ satisfying the dependence-balance constraint
$$
I(X_1; X_2 \mid Z) \le I(X_1; X_2 \mid Y, Z).
$$

**Does $C_{\mathrm{sym}}(\mathrm{BMC}) = C_{\mathrm{DB}}(\mathrm{BMC})$?**

> **Catalog error (flagged 2026-11-26, statement-fix pending).** The functional $C_{\mathrm{DB}}$
> displayed above, which is also the Lean `bmcDependenceBalanceBound`, is the *plain*
> dependence-balance bound. For the BMC this bound is vacuous. For a deterministic channel the
> constraint reads $H(Y\mid Z) \le I(X_1;Y\mid X_2,Z) + I(X_2;Y\mid X_1,Z)$, and it holds
> automatically once the two rate terms sum to at least 1 bit. Consequently
> $C_{\mathrm{DB}}(\mathrm{BMC}) = \log_2\phi \approx 0.69424$, Shannon's outer bound, not
> $0.64628$; see also Bloemen (1996, §6.4.2). The frozen Lean `Statement` therefore asserts
> $C_{\mathrm{sym}} = \log_2\phi$, which is false by the Zhang–Berger–Schalkwijk bound
> $C_{\mathrm{sym}} \le 0.64891$. The value $0.64628$ belongs to the Hekstra–Willems DB bound
> **with an adaptive parallel channel**. The intended question is whether $C_{\mathrm{sym}}$
> equals that bound. Proof, closed form of the corrected bound, numerical reproduction of
> $0.64628$, and proposed Lean text:
> `attempts/binary-multiplier-two-way-channel/2026-11-26-claude-opus-5-5-db-catalog-error-survey.md`.

## Background

Suggested by David Blackwell to Claude Shannon in his 1961 paper on two-way channels, the
binary multiplying channel is the simplest nontrivial two-way channel in existence: a
single logical AND gate observed by both terminals. It plays the same benchmark role for
two-way channels that the binary skew-symmetric channel plays for broadcast channels and
the deletion channel plays for synchronization channels. Despite sixty-five years of
intense study, the exact equal-rate capacity of this one-gate deterministic channel
remains unknown, pinned between $0.63072$ and $0.64628$ bits per channel use.

## What is known

- **Shannon's single-letter bounds (1961)**:
  - Inner bound (independent inputs): $R_{\mathrm{in}} = \max_a a\,h(a) \approx 0.61695$ bits
    at $a \approx 0.70351$.
  - Outer bound (arbitrary joint inputs): $R_{\mathrm{out}} = \log_2 \phi = \log_2\!\big(\frac{1 + \sqrt{5}}{2}\big) \approx 0.69424$ bits,
    attained at $p_{00}=0$, $p_{01}=p_{10}=(5-\sqrt5)/10$, $p_{11}=1/\sqrt5$.
- **Constructive lower bounds (adaptive coding)**:
  - Schalkwijk (1982) broke Shannon's inner bound with a unit-square scheme. After an
    inner-bound transmission with output 0 it uses an intermediate transmission, which can
    enable an outer-bound transmission. It achieves $0.61914$ bits.
  - Schalkwijk (1983) added bootstrapping: the intermediate information is Slepian–Wolf
    compressed and sent by the scheme itself. This achieves $0.63056$ bits
    ($0.6305552557$). Tolhuizen (1985) gave a fixed-length code construction for such
    strategies, and van Overveld (1988) extended it to prove the bootstrapping rate. Schalkwijk
    (1990, 1991) found improvements only in the 8th and 10th decimal places
    ($0.6305552986$, $0.6305552995$), which showed that the 1983 strategy is not optimal.
  - Schalkwijk, Meeuwissen and Bloemen (1995; see Bloemen's 1996 TU/e thesis, Ch. 6)
    combined save-up strategies with bootstrapping and reached the equal-rate point
    $0.63072$ bits. As far as I could find, this is still the best known lower bound
    (Nov 2026).
  - Directed-information and graph-based single-letter inner bounds have so far stayed below
    Schalkwijk's 1983 rate. Ardestanizadeh (PhD thesis, UCSD; as reported by Y.-H. Kim, 2012)
    obtained $0.6191$. Sabag and Permuter (Allerton 2018) gave a single-letter region built
    on auxiliary directed graphs that beats Shannon's inner bound on the BMC.
- **Converse upper bounds**:
  - Zhang, Berger, and Schalkwijk (1986) broke Shannon's outer bound, proving
    $C_{\mathrm{sym}}(\mathrm{BMC}) \le 0.64891$ bits.
  - Hekstra and Willems (1989) introduced the dependence-balance (DB) bound. In its plain
    form (the $C_{\mathrm{DB}}$ displayed above) it does **not** improve on Shannon's outer
    bound for the BMC (see the catalog-error note). With an **adaptive parallel channel**
    (Bloemen 1996, Thm 6.3 and Table 6.2) it gives
    $C_{\mathrm{sym}}(\mathrm{BMC}) \le 0.64628$ bits, which is still the sharpest known
    upper bound. Tandon and Ulukus (2007) showed that HW's choice is optimal among all
    binary adaptive parallel channels. Gohari and Kramer (arXiv:2009.14814) list adaptive
    auxiliary receivers as an open route to stronger DB bounds.
- Closing the $0.0156$-bit gap $[0.63072, 0.64628]$, either by achieving the
  Hekstra–Willems bound or by proving a strictly tighter converse, remains wide open.

## References

- C. E. Shannon, "Two-way communication channels," *Proc. 4th Berkeley Symp. Math. Statist.
  Probab.*, vol. 1, pp. 611–644, 1961.
- J. P. M. Schalkwijk, "The binary multiplying channel — a coding scheme that operates
  beyond Shannon's inner bound region," *IEEE Trans. Inf. Theory*, vol. 28, no. 1,
  pp. 107–110, 1982.
- J. P. M. Schalkwijk, "On an extension of an achievable rate region for the binary
  multiplying channel," *IEEE Trans. Inf. Theory*, vol. 29, no. 3, pp. 445–448, 1983.
- Z. Zhang, T. Berger, and J. P. M. Schalkwijk, "New outer bounds to capacity regions of
  two-way channels," *IEEE Trans. Inf. Theory*, vol. 32, no. 3, pp. 383–386, 1986.
- A. P. Hekstra and F. M. J. Willems, "Dependence balance bounds for single-output two-way
  channels," *IEEE Trans. Inf. Theory*, vol. 35, no. 1, pp. 44–53, 1989.
- H. B. Meeuwissen, *Information Theoretical Aspects of Two-Way Communication*, Ph.D.
  dissertation, Eindhoven University of Technology, 1998.
- L. Tolhuizen, "Discrete coding for the BMC, based on Schalkwijk's strategy," *Proc. 6th
  BeNeLux Symp. Inf. Theory*, pp. 207–212, 1985.
- W. M. C. J. van Overveld, "Fixed length strategies for the BMC," *IEEE Trans. Inf.
  Theory*, vol. 34, no. 2, pp. 314–318, 1988.
- J. P. M. Schalkwijk, "Another 0.63056," *Proc. 11th BeNeLux Symp. Inf. Theory*,
  pp. 155–161, 1990; "Extending the achievable rate region of the binary multiplying
  channel," *Proc. IEEE ISIT*, p. 302, Budapest, 1991.
- J. P. M. Schalkwijk, H. B. Meeuwissen, and A. H. A. Bloemen, "New results on a fundamental
  problem in network information theory," *Tijdschrift van het NERG*, vol. 60, no. 3, 1995;
  H. B. Meeuwissen, J. P. M. Schalkwijk, and A. H. A. Bloemen, "Extension of the achievable
  rate region of Schalkwijk's 1983 coding strategy for the binary multiplying channel,"
  *Proc. IEEE ISIT*, Whistler, 1995.
- A. H. A. Bloemen, *Discrete Coding Strategies for Two-Way Channels*, Ph.D. dissertation,
  Eindhoven University of Technology, 1996, doi:10.6100/IR463500 (Ch. 6: bounds table,
  plain DB vacuous for the BMC, HW parallel channel).
- R. Tandon and S. Ulukus, "On dependence balance bounds for two way channels," *Proc. 41st
  Asilomar Conf. Signals, Systems and Computers*, pp. 868–872, 2007,
  doi:10.1109/ACSSC.2007.4487342.
- O. Sabag and H. H. Permuter, "An achievable rate region for the two-way channel with common
  output," *Proc. 56th Allerton Conf.*, pp. 527–531, 2018, doi:10.1109/ALLERTON.2018.8635930.
- A. Gohari and G. Kramer, "Dependence balance and capacity bounds for multiterminal
  communication and wiretap channels," arXiv:2009.14814.
