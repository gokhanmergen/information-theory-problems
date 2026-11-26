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

## Background

Suggested by David Blackwell to Claude Shannon in his 1961 paper on two-way channels, the
binary multiplying channel is the simplest nontrivial two-way channel in existence: a
single logical AND gate observed by both terminals. It plays the same benchmark role for
two-way channels that the binary skew-symmetric channel plays for broadcast channels and
the deletion channel plays for synchronization channels. Despite sixty-five years of
intense study, the exact equal-rate capacity of this one-gate deterministic channel
remains unknown, pinned between $0.63056$ and $0.64628$ bits per channel use.

## What is known

- **Shannon's single-letter bounds (1961)**:
  - Inner bound (independent inputs): $R_{\mathrm{in}} \approx 0.61695$ bits.
  - Outer bound (arbitrary joint inputs): $R_{\mathrm{out}} = \log_2 \phi = \log_2\!\big(\frac{1 + \sqrt{5}}{2}\big) \approx 0.69424$ bits.
- **Constructive lower bounds (adaptive coding)**:
  - Schalkwijk (1982) broke Shannon's inner bound with a two-step scheme achieving
    $0.61914$ bits.
  - Schalkwijk (1983) introduced a recursive unit-square partitioning scheme achieving
    $0.63056$ bits — a milestone that stood essentially unmatched for decades.
  - Subsequent refinements (Meeuwissen 1998; Kramer 1998; Chaaban–Sezgin) slightly improved
    the achievable rate around $0.63056$–$0.6307$ bits, still far below the best upper bound.
- **Converse upper bounds**:
  - Zhang, Berger, and Schalkwijk (1986) broke Shannon's outer bound, proving
    $C_{\mathrm{sym}}(\mathrm{BMC}) \le 0.64891$ bits.
  - Hekstra and Willems (1989) proved the dependence-balance upper bound
    $C_{\mathrm{sym}}(\mathrm{BMC}) \le C_{\mathrm{DB}}(\mathrm{BMC}) \approx 0.64628$ bits,
    which remains the sharpest known single-letter upper bound.
- Closing the $0.0157$-bit gap $[0.63056, 0.64628]$ — either by achieving
  $C_{\mathrm{DB}}(\mathrm{BMC})$ or by proving a strictly tighter converse — remains wide open.

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
