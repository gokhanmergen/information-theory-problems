---
id: noisy-interactive-communication-rate
title: Exact Interactive Coding Capacity over the Binary Symmetric Channel as ε → 0
status: open
category: statistical-info-theory
posed_by: Leonard J. Schulman; Gillat Kol and Ran Raz
posed_year: 1996
tags: [interactive-coding, bsc, interactive-capacity, coding-theory, communication-complexity]
lean_module: InfoTheory.Problems.NoisyInteractiveCommunicationRate
lean_file: lean/InfoTheory/Problems/NoisyInteractiveCommunicationRate.lean
---

## Statement

Consider simulating an arbitrary $T$-round alternating noiseless two-party binary interactive protocol $\pi$ over a bidirectional **binary symmetric channel** $\mathrm{BSC}(\varepsilon)$ (where every transmitted bit is flipped independently with probability $\varepsilon \in (0, 1/2)$). A simulation rate $R \in [0, 1]$ is achievable if for every $\delta > 0$ and all sufficiently large $T$, every $T$-round noiseless protocol $\pi$ can be simulated over $\mathrm{BSC}(\varepsilon)$ in $N \le T / R$ channel uses so that both parties recover the exact noiseless transcript $\pi(x, y)$ with error probability at most $\delta$ on every input $(x, y)$. Let $C_{\mathrm{int}}(\varepsilon)$ denote the supremum of achievable rates — the **interactive coding capacity** of $\mathrm{BSC}(\varepsilon)$.

By Shannon's channel coding theorem, $C_{\mathrm{int}}(\varepsilon) \le C(\mathrm{BSC}(\varepsilon)) = 1 - h(\varepsilon) = 1 - \Theta(\varepsilon \log(1/\varepsilon))$.

**Determine the exact asymptotic scaling of the rate overhead $1 - C_{\mathrm{int}}(\varepsilon)$ as $\varepsilon \to 0^+$ — and in particular determine whether interactive coding can match the Shannon-capacity scaling (formalized in Lean):**
$$
1 - C_{\mathrm{int}}(\varepsilon) = O\big(h(\varepsilon)\big) \qquad \text{as } \varepsilon \to 0^+,
$$
or whether interactive communication over $\mathrm{BSC}(\varepsilon)$ incurs a strictly larger overhead such as $\Theta(\sqrt{\varepsilon})$ or $\Theta(\sqrt{\varepsilon \log(1/\varepsilon)})$.

## Background

Schulman (1992, 1996) founded the field of interactive coding theory by introducing tree codes and proving that any noiseless interactive protocol can be simulated over $\mathrm{BSC}(\varepsilon)$ with constant rate $C_{\mathrm{int}}(\varepsilon) > 0$ (as opposed to naively encoding each single bit separately, which drives the rate to zero).

For one-way communication, Shannon's theorem establishes the exact capacity $1 - h(\varepsilon)$, so the overhead vanishes as $\Theta(\varepsilon \log(1/\varepsilon))$ as $\varepsilon \to 0$. In the interactive setting, however, a single corrupted bit can cause Alice and Bob to diverge in their execution of $\pi$, requiring rewind/resynchronization mechanisms. Understanding whether synchronization overhead forces a fundamental gap between interactive capacity $C_{\mathrm{int}}(\varepsilon)$ and Shannon capacity $1 - h(\varepsilon)$ as $\varepsilon \to 0$ is the central open question of interactive coding theory.

## What is known

- **Constant-rate achievability:** Schulman (1992, 1996) proved $C_{\mathrm{int}}(\varepsilon) > 0$ for small $\varepsilon > 0$.
- **High-rate achievability as $\varepsilon \to 0$:**
  - Kol and Raz (2013) proved $C_{\mathrm{int}}(\varepsilon) \ge 1 - O(\sqrt{h(\varepsilon)}) = 1 - O(\sqrt{\varepsilon \log(1/\varepsilon)})$ for non-adaptive alternating simulations over $\mathrm{BSC}(\varepsilon)$.
  - Haeupler (2014) improved the achievable rate to $1 - O(\sqrt{\varepsilon \log\log(1/\varepsilon)})$ for non-adaptive protocols and $1 - O(\sqrt{\varepsilon})$ when adaptive speaking order (or shared randomness) is allowed.
- **Upper bounds / converses:**
  - Trivially $C_{\mathrm{int}}(\varepsilon) \le 1 - h(\varepsilon)$.
  - Kol and Raz (2013) proved that non-adaptive protocols over $\mathrm{BSC}(\varepsilon)$ cannot achieve Shannon capacity $1 - h(\varepsilon)$ in general (establishing a strict separation below $1 - h(\varepsilon)$), and Efremenko, Gelles, and Haeupler (2016) analyzed maximal tolerable noise and rate limits across erasure, feedback, and BSC models.
- **Exact scaling of $1 - C_{\mathrm{int}}(\varepsilon)$ remains open:** Between the Shannon lower bound $\Omega(\varepsilon \log(1/\varepsilon))$ and the Haeupler upper bound $O(\sqrt{\varepsilon \log\log(1/\varepsilon)})$ (or $O(\sqrt{\varepsilon})$ with adaptivity), the true order of magnitude of $1 - C_{\mathrm{int}}(\varepsilon)$ as $\varepsilon \to 0^+$ remains completely open (Gelles 2017).

## References

- L. J. Schulman, "Communication on noisy channels: A coding theorem for computation," *Proc. 33rd IEEE FOCS*, 724–733 (1992); full version "Coding for interactive communication," *IEEE Trans. Inf. Theory* **42**(6), 1745–1756 (1996).
- G. Kol and R. Raz, "Interactive channel capacity," *Proc. 45th ACM STOC*, 715–724 (2013).
- B. Haeupler, "Interactive channel capacity revisited," *Proc. 55th IEEE FOCS*, 226–235 (2014).
- K. Efremenko, R. Gelles, and B. Haeupler, "Maximal noise in interactive communication over erasure channels and channels with feedback," *IEEE Trans. Inf. Theory* **62**(8), 4575–4588 (2016).
- R. Gelles, "Coding for interactive communication: A survey," *Found. Trends Theor. Comput. Sci.* **13**(1–2), 1–157 (2017).
