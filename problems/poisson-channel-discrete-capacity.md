---
id: poisson-channel-discrete-capacity
title: Optimal Support Size and Capacity of the Discrete-Time Poisson Channel
status: open
category: channel-capacity
posed_by: Shlomo Shamai (Shitz); Amos Lapidoth and Stefan M. Moser; Mahdi Cheraghchi and João Ribeiro
posed_year: 1990
tags: [channel-capacity, poisson-channel, optical-communications, discrete-support]
lean_module: InfoTheory.Problems.PoissonChannelDiscreteCapacity
lean_file: lean/InfoTheory/Problems/PoissonChannelDiscreteCapacity.lean
---

## Statement

Consider the memoryless **discrete-time Poisson channel (DTPC)** with dark current $\lambda_0 \ge 0$, peak-amplitude constraint $A > 0$, and average-power constraint $\mu \in (0, A]$. Given a nonnegative input intensity $X \in [0, A]$ with $\mathbb{E}[X] \le \mu$, the channel output $Y \in \mathbb{Z}_{\ge 0}$ is Poisson-distributed with mean $X + \lambda_0$:
$$W_{\lambda_0}(y \mid x) = e^{-(x + \lambda_0)} \frac{(x + \lambda_0)^y}{y!}, \qquad y = 0, 1, 2, \dots$$
The channel capacity (in bits per channel use) is
$$C_{\mathrm{DTPC}}(\lambda_0, A, \mu) := \sup_{\substack{0 \le X \le A \\ \mathbb{E}[X] \le \mu}} I(X; Y).$$

Shamai (1990) proved that for every finite peak constraint $A > 0$, the capacity-achieving input distribution $P_X^*$ is unique and **discrete with finitely many mass points** in $[0, A]$. Because $C_{\mathrm{DTPC}}(\lambda_0, A, A) = \frac{1}{2}\log_2 A + O(1)$ as $A \to \infty$ (Lapidoth–Moser, 2009), any capacity-achieving distribution must have support cardinality $|\mathrm{supp}(P_X^*)| = \Omega(\sqrt{A})$.

**Conjecture (Sharp $\Theta(\sqrt{A})$ Support-Size Conjecture for the DTPC).** For every dark current $\lambda_0 \ge 0$, there exists a constant $K = K(\lambda_0) > 0$ such that for all peak amplitudes $A \ge 1$ and all average-power constraints $\mu \in (0, A]$, the capacity $C_{\mathrm{DTPC}}(\lambda_0, A, \mu)$ is achieved by a discrete input distribution supported on at most $\lceil K \sqrt{A} \rceil$ points in $[0, A]$.

## Background

The discrete-time Poisson channel is the fundamental mathematical model for direct-detection optical communication with photon counting (intensity modulation / pulse-amplitude modulation). Unlike the continuous-time Poisson channel — whose exact capacity under peak and average power constraints was solved in closed form by Kabanov (1978), Davis (1980), and Wyner (1988) — the **discrete-time** Poisson channel has no known closed-form capacity formula for any non-trivial $(A, \mu, \lambda_0)$ (nor under an average-power-only constraint $\mathbb{E}[X] \le \mu$).

In 1990, Shamai adapted J. G. Smith's KKT/identity-theorem framework to prove that under a peak constraint $0 \le X \le A$, the optimal input distribution is discrete with finitely many mass points (and under an average-power-only constraint, discrete with countably infinitely many mass points accumulating only at $+\infty$, later sharpened by Cao–Hranilovic–Chen 2014). Determining both the exact capacity curve $C_{\mathrm{DTPC}}(\lambda_0, A, \mu)$ and the sharp growth rate of the optimal support size $|\mathrm{supp}(P_X^*)|$ — bridging the gap between the information-theoretic $\Omega(\sqrt{A})$ lower bound and the best known $O(A)$ oscillation-theoretic upper bounds — remains a flagship open problem in optical information theory.

## What is known

- **Discreteness and uniqueness of optimal inputs (Shamai, 1990; Brady–Verdú, 1990; Cao–Hranilovic–Chen, 2014):** Under peak power $0 \le X \le A$ (with or without average power $\mathbb{E}[X] \le \mu$), $P_X^*$ is unique and finitely supported (with an atom at $0$). Under average power only ($\mathbb{E}[X] \le \mu$), $P_X^*$ is discrete with countably infinite support and no finite accumulation points.
- **High- and low-power capacity asymptotics (Lapidoth–Moser, 2009; Lapidoth–Shamai–Moser, 2011):** Established tight high-SNR asymptotics $C_{\mathrm{DTPC}}(\lambda_0, A, A) = \frac{1}{2}\ln\frac{2A}{\pi e} + o(1)$ (nats) and $C_{\mathrm{DTPC}}(0, \infty, \mu) = \frac{1}{2}\ln\frac{e\mu}{2\pi} + o(1)$, as well as exact low-power scaling.
- **Non-asymptotic duality upper bounds (Martinez, 2007; Lapidoth–Moser, 2009; Cheraghchi–Ribeiro, 2019):** Convex duality with tailored output test distributions (including modified digamma distributions in Cheraghchi–Ribeiro 2019) yields sharp non-asymptotic upper bounds across all regimes, though no closed-form capacity is known.
- **Bounds on optimal support cardinality (Dytso–Fauß–Poor, 2019/2020):** Using total positivity and oscillation theorems for the Poisson kernel, Dytso, Fauß, and Poor proved explicit upper bounds of order $O(A)$ (specifically $|\mathrm{supp}(P_X^*)| \le O(A)$ for peak amplitude $A$) and lower bounds of order $\Omega(\sqrt{A})$. Closing the gap from $O(A)$ down to the conjectured sharp order $\Theta(\sqrt{A})$ remains open.

## References

- S. Shamai (Shitz), "Capacity of a pulse amplitude modulated direct detection photon channel," *IEE Proc. I — Commun., Speech and Vision*, 137(6):424–430, 1990.
- A. Lapidoth and S. M. Moser, "On the capacity of the discrete-time Poisson channel," *IEEE Trans. Inf. Theory*, 55(1):303–322, 2009.
- J. Cao, S. Hranilovic, and J. Chen, "Capacity-achieving distributions for the discrete-time Poisson channel — Part I & II," *IEEE Trans. Commun.*, 62(1):194–213, 2014.
- M. Cheraghchi and J. Ribeiro, "Improved capacity upper bounds for the discrete-time Poisson channel," *IEEE Trans. Inf. Theory*, 65(7):4052–4068, 2019.
- A. Dytso, M. Fauß, and H. V. Poor, "The vector Poisson channel: On the linearity of the conditional mean estimator and bounds on the capacity-achieving input support," *IEEE Trans. Signal Process. / IEEE Trans. Inf. Theory*, 2019–2020.
