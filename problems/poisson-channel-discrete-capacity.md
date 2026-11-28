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

**Problem (Sublinear Support Size for the Amplitude-Constrained DTPC).** Let $N(\lambda_0, A) := |\mathrm{supp}(P_X^*)|$ be the number of mass points of the (unique) capacity-achieving input under the amplitude constraint $0 \le X \le A$ alone. Determine the order of growth of $N(\lambda_0, A)$ as $A \to \infty$; in particular, is it polynomially sublinear? Formally: for every $\lambda_0 \ge 0$, do there exist $\delta > 0$ and $K > 0$ such that for all $A \ge 1$ the capacity $C_{\mathrm{DTPC}}(\lambda_0, A, A)$ is achieved by a discrete input on $[0, A]$ with at most $K A^{1-\delta}$ mass points?

> **Statement-fix (2026-11-27).** The previous version stated a "sharp $\Theta(\sqrt{A})$ support-size conjecture", uniformly over an additional average-power budget $\mu \in (0, A]$. No such conjecture appears in the literature, and the published numerics contradict it: Barletta–Dytso–Shamai (arXiv:2401.05045, 2024) fit $N(A) \approx A^{0.71}$ at $\lambda_0 = 0$ and state that "neither the upper nor lower bounds are tight", leaving "the exact order of the size of the support" as the open question. The proved bounds are $\Omega(\sqrt{A}) \le N \le O(A)$. The statement now asks the first open step, polynomial sublinearity, under the amplitude constraint only (the Lean statement uses `dtpcCapacity lam₀ A A`, where $\mathbb{E}[X] \le A$ holds automatically). The general $(A, \mu)$ capacity $C_{\mathrm{DTPC}}(\lambda_0, A, \mu)$ is kept as background.

## Formal statement (Lean)

`InfoTheory.Problems.PoissonChannelDiscreteCapacity.Statement`:
$$\forall \lambda_0 \ge 0,\ \exists \delta, K > 0,\ \forall A \ge 1,\ \exists k,\ \mathrm{pts} \in [0, A]^k,\ w \in \Delta_k:\ k \le K A^{1-\delta} \ \wedge\ I_{\lambda_0}(\mathrm{pts}, w) = C_{\mathrm{DTPC}}(\lambda_0, A, A),$$
where $C_{\mathrm{DTPC}}$ is the supremum of $I(X;Y)$ over finitely supported inputs (equal to the supremum over all Borel inputs on $[0,A]$ by Shamai 1990). Certificate: `lean/InfoTheory/Known/Certificates/PoissonChannelDiscreteCapacity.lean` (Poisson kernel normalisation, junk-free boundedness of the capacity set, $C \ge 0$, $C(\lambda_0, 0, \mu) = 0$).

## Background

The discrete-time Poisson channel is the fundamental mathematical model for direct-detection optical communication with photon counting (intensity modulation / pulse-amplitude modulation). Unlike the continuous-time Poisson channel — whose exact capacity under peak and average power constraints was solved in closed form by Kabanov (1978), Davis (1980), and Wyner (1988) — the **discrete-time** Poisson channel has no known closed-form capacity formula for any non-trivial $(A, \mu, \lambda_0)$ (nor under an average-power-only constraint $\mathbb{E}[X] \le \mu$).

In 1990, Shamai adapted J. G. Smith's KKT/identity-theorem framework to prove that under a peak constraint $0 \le X \le A$, the optimal input distribution is discrete with finitely many mass points (and under an average-power-only constraint, discrete with countably infinitely many mass points accumulating only at $+\infty$, later sharpened by Cao–Hranilovic–Chen 2014). Determining both the exact capacity curve $C_{\mathrm{DTPC}}(\lambda_0, A, \mu)$ and the sharp growth rate of the optimal support size $|\mathrm{supp}(P_X^*)|$ — bridging the gap between the information-theoretic $\Omega(\sqrt{A})$ lower bound and the best known $O(A)$ oscillation-theoretic upper bounds — remains a flagship open problem in optical information theory.

## What is known

- **Discreteness and uniqueness of optimal inputs (Shamai, 1990; Brady–Verdú, 1990; Cao–Hranilovic–Chen, 2014):** Under peak power $0 \le X \le A$ (with or without average power $\mathbb{E}[X] \le \mu$), $P_X^*$ is unique and finitely supported (with an atom at $0$). Under average power only ($\mathbb{E}[X] \le \mu$), $P_X^*$ is discrete with countably infinite support and no finite accumulation points.
- **High- and low-power capacity asymptotics (Lapidoth–Moser, 2009; Lapidoth–Shamai–Moser, 2011):** Established tight high-SNR asymptotics $C_{\mathrm{DTPC}}(\lambda_0, A, A) = \frac{1}{2}\ln\frac{2A}{\pi e} + o(1)$ (nats) and $C_{\mathrm{DTPC}}(0, \infty, \mu) = \frac{1}{2}\ln\frac{e\mu}{2\pi} + o(1)$, as well as exact low-power scaling.
- **Non-asymptotic duality upper bounds (Martinez, 2007; Lapidoth–Moser, 2009; Cheraghchi–Ribeiro, 2019):** Convex duality with tailored output test distributions (including modified digamma distributions in Cheraghchi–Ribeiro 2019) yields sharp non-asymptotic upper bounds across all regimes, though no closed-form capacity is known.
- **Bounds on optimal support cardinality (Dytso–Barletta–Shamai, 2021; Barletta–Dytso–Shamai, 2024):** Dytso, Barletta and Shamai proved $N(A) = O(A \log^2 A)$ and $N(A) = \Omega(\sqrt{A})$ (the latter from $N \ge e^{C}$ and $C \approx \frac12 \log A$); Barletta, Dytso and Shamai (arXiv:2401.05045) sharpened the upper bound to $O(A)$ for $\lambda_0 = 0$, gave an explicit bound linear in $A$ for fixed $\lambda_0 > 0$, showed exactly two mass points when $A + \lambda_0 < e$, and report numerics suggesting $N(A) \approx A^{0.71}$, i.e. that neither bound is tight. The exact order is open.

## References

- S. Shamai (Shitz), "Capacity of a pulse amplitude modulated direct detection photon channel," *IEE Proc. I — Commun., Speech and Vision*, 137(6):424–430, 1990.
- A. Lapidoth and S. M. Moser, "On the capacity of the discrete-time Poisson channel," *IEEE Trans. Inf. Theory*, 55(1):303–322, 2009.
- J. Cao, S. Hranilovic, and J. Chen, "Capacity-achieving distributions for the discrete-time Poisson channel — Part I & II," *IEEE Trans. Commun.*, 62(1):194–213, 2014.
- M. Cheraghchi and J. Ribeiro, "Improved capacity upper bounds for the discrete-time Poisson channel," *IEEE Trans. Inf. Theory*, 65(7):4052–4068, 2019.
- A. Dytso, L. Barletta, and S. Shamai (Shitz), "Properties of the support of the capacity-achieving distribution of the amplitude-constrained Poisson noise channel," *IEEE Trans. Inf. Theory*, 2021 (arXiv:2104.14431).
- L. Barletta, A. Dytso, and S. Shamai (Shitz), "Improved bounds on the number of support points of the capacity-achieving input for amplitude constrained Poisson channels," arXiv:2401.05045, 2024.
