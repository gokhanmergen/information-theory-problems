---
id: finite-state-channel-capacity
title: Finite-Memory Input Optimality for Indecomposable Finite-State Channels
status: open
category: channel-capacity
posed_by: Robert G. Gallager; Haim H. Permuter, Tsachy Weissman, and Andrea J. Goldsmith
posed_year: 1968
tags: [channel-capacity, finite-state-channel, markov-sources, channel-memory]
lean_module: InfoTheory.Problems.FiniteStateChannelCapacity
lean_file: lean/InfoTheory/Problems/FiniteStateChannelCapacity.lean
---

## Statement

A **Finite-State Channel (FSC)** with finite input alphabet $\mathcal{X}$, output alphabet $\mathcal{Y}$, and state space $\mathcal{S}$ is specified by a conditional transition law $W(y_t, s_t \mid x_t, s_{t-1})$ such that
$$P(y^n, s^n \mid x^n, s_0) = \prod_{t=1}^{n} W(y_t, s_t \mid x_t, s_{t-1}).$$
Following Gallager (1968, Sec. 4.6), an FSC is **indecomposable** if the influence of the initial state $s_0$ vanishes asymptotically: there exists $N \ge 1$ such that for every input block $x^N \in \mathcal{X}^N$, there exists a state $s^* \in \mathcal{S}$ reachable with strictly positive probability from *every* initial state $s_0 \in \mathcal{S}$ (i.e., $P(s_N = s^* \mid x^N, s_0) > 0$ for all $s_0 \in \mathcal{S}$).

By Gallager's coding theorem, the non-feedback capacity of an indecomposable FSC is independent of the initial state $s_0$ and equals the multi-letter limit
$$C(W) = \lim_{n \to \infty} \frac{1}{n} \max_{P(x^n)} I(X^n; Y^n \mid s_0).$$

**Problem (Finite-Order Markov Optimality for Indecomposable FSCs).** Does every indecomposable finite-state channel $W$ admit a *finite-order* stationary Markov input process (of some finite memory $M = M(W) < \infty$) whose asymptotic mutual information rate equals the exact capacity $C(W)$ — or does there exist an indecomposable FSC for which infinite input memory is strictly required to attain $C(W)$?

## Background

In his 1968 textbook, Gallager proved the coding theorem for indecomposable finite-state channels, expressing capacity as the multi-letter limit $C(W) = \lim_{n\to\infty} \frac{1}{n} \max_{P(x^n)} I(X^n; Y^n \mid s_0)$ and providing asymptotically converging upper and lower bounds $\underline{C}_n(W) \le C(W) \le \overline{C}_n(W)$. Yet even for the simplest two-state indecomposable FSCs without feedback — such as **Blackwell's Trapdoor Channel** (1961) and the **2-state Ising Channel** ($Y_t = X_t$ or $X_{t-1}$ with probability $1/2$ each) — no exact closed-form or single-letter capacity formula is known.

By contrast, when **noiseless feedback** is available, Permuter, Cuff, Van Roy, and Weissman (2008) and Permuter, Weissman, and Goldsmith (2009) showed that feedback capacity of unifilar indecomposable FSCs can be formulated via directed information and solved as an average-reward dynamic program — yielding exact closed-form capacities for the Trapdoor channel ($\log_2 \phi$, the golden ratio) and the Ising channel! Without feedback, however, the encoder cannot track the decoder's belief state, and even determining whether finite-order Markov inputs (the standard computational ansatz of Vontobel–Arnold 2001 and Kavčić 2001) can achieve the exact capacity $C(W)$ of every indecomposable FSC remains open.

## What is known

- **Multi-letter capacity theorem (Gallager, 1968):** For every indecomposable FSC, $C(W) = \lim_{n \to \infty} \frac{1}{n} \max_{P(x^n)} I(X^n; Y^n \mid s_0)$ exists independently of $s_0$ and satisfies $\underline{C}_n \le C(W) \le \overline{C}_n$ with $\overline{C}_n - \underline{C}_n \le \frac{\log_2 |\mathcal{S}|}{n}$.
- **Density of finite-order Markov sources:** The supremum over all finite-order stationary Markov input processes approaches $C(W)$ as the Markov order $M \to \infty$ (i.e., $\sup_{M \ge 0} C^{(M)}(W) = C(W)$), and generalized Blahut–Arimoto algorithms (Vontobel–Arnold 2001; Kavčić 2001) compute tight lower bounds $C^{(M)}(W)$ for small $M$.
- **Exact solutions with feedback (Permuter–Cuff–Van Roy–Weissman, 2008; Elishco–Permuter, 2014):** Dynamic programming yields closed-form *feedback* capacities for the Trapdoor channel ($\log_2 \frac{1+\sqrt{5}}{2} \approx 0.6942$ bits), the Ising channel, and several unifilar FSCs, whereas their *non-feedback* capacities remain open.
- **Computability for general non-indecomposable FSCs (Boche–Schaefer–Poor, 2020):** Without indecomposability, channel capacity can be Turing-uncomputable; with indecomposability, $C(W)$ is approximable via Gallager's bounds, while exact attainment by finite-order Markov inputs remains open.

## References

- R. G. Gallager, *Information Theory and Reliable Communication*, Wiley, 1968 (Section 4.6).
- D. Blackwell, "Information theory," in *Modern Mathematics for the Engineer*, 2nd series, McGraw-Hill, pp. 182–193, 1961.
- P. O. Vontobel and D. M. Arnold, "An upper bound on the capacity of channels with memory and constraint input," *Proc. IEEE Information Theory Workshop (ITW)*, pp. 147–149, 2001.
- H. H. Permuter, P. Cuff, B. Van Roy, and T. Weissman, "Capacity of the trapdoor channel with feedback," *IEEE Trans. Inf. Theory*, 54(7):3150–3165, 2008.
- H. H. Permuter, T. Weissman, and A. J. Goldsmith, "Finite state channels with time-invariant deterministic feedback," *IEEE Trans. Inf. Theory*, 55(2):644–662, 2009.
- O. Elishco and H. H. Permuter, "Capacity and coding for the Ising channel with feedback," *IEEE Trans. Inf. Theory*, 60(9):5138–5149, 2014.
