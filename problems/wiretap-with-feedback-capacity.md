---
id: wiretap-with-feedback-capacity
title: Secrecy Capacity of the General Wiretap Channel with Noiseless Output Feedback
status: open
category: security-privacy
posed_by: Rudolf Ahlswede and Ning Cai
posed_year: 2006
tags: [information-theoretic-security, wiretap-channel, feedback, secrecy-capacity]
lean_module: InfoTheory.Problems.WiretapWithFeedbackCapacity
lean_file: lean/InfoTheory/Problems/WiretapWithFeedbackCapacity.lean
---

## Statement

Consider a discrete memoryless wiretap channel $W(y, z \mid x)$ over finite alphabets $\mathcal{X}, \mathcal{Y}, \mathcal{Z}$ equipped with **noiseless causal secure output feedback** from the legitimate receiver $Y$ to the transmitter $X$: at each channel use $i \in \{1, \dots, n\}$, the transmitter chooses $X_i$ as a function of the secret message $M$, local randomness $R$, and the past legitimate channel outputs $Y^{i-1}$ (which are not observed by the eavesdropper $Z$). A secrecy rate $R \ge 0$ is achievable if for every $\varepsilon > 0$ and sufficiently large $n$ there exists a feedback code of rate $R$ with average decoding error $\Pr[\hat{M}(Y^n) \ne M] \le \varepsilon$ and weak secrecy $I(M; Z^n) \le n \varepsilon$. Let $C_s^{\mathrm{fb}}(W)$ denote the supremum of achievable secrecy rates.

Ahlswede and Cai (2006) proved the universal single-letter upper bound
$$
C_s^{\mathrm{fb}}(W) \le \max_{P_X} \min\big\{ I(X; Y), \; H(Y \mid Z) \big\},
$$
and proved that equality holds for all physically degraded wiretap channels ($X - Y - Z$).

**Determine a single-letter characterization of $C_s^{\mathrm{fb}}(W)$ for a general (non-degraded) discrete memoryless wiretap channel $W(y, z \mid x)$ — and in particular determine whether the Ahlswede–Cai bound $\max_{P_X} \min\{I(X; Y), H(Y \mid Z)\}$ equals $C_s^{\mathrm{fb}}(W)$ for all DM wiretap channels.**

## Background

Unlike point-to-point channel capacity — which Shannon (1956) proved is never increased by feedback — noiseless output feedback can dramatically enlarge the secrecy capacity of a wiretap channel. Even when Eve's channel is strictly less noisy than Bob's (so the no-feedback secrecy capacity $C_s(W)$ is zero), Bob's private channel noise can be fed back to Alice to generate a secret key at rate $H(Y \mid X, Z)$, which Alice then uses as a one-time pad to transmit confidential messages.

However, when the channel is neither degraded ($X - Y - Z$) nor reversely degraded ($X - Z - Y$), a fundamental tension arises between sending high-rate codewords (which reduces $H(Y^n \mid Z^n)$ below $n H(Y \mid Z)$ by leaking $X^n$ to Eve) and sending unstructured randomness for secret-key generation. Resolving the optimal tradeoff between message coding and key generation via feedback remains open.

## What is known

- **Physically degraded wiretap channels ($X - Y - Z$):** Ahlswede and Cai (2006) proved
  $$
  C_s^{\mathrm{fb}}(W) = \max_{P_X} \min\{I(X; Y), \; H(Y \mid Z)\}.
  $$
- **Reversely degraded wiretap channels ($X - Z - Y$):** Ardestanizadeh, Franceschetti, Javidi, and Kim (2009) established the exact secrecy capacity with rate-limited secure feedback $R_f$; for unlimited noiseless output feedback, this again gives $C_s^{\mathrm{fb}}(W) = \max_{P_X} \min\{I(X; Y), \; H(Y \mid Z)\}$ (since $H(Y \mid X, Z) = H(Y \mid Z)$).
- **General non-degraded wiretap channels:**
  - The Ahlswede–Cai upper bound $C_s^{\mathrm{fb}}(W) \le \max_{P_X} \min\{I(X; Y), \; H(Y \mid Z)\}$ holds universally by Fano's inequality and the chain rule ($n R \lesssim I(M; Y^n \mid Z^n) \le H(Y^n \mid Z^n) \le \sum_i H(Y_i \mid Z_i)$).
  - Achievable lower bounds combining wiretap coding, block-Markov secret-key agreement from feedback, and auxiliary variables were developed by Ahlswede–Cai (2006), Lai–El Gamal–Poor (2008), Ardestanizadeh et al. (2009), Cohen–Kramer (2013), and Bassi–Piantanida–Shamai (2019), but they do not match the upper bound for general non-degraded channels (such as two independent binary symmetric channels $Y = X \oplus N_1$, $Z = X \oplus N_2$).
- **Public feedback:** When Eve also observes the feedback (public output feedback), feedback can still strictly increase secrecy capacity for non-degraded channels, and its single-letter capacity is likewise open in general.

## References

- R. Ahlswede and N. Cai, "Transmission, identification and common randomness capacities for wire-tap channels with secure feedback from the decoder," *General Theory of Information Transfer and Combinatorics*, LNCS **4123**, 258–275 (2006).
- L. Lai, H. El Gamal, and H. V. Poor, "The wiretap channel with feedback: Encryption over the channel," *IEEE Trans. Inf. Theory* **54**(11), 5059–5067 (2008).
- E. Ardestanizadeh, M. Franceschetti, T. Javidi, and Y.-H. Kim, "Wiretap channel with secure rate-limited feedback," *IEEE Trans. Inf. Theory* **55**(12), 5353–5361 (2009).
- A. Cohen and G. Kramer, "Feedback capacity of the wiretap channel," *Proc. IEEE ISIT*, 2013.
- G. Bassi, P. Piantanida, and S. Shamai (Shitz), "The wiretap channel with generalized feedback: Secure communication and key generation," *IEEE Trans. Inf. Theory* **65**(4), 2213–2233 (2019).
