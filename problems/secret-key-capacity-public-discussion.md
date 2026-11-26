---
id: secret-key-capacity-public-discussion
title: Single-Letter Characterization of Secret Key Capacity with Unlimited Public Discussion
status: open
category: security-privacy
posed_by: Ueli M. Maurer; Rudolf Ahlswede and Imre Csiszár
posed_year: 1993
tags: [information-theoretic-security, secret-key-agreement, public-discussion, single-letterization]
lean_module: InfoTheory.Problems.SecretKeyCapacityPublicDiscussion
lean_file: lean/InfoTheory/Problems/SecretKeyCapacityPublicDiscussion.lean
---

## Statement

Alice, Bob, and Eve observe $n$ i.i.d. draws $(X^n, Y^n, Z^n)$ from a discrete memoryless source $P_{XYZ}$ over finite alphabets $\mathcal{X} \times \mathcal{Y} \times \mathcal{Z}$. Alice and Bob communicate interactively over an authenticated, noiseless, unlimited-rate public channel visible to Eve, producing a public transcript $T$ and local keys $K_A = K_A(X^n, T, R_A)$, $K_B = K_B(Y^n, T, R_B)$ over an alphabet $\mathcal{K}$. A secret key rate $R \ge 0$ is achievable if for every $\varepsilon > 0$ and sufficiently large $n$ there exists a protocol with $\frac{1}{n} \log_2 |\mathcal{K}| \ge R - \varepsilon$, agreement error $\Pr[K_A \ne K_B] \le \varepsilon$, and secrecy/uniformity $\log_2 |\mathcal{K}| - H(K_A \mid Z^n, T) \le n \varepsilon$. The supremum of achievable rates is the **secret key capacity** $S(X; Y \mathbin{\|} Z)$.

**Determine a single-letter (computable) characterization of $S(X; Y \mathbin{\|} Z)$ for a general discrete memoryless source $P_{XYZ}$.**

In particular, the accompanying Lean statement formalizes whether the strongest general single-letter upper bound — the Gohari–Anantharam (2010) sharpening of Renner–Wolf's reduced intrinsic information,
$$
U_{\mathrm{GA}}(X; Y \mathbin{\|} Z) := \inf_{P_{U \mid XYZ}} \big[ I(X; Y \downarrow Z U) + I(U; X, Y \mid Z) \big],
$$
equals $S(X; Y \mathbin{\|} Z)$ for all finite-alphabet sources $P_{XYZ}$.

## Background

Introduced independently by Maurer (1993) and Ahlswede and Csiszár (1993), secret key agreement from correlated randomness over a public channel is the foundational model of information-theoretic key generation. Unlike one-way communication (where Ahlswede and Csiszár gave an exact single-letter formula), allowing two-way interactive public discussion fundamentally changes the problem: Maurer's advantage distillation protocol achieves positive secret key rates even when Eve's channel is strictly less noisy than Bob's and the one-way capacity is zero.

Despite more than thirty years of intensive work, no single-letter characterization of $S(X; Y \mathbin{\|} Z)$ is known — not even for the elementary "satellite" binary source where $X, Y, Z$ are independent noisy observations of a common uniform bit through binary symmetric channels.

## What is known

- **One-way and bounded-round capacities:** Ahlswede and Csiszár (1993) characterized the one-way secret key capacity $S_{\to}(X; Y \mathbin{\|} Z) = \max_{U - V - X - YZ} [I(V; Y \mid U) - I(V; Z \mid U)]$. Multi-letter ($r$-round) interactive formulas with $r$ auxiliary random variables are known for every fixed round count $r$ (Gohari–Anantharam 2010), and $S_1 < S_2$ can be strict (Maurer 1993).
- **Solved special classes:**
  - When $Z = \emptyset$ (no eavesdropper), $S(X; Y) = I(X; Y)$ (Ahlswede–Csiszár 1993).
  - When $X - Y - Z$ or $Y - X - Z$ forms a Markov chain (degraded source), $S(X; Y \mathbin{\|} Z) = I(X; Y \mid Z)$.
  - Certain binary erasure and structured sources admit exact evaluations (Csiszár–Narayan 2004; Gohari–Anantharam 2010).
- **General upper bounds:**
  - **Intrinsic information** (Maurer–Wolf 1999): $S(X; Y \mathbin{\|} Z) \le I(X; Y \downarrow Z) := \inf_{P_{\bar{Z}|Z}} I(X; Y \mid \bar{Z})$, shown strictly loose in general by Renner and Wolf (2003).
  - **Reduced intrinsic information** (Renner–Wolf 2003): $S(X; Y \mathbin{\|} Z) \le I(X; Y \downarrow\downarrow Z) := \inf_{P_{U|XYZ}} [I(X; Y \downarrow ZU) + H(U)]$, classical analogue of squashed entanglement.
  - **Gohari–Anantharam upper bound** (2010): $S(X; Y \mathbin{\|} Z) \le \inf_{P_{U|XYZ}} [I(X; Y \downarrow ZU) + I(U; X, Y \mid Z)]$, which sharpens $I(X; Y \downarrow\downarrow Z)$ and remains tight on all known evaluated classes; whether it equals $S(X; Y \mathbin{\|} Z)$ in general is open.

## References

- U. M. Maurer, "Secret key agreement by public discussion from common information," *IEEE Trans. Inf. Theory* **39**(3), 733–742 (1993).
- R. Ahlswede and I. Csiszár, "Common randomness in information theory and cryptography—Part I: Secret sharing," *IEEE Trans. Inf. Theory* **39**(4), 1121–1132 (1993).
- U. M. Maurer and S. Wolf, "Unconditionally secure key agreement and the intrinsic conditional information," *IEEE Trans. Inf. Theory* **45**(2), 499–514 (1999).
- R. Renner and S. Wolf, "New bounds in secret-key agreement: The gap between formation and secrecy extraction," *EUROCRYPT 2003*, LNCS **2656**, 562–577 (2003).
- I. Csiszár and P. Narayan, "Secrecy capacities for multiple terminals," *IEEE Trans. Inf. Theory* **50**(12), 3047–3061 (2004).
- A. A. Gohari and V. Anantharam, "Information-theoretic key agreement of multiple terminals—Part I," *IEEE Trans. Inf. Theory* **56**(8), 3973–3996 (2010).
