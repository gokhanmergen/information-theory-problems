---
id: broadcast-channel-three-receivers
title: Capacity Region of the Three-Receiver Broadcast Channel
status: open
category: network-info-theory
posed_by: Thomas Cover
posed_year: 1972
tags: [network-information-theory, broadcast-channel, three-receivers, multiuser]
lean_module: InfoTheory.Problems.BroadcastChannelThreeReceivers
lean_file: lean/InfoTheory/Problems/BroadcastChannelThreeReceivers.lean
---

## Statement

A three-receiver discrete memoryless broadcast channel (3-DMBC) is a channel
$W : \mathcal{X} \to \mathcal{Y}_1 \times \mathcal{Y}_2 \times \mathcal{Y}_3$ specified
by transition probabilities $p(y_1, y_2, y_3 \mid x)$. A single transmitter sends three
independent private messages $(M_1, M_2, M_3)$ at rates $(R_1, R_2, R_3)$ so that receiver
$j \in \{1, 2, 3\}$ reliably decodes $M_j$ from $Y_j^n$.

The **UM region** of Padakandla and Pradhan ("unstructured Marton" coding) is, in their words,
the currently known largest achievable rate region for the 3-DMBC built from unstructured
codes (superposition and binning). Fix finite auxiliaries and a pmf
$p(q, w, u_{12}, u_{23}, u_{31}, v_1, v_2, v_3, x)$ with
$(Q, W, U_{12}, U_{23}, U_{31}, V_1, V_2, V_3) - X - (Y_1, Y_2, Y_3)$. Here $Q$ is time sharing,
$W$ a public cloud decoded by all receivers, $U_{ij}$ a semi-private cloud decoded by
receivers $i$ and $j$, and $V_j$ a private satellite decoded by receiver $j$. Message $j$ is
split as $R_j = K_j + K_{jk} + L_{ij} + T_j$ (public part, its parts in $U_{jk}$ and $U_{ij}$,
private part), and the $U_{ij}$- and $V_j$-codebooks are binned at rates $S_{ij}$ and $S_j$.
Below, $(i, j, k)$ ranges over the cyclic triples $(1,2,3), (2,3,1), (3,1,2)$,
$U := (U_{12}, U_{23}, U_{31})$, $\Sigma_U := S_{12} + S_{23} + S_{31}$, and
$I(A;B;C \mid D) := I(A;B \mid D) + I(A,B;C \mid D)$. Write
$J_i := I(V_i; U_{jk} \mid U_{ij}, U_{ki}, W, Q)$ and $\Gamma_U := I(U_{12}; U_{23}; U_{31} \mid W, Q)$.

*Covering (encoding) constraints*, for each cyclic $(i, j, k)$:
$$
\begin{aligned}
S_{ij} + S_{jk} &\ge I(U_{ij}; U_{jk} \mid W, Q), \qquad \Sigma_U \ge \Gamma_U, \qquad
S_i + \Sigma_U \ge \Gamma_U + J_i, \\
S_i + S_j + \Sigma_U &\ge J_i + J_j + \Gamma_U + I(V_i; V_j \mid U, W, Q), \\
S_1 + S_2 + S_3 + \Sigma_U &\ge J_1 + J_2 + J_3 + I(V_1; V_2; V_3 \mid U, W, Q) + \Gamma_U.
\end{aligned}
$$
*Packing (decoding) constraints* at receiver $i$, with $\Delta_i := I(U_{ij}; U_{ki} \mid Q, W)$:
$$
\begin{aligned}
T_i + S_i &\le I(V_i; Y_i \mid Q, W, U_{ij}, U_{ki}), \\
K_{ij} + L_{ij} + S_{ij} + T_i + S_i &\le I(U_{ij}, V_i; Y_i \mid Q, W, U_{ki}) + \Delta_i, \\
K_{ki} + L_{ki} + S_{ki} + T_i + S_i &\le I(U_{ki}, V_i; Y_i \mid Q, W, U_{ij}) + \Delta_i, \\
K_{ij} + L_{ij} + S_{ij} + K_{ki} + L_{ki} + S_{ki} + T_i + S_i
  &\le I(U_{ij}, U_{ki}, V_i; Y_i \mid Q, W) + \Delta_i, \\
K_1 + K_2 + K_3 + K_{ij} + L_{ij} + S_{ij} + K_{ki} + L_{ki} + S_{ki} + T_i + S_i
  &\le I(W, U_{ij}, U_{ki}, V_i; Y_i \mid Q) + \Delta_i.
\end{aligned}
$$
The UM region $\alpha_U(W)$ is the closed convex hull of the union, over all such pmfs, of the
rate triples for which nonnegative $K_j, K_{ij}, L_{ij}, S_{ij}, T_j, S_j$ satisfying all these
constraints exist (Padakandla–Pradhan, arXiv:1207.3146v6, §II-D, eqs. (1)–(11), without
cost). The source uses strict inequalities and $S_i > 0$; taken literally these make the
region empty whenever one output is independent of the input, so the formal statement uses
non-strict inequalities. Padakandla–Pradhan prove achievability of the strict-inequality
region (their Theorem 2). The non-strict region is still achievable (sketch, 2026-11-27 review):
if every receiver has positive capacity, mixing in a strictly feasible test channel ($V_i = X$
with small bin rates) through $Q$ with weight $\varepsilon$ makes every non-strict point a limit
of strict ones; if receiver $k$ has zero capacity, its constraints force $R_k = 0$ and the other
two rates lie in Marton's region by the projection argument in the caveat below. So
$\alpha_U(W) \subseteq \mathcal{C}_3(W)$.

**Does the UM region equal the exact capacity region $\mathcal{C}_3(W)$ for every
finite-alphabet three-receiver discrete memoryless broadcast channel $W$?**

In Lean (`umRegion`), all auxiliary alphabets are `Fin k` for one `k`; `U i` and `V i` are
indexed by `i : Fin 3`, with `U 0, U 1, U 2 = U₁₂, U₂₃, U₃₁`; the rate vectors are
`K j = K_j`, `Ks i = K_{i,i+1}`, `L i = L_{i,i+1}`, `S i = S_{i,i+1}`, `T j = T_j`, `Sv j = S_j`.

> **Statement-fix (2026-11-27).** The previous statement asked whether a region with a common
> cloud $W_0$ and multivariate covering over $(U_1, U_2, U_3)$ (in Lean: pairwise clouds folded
> into the binned auxiliaries) equals capacity. That was false: with a constant third output it
> collapses to Marton's region *without* a superposition variable for receivers 1 and 2, which
> is certifiably below capacity for the degraded Gohari–El Gamal–Anantharam channel
> (`sup (R₁ + 2.35 R₂) ≤ 0.12131588 < 0.12131597`; an independent review certified the
> stronger bound `≤ 0.1201`); see
> `attempts/broadcast-channel-three-receivers/2026-11-26-claude-opus-5-5-useless-receiver-catalog-error.md`.
> The UM region passes this test: for every 3-DMBC, taking $Q, W$ constant, $U_{12}$ as
> Marton's common auxiliary and $U_{23}, U_{31}, V_3$ constant reduces its constraints to the
> rate-split form of Marton's region *with* common auxiliary for $(Y_1, Y_2)$, so
> $\alpha_U(W) \supseteq \mathcal{R}_{\mathrm{Marton}}(Y_1, Y_2) \times \{0\}$ (in particular
> it contains superposition coding).

## Background

Moving from two receivers to three introduces genuinely new network phenomena that do not
appear in the two-receiver setting. Even for **degraded message sets** — where all three
receivers demand a common message $M_0$ and only receiver $1$ demands a private message
$M_1$ — Nair and El Gamal (2009) proved that the natural generalization of Körner–Marton
superposition coding is strictly suboptimal, and that **indirect decoding** (where a
receiver decodes a satellite codeword without being required to output its message) strictly
enlarges the achievable region. For three private messages, pairwise clouds
$(U_{12}, U_{23}, U_{31})$, indirect decoding, and structured coding may all interact,
making the three-receiver broadcast channel substantially harder than the two-receiver case.

## What is known

- The capacity region is known for three-receiver *degraded* broadcast channels
  (Bergmans 1973; Gallager 1974), *less noisy* three-receiver broadcast channels, where
  superposition coding is optimal (Nair–Wang 2011), and *Gaussian MIMO* broadcast channels
  (Weingarten–Steinberg–Shamai 2006).
- For three-receiver broadcast channels with degraded message sets $(M_0, M_1)$, Körner–Marton
  superposition is strictly suboptimal (Nair–El Gamal 2009); Nair and El Gamal established
  capacity for the case where $Y_1$ is less noisy than $Y_2$ or $Y_3$ and introduced the
  indirect-decoding inner bound, whose optimality in general remains open.
- For three-receiver *deterministic* broadcast channels (unlike the two-receiver case solved
  by Marton 1979 / Pinsker 1978), even the capacity region with common and private messages
  is open in general, though special cases (e.g., degraded message sets or two-message
  deterministic channels) have been resolved (Nair–El Gamal 2009; Borade–Zheng–Trott 2007).
- Multivariate covering (El Gamal–Kim 2011, Lemma 8.2) combined with superposition gives
  three-receiver Marton-type inner bounds; the UM region above, with public, semi-private and
  private layers, is the largest known one built from unstructured codes
  (Padakandla–Pradhan).
  Indirect decoding (Nair–El Gamal 2009) and auxiliary-receiver outer bounds (Gohari–Nair
  2022) have been studied; no matching converse is known. The UM region contains the capacity region of
  degraded 3-DMBCs ($W$, $U_{12}$, $V_1$ carry $M_3$, $M_2$, $M_1$).
- **The UM region is not always optimal with costs.** Padakandla–Pradhan (arXiv:1207.3146)
  give 3-DMBCs *with input cost constraints* on which coset (linear) codes strictly beat the
  UM region. Whether this happens without costs, as asked above, is open.
- **Caveat via two receivers.** With a useless third receiver the question above contains the
  two-receiver question "Marton's region = capacity" (`broadcast-channel`). Huang, Liu and Liu
  (arXiv:2608.19869, 2026; not yet peer reviewed) claim a two-receiver DMBC on which
  multi-letter Marton coding beats the single-letter Marton region. Conversely, for every
  3-DMBC the $(R_1, R_2)$ projection of the UM region lies inside Marton's region for
  $(Y_1, Y_2)$ (sketch, 2026-11-27 review: set $\bar W = (Q, W, U_{12})$,
  $\bar U = (U_{31}, V_1)$, $\bar V = (U_{23}, V_2)$ and combine receiver 1's constraint (11),
  receiver 2's (8) and (11), and covering constraint (5); an LP check on 3000 random instances
  found no violation). So the statement here implies the two-receiver statement, and if the
  Huang–Liu–Liu claim holds the answer here is "no" as well. A reviewer (2026-11-27) judged the UM-based statement probably false even
  without costs. It is kept because it is the sharpest unstructured-code question the
  literature poses, and a disproof would be a genuine result.
## References

- T. M. Cover, "Broadcast channels," *IEEE Trans. Inf. Theory*, vol. 18, no. 1, pp. 2–14,
  1972.
- C. Nair and A. El Gamal, "The capacity region of a class of three-receiver broadcast
  channels with degraded message sets," *IEEE Trans. Inf. Theory*, vol. 55, no. 10,
  pp. 4479–4493, 2009.
- C. Nair and Z. V. Wang, "The capacity region of the three receiver less noisy broadcast
  channel," *IEEE Trans. Inf. Theory*, vol. 57, no. 7, pp. 4058–4062, 2011.
- A. Gohari and C. Nair, "Outer bounds for multiuser settings: the auxiliary receiver
  approach," *IEEE Trans. Inf. Theory*, vol. 68, no. 2, pp. 701–736, 2022.
- A. El Gamal and Y.-H. Kim, *Network Information Theory*, Cambridge Univ. Press, 2011,
  Ch. 8.
- A. Gohari, A. El Gamal, and V. Anantharam, "On Marton's inner bound for the general
  broadcast channel," *IEEE Trans. Inf. Theory*, vol. 60, no. 7, 2014 (arXiv:1006.5166).
- A. Padakandla and S. S. Pradhan, "Achievable rate region for three user discrete broadcast
  channel based on coset codes," arXiv:1207.3146v6, 2015 (conference version: Proc. IEEE ISIT
  2013).
- P. P. Bergmans, "Random coding theorem for broadcast channels with degraded components,"
  *IEEE Trans. Inf. Theory*, vol. 19, no. 2, pp. 197–207, 1973.
- M. Huang, Y. Liu, and Y. Liu, "Sub-optimality of Marton's inner bound for the
  two-receiver broadcast channel," arXiv:2608.19869, 2026.
