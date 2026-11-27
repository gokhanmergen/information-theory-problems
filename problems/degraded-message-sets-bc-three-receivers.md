---
id: degraded-message-sets-bc-three-receivers
title: Three-Receiver Broadcast Channel with Two Degraded Message Sets
status: open
category: network-info-theory
posed_by: János Körner and Katalin Marton; Chandra Nair and Abbas El Gamal
posed_year: 2009
tags: [network-information-theory, broadcast-channel, degraded-message-sets, three-receivers, indirect-decoding, superposition-coding]
lean_module: InfoTheory.Problems.DegradedMessageSetsBcThreeReceivers
lean_file: lean/InfoTheory/Problems/DegradedMessageSetsBcThreeReceivers.lean
review: expert-approved (2026-11-26)
---

## Statement

A three-receiver discrete memoryless broadcast channel (3-DMBC) $p(y_1, y_2, y_3 \mid x)$ on
finite alphabets carries two messages:

- a common message $M_0 \in [2^{nR_0}]$, which must be decoded by all three receivers;
- a private message $M_1 \in [2^{nR_1}]$, which must be decoded by receiver $Y_1$ only.

This is the "two degraded message sets" configuration. The capacity region $\mathcal{C}(W)$ is
the closure of the achievable $(R_0, R_1)$ under average error over uniform messages.

Nair and El Gamal (2009, Prop. 5) proved that the following region is achievable. It
combines superposition coding, Marton-style binning of two satellite layers, and *indirect
decoding*. The region is the set of $(R_0, R_1) \ge 0$ such that
$$
\begin{aligned}
R_0 &\le \min\{I(U_2;Y_2),\, I(U_3;Y_3)\},\\
2R_0 &\le I(U_2;Y_2) + I(U_3;Y_3) - I(U_2;U_3 \mid U_1),\\
R_1 &\le \min\{I(X;Y_1 \mid U_2) + I(X;Y_1 \mid U_3),\, I(X;Y_1 \mid U_1)\},\\
R_0 + R_1 &\le \min\{I(X;Y_1),\, I(U_2;Y_2) + I(X;Y_1 \mid U_2),\, I(U_3;Y_3) + I(X;Y_1 \mid U_3)\},\\
2R_0 + R_1 &\le I(U_2;Y_2) + I(U_3;Y_3) + I(X;Y_1 \mid U_2, U_3) - I(U_2;U_3 \mid U_1),\\
2R_0 + 2R_1 &\le I(U_2;Y_2) + I(X;Y_1 \mid U_2) + I(U_3;Y_3) + I(X;Y_1 \mid U_3) - I(U_2;U_3 \mid U_1),
\end{aligned}
$$
for some $p(u_1, u_2, u_3, x)$ such that $U_1 \to U_2 \to (U_3, X)$ and
$U_1 \to U_3 \to (U_2, X)$ are Markov chains.

**Does this Nair–El Gamal inner bound (closed) equal $\mathcal{C}(W)$ for every finite-alphabet
3-DMBC?**

A disproof (a channel where some scheme strictly beats it) and a proof (a matching converse)
would both resolve the question. In general, neither is known.

## Background

For two receivers, Körner and Marton (1977) showed that superposition coding achieves the
capacity region with degraded message sets:
$R_0 \le \min_j I(U;Y_j)$ and $R_1 \le I(X;Y_1 \mid U)$. The straightforward extension to
three receivers adds $I(U;Y_3)$ to the minimum. It was conjectured to be optimal for
multilevel channels (Borade–Zheng–Trott 2007, Conjecture 5). Nair and El Gamal (2009)
disproved this. They showed that receiver $Y_2$, which cannot decode the cloud centre
directly, can still recover $M_0$ by decoding a list of satellite codewords ("indirect
decoding"), and that this enlarges the region strictly. They established the capacity region of
the multilevel channel ($Y_3$ a degraded version of $Y_1$), and their two bounds coincide
whenever $Y_1$ is less noisy than $Y_3$. In general the inner bound above and their outer
bound (Prop. 6) "appear to be very different". The authors argue that the three-receiver
degraded-message-set problem is at least as hard as the two-receiver broadcast channel with
common and private messages, which is itself open.

## What is known

- **Two receivers:** solved (Körner–Marton 1977).
- **Three receivers, $M_0$ to all and $M_1$ to $Y_1$ (this problem):**
  - Capacity is known for the multilevel broadcast channel
    $p(y_1,y_2 \mid x)\, p(y_3 \mid y_1)$, where it equals the region above with $U_3 = U_1$
    (Nair–El Gamal 2009, Thm. 1). It is also known when $Y_1$ is less noisy than $Y_3$ (Prop. 7;
    by symmetry also $Y_2$). In both cases the straightforward Körner–Marton extension is
    strictly suboptimal for some channels (Nair–El Gamal 2009, Sec. IV).
  - The general outer bound is Nair–El Gamal 2009, Prop. 6. Inner and outer bounds do not
    match in general.
  - Further tight cases are recorded in
    `attempts/degraded-message-sets-bc-three-receivers/2026-11-26-claude-opus-5-5-audit-and-crossed-products.md`
    (unverified). The first is *crossed degraded products*: X = (A, B), receiver 2 sees only
    A, receiver 3 sees only B, and receiver 1 sees degraded versions of both. There none of
    the orderings above hold, and the inequality 2R₀ + R₁ ≤ … of the inner bound is a
    capacity face. The second, probably folklore, is the case where Y₂ is less noisy than Y₃
    or vice versa, which reduces to Körner–Marton. The same attempt re-derives Prop. 5 from the
    code constraints by Fourier–Motzkin elimination and finds no transcription error.
  - Salman–Varanasi (arXiv:1812.10520) extend capacity results to further classes defined by
    pairwise less-noisy and more-capable orderings, for $K$ receivers with two nested
    multicast messages. They split the private message into as many parts as there are
    common-message-only receivers and use indirect decoding.
- **Three receivers, $M_0$ to all and $M_1$ to $Y_1$ and $Y_2$ (the other two-message
  configuration):** Nair–El Gamal (2009, Cor. 1) show that the natural superposition region
  is optimal for deterministic channels and when $Y_1$ and $Y_2$ are both less noisy than
  $Y_3$. Nair–Wang (ISIT 2009) prove tightness for a class where the standard inner and outer
  bounds differ. Nair–Yazdanpanah (ISIT 2017) show that superposition coding is **not** optimal
  in general, which resolves Open Problem 8.2 of El Gamal–Kim. This configuration is not the one
  formalized here.
- **More general message sets / more receivers:** for general message sets, Romero–Varanasi
  (arXiv:2011.04745) give a general rate-splitting, superposition and binning framework. For
  degraded and less-noisy orderings see Nair–Wang (2011). For three-receiver more-capable
  channels, superposition coding is not optimal for private messages (Nair–Xia 2012).
- No paper we found (searches: Nair–El Gamal follow-ups, the Salman–Varanasi and
  Romero–Varanasi frameworks, the 2024 quantum three-receiver papers) claims either a matching
  converse for the inner bound above in general, or a channel where it is strictly beaten in
  this configuration.

## Notes on the formalization (for expert review)

- **Auxiliaries.** The Lean definition takes an arbitrary $p(u_1,u_2,u_3,x)$ and uses
  $V_2 = (U_1,U_2)$ and $V_3 = (U_1,U_3)$ in place of $U_2, U_3$. This makes the two Markov chains
  hold automatically. Conversely, for any distribution satisfying them, the mutual
  informations are unchanged by this substitution: $I(U_1U_2;Y_2) = I(U_2;Y_2)$ and
  $I(X;Y_1 \mid U_1U_2) = I(X;Y_1 \mid U_2)$. So the union equals Prop. 5's region
  (cf. Nair–El Gamal 2009, Remark 1 after Prop. 5).
- **Convexity.** The region is convex without an explicit time-sharing variable. Absorbing $Q$
  into $U_1$ keeps every conditional term equal to its $Q$-average and can only increase the
  unconditional terms $I(V_j;Y_j)$ and $I(X;Y_1)$. The subtracted term $I(V_2;V_3 \mid U_1)$
  stays equal to its average. So `Statement` cannot be refuted merely by non-convexity.
- **Sanity checks.** With all auxiliaries constant, the bound gives the axis segment
  $R_1 \le I(X;Y_1)$. With $U_1 = U_2 = U_3 = X$ it gives
  $R_0 \le \min\{I(X;Y_1), I(X;Y_2), I(X;Y_3)\}$, the compound-channel common-message rate. Both
  are correct. The certificate proves that the operational region's $R_0 = 0$ edge is exactly
  $[0, C(p(y_1|x))]$ and that $R_0 + R_1 \le C(p(y_1|x))$ on the operational region.
- **Choice of question.** Asking whether this *particular* inner bound is tight is a design
  choice. It mirrors the catalog's existing "Marton = capacity" entries. If an improved scheme
  for this configuration appears, the statement becomes refutable. That is a legitimate
  resolution, but the expert should confirm that no such improvement is already known (e.g.
  from the Salman–Varanasi or Romero–Varanasi frameworks specialised to three receivers).

## References

- J. Körner and K. Marton, "General broadcast channels with degraded message sets," *IEEE
  Trans. Inf. Theory*, vol. 23, no. 1, pp. 60–64, 1977.
- S. Borade, L. Zheng, M. Trott, "Multilevel broadcast networks," *Proc. IEEE ISIT*, 2007.
- C. Nair and A. El Gamal, "The capacity region of a class of three-receiver broadcast channels
  with degraded message sets," *IEEE Trans. Inf. Theory*, vol. 55, no. 10, pp. 4479–4493, 2009
  (arXiv:0712.3327).
- C. Nair and Z. V. Wang, "On the inner and outer bounds of 3-receiver broadcast channels with
  2-degraded message sets," *Proc. IEEE ISIT*, pp. 1844–1848, 2009 (arXiv:0806.4415).
- C. Nair and Z. V. Wang, "The capacity region of the three receiver less noisy broadcast
  channel," *IEEE Trans. Inf. Theory*, vol. 57, no. 7, pp. 4058–4062, 2011.
- C. Nair and L. Xia, "On three-receiver more capable channels," *Proc. IEEE ISIT*,
  pp. 378–382, 2012.
- C. Nair and M. Yazdanpanah, "Sub-optimality of superposition coding region for three
  receiver broadcast channel with two degraded message sets," *Proc. IEEE ISIT*,
  pp. 1038–1042, 2017.
- M. Salman and M. K. Varanasi, "Capacity results for the K-user broadcast channel with two
  nested multicast messages," arXiv:1812.10520, 2018.
- H. Romero and M. K. Varanasi, "Rate splitting, superposition coding and binning for
  groupcasting over the broadcast channel: a general framework," arXiv:2011.04745, 2020.
- A. El Gamal and Y.-H. Kim, *Network Information Theory*, Cambridge Univ. Press, 2011, §8.1–8.2.
