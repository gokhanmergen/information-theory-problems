---
id: relay-channel
title: Capacity of the Relay Channel
status: open
category: network-info-theory
posed_by: van der Meulen
posed_year: 1971
tags: [network-information-theory, relaying, cooperation]
lean_module: InfoTheory.Problems.RelayChannel
lean_file: lean/InfoTheory/Problems/RelayChannel.lean
---

## Statement

A relay channel $(\mathcal{X} \times \mathcal{X}_r,\; p(y, y_r \mid x, x_r),\;
\mathcal{Y} \times \mathcal{Y}_r)$ has a sender $X$, a receiver observing $Y$, and a
relay that observes $Y_r$ and transmits $X_r$ (causally, with $X_{r,i}$ a function of
$Y_r^{i-1}$) to help.

**Determine the capacity $C$ — a single-letter characterization — of the general
discrete memoryless relay channel.** The Gaussian case with fixed channel gains is
already open.

The formal statement asks whether the best classical single-letter scheme, Cover–El Gamal
Theorem 7 (partial decode-forward combined with compress-forward, with time sharing), is
capacity-achieving. In the three-constraint form of Chong–Motani (2011, Lemma 2) and
El Gamal–Gohari–Nair (orthogonal-receiver paper, Theorem 1), $R_{\rm Thm7}$ is the
supremum of all $R$ with
$$
\begin{aligned}
R &\le I(X, X_r; Y \mid Q) - I(Y_r; V \mid U, X, X_r, Y, Q),\\
R &\le I(X; V, Y \mid U, X_r, Q) + I(U; Y_r \mid W, X_r, Q),\\
R &\le I(X; V, Y \mid U, X_r, Q) + I(U; Y_r \mid W, X_r, Q) + I(X_r; Y \mid W, Q)
       - I(Y_r; V \mid U, X_r, Y, Q).
\end{aligned}
$$
for some finite auxiliaries with joint law
$p(q)\,p(w\mid q)\,p(u\mid w,q)\,p(x\mid u,q)\,p(x_r\mid w,q)\,p(y,y_r\mid x,x_r)\,p(v\mid u,x_r,y_r,q)$.

**Does $R_{\rm Thm7} = C$ for every finite-alphabet discrete memoryless relay channel $p(y, y_r \mid x, x_r)$?** (The auxiliary $W$ above is not the channel; in Lean the channel is `W` and the auxiliary alphabet is `Fin kW`.)

In Lean: `Statement : ∀ kX kXr kY kYr (W : RelayChannel (Fin kX) (Fin kXr) (Fin kY) (Fin kYr)),
relayCapacity W = coverElGamalTheorem7Rate W`. `thm7Joint` is the joint law above on tuples
$(q, w, u, x, x_r, y, y_r, v)$, with all auxiliary alphabets `Fin k`; `thm7MinRate` is the
minimum of the three right-hand sides; `coverElGamalTheorem7Rate W` is its `sSup` over all
auxiliary alphabets and kernels. That set is nonempty and bounded by $\log_2|\mathcal Y|$
(`Known.Certificates.RelayChannel`).

> **Statement-fix (2026-11-27).** The previous `coverElGamalTheorem7Rate` kept only two of
> Theorem 7's three constraints and allowed an arbitrary joint law $P(u,x,x_r)$, which credits
> compress-forward with coherent source and relay inputs. On a 4×2→6×2 channel (the relay
> observes the destination's noise; the destination sees $X_1\oplus Z$ and the adder
> $X_2+X_r$) capacity is $3/2$ but the old functional equals $\log_2 3$, so the old statement
> was false. The statement now uses the faithful three-constraint form above, which equals
> $3/2$ on that channel; see
> `attempts/relay-channel/2026-11-26-claude-opus-5-5-thm7-transcription-catalog-error.md`.
> The mathematical problem remains open.
>
> *Pending proposal (not applied).* An alternative repair would freeze the larger Chong–Motani
> Theorem 2 rate instead. With that rate frozen, a proof of Chong–Motani's conjecture
> (Theorem 2 > Theorem 7 on some channel) could not refute the Statement. Ready-to-apply Lean
> files are in
> `attempts/relay-channel/2026-11-27-claude-opus-5-5-chong-motani-statement-proposal.md`.

## Background

The three-node relay channel is the smallest network in which *cooperation* appears,
and it is the building block of every multi-hop and cooperative scheme in modern
wireless systems. Cover and El Gamal's 1979 paper introduced decode-and-forward and
compress-and-forward, the two strategies that (with their descendants, including noisy
network coding) still bracket what is achievable. That a three-node memoryless network
has unknown capacity after fifty years is the cleanest illustration of how hard network
information theory is.

## What is known

- Capacity is known for degraded and reversely degraded relay channels, and with
  feedback (Cover–El Gamal 1979); for semideterministic relay channels
  (El Gamal–Aref 1982); and for some classes with orthogonal components
  (El Gamal–Zahedi).
- The cutset bound (Cover–El Gamal) is the standard upper bound; it is **not tight in
  general** — Zhang (1988) showed a gap for a class of channels. Wu–Barnes–Özgür
  (2019) resolved Cover's 1987 question for the Gaussian primitive relay channel via
  high-dimensional isoperimetry: $C(C_0) < C(\infty)$ for **every finite** relay-link
  rate $C_0$, at every SNR — the critical rate is infinite. Reverse-hypercontractivity
  proofs followed (Liu–Özgür 2018), and El Gamal–Gohari–Nair (2022) gave a
  strengthened cutset bound by classical converse techniques, strictly tighter for
  Gaussian relay channels with nonzero gains and for binary symmetric relay channels,
  resolving Kim's conjecture for orthogonal-receiver relay channels.
- For the primitive relay channel with BSC components, capacity is known exactly for
  $R_0 \leq I(X;Z) - I(X;Y)$ (decode-forward meets the cutset bound) and
  $R_0 \geq H(Z\mid Y)$ (compress-forward meets it); in the interior interval the
  evaluated achievable rates and the cutset bound separate by up to ~0.1 bit in the
  repository's examples. An attempt to numerically maximize the
  El Gamal–Gohari–Nair converse objective produced candidate objective values, but
  these are lower estimates of a maximization-defined upper bound and therefore do
  not certify a tighter capacity upper bound. For the symmetric benchmark
  $\delta_1=\delta_2=0.1$, $R_0=0.2$, a later branch-and-bound evaluation of the
  specialized EGN theorem does certify
  $0.606432<C<0.649557$, improving the cutset upper bound $0.731004$. A
  fixed-input-bias concavity lemma reduces this certificate to a one-dimensional
  interval calculation (see attempt log).
- Best general achievability: combinations of partial decode-forward and
  compress-forward; noisy network coding (Lim–Kim–El Gamal–Chung 2011) recovers and
  extends compress-forward to networks. None matches the best known converses in
  general.
  - Cover–El Gamal Theorem 7 is stated in its three-constraint form by Chong–Motani
    (IEEE Trans. Inf. Theory 57(3), 2011, Lemma 2). Their Theorem 2 is at least as large,
    and they conjectured it can be strictly larger. El Gamal–Gohari–Nair ("Achievable rates
    for the relay channel with orthogonal receiver components") showed the two coincide
    for orthogonal receiver components, simplified the expression, and showed the
    Mondelli–Hassani–Urbanke (2019) scheme is subsumed by it. They also showed that
    time-sharing strictly improves pure compress-forward, which disproves an Ahlswede–Han
    conjecture.
  - We know of no standard DM relay channel on which a scheme provably beats Theorem 7. Wu
    (arXiv:1504.04515) beats it only with relay-to-source feedback, or when the source
    observes the relay's signal.
  - Ponniah (arXiv:2609.15709, 2026, unrefereed) claims $C=\max\{R_{\rm DF},R_{\rm U\text{-}CF},R_{\rm C\text{-}CF}\}$.
    This is refuted by the primitive-BSC time-sharing example, viewed as a DM relay channel
    with an orthogonal BSC link of capacity $0.3$: capacity is at least $0.5396$, while all
    three of Ponniah's rates are at most $0.5310$. The paper's definitions (82)–(97) are
    partly inconsistent. This bound reads each rate under the same joint law as its own
    feasibility constraint (see attempt log).
- Approximate capacity: for Gaussian relay networks, capacity is known within a
  constant gap (Avestimehr–Diggavi–Tse deterministic-model program).

## References

- E. C. van der Meulen, "Three-terminal communication channels," Adv. Appl.
  Probability, 1971.
- T. M. Cover and A. El Gamal, "Capacity theorems for the relay channel," IEEE Trans.
  Inf. Theory, 1979.
- Z. Zhang, "Partial converse for a relay channel," IEEE Trans. Inf. Theory, 1988.
- A. S. Avestimehr, S. N. Diggavi, and D. N. C. Tse, "Wireless network information
  flow: a deterministic approach," IEEE Trans. Inf. Theory, 2011.
- X. Wu, L. P. Barnes, and A. Özgür, "'The capacity of the relay channel': solution
  to Cover's problem in the Gaussian case," IEEE Trans. Inf. Theory, 2019;
  arXiv:1701.02043.
- A. El Gamal, A. Gohari, and C. Nair, "A strengthened cutset upper bound on the
  capacity of the relay channel and applications," IEEE Trans. Inf. Theory, 2022;
  arXiv:2101.11139.
- H.-F. Chong and M. Motani, "On achievable rates for the general relay channel," IEEE
  Trans. Inf. Theory 57(3):1249–1266, 2011.
- A. El Gamal, A. Gohari, and C. Nair, "Achievable rates for the relay channel with
  orthogonal receiver components," manuscript,
  http://chandra.ie.cuhk.edu.hk/pub/papers/NIT/Prim-Rel-LB.pdf.
- J. Liu and A. Özgür, "Capacity upper bounds for the relay channel via reverse
  hypercontractivity," IEEE Trans. Inf. Theory 66(9):5448–5455, 2020.
- X. Wu, A. Özgür, and L.-L. Xie, "Improving on the cut-set bound via geometric analysis
  of typical sets," IEEE Trans. Inf. Theory 63(4):2254–2277, 2017.
- M. Aleksic, P. Razaghi, and W. Yu, "Capacity of a class of modulo-sum relay channels,"
  IEEE Trans. Inf. Theory 55(3):921–930, 2009.
