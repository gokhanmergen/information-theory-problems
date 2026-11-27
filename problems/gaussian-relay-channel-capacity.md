---
id: gaussian-relay-channel-capacity
title: "Minimum Energy per Bit of the Symmetric Gaussian Relay Channel: Is Linear Relaying Optimal?"
status: open
category: network-info-theory
posed_by: Abbas El Gamal, Mehdi Mohseni, and Sina Zahedi
posed_year: 2006
tags: [network-information-theory, relay-channel, gaussian, cooperation, energy-per-bit, low-snr, linear-relaying]
lean_module: InfoTheory.Problems.GaussianRelayChannelCapacity
lean_file: lean/InfoTheory/Problems/GaussianRelayChannelCapacity.lean
---

## Statement

Consider the memoryless three-node AWGN relay channel with real channel gains
$(g_{12}, g_{13}, g_{23})$:
$$
Y_{r,i} = g_{12} X_i + Z_{r,i}, \qquad Y_i = g_{13} X_i + g_{23} X_{r,i} + Z_i,
$$
where $Z_{r,i}, Z_i \stackrel{\text{i.i.d.}}{\sim} \mathcal{N}(0, 1)$ are independent
standard Gaussian noises.

A rate $R \ge 0$ is *achievable at powers* $(P_1, P_2)$ if for every $\varepsilon > 0$ there is
$N$ such that for **every** $n \ge N$ there is a code with $M = \max(1, \lfloor 2^{nR} \rfloor)$
messages consisting of:
- source codewords $x^n(m)$ with $\sum_{i=1}^n x_i(m)^2 \le n P_1$ for every $m$;
- measurable, strictly causal relay maps $X_{r,i} = f_i(Y_r^{i-1})$ whose expected energy
  satisfies $\mathbb{E}\big[\sum_{i=1}^n X_{r,i}^2 \,\big|\, M = m\big] \le n P_2$ for every
  message $m$ (expectation over the relay noise);
- a measurable decoder with average error probability at most $\varepsilon$.

The code uses **linear relaying** if $f_i(y_r^{i-1}) = \sum_{j < i} d_{ij}\, y_{r,j}$ for some
real coefficients $d_{ij}$. The source encoder and the decoder remain arbitrary.

The **minimum energy per bit** counts source and relay energy with equal weight:
$$
E^*(g_{12}, g_{13}, g_{23}) = \inf\Big\{ \frac{P_1 + P_2}{R} \;:\; P_1, P_2 > 0,\ R > 0,\ R \text{ achievable at } (P_1, P_2) \Big\},
$$
evaluated in $[0, \infty]$, so an empty set gives $\infty$. Let $E^*_{\mathrm{lin}}$ be the same
infimum over linear-relaying codes only. Always $E^* \le E^*_{\mathrm{lin}}$.

**At unit gains $g_{12} = g_{13} = g_{23} = 1$, is $E^*(1, 1, 1) = E^*_{\mathrm{lin}}(1, 1, 1)$?**
That is, does linear relaying achieve the minimum energy per bit of the symmetric AWGN relay
channel?

Known: $\tfrac34 \cdot 2 \ln 2 \le E^*(1,1,1) \le E^*_{\mathrm{lin}}(1,1,1) \le 2 \ln 2$.

In Lean, with both sides valued in `ℝ≥0∞`:
`Statement : gaussianRelayMinEnergyPerBit false 1 1 1 = gaussianRelayMinEnergyPerBit true 1 1 1`.
The flag `true` restricts `IsGaussianRelayAchievable` to linear relays (`IsLinearRelay`).

## Background

The AWGN relay channel is the canonical continuous-alphabet model of wireless cooperative
communication. Even though it is defined by three scalar gains and two power constraints, its
capacity has remained open since Cover and El Gamal (1979).

El Gamal, Mohseni, and Zahedi (2006) showed that the minimum energy per bit, the low-power end of
the capacity question, is $E^* = \inf_{\gamma \ge 0} \lim_{P \to 0} (1 + \gamma) P / C(P, \gamma P)$.
It is also unknown. At low power, linear relaying (the relay forwards a linear combination of what
it has heard) gives the best known energy per bit in many regimes. Its own optimum is a
multi-letter, nonconvex problem (El Gamal–Mohseni–Zahedi 2006; Kosut–Effros–Langberg 2024).

The symmetric channel is the natural test case. There the relay hears the source exactly as well
as the destination does, decode-forward and compress-forward cannot save any energy (sketched
below), and it is not known whether relaying can lower the energy per bit at all. The question asks
whether the linear family is optimal there. A "yes" needs a new converse; a "no" needs a nonlinear
relaying scheme that provably beats every linear one.

## What is known

**Capacity.**
- The Gaussian cutset bound is
  $C_{\mathrm{CS}} = \max_{\rho \in [0, 1]} \min\!\big(C((g_{12}^2 + g_{13}^2)(1 - \rho^2) P_1),\; C(g_{13}^2 P_1 + g_{23}^2 P_2 + 2 \rho |g_{13} g_{23}| \sqrt{P_1 P_2})\big)$,
  with $C(s) = \tfrac12 \log_2(1 + s)$.
- El Gamal, Gohari, and Nair (2022) proved that the capacity of the Gaussian relay channel
  is **strictly smaller** than the cutset bound whenever $g_{12}, g_{13}, g_{23} \ne 0$
  and $P_1, P_2 > 0$. Their Theorem 2 gives an explicit Gaussian evaluation of the stronger
  bound. They do not discuss low SNR or energy per bit.
- For the *primitive* Gaussian relay channel (orthogonal noiseless relay-to-destination
  pipe of rate $C_0$), Wu, Barnes, and Özgür (2019) used spherical concentration of measure
  to prove that $C(C_0) < C(\infty)$ for every finite $C_0$, resolving Cover's 1987 open
  problem in the Gaussian case.
- Constant-gap capacity: compress-and-forward (and noisy network coding) achieves capacity
  to within $1/2$ bit per channel use for all channel gains and powers
  (Avestimehr–Diggavi–Tse 2011; Lim–Kim–El Gamal–Chung 2011).
- El Gamal, Mohseni, and Zahedi (2006) observed that the Gaussian compress-and-forward
  (side-information) rate is not concave in the power and improved it by bursty
  time-sharing (their eq. (8): transmit at powers $(P_1/\lambda, P_2/\lambda)$ a fraction
  $\lambda$ of the time). They also showed that a block-length-2 linear relaying scheme
  (their Example 1: the source repeats a scaled symbol, and the relay forwards a scaled copy
  of its previous received symbol) can beat both the generalized block-Markov
  (decode-and-forward) rate and the Gaussian compress-and-forward rate, notably at low SNR
  (their Fig. 3).
- Capacity is known exactly when $g_{13} = 0$: the channel is then physically degraded and
  decode-and-forward meets the cutset bound, giving
  $C = \min(C(g_{12}^2 P_1), C(g_{23}^2 P_2))$. As $g_{12} \to \infty$, decode-and-forward
  approaches the cutset bound. For this model (independent noises, all gains nonzero),
  however, the generalized block-Markov lower bound never meets the cutset bound
  (El Gamal–Mohseni–Zahedi 2006, Sec. 2), consistent with the strict gap of El Gamal–Gohari–Nair.
- The Gaussian hybrid DF/CF rate (Cover–El Gamal Theorem 7 with jointly Gaussian inputs, no
  time-sharing) is not the capacity. It equals the closed-form Gaussian compress-forward rate
  when $g_{12}^2 \le g_{13}^2$, and it is strictly beaten by bursty compress-forward and by EMZ
  Example 1 (e.g. $0.0883 > 0.0738$ at unit gains, $P_1 = P_2 = 1/10$). See
  `attempts/gaussian-relay-channel-capacity/2026-11-26-claude-opus-5-5-time-sharing-catalog-error.md`.

**Low SNR at unit gains with $P_1 = P_2 = P$.**
- The direct link with a silent relay gives $C_{\mathrm{Gauss}} \ge \tfrac12\log_2(1+P)$, i.e.
  slope $\ge 1/(2\ln 2) \approx 0.7213$ bits per unit power. This is certified in Lean.
- EMZ Example 1 with bursting gives $C_{\mathrm{Gauss}} \ge 0.88283\,P$ for $P \in (0, 1/10]$
  (2026-11-26 attempt).
- The cutset slope is $1/\ln 2 \approx 1.4427$.
- *[sketch + numerics; 2026-11-27 attempt]* The El Gamal–Gohari–Nair Gaussian bound is
  strictly below the cutset bound **to first order**:
  $C_{\mathrm{Gauss}}(1,1,1,P,P) \lesssim 1.1106\,P$ bits as $P \to 0$. A closed form of the
  first-order bound is certified $\le 1.1109$ by interval arithmetic. The reduction to that
  closed form is a sketch supported by a dense global search. See
  `attempts/gaussian-relay-channel-capacity/2026-11-27-claude-opus-5-5-egn-low-snr-slope.md`.

**Minimum energy per bit.** We use EMZ's normalization: $g_{13} = 1$, $a = g_{12}$,
$b = g_{23}$, unit noise variances.
- EMZ 2006, Thm. 1: $E^* = \inf_{\gamma \ge 0} \lim_{P \to 0} (1+\gamma)P / C(P, \gamma P)$.
  Moreover $(1+\gamma)P/C(P,\gamma P)$ is nondecreasing in $P$ (their Lemma 1).
- Cutset lower bound (EMZ 2006, Table II; Kosut–Effros–Langberg 2024, eq. (9)):
  $E^* \ge 2 \ln 2 \cdot \frac{1 + a^2 + b^2}{(1 + a^2)(1 + b^2)}$, which is
  $\tfrac34 \cdot 2 \ln 2 \approx 1.040$ at $a = b = 1$. It is attained at power ratio
  $P_2/P_1 \approx 0.2$, not at $P_1 = P_2$.
- Upper bounds:
  - Direct transmission gives $E^* \le 2 \ln 2$.
  - The block-Markov (decode-forward) bound is
    $2 \ln 2 \cdot \min\{1, \frac{a^2 + b^2}{a^2(1 + b^2)}\}$ for $\min(a,b) \le 1$ (EMZ 2006,
    Table II; KEL 2024, eq. (7)). It equals $2 \ln 2$ at $a = b = 1$.
  - Linear relaying improves the upper bound for many gains. EMZ Example 1 with time-sharing
    reduces the worst ratio of upper to lower bound from 2 to 1.7 (EMZ 2006, Sec. V-A, Fig. 8;
    the curves shown are for $b \in \{2, 5, 10, 20, 50\}$).
  - Kosut–Effros–Langberg (2024) obtained better bounds from high-dimensional rank-1 linear
    codes (via a differential equation; their Fig. 1 uses $a = 1.1$).
- Capacity with linear relaying is a limit of $k$-letter nonconvex optimizations
  (EMZ 2006, Sec. V). A single-letter characterization is known only for the
  frequency-division model, and is an open problem for the general model (EMZ 2006,
  Conclusion). $E^*_{\mathrm{lin}}$ has no closed form, and only upper bounds are known.
- For the frequency-division (FD-AWGN) relay channel, EMZ show that the bounds coincide for
  $b \le 1$, so relaying does not reduce the minimum energy per bit there. For the full-duplex
  model in the Statement, no such result is known.
- At $a = b = 1$, no published scheme is known to beat $2 \ln 2$:
  - *[sketch]* Decode-forward is limited by the relay cut $R \le C(g_{12}^2 P_1) = C(P_1)$, so
    $E \ge 2 \ln 2$.
  - *[sketch]* Gaussian compress-forward in all its variants (plain, bursty or time-shared, or
    with a coded time-sharing variable) uses independent source and relay signals. The
    multiple-access cut then gives $R \le C(P_1 + P_2)$, so again $E \ge 2 \ln 2$. The Thm. 7
    hybrid without coded time-sharing equals CF when $g_{12}^2 \le g_{13}^2$, so the same holds
    for it and its bursty versions.
  - *[heuristic]* Local optimization of the linear-relaying energy (EMZ / KEL eq. (6)) over
    block lengths $k \le 12$ finds nothing below $2 \ln 2$ at $a = b = 1$. At $a = 1$ it does
    beat $2 \ln 2$ for $b \ge 1.05$ (with $k = 12$), and this threshold decreases with $k$.
    It is therefore not known whether $E^*_{\mathrm{lin}}(1,1,1) < 2 \ln 2$ (2026-11-27 attempt,
    `code/lr_energy.py`).
- *[heuristic]* Optimizing the first-order El Gamal–Gohari–Nair bound over the power ratio gives
  $E^*(1,1,1) \gtrsim 0.934 \cdot 2 \ln 2$ (2026-11-27 attempt). So the cutset bound is very
  probably not tight for $E^*$. The window $[\approx 0.93, 1] \cdot 2 \ln 2$ remains open, as
  does whether linear relaying attains its bottom.

## Notes on the formalization (for expert review)

- **Statement fix 1 (2026-11-27).**
  - The original statement was "capacity = Cover–El Gamal Thm. 7 Gaussian hybrid DF/CF rate for
    all gains and powers". It was false: the rate has no power time-sharing, and EMZ 2006 beat it
    with bursty CF (eq. (8)) and with Example 1.
  - See the 2026-11-26 attempt, which has been verified.
- **Statement fix 2 (2026-11-27).**
  - Statement fix 1 (commit 49c683f) replaced it with "does
    $C_{\mathrm{Gauss}}(1,1,1,P,P)/P \to 1/\ln 2$ as $P \to 0^+$?", presented as equivalent to
    "minimum energy per bit = cutset lower bound".
  - That statement is believed **false**. The published El Gamal–Gohari–Nair (2022) Gaussian
    upper bound gives, to first order, $C_{\mathrm{Gauss}}(1,1,1,P,P) \lesssim 1.1106\,P$ bits.
  - Evidence level: the closed-form first-order functional is certified $\le 0.7700 \times$
    cutset by interval arithmetic. The step from the exact EGN bound to that functional is a
    `[sketch]`, supported by a dense 4-D grid plus multistart at $P = 10^{-2},\dots,10^{-5}$
    that converges to the same value. EGN's own theorems are cited. The implementation
    reproduces EGN's Fig. 4.
  - Details are in `attempts/gaussian-relay-channel-capacity/2026-11-27-claude-opus-5-5-egn-low-snr-slope.md`.
  - Two claims of that version were also wrong.
    - The fixed-ratio slope question is not EMZ's energy-per-bit question. $E^*$ optimizes the
      power split, and at unit gains the cutset value $\tfrac34 \cdot 2 \ln 2$ is attained at
      $P_2/P_1 \approx 0.2$, not at $P_1 = P_2$.
    - The claim that no converse improves the cutset slope at low SNR is contradicted by EGN's
      bound.
  - The old proposition is kept in Lean as `LowSnrCutsetSlopeStatement`, marked RETIRED. It is
    not the catalog `Statement`. A future Lean disproof would target it.
- **Choice of question (judgment call).** The minimum energy per bit is EMZ's open quantity.
  Asking whether the linear class attains it at unit gains is this catalog's formulation: no
  published conjecture gives a value for $E^*$. Two candidate values were rejected:
  - the cutset value, which is very probably settled negatively by the EGN computation above;
  - $2 \ln 2$ (relaying is useless at unit gains), which is fragile. Linear codes with $k = 12$
    already beat $2 \ln 2$ at $a = 1$, $b = 1.05$, so a large-$k$ computation might refute it.
    If $E^*_{\mathrm{lin}}(1,1,1) = 2 \ln 2$, it is equivalent to the chosen statement.

  The "is the linear class optimal?" form follows the catalog precedent
  `gaussian-mac-feedback-linear-optimality`.
- **Why the chosen statement is believed open.** No published bound or scheme settles it either
  way, and we see no way to settle it by evaluating existing schemes or converses.
  - The best lower bound on $E^*(1,1,1)$ is the cutset value $\tfrac34 \cdot 2\ln 2$
    (published), or about $0.93 \cdot 2 \ln 2$ via EGN (numerical).
  - $E^*_{\mathrm{lin}}(1,1,1)$ is only known to be at most $2 \ln 2$.
  - No nonlinear scheme is known to beat linear relaying, or even direct transmission, at these
    gains. This includes the EMZ 2006 Table II bounds and Example 1; Fig. 8 has no $b = 1$
    curve.
  - *Proving* the statement needs a converse for arbitrary relaying that matches the linear
    family. If $E^*_{\mathrm{lin}}(1,1,1) = 2\ln 2$, that includes showing that relaying is
    useless here, the full-duplex analogue of EMZ's FD-AWGN result.
  - *Refuting* it needs a nonlinear code that provably beats every linear one, which needs a
    lower bound on $E^*_{\mathrm{lin}}$ valid for all block lengths. None is known beyond the
    general converses (compare EMZ's second open problem).
- **Model.** The operational model of the previous versions is unchanged except for a
  `linearOnly : Bool` flag on `IsGaussianRelayAchievable`. With `false`, the new conjunct
  `false = true → IsLinearRelay relay` is vacuous.
  - The source constraint is per codeword.
  - The relay constraint is the expected relay energy per message, as a lintegral in
    $\mathbb{R}_{\ge0}^\infty$.
  - The relay is strictly causal and measurable; the decoder is measurable.
  - Codes are required for every $n \ge N$, with average error.
  - `IsLinearRelay` is $x_{r,i} = \sum_{j<i} d_{ij} y_{r,j}$, with coefficients chosen per code
    (a strictly lower-triangular $D$), as in EMZ Sec. V and KEL Sec. II. Constant offsets are
    excluded, since they only waste power.
- **Energy per bit.** `gaussianRelayMinEnergyPerBit linearOnly g₁₂ g₁₃ g₂₃` is the `sInf` in
  $\mathbb{R}_{\ge0}^\infty$ of `ofReal ((P₁ + P₂) / R)` over operating points with
  `0 < P₁`, `0 < P₂`, `0 < R` and `R` achievable.
  - It is defined directly from the operational predicate.
  - An empty set gives `⊤`, and `R > 0` prevents division by zero.
  - Excluding $P_2 = 0$ does not change the infimum, because the constraints are monotone in
    the powers.
  - Difference from EMZ/KEL: they charge the relay its worst-case energy $\max_{y_r^n}$, while
    this model charges the expected energy per message. EMZ themselves evaluate linear relaying,
    whose output is unbounded, under an expected constraint. The cutset converse uses only
    average powers, so $\tfrac34 \cdot 2 \ln 2$ applies here too.
  - `gaussianRelayCapacity` keeps the `sSup`-in-$\mathbb{R}_{\ge0}^\infty$ guard of 094f988.
- **Certificate** (`Known/Certificates/GaussianRelayChannelCapacity.lean`, added in 49c683f,
  rewritten for statement fix 2).
  - Kept, generalized to the `linearOnly` flag:
    - the noise-model bridge `Measure.pi gaussianReal = withDensity ∏ φ`;
    - rate 0 is achievable;
    - the silent-relay AWGN transfer and the direct-link capacity lower bound;
    - the ratio facts about the retired statement.
  - New:
    - the silent relay is linear;
    - $E^* \le E^*_{\mathrm{lin}}$ for all gains;
    - `statement_iff : Statement ↔ E*_lin(1,1,1) ≤ E*(1,1,1)`;
    - $E^*(1,1,1) \le E^*_{\mathrm{lin}}(1,1,1) \le 2 \ln 2$, so neither side is `⊤`.
  - **Not certified:**
    - $E^* \ge \tfrac34 \cdot 2 \ln 2$, in particular $E^* > 0$ (needs a cutset converse for
      this model). If both sides were the junk value $0$, `Statement` would hold vacuously; the
      cutset bound rules this out on paper.
    - Any value of $E^*_{\mathrm{lin}}$ below $2 \ln 2$.

## References

- T. M. Cover and A. El Gamal, "Capacity theorems for the relay channel," *IEEE Trans. Inf.
  Theory*, vol. 25, no. 5, pp. 572–584, 1979.
- A. El Gamal, M. Mohseni, and S. Zahedi, "Bounds on capacity and minimum energy-per-bit
  for AWGN relay channels," *IEEE Trans. Inf. Theory*, vol. 52, no. 4, pp. 1545–1561, 2006.
  (Thm. 1 and Table II in Sec. III; linear relaying, Example 1 and Sec. V-A in Sec. V; Conclusion.)
- O. Kosut, M. Effros, and M. Langberg, "Nobody expects a differential equation: minimum
  energy-per-bit for the Gaussian relay channel with rank-1 linear relaying," *Proc. IEEE
  ISIT*, 2024, DOI 10.1109/ISIT57864.2024.10619129; arXiv:2401.15495.
- A. El Gamal, A. Gohari, and C. Nair, "A strengthened cutset upper bound on the capacity
  of the relay channel and applications," *IEEE Trans. Inf. Theory*, vol. 68, no. 7,
  pp. 4247–4263, 2022; arXiv:2101.11139.
- A. S. Avestimehr, S. N. Diggavi, and D. N. C. Tse, "Wireless network information flow:
  a deterministic approach," *IEEE Trans. Inf. Theory*, vol. 57, no. 4, pp. 1872–1905, 2011.
- S. H. Lim, Y.-H. Kim, A. El Gamal, and S.-Y. Chung, "Noisy network coding," *IEEE Trans.
  Inf. Theory*, vol. 57, no. 5, pp. 3132–3152, 2011.
- X. Wu, L. P. Barnes, and A. Özgür, "'The capacity of the relay channel': solution to
  Cover's problem in the Gaussian case," *IEEE Trans. Inf. Theory*, vol. 65, no. 1,
  pp. 255–275, 2019.
