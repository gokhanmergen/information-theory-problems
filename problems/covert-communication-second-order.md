---
id: covert-communication-second-order
title: Second-Order Asymptotics and Keyless Dispersion of Square-Root-Law Covert Communication
status: open
category: security-privacy
posed_by: Boulat A. Bash, Dennis Goeckel, and Don Towsley; Ligong Wang, Gregory W. Wornell, and Lizhong Zheng; Matthieu R. Bloch
posed_year: 2013
tags: [information-theoretic-security, covert-communication, square-root-law, second-order-asymptotics]
lean_module: InfoTheory.Problems.CovertCommunicationSecondOrder
lean_file: lean/InfoTheory/Problems/CovertCommunicationSecondOrder.lean
---

## Statement

Consider covert communication over a discrete memoryless wiretap channel $W(y, z \mid x)$ with an "innocent" (off) input symbol $x_0 \in \mathcal{X}$. Let $P_0 = W_Y(\cdot \mid x_0)$ and $Q_0 = W_Z(\cdot \mid x_0)$ denote the receiver and warden output distributions when no transmission occurs. Over $n$ channel uses, Alice transmits a uniformly random message $M \in \{1, \dots, M_n\}$ subject to:
- **Reliability:** maximal (over messages and keys) decoding error at Bob is at most $\varepsilon \in (0, 1)$;
- **Covertness:** the warden's induced output distribution $Q_Z^{(n)}$ satisfies $D_{\mathrm{KL}}(Q_Z^{(n)} \mathbin{\|} Q_0^{\otimes n}) \le \delta$ (or total variation $\mathrm{TV}(Q_Z^{(n)}, Q_0^{\otimes n}) \le \delta$).

Under standard non-degeneracy conditions ($Q_1 \ll Q_0$, $Q_1 \ne Q_0$, and $Q_0$ not a convex combination of other warden rows), the **square-root law** holds: the maximum number of covert bits scales as $\log M^*(n, \varepsilon, \delta) = L_{\mathrm{KL}} \sqrt{n \delta} + O(n^{1/4})$.

**Determine the exact second-order ($n^{1/4}$ dispersion) term of $\log M^*(n, \varepsilon, \delta)$ for general DMCs under KL and total variation covertness constraints — both with and without a shared secret key.**

In particular, the accompanying Lean statement (statement-fix 2026-11-27) formalizes the open conjecture of Tahmasbi and Bloch (2019) for the **missed-detection** covertness metric. Fix a binary-input DMC with $P_1 \ll P_0$, $Q_1 \ll Q_0$, $Q_1 \ne Q_0$, an error level $\varepsilon \in (0,1)$, a false-alarm level $\alpha \in (0,1)$ and $\delta \in (0, 1-\alpha)$. Let $M^*_\beta(n, \varepsilon, \delta, \alpha)$ be the largest message count achievable with maximal error at most $\varepsilon$ and warden missed-detection probability $\beta_\alpha(Q_0^{\otimes n}, \widehat{P}_{Z^n}) \ge 1 - \alpha - \delta$. The conjecture states
$$
\log M^*_\beta(n, \varepsilon, \delta, \alpha) \ge \frac{(\Lambda + \Upsilon) D(P_1 \| P_0)}{\sqrt{\chi^2(Q_1 \| Q_0)}} \sqrt{n} - \sqrt{\frac{(\Lambda + \Upsilon) V_P}{\sqrt{\chi^2(Q_1 \| Q_0)}}}\, Q^{-1}(\varepsilon)\, n^{1/4} - o(n^{1/4}),
$$
where $\Lambda = Q^{-1}(1 - \alpha - \delta)$, $\Upsilon = Q^{-1}(\alpha)$ and $V_P = \mathrm{Var}_{P_1}[\log (P_1 / P_0)]$. This would match the converse proved by Tahmasbi and Bloch up to $o(n^{1/4})$.

## Background

Bash, Goeckel, and Towsley (2013) discovered the **square-root law** for covert (low probability of detection) communication over AWGN channels: only $O(\sqrt{n})$ reliable covert bits can be transmitted in $n$ channel uses, yielding zero asymptotic Shannon rate. Wang, Wornell, and Zheng (2016) and Bloch (2016) established the exact first-order constant $L_{\mathrm{KL}}$ for general discrete memoryless channels and showed that when Bob's channel beats the warden's ($D(P_1 \| P_0) > D(Q_1 \| Q_0)$), no shared secret key is needed to achieve the optimal $\sqrt{n}$ throughput.

Because the effective number of active (non-innocent) channel uses is $\Theta(\sqrt{n})$, central-limit fluctuations in the information spectrum occur at scale $(\sqrt{n})^{1/2} = n^{1/4}$ rather than $\sqrt{n}$. Characterizing this $n^{1/4}$ second-order dispersion for general non-binary DMCs and for keyless schemes is the central finite-blocklength open problem of covert communication.

## What is known

- **Exact first-order square-root law:** Wang, Wornell, and Zheng (2016) and Bloch (2016) proved that for binary-input DMCs with $Q_1 \ll Q_0, Q_1 \ne Q_0$,
  $$
  \lim_{n \to \infty} \frac{\ln M^*(n, \varepsilon, \delta)}{\sqrt{n \delta}} = \sqrt{\frac{2}{\chi^2(Q_1 \mathbin{\|} Q_0)}} \, D_{\mathrm{KL}}(P_1 \mathbin{\|} P_0),
  $$
  and Bloch (2016) proved that when $D_{\mathrm{KL}}(P_1 \mathbin{\|} P_0) > D_{\mathrm{KL}}(Q_1 \mathbin{\|} Q_0)$, zero secret key is required at first order.
- **Second-order asymptotics for binary-input DMCs (Tahmasbi–Bloch 2019):** under maximal error and KL covertness they prove the exact expansion $\log M^*_D = \sqrt{2\delta/\chi^2(Q_1\|Q_0)}\, D_P \sqrt{n} - \sqrt{\sqrt{2\delta/\chi^2(Q_1\|Q_0)}\, V_P}\, Q^{-1}(\varepsilon)\, n^{1/4} + O(\log n)$. This needs only $(1+\rho)\sqrt{2\delta/\chi^2}\,[D_Q - D_P]^+ \sqrt{n}$ key bits, so no key when $D_P > D_Q$. For the variational-distance and missed-detection metrics they prove matching first-order terms but non-matching second-order bounds (converses (25) and (29), achievability (26) and (30)). Under average error even the first-order term depends on $\varepsilon$ (their Appendix A).
- **What remains open (Tahmasbi–Bloch 2019; Bloch et al. 2021):**
  1. **Variational distance and missed-detection metrics:** Tahmasbi–Bloch prove the converses (25) and (29) and conjecture that both can be achieved. The variational-distance case is claimed by Zhang, Zhou, and Li (arXiv:2609.24675, Sept 2026); the missed-detection case remains open and is the formal statement here. (The keyless question is *not* open under maximal error. In the regime $D(P_1\|P_0) > D(Q_1\|Q_0)$, the achievability proof of Tahmasbi–Bloch's Theorem 1 already uses no key, see eq. (196).)
  2. **General non-binary input DMCs ($|\mathcal{X}| \ge 3$):** When multiple active input symbols are available and the first-order optimal input distribution is not uniquely supported on a single active symbol, the exact $n^{1/4}$ dispersion under KL and TV constraints remains open.

## Formal statement and certificate

- **Statement-fix (2026-11-27).**
  - **What the old statement asked.** Under KL covertness and *average* error: is `log₂ M_keyed − log₂ M_keyless = o(n^{1/4})` when `D(P₁‖P₀) > D(Q₁‖Q₀)`?
  - **Why it had to change.** Under the *maximal* error criterion used by Tahmasbi–Bloch, the question is settled by their Theorem 1. The achievability proof (eq. (196)) takes `log M + log K = max(log M, (1+ρ) ℓ_n D_Q)`, so for `(1+ρ) D_Q < D_P` no key is used, and keyless codes reach `log M*_D` up to `O(log n)`. Under average error nobody posed the question, and Tahmasbi–Bloch (Appendix A) show that even the first-order term then depends on `ε`.
  - **New statement.** The Lean statement now formalizes the open conjecture Tahmasbi–Bloch state after Theorem 3: under the **missed-detection** covertness metric, their converse (29), `log₂ M*_β ≤ a√n − b n^{1/4} + O(log n)`, is achievable up to `o(n^{1/4})`. Here `a = (Λ+Υ) D_P/√χ²(Q₁‖Q₀)`, `b = √((Λ+Υ) V_P/√χ²) · Q⁻¹(ε)`, `Λ = Q⁻¹(1−α−δ)`, and `Υ = Q⁻¹(α)`. The setting is maximal error and any key size.
  - **The variational-distance analogue** is claimed by Zhang–Zhou–Li, arXiv:2609.24675 (Sept 2026, unverified here).
- **Certificate** `lean/InfoTheory/Known/Certificates/CovertCommunicationSecondOrder.lean` (kernel-checked, standard axioms only) proves:
  - `β_α ∈ [0, 1]`, and `β_α(P, P) ≥ 1 − α`;
  - every feasible code has `m(1−ε) ≤ kYⁿ`, so `1 ≤ M*_β ≤ kYⁿ/(1−ε)` and `log₂ M*_β ≥ 0`, because the all-innocent one-message code is feasible;
  - `χ²(Q₁‖Q₀) > 0` under the hypotheses.
- Not certified: the Tahmasbi–Bloch bounds (29)–(30), and any property of `Q⁻¹`.

## References

- B. A. Bash, D. Goeckel, and D. Towsley, "Limits of reliable communication with low probability of detection on AWGN channels," *IEEE J. Sel. Areas Commun.* **31**(9), 1921–1930 (2013).
- M. R. Bloch, "Covert communication over noisy channels: A resolvability perspective," *IEEE Trans. Inf. Theory* **62**(5), 2334–2354 (2016).
- L. Wang, G. W. Wornell, and L. Zheng, "Fundamental limits of communication with low probability of detection," *IEEE Trans. Inf. Theory* **62**(6), 3493–3503 (2016).
- M. Tahmasbi and M. R. Bloch, "First and second order asymptotics in covert communication," *IEEE Trans. Inf. Theory* **65**(4), 2190–2212 (2019).
- Q. Zhang, L. Zhou, and X. Li, "Exact second-order asymptotics for covert communication over DMCs with variational distance constraints," *arXiv:2609.24675* (2026).
- M. R. Bloch, O. Günlü, A. Yener, F. Oggier, H. V. Poor, L. Sankar, and R. F. Schaefer, "An overview of information-theoretic security and privacy: Metrics, limits and applications," *IEEE J. Sel. Areas Inf. Theory* **2**(1), 5–22 (2021).
