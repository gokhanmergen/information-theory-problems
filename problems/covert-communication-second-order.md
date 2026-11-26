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
- **Reliability:** average decoding error at Bob is at most $\varepsilon \in (0, 1/2)$;
- **Covertness:** the warden's induced output distribution $Q_Z^{(n)}$ satisfies $D_{\mathrm{KL}}(Q_Z^{(n)} \mathbin{\|} Q_0^{\otimes n}) \le \delta$ (or total variation $\mathrm{TV}(Q_Z^{(n)}, Q_0^{\otimes n}) \le \delta$).

Under standard non-degeneracy conditions ($Q_1 \ll Q_0$, $Q_1 \ne Q_0$, and $Q_0$ not a convex combination of other warden rows), the **square-root law** holds: the maximum number of covert bits scales as $\log M^*(n, \varepsilon, \delta) = L_{\mathrm{KL}} \sqrt{n \delta} + O(n^{1/4})$.

**Determine the exact second-order ($n^{1/4}$ dispersion) term of $\log M^*(n, \varepsilon, \delta)$ for general DMCs under KL and total variation covertness constraints — both with and without a shared secret key.**

In particular, for a binary-input DMC in the **keyless covert regime** $D_{\mathrm{KL}}(P_1 \mathbin{\|} P_0) > D_{\mathrm{KL}}(Q_1 \mathbin{\|} Q_0)$ (where Bloch 2016 proved that zero secret key suffices at first order $\Theta(\sqrt{n})$), the accompanying Lean statement formalizes the open question of Tahmasbi and Bloch (2019): does keyless covert communication also match the key-assisted second-order ($n^{1/4}$) dispersion, i.e.,
$$
\log_2 M_{\mathrm{keyed}}^*(n, \varepsilon, \delta) - \log_2 M_{\mathrm{keyless}}^*(n, \varepsilon, \delta) = o(n^{1/4}) \quad ?
$$

## Background

Bash, Goeckel, and Towsley (2013) discovered the **square-root law** for covert (low probability of detection) communication over AWGN channels: only $O(\sqrt{n})$ reliable covert bits can be transmitted in $n$ channel uses, yielding zero asymptotic Shannon rate. Wang, Wornell, and Zheng (2016) and Bloch (2016) established the exact first-order constant $L_{\mathrm{KL}}$ for general discrete memoryless channels and showed that when Bob's channel beats the warden's ($D(P_1 \| P_0) > D(Q_1 \| Q_0)$), no shared secret key is needed to achieve the optimal $\sqrt{n}$ throughput.

Because the effective number of active (non-innocent) channel uses is $\Theta(\sqrt{n})$, central-limit fluctuations in the information spectrum occur at scale $(\sqrt{n})^{1/2} = n^{1/4}$ rather than $\sqrt{n}$. Characterizing this $n^{1/4}$ second-order dispersion for general non-binary DMCs and for keyless schemes is the central finite-blocklength open problem of covert communication.

## What is known

- **Exact first-order square-root law:** Wang, Wornell, and Zheng (2016) and Bloch (2016) proved that for binary-input DMCs with $Q_1 \ll Q_0, Q_1 \ne Q_0$,
  $$
  \lim_{n \to \infty} \frac{\ln M^*(n, \varepsilon, \delta)}{\sqrt{n \delta}} = \sqrt{\frac{2}{\chi^2(Q_1 \mathbin{\|} Q_0)}} \, D_{\mathrm{KL}}(P_1 \mathbin{\|} P_0),
  $$
  and Bloch (2016) proved that when $D_{\mathrm{KL}}(P_1 \mathbin{\|} P_0) > D_{\mathrm{KL}}(Q_1 \mathbin{\|} Q_0)$, zero secret key is required at first order.
- **Second-order dispersion for binary-input DMCs *with* secret key:** Tahmasbi and Bloch (2019) proved the exact $n^{1/4}$ second-order expansion for binary-input DMCs under KL, TV, and missed-detection covertness constraints when sufficient shared secret key is available (of size $O(\sqrt{n})$ or $O(n^{1/4})$ depending on the regime).
- **What remains open (Tahmasbi–Bloch 2019; Bloch et al. 2021):**
  1. **Keyless second-order dispersion:** Even for binary-input DMCs with $D(P_1 \| P_0) > D(Q_1 \| Q_0)$, it is open whether keyless codes achieve the same $n^{1/4}$ second-order term as key-assisted codes (or incur an unavoidable $\Theta(n^{1/4})$ penalty from channel resolvability without shared key).
  2. **General non-binary input DMCs ($|\mathcal{X}| \ge 3$):** When multiple active input symbols are available and the first-order optimal input distribution is not uniquely supported on a single active symbol, the exact $n^{1/4}$ dispersion under KL and TV constraints remains open.

## References

- B. A. Bash, D. Goeckel, and D. Towsley, "Limits of reliable communication with low probability of detection on AWGN channels," *IEEE J. Sel. Areas Commun.* **31**(9), 1921–1930 (2013).
- M. R. Bloch, "Covert communication over noisy channels: A resolvability perspective," *IEEE Trans. Inf. Theory* **62**(5), 2334–2354 (2016).
- L. Wang, G. W. Wornell, and L. Zheng, "Fundamental limits of communication with low probability of detection," *IEEE Trans. Inf. Theory* **62**(6), 3493–3503 (2016).
- M. Tahmasbi and M. R. Bloch, "First and second order asymptotics in covert communication," *IEEE Trans. Inf. Theory* **65**(4), 2190–2212 (2019).
- M. R. Bloch, O. Günlü, A. Yener, F. Oggier, H. V. Poor, L. Sankar, and R. F. Schaefer, "An overview of information-theoretic security and privacy: Metrics, limits and applications," *IEEE J. Sel. Areas Inf. Theory* **2**(1), 5–22 (2021).
