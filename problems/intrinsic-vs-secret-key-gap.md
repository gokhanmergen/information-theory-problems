---
id: intrinsic-vs-secret-key-gap
title: Classical Bound Information and the Gap Between Intrinsic Information and Secret Key Capacity
status: open
category: security-privacy
posed_by: Ueli M. Maurer and Stefan Wolf; Nicolas Gisin and Stefan Wolf
posed_year: 1999
tags: [information-theoretic-security, intrinsic-information, bound-information, secret-key-agreement]
lean_module: InfoTheory.Problems.IntrinsicVsSecretKeyGap
lean_file: lean/InfoTheory/Problems/IntrinsicVsSecretKeyGap.lean
---

## Statement

For a discrete memoryless source $P_{XYZ}$ over finite alphabets $\mathcal{X} \times \mathcal{Y} \times \mathcal{Z}$, its **intrinsic conditional mutual information** (Maurer–Wolf 1999) is
$$
I(X; Y \downarrow Z) := \inf_{P_{\bar{Z} \mid Z}} I(X; Y \mid \bar{Z}),
$$
where the infimum ranges over all discrete memoryless channels $Z \to \bar{Z}$. Maurer and Wolf proved that $S(X; Y \mathbin{\|} Z) \le I(X; Y \downarrow Z)$ always holds, and Renner and Wolf (2003) proved that the inequality can be strict.

**Characterize the exact class of distributions $P_{XYZ}$ for which $S(X; Y \mathbin{\|} Z) = I(X; Y \downarrow Z)$ versus a strict gap $S(X; Y \mathbin{\|} Z) < I(X; Y \downarrow Z)$, and in particular resolve the Classical Bound Information Conjecture (Gisin–Wolf 2000; formalized in Lean):**

Does there exist a finite-alphabet bipartite distribution $P_{XYZ}$ exhibiting **classical bound information** — namely, strictly positive intrinsic information yet zero secret key capacity:
$$
I(X; Y \downarrow Z) > 0 \qquad \text{and} \qquad S(X; Y \mathbin{\|} Z) = 0 \quad ?
$$

## Background

Intrinsic information $I(X; Y \downarrow Z)$ measures the residual correlation between Alice ($X$) and Bob ($Y$) that cannot be explained away by any post-processing of Eve's observation $Z$. In analogy with quantum entanglement theory — where PPT bound entangled states cannot be distilled into Bell pairs despite being entangled — Gisin and Wolf (2000) proposed the classical analogue of **bound information**: correlated distributions $P_{XYZ}$ that require secret bits to generate ($I(X; Y \downarrow Z) > 0$, hence positive secret-key formation cost) yet from which zero secret key can be extracted ($S(X; Y \mathbin{\|} Z) = 0$).

Although Renner and Wolf (2003) proved that the gap between $I(X; Y \downarrow Z)$ and $S(X; Y \mathbin{\|} Z)$ can be arbitrarily large, whether $S(X; Y \mathbin{\|} Z)$ can vanish identically while $I(X; Y \downarrow Z) > 0$ remains a celebrated open problem bridging classical cryptography and quantum entanglement theory.

## What is known

- **Upper bound and cardinality bound:** Maurer and Wolf (1999) proved $S(X; Y \mathbin{\|} Z) \le I(X; Y \downarrow Z)$, and Christandl, Renner, and Wolf (2003) proved that the infimum in $I(X; Y \downarrow Z)$ is achieved with $|\bar{\mathcal{Z}}| \le |\mathcal{Z}|$.
- **Arbitrarily large strict gap:** Renner and Wolf (2003) constructed explicit families of distributions $P_{XYZ}$ for which $I(X; Y \downarrow Z)$ is arbitrarily large while $S(X; Y \mathbin{\|} Z)$ is arbitrarily small (proving $S(X; Y \mathbin{\|} Z) \ne I(X; Y \downarrow Z)$ in general). However, in their constructions $S(X; Y \mathbin{\|} Z)$ remained strictly positive (or was only bounded above by a small positive quantity rather than shown equal to $0$).
- **Multipartite bound information exists:** Acín, Cirac, and Masanes (2004) proved that *tripartite* classical bound information exists for three honest parties against an eavesdropper, derived by measuring multipartite bound entangled quantum states.
- **Bipartite classical bound information remains open:** For two honest parties ($X, Y$) and an eavesdropper ($Z$), no distribution $P_{XYZ}$ is known with $I(X; Y \downarrow Z) > 0$ and $S(X; Y \mathbin{\|} Z) = 0$, nor is there a proof that $I(X; Y \downarrow Z) > 0 \implies S(X; Y \mathbin{\|} Z) > 0$. Gohari and Anantharam (2010) gave necessary and sufficient conditions for $S(X; Y \mathbin{\|} Z) = 0$ in restricted classes, leaving the general characterization open.

## References

- U. M. Maurer and S. Wolf, "Unconditionally secure key agreement and the intrinsic conditional information," *IEEE Trans. Inf. Theory* **45**(2), 499–514 (1999).
- N. Gisin and S. Wolf, "Linking classical and quantum key agreement: Is there 'bound information'?," *CRYPTO 2000*, LNCS **1880**, 482–500 (2000).
- M. Christandl, R. Renner, and S. Wolf, "A property of the intrinsic mutual information," *Proc. IEEE ISIT*, 258 (2003).
- R. Renner and S. Wolf, "New bounds in secret-key agreement: The gap between formation and secrecy extraction," *EUROCRYPT 2003*, LNCS **2656**, 562–577 (2003).
- A. Acín, J. I. Cirac, and Ll. Masanes, "Multipartite bound information exists and can be activated," *Phys. Rev. Lett.* **92**, 107903 (2004).
- A. A. Gohari and V. Anantharam, "Information-theoretic key agreement of multiple terminals—Part I," *IEEE Trans. Inf. Theory* **56**(8), 3973–3996 (2010).
