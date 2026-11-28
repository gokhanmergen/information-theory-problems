---
id: secret-sharing-optimal-info-ratio
title: Super-Linear Lower Bounds on the Optimal Information Ratio of Secret Sharing
status: open
category: security-privacy
posed_by: László Csirmaz
posed_year: 1997
tags: [information-theoretic-security, secret-sharing, entropy-inequalities, shannon-barrier]
lean_module: InfoTheory.Problems.SecretSharingOptimalInfoRatio
lean_file: lean/InfoTheory/Problems/SecretSharingOptimalInfoRatio.lean
---

## Statement

A monotone **access structure** $\Gamma$ on $n$ participants $\{1, \dots, n\}$ is an upward-closed family of nonempty subsets (the *qualified* sets). A **perfect secret sharing scheme** realizing $\Gamma$ is a joint distribution $(S_0, S_1, \dots, S_n)$ (where $S_0$ is the secret with $H(S_0) > 0$ and $S_i$ is participant $i$'s share) satisfying:
- **Correctness:** $H(S_0 \mid S_A) = 0$ for every qualified set $A \in \Gamma$;
- **Perfect secrecy:** $H(S_0 \mid S_A) = H(S_0)$ for every unqualified set $A \notin \Gamma$.

The **optimal information ratio** (worst-case share-size-to-secret-size ratio) of $\Gamma$ is
$$
\sigma(\Gamma) := \inf \max_{1 \le i \le n} \frac{H(S_i)}{H(S_0)},
$$
where the infimum ranges over all perfect secret sharing schemes realizing $\Gamma$.

**Determine the worst-case asymptotic growth of $\max_{\Gamma} \sigma(\Gamma)$ over all $n$-party monotone access structures $\Gamma$ — and in particular determine whether there exists a family of $n$-party access structures whose optimal information ratio grows super-linearly ($\omega(n)$), breaking the Csirmaz linear barrier of Shannon-type inequalities:**
$$
\forall C > 0, \quad \exists n \ge 1, \;\exists \Gamma \text{ on } n \text{ parties}, \quad \sigma(\Gamma) > C n.
$$

## Background

Secret sharing was introduced by Shamir (1979) and Blakley (1979) for threshold access structures, where every share has the same size as the secret ($\sigma = 1$). Ito, Saito, and Nishizeki (1987) showed that *every* monotone access structure admits a perfect secret sharing scheme, but their construction uses shares of exponential size $O(2^n / \sqrt{n})$.

A staggering exponential gap has persisted for nearly thirty years between the best general upper bounds ($2^{0.585 n}$) and the best known lower bounds ($\Omega(n / \log n)$). Even more remarkably, Csirmaz (1997) proved that **no argument relying solely on Shannon-type information inequalities** (polymatroid axioms) can ever prove a lower bound better than $n$ for *any* $n$-party access structure! Breaking the $\omega(n)$ barrier therefore requires genuinely non-Shannon information inequalities or fundamentally new combinatorial/algebraic techniques.

## What is known

- **Best known general lower bound:** Csirmaz (1997) constructed an explicit family of $n$-party monotone access structures with $\sigma(\Gamma) = \Omega(n / \log n)$ using Shannon inequalities, and simultaneously proved that the polymatroid relaxation of $\sigma(\Gamma)$ is always at most $n$ for every $n$-party access structure.
- **Role of non-Shannon inequalities:** Beimel and Orlov (2011) showed that all known non-Shannon information inequalities on 4 and 5 variables (including Zhang–Yeung 1998 and Dougherty–Freiling–Zeger) still cannot yield lower bounds exceeding $O(n)$ on general access structures.
- **Best known general upper bounds:**
  - Classic CNF/DNF construction: $\sigma(\Gamma) \le 2^{n - o(n)}$ (Ito–Saito–Nishizeki 1987).
  - Liu and Vaikuntanathan (2018) achieved the first sub-$2^n$ upper bound for all monotone access structures: $\sigma(\Gamma) \le 2^{0.994 n + o(n)}$.
  - Applebaum, Beimel, Farràs, Nir, and Peter (2020) and Applebaum–Nir (2021) improved the general upper bound to $\sigma(\Gamma) \le 2^{0.585 n + o(n)}$ (and $2^{0.7576 n}$ for linear schemes).
- **Restricted scheme classes:** For *linear* secret sharing schemes (monotone span programs), Babai–Gál–Wigderson (1999) and Pitassi–Robere (2018) proved super-polynomial / exponential lower bounds (e.g., $2^{\Omega(\sqrt{n})}$ or higher for specific classes), whereas for unrestricted (possibly nonlinear) information-theoretic secret sharing, **no lower bound exceeding $O(n / \log n)$ is known for any access structure** (Beimel 2011).

## References

- A. Shamir, "How to share a secret," *Commun. ACM* **22**(11), 612–613 (1979).
- M. Ito, A. Saito, and T. Nishizeki, "Secret sharing scheme realizing general access structure," *Proc. IEEE GLOBECOM*, 99–102 (1987).
- L. Csirmaz, "The size of a share must be large," *J. Cryptology* **10**(4), 223–231 (1997).
- A. Beimel, "Secret-sharing schemes: A survey," *Coding and Cryptology (IWCC 2011)*, LNCS **6639**, 11–46 (2011).
- A. Beimel and I. Orlov, "Secret sharing and non-Shannon information inequalities," *IEEE Trans. Inf. Theory* **57**(9), 5634–5649 (2011).
- T. Liu and V. Vaikuntanathan, "Breaking the circuit-size barrier in secret sharing," *Proc. 50th ACM STOC*, 699–708 (2018).
- B. Applebaum, A. Beimel, O. Farràs, O. Nir, and N. Peter, "Secret-sharing schemes for general and uniform access structures," *EUROCRYPT 2019* / *STOC 2020* (2020).

## Formal statement and certificate

- **Adversarial check (2026-11-27): Statement is faithful and still open.** `optimalSecretSharingRatio Γ`
  is the `sInf` of all `r` that bound `H(S_i)/H(S_0)` for every `i`, taken over perfect schemes
  with a finite common share alphabet `Fin k` (no generality is lost: pad the alphabets). The
  set is bounded below by `0`. If no scheme existed, the `sInf` would be the junk value `0`,
  which can only make `Statement` harder, but schemes always exist (Ito–Saito–Nishizeki).
  `Statement` (`∀ C, ∃ n Γ, σ(Γ) > C n`) is exactly "super-linear". The best lower bound for
  general schemes is still Csirmaz's `Ω(n / log n)`.
- **Certificate** `lean/InfoTheory/Known/Certificates/SecretSharingOptimalInfoRatio.lean`:
  `exists_essential` (every access structure has an essential participant); `one_le_of_mem` /
  `one_le_of_scheme`, the Karnin–Greene–Hellman bound that every admissible ratio is `≥ 1`
  (some share is at least as large as the secret), proved from Shannon inequalities;
  `one_le_optimalSecretSharingRatio` (`σ(Γ) ≥ 1` once any scheme exists, so not junk); and the
  regression `optimalSecretSharingRatio_oneOfN : σ(1-out-of-(n+1)) = 1` (replicate a uniform
  secret bit).
