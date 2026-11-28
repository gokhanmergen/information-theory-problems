---
id: locally-decodable-codes-3-query
title: Optimal Blocklength of 3-Query Binary Locally Decodable Codes
status: open
category: coding-theory
posed_by: Jonathan Katz and Luca Trevisan
posed_year: 2000
tags: [coding-theory, locally-decodable-codes, 3-query-ldc, lower-bounds]
lean_module: InfoTheory.Problems.LocallyDecodableCodes3Query
lean_file: lean/InfoTheory/Problems/LocallyDecodableCodes3Query.lean
---

## Statement

A **$q$-query binary Locally Decodable Code (LDC)** with message length $k$, blocklength $n$, noise tolerance $\delta > 0$, and advantage $\varepsilon > 0$ consists of an encoding map $E : \{0, 1\}^k \to \{0, 1\}^n$ and a randomized decoder such that for every message $x \in \{0, 1\}^k$, every corrupted word $y \in \{0, 1\}^n$ at Hamming distance at most $\delta n$ from $E(x)$, and every message coordinate $i \in \{1, \dots, k\}$, the decoder queries at most $q$ positions of $y$ and outputs $x_i$ with probability at least $1/2 + \varepsilon$.

For $q = 2$, the optimal blocklength is completely known to be exponential: $n = 2^{\Theta(k)}$ (Goldreich–Karloff–Schulman–Trevisan 2002; Kerenidis–de Wolf 2004). For $q = 3$, there is an enormous gap between the best known upper bound $n \le \exp(\exp(O(\sqrt{\log k \log \log k})))$ and the best known lower bound $n \ge \tilde{\Omega}(k^3)$.

**Open Problem:** Must every 3-query binary Locally Decodable Code with constant noise tolerance $\delta > 0$ and constant advantage $\varepsilon > 0$ have **super-polynomial** blocklength $n = k^{\omega(1)}$? Equivalently, for all $\delta, \varepsilon > 0$ and every polynomial $C k^d$, does $n > C k^d$ hold for all sufficiently large $k$?

## Background

Locally Decodable Codes were formalized by Katz and Trevisan (2000) and sit at the crossroads of coding theory, theoretical computer science, and information-theoretic cryptography (notably Private Information Retrieval, where a $q$-query LDC directly yields a $q$-server PIR protocol). Determining the minimal blocklength $n(k)$ of 3-query LDCs is arguably the most famous open problem in local coding theory.

For several years after Katz and Trevisan, it was widely conjectured that $q$-query LDCs for any constant $q$ require exponential or sub-exponential blocklength $2^{k^{\Omega(1)}}$. Yekhanin (2008) and Efremenko (2009) shattered that expectation by constructing 3-query LDCs of sub-exponential length $\exp(\exp(O(\sqrt{\log k \log \log k})))$ from Matching Vector families over composite moduli. On the lower-bound side, after two decades stuck at $\tilde{\Omega}(k^2)$ (Kerenidis–de Wolf 2004; Woodruff 2007), Alrabiah, Guruswami, Kothari, and Manohar (2023) achieved a breakthrough near-cubic lower bound $n \ge \tilde{\Omega}(k^3)$ using spectral refutation of semirandom CSPs via Kikuchi matrices—yet ruling out polynomial-length 3-query LDCs remains wide open.

## What is known

- **2-query LDCs (settled):** $n = 2^{\Theta(k)}$ (Goldreich–Karloff–Schulman–Trevisan 2002 for linear codes; Kerenidis–de Wolf 2004 for general codes via quantum random-access codes; Hadamard code achieves $n = 2^k$).
- **3-query LDC upper bounds:**
  - Reed–Muller codes give $n = O(2^{\sqrt{k}})$.
  - Yekhanin (2008) (conditionally on infinitely many Mersenne primes) and Efremenko (2009) (unconditionally, using Grolmusz's Matching Vector families modulo $511$ and $6$) constructed 3-query LDCs with blocklength
    $$n = \exp\!\left(\exp\!\left(O(\sqrt{\log k \log \log k})\right)\right).$$
  - Dvir, Gopalan, and Yekhanin (2011) simplified and generalized Matching Vector LDCs.
- **3-query LDC lower bounds:**
  - Katz and Trevisan (2000): $n = \Omega(k^{3/2})$.
  - Kerenidis and de Wolf (2004): $n = \Omega(k^2 / \log k)$ (and Woodruff 2007 improved the log factor).
  - Alrabiah, Guruswami, Kothari, and Manohar (2023, STOC 2024): $n \ge \Omega(k^3 / (\log k)^6)$ for all (even nonlinear) 3-query binary LDCs, via Kikuchi matrix spectral bounds for semirandom 3-XOR refutation.
- **Separation from 3-query LCCs:** Kothari and Manohar (2024) proved an **exponential** lower bound $n \ge 2^{\Omega(k^{1/8})}$ for linear 3-query Locally *Correctable* Codes (LCCs), establishing the first exponential separation between 3-query LCCs and 3-query LDCs.

## Formal statement and certificate

- **Adversarial check (2026-11-27): Statement is faithful and open.** `IsBinaryLDC` is the
  standard (possibly nonlinear) `q`-query `(δ, ε)` LDC. The statement says every `3`-query LDC
  with constant `δ, ε > 0` has `n > C k^d` for all large `k`, i.e. super-polynomial length. Its
  vacuity risk (no LDCs at all) is excluded by the certificate. Status: best lower bound
  `n ≥ Ω̃(k^3)` (Alrabiah–Guruswami–Kothari–Manohar 2023; Janzer–Manohar 2024 give the same
  exponent for `q = 3`), best upper bound `exp(exp(Õ(√log k)))` (Efremenko 2009). Late-2025
  progress concerns *relaxed* LDCs (Gur–Minzer–Weissenberg–Zheng, ECCC TR25-217: 3-query RLDCs of
  length `Õ(k^2)`) and does not affect this statement.
- **Certificate** (`Known/Certificates/LocallyDecodableCodes3Query.lean`):
  - `hadamard_isBinaryLDC`, `hadamard_isBinaryLDC_of_le`: the Hadamard code of length `2^k` is a
    3-query `(δ, ε)`-LDC for every `k` whenever `δ ≤ 1/8`, `ε ≤ 1/4`, so the hypothesis of the
    Statement is satisfiable at every message length (non-vacuity), consistently with the
    conjectured answer;
  - `isBinaryLDC_mono` (antitone in `δ, ε`), `isBinaryLDC_eps_le` (`ε ≤ 1/2` for any LDC).
- **Not certified:** the `Ω̃(k^3)` / `Ω̃(k^2)` lower bounds, matching-vector codes.

## References

- J. Katz and L. Trevisan, "On the efficiency of local decoding procedures for error-correcting codes," *Proc. 32nd ACM STOC*, pp. 80–86, 2000.
- I. Kerenidis and R. de Wolf, "Exponential lower bound for 2-query locally decodable codes via a quantum argument," *J. Comput. System Sci.*, 69(3):395–420, 2004.
- D. Woodruff, "New lower bounds for general locally decodable codes," *Electronic Colloquium on Computational Complexity (ECCC)*, TR07-006, 2007.
- S. Yekhanin, "Towards 3-query locally decodable codes of subexponential length," *J. ACM*, 55(1):1–16, 2008.
- K. Efremenko, "3-query locally decodable codes of subexponential length," *SIAM J. Comput.*, 41(6):1694–1703, 2012 (STOC 2009).
- Z. Dvir, P. Gopalan, and S. Yekhanin, "Matching vector codes," *SIAM J. Comput.*, 40(4):1154–1178, 2011.
- O. Alrabiah, V. Guruswami, P. K. Kothari, and P. Manohar, "A near-cubic lower bound for 3-query locally decodable codes from semirandom CSP refutation," *Proc. 56th ACM STOC*, 2024 (arXiv:2308.01937, 2023).
- P. K. Kothari and P. Manohar, "An exponential lower bound for linear 3-query locally correctable codes," *Proc. 56th ACM STOC*, 2024 (arXiv:2311.00558, 2023).
