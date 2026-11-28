---
id: locally-correctable-codes-constant-rate
title: Optimal Query Complexity of Constant-Rate Binary Locally Correctable Codes
status: open
category: coding-theory
posed_by: Swastik Kopparty, Or Meir, Noga Ron-Zewi, and Shubhangi Saraf
posed_year: 2017
tags: [coding-theory, locally-correctable-codes, constant-rate, query-complexity]
lean_module: InfoTheory.Problems.LocallyCorrectableCodesConstantRate
lean_file: lean/InfoTheory/Problems/LocallyCorrectableCodesConstantRate.lean
---

## Statement

A linear binary code $C \subseteq \mathbb{F}_2^n$ of dimension $k$ (rate $R = k/n$) is a **$q$-query $(\delta, \varepsilon)$-Locally Correctable Code (LCC)** if there exists a randomized local correction algorithm that, given any codeword $c \in C$, any corrupted vector $y \in \mathbb{F}_2^n$ with $\Delta(c, y) \le \delta n$, and any coordinate $i \in \{1, \dots, n\}$, queries at most $q$ coordinates of $y$ and outputs $c_i$ with probability at least $1/2 + \varepsilon$.

**Open Problem:** Do there exist **constant-rate** binary linear Locally Correctable Codes (rate $k/n \ge R > 0$, constant noise tolerance $\delta > 0$, constant advantage $\varepsilon > 0$) with **polylogarithmic query complexity** $q = O((\log n)^c)$ for some constant $c \in \mathbb{N}$?

## Background

Locally Correctable Codes strengthen Locally Decodable Codes by requiring local recovery of *every* codeword symbol rather than only message symbols. For a long time, the best known constant-rate LCCs—such as multivariate multiplicity codes (Kopparty–Saraf–Yekhanin 2014) and lifted Reed–Solomon codes (Guo–Kopparty–Sudan 2013)—required polynomial query complexity $q = n^\alpha$ for arbitrarily small constants $\alpha > 0$.

In a breakthrough, Kopparty, Meir, Ron-Zewi, and Saraf (2017) constructed the first constant-rate LCCs (and LDCs) with **sub-polynomial** query complexity $q = \exp(O(\sqrt{\log n \log \log n})) = n^{o(1)}$, and subsequent work (Hemenway–Ron-Zewi–Wootters 2020; Kopparty–Ron-Zewi–Saraf–Wootters 2020) achieved optimal rate–distance tradeoffs approaching the Singleton bound over large alphabets with $q = n^{o(1)}$ queries. Pushing the query complexity of constant-rate binary LCCs all the way down to $\mathrm{polylog}(n)$—or proving a super-polylogarithmic lower bound—remains one of the foremost open problems in coding theory and complexity theory.

## What is known

- **Constant-rate LCC upper bounds:**
  - Multiplicity codes (Kopparty–Saraf–Yekhanin 2014) and lifted codes (Guo–Kopparty–Sudan 2013): rate arbitrarily close to $1$ with $q = O(n^\varepsilon)$ queries for any constant $\varepsilon > 0$.
  - Kopparty, Meir, Ron-Zewi, and Saraf (2017): constant-rate binary LCCs with sub-polynomial query complexity
    $$q = \exp\!\left(O(\sqrt{\log n \log \log n})\right),$$
    obtained via high-rate locally testable codes (LTCs) and recursive tensoring/distance amplification.
  - Hemenway, Ron-Zewi, and Wootters (2020) and Kopparty, Ron-Zewi, Saraf, and Wootters (2020) achieved optimal rate–distance tradeoffs with $q = n^{o(1)}$ queries.
- **Lower bounds on constant-rate LCCs:**
  - For constant $q$: $q = 2$ requires $n = 2^{\Omega(k)}$ (Kerenidis–de Wolf 2004); $q = 3$ linear LCCs require $n = 2^{\Omega(k^{1/8})}$ (Kothari–Manohar 2024); for general constant $q \ge 4$, Katz–Trevisan (2000) and Woodruff (2007) give $n = \Omega(k^{1 + 1/(\lceil q/2 \rceil - 1)} / \log k)$, ruling out constant rate for any constant $q$.
  - For growing $q = \omega(1)$ at constant rate $k = \Omega(n)$, no super-logarithmic lower bound is known: the gap between $\Omega(\log n)$ and $\exp(O(\sqrt{\log n \log \log n}))$ (and in particular whether $q = \mathrm{polylog}(n)$ is achievable) remains completely open.
- **Related contrast with LTCs:** In 2022, Dinur–Evra–Livne–Lubotzky–Mozes and Panteleev–Kalachev constructed constant-rate, constant-distance Locally *Testable* Codes (LTCs) with $O(1)$ queries. No analogous $O(1)$-query or $\mathrm{polylog}(n)$-query construction is known for constant-rate LCCs.

## Formal statement and certificate

- **Adversarial check (2026-11-27): Statement is faithful and open.** `IsBinaryLCC` is the
  standard linear `q`-query `(δ, ε)` LCC (uniform seed, non-adaptive queries, success
  `≥ 1/2 + ε` at every coordinate for every codeword and every `y` within `δ n`). The statement
  asks for constant `R, δ, ε` and `q ≤ C (log n)^c` along infinitely many `n`; no cheat makes it
  trivial (`δ n → ∞`). Recent related results do **not** settle it: Kumar–Mon (STOC 2024) get
  polylog queries only for *relaxed* LCCs; Yankovitz (ECCC TR25-168, rev. 2026) gets constant-rate
  polylog-query block-wise LCCs only over alphabets with `log |Σ| ≤ k^ε` (concatenating to binary
  multiplies the query count by `k^ε`). Best binary: `exp(Õ(√log n))` (Kopparty–Meir–Ron-Zewi–Saraf 2017).
- **Certificate** (`Known/Certificates/LocallyCorrectableCodesConstantRate.lean`):
  - `card_good_ge`: the union bound behind 2-query self-correction;
  - regression `hadamard_isBinaryLCC`: the Hadamard code (length `2^k`, dimension `k`) is a
    2-query `(1/8, 1/4)`-LCC for every `k`. So the predicate is satisfiable with constant
    `δ, ε, q` at exponentially small rate; the difficulty is entirely the rate/query trade-off;
  - `isBinaryLCC_mono_queries`: more queries never hurt.
- **Not certified:** constant-rate constructions (multiplicity codes, KMRS) and lower bounds.

## References

- J. Katz and L. Trevisan, "On the efficiency of local decoding procedures for error-correcting codes," *Proc. 32nd ACM STOC*, pp. 80–86, 2000.
- S. Kopparty, S. Saraf, and S. Yekhanin, "High-rate codes with sublinear-time decoding," *J. ACM*, 61(5):28:1–28:20, 2014 (STOC 2011).
- A. Guo, S. Kopparty, and M. Sudan, "New affine-invariant codes from lifting," *Proc. 4th ITCS*, pp. 529–540, 2013.
- S. Kopparty, O. Meir, N. Ron-Zewi, and S. Saraf, "High-rate locally correctable and locally testable codes with sub-polynomial query complexity," *J. ACM*, 64(2):11:1–11:42, 2017 (STOC 2016).
- B. Hemenway, N. Ron-Zewi, and M. Wootters, "Local list recovery of high-rate tensor codes and applications," *SIAM J. Comput.*, 49(4):FOCS17-157–FOCS17-195, 2020.
- P. K. Kothari and P. Manohar, "An exponential lower bound for linear 3-query locally correctable codes," *Proc. 56th ACM STOC*, 2024.
