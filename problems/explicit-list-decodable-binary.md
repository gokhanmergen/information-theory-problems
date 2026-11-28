---
id: explicit-list-decodable-binary
title: Explicit Polynomial-Time List-Decodable Binary Codes Achieving Capacity
status: open
category: coding-theory
posed_by: Venkatesan Guruswami and Madhu Sudan
posed_year: 2000
tags: [coding-theory, list-decoding, explicit-codes, binary-codes]
lean_module: InfoTheory.Problems.ExplicitListDecodableBinary
lean_file: lean/InfoTheory/Problems/ExplicitListDecodableBinary.lean
---

## Statement

For any error fraction $p \in (0, 1/2)$ and gap $\varepsilon > 0$, random binary codes of rate $R = 1 - h(p) - \varepsilon$ are $(p, L)$-list-decodable with constant list size $L = O(1/\varepsilon)$. However, no known code construction over the binary alphabet achieves rate $1 - h(p) - \varepsilon$ together with an efficient (polynomial-time, or even polynomial-size circuit) list-decoding algorithm.

**Open Problem:** For every $p \in (0, 1/2)$ and $\varepsilon > 0$, do there exist an explicit family of binary codes $E_n : \{0, 1\}^k \to \{0, 1\}^n$ of rate $k/n \ge 1 - h(p) - \varepsilon$, a constant list size $L = L(p, \varepsilon)$, and polynomial-time (in particular, polynomial-size Boolean circuit) encoding and list-decoding algorithms such that for every received word $y \in \{0, 1\}^n$, the decoder outputs a list of at most $L$ messages containing every $m \in \{0, 1\}^k$ with $\Delta(E_n(m), y) \le p n$?

## Background

A landmark achievement of modern algebraic coding theory was the construction of explicit, efficiently list-decodable codes achieving list-decoding capacity over **large** alphabets: Parvaresh and Vardy (2005) and Guruswami and Rudra (2008) achieved rate $1 - p - \varepsilon$ over polynomial-sized (and later large constant-sized) alphabets using Folded Reed–Solomon codes, and Kopparty, Ron-Zewi, Saraf, and Wootters (2018) reduced the list size of Folded Reed–Solomon and multiplicity codes to a constant $L = O_\varepsilon(1)$ independent of blocklength (with later refinements reaching $L = O(1/\varepsilon)$).

Despite this success over large alphabets, bringing explicit capacity-achieving list decoding down to the **binary alphabet** $\{0, 1\}$ has remained completely out of reach. Standard code concatenation with inner random/brute-force binary codes achieves only the Zyablov or Blokh–Zyablov list-decoding bound, which stays strictly below $1 - h(p)$ for every $p \in (0, 1/2)$. Even in the non-uniform circuit model ($\mathsf{P}/\mathsf{poly}$), no binary code family is known to admit polynomial-size list-decoding circuits at rate $1 - h(p) - \varepsilon$.

## What is known

- **Large constant alphabets:** Folded Reed–Solomon codes (Guruswami–Rudra 2008) and univariate multiplicity codes (Kopparty 2015; Kopparty–Ron-Zewi–Saraf–Wootters 2018; Srivastava 2025; Chen–Zhang 2025) explicitly achieve list-decoding capacity $1 - p - \varepsilon$ over alphabets of size $q = \mathrm{poly}(1/\varepsilon)$ or $2^{O(1/\varepsilon)}$ with constant list size (down to $O(1/\varepsilon)$) and polynomial-time list decoding.
- **High-noise binary regime ($p = 1/2 - \varepsilon$):**
  - Random codes achieve rate $\Theta(\varepsilon^2)$.
  - Guruswami–Rudra concatenation gives rate $\Omega(\varepsilon^3)$.
  - Ta-Shma (2017) constructed explicit binary codes with distance $1/2 - \varepsilon$ and rate $\Omega(\varepsilon^{2 + o(1)})$ using expander walks, and Jeronimo, Quintana, Srivastava, and Tulsiani (2021) gave polynomial-time list-decoding algorithms for Ta-Shma-type codes near $p = 1/2 - \varepsilon$ at rate $\Omega(\varepsilon^{2 + o(1)})$—still far from achieving $1 - h(p) - \varepsilon$ for fixed $p \in (0, 1/2)$.
- **Concatenated / expander-based binary codes for fixed $p \in (0, 1/2)$:** Guruswami and Rudra (2008, 2011) achieved the binary Blokh–Zyablov list-decoding tradeoff via multilevel concatenation, which remains strictly below $1 - h(p)$ for all $p \in (0, 1/2)$.
- **Randomized (non-explicit) binary codes:** Random linear codes and random LDPC codes (Mosheiff et al. 2020) achieve list-decoding capacity $1 - h(p) - \varepsilon$ with constant list size, but have no known polynomial-time (or polynomial-size circuit) list-decoding algorithm up to $p$.

## Formal statement and certificate

- **Statement-fix (2026-11-27).** The previous Lean statement required uniform Turing machines
  with message length exactly `k = ⌊(1 - h(p) - ε) n⌋` for *every real* `p, ε` and every large
  `n`. The decoder lays out its list in `k`-bit blocks and so must compute `k` from `n`; for
  non-computable `1 - h(p) - ε` (all but countably many `ε`) no Turing machine can, so the
  formal statement could fail for computability reasons unrelated to coding. The encoder also
  saw only `k`, although several `n` share one `k`. The fixed statement lets the construction
  pick a **rational rate `a/b ≥ 1 - h(p) - ε`** and uses the lengths `n = b m`, `k = a m`
  (`m ≥ N₀`), which is the standard notion of an explicit family. Everything else is unchanged:
  uniform single-tape TMs, time `c n^d`, injective encoder, constant list size `L`, worst-case
  radius `p n`.
- **Still open (checked 2026-11):** explicit capacity-achieving list decoding is known only over
  large alphabets (folded RS, multiplicity codes, and the 2025 expander-based constructions with
  list size `O(1/ε)`); for binary codes the best explicit efficiently list-decodable trade-off is
  still the Blokh–Zyablov bound (Guruswami–Rudra), strictly below `1 - h(p)`.
- **Certificate** (`Known/Certificates/ExplicitListDecodableBinary.lean`):
  - `statement_iff`: `Statement` unfolds to a per-length predicate `Body`;
  - `idTM_run`: semantics check of the TM model (a one-step machine halts with its input on
    the tape and `readTapeBits` returns it);
  - regression `body_identity_zero_radius`: at `p = 0` the identity code (`E = D = idTM`, rate
    `1 = 1 - h(0)`, `L = 1`, one step) satisfies `Body` for every length, so halting, readout and
    list layout are honest, not junk;
  - `body_injective_rate_le`: any witness has rate `a/b ≤ 1`.
- **Not certified:** the list-decoding converse and random-coding achievability.

## References

- V. Guruswami and M. Sudan, "List decoding algorithms for certain concatenated codes," *Proc. 32nd ACM STOC*, pp. 181–190, 2000.
- V. Guruswami and A. Rudra, "Explicit codes achieving list decoding capacity: Error-correction with optimal redundancy," *IEEE Trans. Inf. Theory*, 54(1):135–150, 2008.
- A. Ta-Shma, "Explicit, almost optimal, epsilon-balanced codes," *Proc. 49th ACM STOC*, pp. 238–251, 2017.
- S. Kopparty, N. Ron-Zewi, S. Saraf, and M. Wootters, "Improved decoding of folded Reed–Solomon and multiplicity codes," *Proc. 59th IEEE FOCS*, pp. 212–223, 2018 (SIAM J. Comput., 2023).
- F. G. Jeronimo, T. Mittal, S. Srivastava, and M. Tulsiani, "Explicit codes approaching distance $1/2$ with near-optimal rate and polynomial-time list decoding," *Proc. 53rd ACM STOC* / *62nd IEEE FOCS*, 2021.
- J. Mosheiff, N. Resch, N. Ron-Zewi, S. Silas, and M. Wootters, "LDPC codes achieve list decoding capacity," *Proc. 61st IEEE FOCS*, pp. 458–469, 2020.
