---
problem: shannon-capacity-c7
date: 2026-07-18
attempter: gpt-5-codex
model: gpt-5-codex
type: dead-end
status: unverified
---

## Summary

I exhaustively searched the one-generator circular codes

$$D(n,q)=\{t(1,q,q^2,q^3,q^4):t\in\mathbb Z_n\}$$

for a direct improvement to the lower bound on $\Theta(C_7)$. No choice of
$368\leq n\leq100{,}000$ and $q\in\mathbb Z_n$ has enough cyclic
$\ell_\infty$ distance to map directly to an independent $n$-set in
$C_7^{\boxtimes5}$. The exact search checks 4,999,982,472 parameter pairs.

This closes a large finite range of the most direct version of the circular-code
strategy, but it does not exclude the pruning-and-extension method that produced the
current 367-word record.

## Approach

For $a\in\mathbb Z_n$, write $\|a\|_n=\min(a,n-a)$ using the representative
$a\in\{0,\ldots,n-1\}$. Define

$$k(n,q)=\min_{1\leq t<n}\max_{0\leq j<5}\|tq^j\|_n.$$

Then $D(n,q)$ is an independent $n$-set in the fifth power of the circular graph
$C_{k(n,q),n}$. The circular-graph homomorphism ordering used by
Polak--Schrijver implies

$$\frac{n}{k(n,q)}\leq\frac72
  \quad\Longrightarrow\quad
  \alpha(C_7^{\boxtimes5})\geq n.$$

Thus any $n\geq368$ satisfying $k(n,q)\geq\lceil2n/7\rceil$ would improve the
published 367-word lower bound. The program tests this integer condition for every
parameter pair in the stated range and exits immediately if it finds a construction.

## Claims

1. **[proved]** For every integer $n$ with $368\leq n\leq100{,}000$ and every
   $q\in\mathbb Z_n$, one has
   $k(n,q)<\lceil2n/7\rceil$.
2. **[proved]** No code $D(n,q)$ in this parameter range directly improves
   $\alpha(C_7^{\boxtimes5})\geq367$ through the circular-graph homomorphism
   criterion $n/k(n,q)\leq7/2$.
3. **[heuristic]** Searching substantially larger $n$ in the same one-generator
   family has low priority unless some arithmetic structure replaces brute force;
   richer generator vectors or pruning-and-extension are more plausible routes.

## Details

For two codewords indexed by $s,t\in\mathbb Z_n$, their difference is indexed by
$t-s$. Hence the minimum distance is obtained by scanning the nonzero multipliers.
The distance for multiplier $u$ equals that for $n-u$, so it is enough to check
$1\leq u\leq\lfloor n/2\rfloor$. All arithmetic is integral and the five powers of
$q$ are reduced modulo $n$.

The threshold in the program is exactly

$$\left\lceil\frac{2n}{7}\right\rceil=\frac{2n+6}{7}$$

with integer division. A parameter pair is rejected as soon as one multiplier has
all five cyclic coordinate distances below this threshold. This early rejection is
why an exhaustive search of nearly five billion pairs is practical.

As a consistency check, the Polak--Schrijver seed has $(n,q)=(382,7)$ and
$k(382,7)=108$, while a direct map would require
$\lceil764/7\rceil=110$. Its ratio therefore just misses the direct criterion; their
successful 367-set comes from translating and quantizing this near-miss, discarding
conflicting words, and optimally extending the remainder.

## Reproducible computation

The complete C++20 program is
[`code/search_cyclic_direct.cpp`](code/search_cyclic_direct.cpp). Run from the
repository root:

```sh
clang++ -O3 -std=c++20 \
  attempts/shannon-capacity-c7/code/search_cyclic_direct.cpp \
  -o /tmp/search_cyclic_direct
/tmp/search_cyclic_direct 100000
```

Output on 2026-07-18:

```text
no direct cyclic construction for 368 <= n <= 100000
parameter pairs tested: 4999982472
```

The pair count also has the independent closed-form check

$$\sum_{n=368}^{100000}n=4{,}999{,}982{,}472.$$

## Verification

The search completed successfully with Apple clang. The source scans every residue
$q=0,\ldots,n-1$ and every multiplier up to the sign symmetry. It uses no randomness,
floating-point comparisons, external solver, or nonstandard library.

The arithmetic reduction and source remain `unverified` in the repository sense. A
short independent implementation split by ranges of $n$, ideally with stored checksums
or witness multipliers for each rejected pair, would strengthen the computational
certificate.

## Dead ends

The direct one-generator strategy fails throughout the tested range. This is a precise
family-specific obstruction, not an upper bound on $\alpha(C_7^{\boxtimes5})$.

The computation does not cover $n>100{,}000$, arbitrary generator vectors
$(1,q_1,q_2,q_3,q_4)$, unions of cyclic orbits, nonlinear codes, or the
translation/quantization/pruning/extension procedure of Polak--Schrijver. In
particular, it cannot show that 367 is globally optimal or improve any Shannon-capacity
upper bound.

## Novelty check

I read the problem file and both earlier attempts in this directory. I checked
Polak--Schrijver's paper, which introduces $k(n,d,q)$ and says its 382-word seed was
found by computer for $n\geq350$, but does not state a search cutoff or a finite
exclusion theorem. On 2026-07-18 I searched the web and arXiv for “$k(n,d,q)$,”
“cyclic code search,” “$C_7$,” “382,” and explicit search ranges including 100,000.
I found no reported cutoff comparable to Claim 1. I therefore believe this exact
finite exclusion is not recorded in the cited literature, but I do not claim an
exhaustive review of unpublished code or theses.

## References

- `2026-07-18-gpt-5-codex-four-exchange.md` (prior attempt).
- `2026-07-18-gpt-5-codex-five-exchange.md` (prior attempt).
- S. C. Polak and A. Schrijver, “New lower bound on the Shannon capacity of $C_7$
  from circular graphs,” *Information Processing Letters* 143 (2019), 37--40;
  [arXiv:1808.07438](https://arxiv.org/abs/1808.07438).
- S. C. Polak, *New Methods in Coding Theory: Error-Correcting Codes and the Shannon
  Capacity*, PhD thesis, University of Amsterdam, 2019.
- L. Lovász, “On the Shannon capacity of a graph,” *IEEE Transactions on Information
  Theory* 25 (1979), 1--7.
