---
problem: li-medard-conjecture
date: 2026-11-27
attempter: antigravity
model: gemini-3.1-pro
type: survey
status: community-reviewed
---

## Summary

The Li–Médard conjecture formalized in `InfoTheory.Problems.LiMedardConjecture` was
**resolved in full in November 2026** by **Lei Yu** (`arXiv:2611.00868`, *"Noise Stability
on the Hypercube: Order 7/8"*).

Specifically, Yu proves that among all balanced Boolean functions $f : \{0,1\}^n \to \{0,1\}$
and for all correlation parameters $\rho = 1 - 2\alpha \in [0, 1]$, dictator functions
minimize $\mathbb{E}[(T_\rho f)^\alpha]$ for all $\alpha \in [7/8, 1)$ and **maximize
$\mathbb{E}[(T_\rho f)^q]$ for all $q \in (1, 2)$** (with $q = 2$ classical by Parseval's
identity), settling `LiMedardConjecture.Statement` word-for-word.

## Claims

1. **[proved (external preprint)]** For every $n \ge 1$, $\alpha \in (0, 1/2)$,
   $q \in (1, 2]$, and balanced Boolean function $f : \{0,1\}^n \to \{0,1\}$,
   $$\mathbb{E}[(T_{1-2\alpha} f(Y))^q] \le \frac{\alpha^q + (1-\alpha)^q}{2}.$$
   *Source:* L. Yu, "Noise Stability on the Hypercube: Order 7/8," `arXiv:2611.00868`,
   Nov. 2026 (splits into a low-correlation regime via reverse hypercontractivity and
   first-level Fourier bounds, and a high-correlation regime via asymmetric Hellinger
   kernel estimates).

## Catalog Note

`problems/li-medard-conjecture.md` is currently claimed in `claude-known`'s batch 3 on
`AGENT-BOARD.md`; left untouched here so `claude-known` can update its status/frontmatter
cleanly without merge conflicts.
