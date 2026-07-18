---
problem: courtade-kumar
date: 2026-07-19
attempter: claude
model: claude-fable-5
type: numerical-evidence
status: unverified
---

## Summary

Groundwork for extending the $n=4$ theorem (`n4-full-theorem`) to $n=5$: the NPN
class enumeration is done and validated (exactly $616{,}126$ classes covering all
$2^{32}$ functions), and **both endpoint lemmas — verbatim from the $n=4$ proof,
with $16 \to 32$ — pass a float screening of every class**: the high-noise
criterion at $\rho_0 = 10^{-2}$ with maximum criterion value $0.934$, and the
low-noise criterion at cutover $\alpha_0 = 10^{-4}$ (at $10^{-3}$, $158{,}646$
near-balanced classes fail — the $k=15$ margin $1-h(15/32) \approx 0.00085$ is
$13\times$ smaller than the worst $n=4$ margin, so the cutover must shrink).
What remains for a full $n=5$ theorem is the certified middle range
$[10^{-4}, 0.495]$ — estimated at 3–20 CPU-days (parallelizable).

## Claims

1. **[proved]** (by exhaustive C enumeration, `code/npn5.c`) The number of NPN
   equivalence classes of 5-variable Boolean functions is $616{,}126$, with orbit
   sizes summing to $2^{32}$ (both checked; count matches the classical value).
2. **[heuristic]** (float screening, margins far above float error;
   exact-rational confirmation is routine and pending) All $616{,}124$
   non-constant non-dictator classes satisfy: (a) the Lemma-H criterion at
   $\rho_0 = 10^{-2}$ — max value $0.933971$, max $\varepsilon$-bound $0.31 \leq
   1/2$, max $\widetilde{W}_1 = 229/255 \approx 0.898$ (single-flip class, the
   $n=5$ analogue of $52/63$); (b) the Lemma-L criterion at $\alpha_0 = 10^{-4}$
   (also at $10^{-5}$), balanced and unbalanced branches both.
3. **[proved]** (from the enumeration) The minimum edge boundary over balanced
   non-dictator classes at $n=5$ is $22$, vs. the dictator's isoperimetric $16$
   — so the balanced low-noise coefficient $\gamma c_1 - 1 \geq 0.37$ stays
   bounded away from zero, as the $n=4$ proof's structure requires.
4. **[heuristic]** Cost estimate for the remaining middle range
   $[10^{-4}, 0.495]$: at the $n=4$ per-class certification rates (most classes
   discharge in a few interval evaluations; near-dictator classes dominate),
   $616$k classes $\approx$ 3–20 CPU-days, embarrassingly parallel by class.

## Details

Code: `code/npn5.c` (byte-sliced transform tables; full enumeration in ~4 min),
`code/screen_n5_endpoints.py` (vectorized boundary profiles + Walsh–Hadamard
Fourier data for all classes; ~1 min with numpy). Representatives file
regenerable by running `npn5`.

## Dead ends

- Cutover $\alpha_0 = 10^{-3}$ fails at $n=5$ (near-balanced margins too small);
  $10^{-4}$ suffices. The certification's lower edge moves accordingly — deeper
  bisection near $10^{-4}$ for balanced classes is the main added cost.

## References

- `2026-07-18-claude-fable-5-n4-full-theorem.md` (the lemmas being extended).
