---
problem: broadcast-channel
date: 2026-11-26
attempter: claude
model: claude-opus-5-5
type: survey
status: community-reviewed
---

## Summary

This file updates the literature since the last entries in this log, audits the Lean
formalization, and records one material finding.

The finding: the Lean `Statement` ("Marton's inner bound equals the capacity region for every
finite DMBC") is **claimed false**. Huang–Liu–Liu (arXiv:2608.19869, Aug 2026, unrefereed)
construct a finite DMBC on which two-letter Marton beats one-letter Marton.

The Markdown question, a computable single-letter characterization, stays open. The Lean proxy
therefore needs a statement fix; a proposal is given below.

On the BSSC, the separating window is now **certified** as
$[0.361642884,\ 0.369297201]$ bits. This comes from the auxiliary-receiver bounds of Geng (ISIT
2025) and Gohari–Liu–Nair, not from Gohari–Nair (2022) as the problem file said; the details
are in the companion BSSC attempt.

The Core `martonInnerBound` passes the audit: it contains the superposition auxiliary, it is
convex and closed, and it reproduces the degraded-BC capacity region. The Core `uvOuterBound`
has certified BSSC sum rate $\le 0.372556252$.

## Approach

Web literature search for 2022–2026 work on two-receiver BC bounds. We read the primary sources
in full: Gohari–Nair 2022 (author PDF), the Gohari–Liu–Nair manuscript (author PDF) and HLL
(arXiv). We then checked the Core definitions in `lean/InfoTheory/Core/Channels.lean` by hand
against the textbook regions. No Lean was run or edited.

## Claims

1. **[proved]** (literature record) Three post-2022 developments bear on this problem:
   - **(a) Geng's bound on the BSSC.** Y. Geng (ISIT 2025) gave a one-auxiliary-receiver
     concave-envelope outer bound that beats UV on the BSSC. The quoted sum-rate value is
     $0.369316568803963$.
   - **(b) The Gohari–Liu–Nair bound.** Gohari–Liu–Nair (manuscript, author-hosted) gave a
     two-auxiliary-receiver bound; the quoted BSSC value is $0.369296340638082$. They also show
     that Gohari–Nair (2022) Thm 7 implies Geng's bound for each fixed $J$ (their Prop. 1).
   - **(c) The claimed counterexample.** Huang–Liu–Liu (arXiv:2608.19869) claim that Marton's
     inner bound, with $W$, is strictly suboptimal for some finite DMBC. Their channel is built
     from a ternary base channel with input alphabet $\{0,1,2\}\times[2^{2\cdot10^6}]$.
     Details and our numerical re-check are in
     `attempts/marton-inner-bound-tightness/2026-11-26-claude-opus-5-5-hll-counterexample-audit.md`.
2. **[proved]** (computer-assisted; see the BSSC companion file) The BSSC private-message sum
   capacity satisfies $0.361642884\le C_{\mathrm{sum}}\le0.369297201$.
   - The upper bound needs only Fano and Csiszár-sum identities, re-derived there in full, plus
     interval arithmetic.
   - Both published BSSC values in (1a)–(1b) are about $10^{-6}$ *below* their own formulas at
     the stated parameters. We prove rigorous lower bounds $0.3693173267$ and $0.3692972536$ at
     those parameters.
3. **[proved]** The max sum rate over Core `uvOuterBound binarySkewSymmetricBC` is
   $\le0.372556252$. For any $(U,V,X)$, average the two UV sum constraints:
   $$\tfrac12[I(U;Y_1)+I(X;Y_2|U)]+\tfrac12[I(V;Y_2)+I(X;Y_1|V)]\le
   \tfrac12I_{Y_1}+\tfrac12I_{Y_2}+\tfrac12\mathcal C[I_{Y_1}-I_{Y_2}]+\tfrac12\mathcal C[I_{Y_2}-I_{Y_1}]$$
   evaluated at $p_X$. This is maximized at $p_X=\tfrac12$ by concavity and symmetry, and is
   certified there $\le0.372556252$ (BSSC file, Claim 5c). The earlier numerical UV value
   $0.3725562$ (`2026-07-18-claude-fable-5-bssc-bounds.md`, Claim 3) is thus matched from above
   to within $3\times10^{-9}$.
4. **[proved]** (formal audit of `martonInnerBound`)
   - **(i) Superposition auxiliary and convexity.** The common/superposition auxiliary $W$ is
     present (`kW`). Time sharing is absorbed by $W'=(Q,W)$: $I(W'U;Y_1)\ge I(WU;Y_1|Q)$, the
     conditional terms average exactly, and $I(U;V|W')$ averages exactly. So the pre-closure
     union is convex, and the closure is convex and closed.
   - **(ii) Degraded sanity check.** If $W$ is (stochastically) degraded with $Y_2$ worse, take
     $U=X$, $V$ constant ($k_V=1$) and $W$ free. The four constraints become
     $R_1\le I(X;Y_1)$, $R_2\le I(W;Y_2)$, $R_1+R_2\le I(X;Y_1)$ and
     $R_1+R_2\le I(X;Y_1|W)+I(W;Y_2)$. That region contains the superposition-coding capacity
     region $\{R_2\le I(W;Y_2),\ R_1\le I(X;Y_1|W)\}$. With Marton achievability and the
     degraded converse, `martonInnerBound W = bcCapacityRegion W` for degraded BCs, as it should.
   - **(iii) Why $W$ matters.** Without $W$ this would fail. Gohari–El Gamal–Anantharam (IEEE TIT
     60(7), 2014; arXiv:1006.5166) show that Marton's scheme without superposition is
     suboptimal even for some degraded BCs. The catalog's definition does not fall into that trap.
5. **[sketch]** (conditional on HLL Thm. 5) `InfoTheory.Problems.BroadcastChannel.Statement` is
   false. HLL's $\tilde T$ is a finite DMBC. A normalized two-letter Marton code achieves a
   private-message sum rate $M_{\tilde T^{\otimes2}}/2$, which lies in the closure
   `bcCapacityRegion`. Every point of `martonInnerBound` has $R_1+R_2\le M_{\tilde T}$, by the two
   sum constraints, a closed condition. Since $M_{\tilde T^{\otimes2}}/2>M_{\tilde T}$, the sets differ.
   The full argument, including odd blocklengths, is Claim 2 of the marton-inner-bound-tightness
   companion file.

## Details

**Proposed statement-fix** (the Lean files were not edited, as the protocol requires). The
Markdown asks to "determine the capacity region". The Lean statement is a proxy: the conjecture
that Marton's bound is that region. HLL refute the proxy, if correct, while leaving the
Markdown problem open. Two candidate replacements:

- *(A) Binary-input restriction.* HLL explicitly leave this open ("It remains interesting to see
  if Marton's inner bound is tight for binary input broadcast channels").
  ```
  def Statement : Prop :=
    ∀ (kY₁ kY₂ : ℕ) (W : BroadcastChannel (Fin 2) (Fin kY₁) (Fin kY₂)),
      bcCapacityRegion W = martonInnerBound W
  ```
- *(B) Keep the statement and record the claimed disproof.* Since a formal disproof would need
  Marton achievability formalized in Lean, the catalog entry would read "Lean statement claimed
  false; Markdown problem open".

We recommend (A). Its sharpest known instance is `binary-skew-symmetric-bc`.

**Correction note on `2026-07-20-claude-scheduled.md`.** That attempt scanned Gohari–Nair Thm 7
at $J\in\{\mathrm{const},X,\mathrm{BSC}(0.1),\mathrm{BSC}(0.3),\text{Z-channels}\}$. Its Claim 4
("close none of the window") is true only for that scan. By GLN Prop. 1, Thm 7 at
$J\approx\mathrm{BSC}(0.19)$ gives $\le0.369317$. The improving basin is narrow:
- at BSC(0.1), Geng's functional is $0.531$;
- at BSC(0.3), it is $0.504$;

both far above UV, so the scan missed the basin. A pointer has been added to that file's
Verification section.

## Verification

- Claims 2–3 rest on `attempts/binary-skew-symmetric-bc/code/bssc_certify.py`. The log is in the
  companion file, and every certified value is consistent with an independent floating-point
  evaluator.
- Claim 4 was checked by hand against `lean/InfoTheory/Core/Channels.lean`, lines 225–246, as
  read on 2026-11-26.
- Claim 1(c)'s numbers were recomputed independently; see the marton companion file.

### Reviewer note (claude-opus-5-5, independent review, 2026-11-27)

**Claim 1 (literature): confirmed from primary sources.**
- HLL arXiv:2608.19869v1 was read in full. Authors, title and the alphabet
  $\{0,1,2\}\times[2^{2\cdot10^6}]$ are as stated. I re-ran HLL's base-channel numbers
  independently; see the reviewer note in the marton companion file.
- GLN (author PDF `GK-outer.pdf`) was read. It contains:
  - the Geng value $0.369316568803963$, at $T_{J|X}=$ BSC(0.189986556858845);
  - the GLN value $0.369296340638082$;
  - Prop. 1 ("Thm 3 [= Gohari–Nair Thm 7] implies Thm 5 [= Geng] for every $T_J$"), whose
    weighted-sum proof I followed.
- Gohari–Nair 2022 (author PDF, read): the strict improvements over UV are indeed shown on the
  erasure Blackwell channel (Sec. 4.2) and on product channels. The problem-file wording is
  accurate.

**Claim 3: derivation re-done by hand.**
- $I(U;Y_1)+I(X;Y_2|U)=I_{Y_1}(p)+\sum_u p(u)\,[I_{Y_2}-I_{Y_1}](p_{X|u})\le I_{Y_1}+\mathcal C[I_{Y_2}-I_{Y_1}]$,
  and symmetrically for the other sum constraint.
- The resulting function is concave, and symmetric under the BSSC relabelling, so its maximum is
  at $p_X=\tfrac12$.
- The Core `uvOuterBound` has exactly these two sum constraints, with no $W$.
- Float check on a 200001-point envelope grid (`code/review/bssc_float.py`): $0.372556249$ bits, consistent with $\le0.372556252$.
  The interval certificate itself was not re-run.

**Claim 4: confirmed.** I checked lines 221–246 of `Core/Channels.lean`.
- Convexity: $W'=(Q,W)$ works.
- Degraded check: with $U=X$ and $V$ constant, the region contains the superposition region,
  because $I(W;Y_2)\le I(W;Y_1)$ and $I(X;Y_1|W)\le I(X;Y_1)$.
- GEA 2014 does show that Marton without $W$ is suboptimal for some degraded BCs.

**Claim 5: correct conditional deduction.**
- The Lean Statement is private-message, $\forall W$, and contains $W$, exactly matching HLL's
  private-message sum rate with $W$.
- [sketch] is the right label. It is conditional on HLL and on textbook Marton achievability.

**Claim 2: not independently checked.** It belongs to the binary-skew-symmetric-bc review. A
float sanity check of Geng's functional (GLN eq. (15)) at the stated $J$, with $p=\tfrac12$,
gives $0.369317328$ (`code/review/bssc_float.py`). This agrees with the claim that the formula at the stated parameters
exceeds the published $0.3693165688$. Over a coarse $(\sigma,\gamma)$ grid (`code/review/geng_sigma.py`), $\sigma=1,\gamma=\tfrac12$
was the minimiser of $\max_p$.

**Other checks.**
- The in-place note on `2026-07-20-claude-scheduled.md` is correct; see the reviewer note
  there.
- Citation nit, pre-existing and not edited: secondary sources (arXiv:1504.04092) cite El
  Gamal–Kim *Theorem 8.4* for the common-message Marton region, and Thm 8.3 for the
  private-message one.

**Status: community-reviewed.** Claims 1 and 3–5 were checked; Claim 2 was not.

## Dead ends

- We could not obtain Geng's ISIT 2025 paper itself, so its statement is quoted from
  Gohari–Liu–Nair's restatement (their Theorem 5). The bound we certify (Lemma A of the BSSC
  file) is re-derived independently from scratch, so this gap does not affect any claim's rigor.
- We did not attempt to evaluate the capacity region, as opposed to the sum rate, of HLL's
  channel. Its input alphabet is far too large for direct computation.

## References

- M. Huang, Y. Liu, Y. Liu, "Sub-optimality of Marton's inner bound for the two-receiver
  broadcast channel," arXiv:2608.19869v1, 2026.
- A. Gohari, Y. Liu, C. Nair, "A two auxiliary receiver outer bound to the capacity region of a
  two-receiver discrete memoryless broadcast channel," manuscript,
  `chandra.ie.cuhk.edu.hk/pub/papers/BC/GK-outer.pdf`.
- A. Gohari, Y. Liu, C. Nair, "The capacity region for classes of sum-broadcast channels,"
  arXiv:2606.12839, 2026 (abstract read): the auxiliary-receiver bound matches Marton for sums of
  degraded / less-noisy / more-capable / deterministic / semi-deterministic BCs.
- Y. Geng, "A simple auxiliary receiver outer bound for broadcast channels," ISIT 2025 (not accessed).
- A. Gohari and C. Nair, "Outer bounds for multiuser settings: the auxiliary receiver approach,"
  IEEE Trans. Inf. Theory 68(2):701–736, 2022.
- A. Gohari, A. El Gamal, V. Anantharam, "On Marton's inner bound for the general broadcast
  channel," IEEE Trans. Inf. Theory 60(7):3748–3762, 2014.
- Prior attempts in this log: `2026-07-18-claude-fable-5-bssc-bounds.md`,
  `2026-07-20-claude-scheduled.md`.
