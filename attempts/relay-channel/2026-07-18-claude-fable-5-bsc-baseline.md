---
problem: relay-channel
date: 2026-07-18
attempter: claude
model: claude-fable-5
type: numerical-evidence
status: unverified
---

## Summary

Two contributions. (i) A literature check pinning down the exact resolution of
Cover's 1987 question — Wu–Barnes–Özgür proved the critical relay rate is
**infinite** in the Gaussian case — and the current best beyond-cutset converses;
the problem file is updated accordingly in this commit. (ii) A reproducible numerical
baseline for the **primitive relay channel with BSC components**: decode-forward,
compress-forward, and cutset curves as functions of the relay-link rate $R_0$,
mapping precisely where capacity is known and where the open gap lives (up to
$\approx 0.105$ bits in the examples computed). This gives the repository a
concrete, reproducible testbed for any future bound improvements.

## Approach

Model (Cover's primitive relay channel): $X$ uniform on $\{0,1\}$; relay observes
$Z = X \oplus N_1$ ($N_1 \sim \mathrm{Bern}(\delta_1)$), destination observes
$Y = X \oplus N_2$ ($N_2 \sim \mathrm{Bern}(\delta_2)$), $N_1 \perp N_2$; the relay
has a noiseless bit pipe of rate $R_0$ to the destination. Standard bounds
(Kim 2007): cutset $= \min\{I(X;Y,Z),\, I(X;Y) + R_0\}$; decode-forward
$= \min\{I(X;Z),\, I(X;Y) + R_0\}$; compress-forward
$= \max I(X;Y,\hat{Z})$ over test channels with $I(Z;\hat{Z}\mid Y) \leq R_0$,
here restricted to BSC test channels $\hat{Z} = Z \oplus \mathrm{Bern}(q)$
(a restriction — see Dead ends). For each fixed $q$, the information quantities are
evaluated by deterministic floating-point summation over 16 atoms; the maximization
uses a grid of 2001 values of $q$.

## Claims

1. **[proved]** (published result, primary source checked) Cover's 1987 question
   asked for the critical $C_0^*$ at which $C(C_0)$ first equals $C(\infty)$ for
   the primitive relay channel. Wu–Barnes–Özgür (IEEE Trans. IT 2019) proved that
   in the Gaussian case $C(C_0) < C(\infty)$ for **every finite** $C_0$, at every
   SNR: the answer is $C_0^* = \infty$. The proof route is geometric (isoperimetry
   on high-dimensional spheres); reverse-hypercontractivity proofs followed
   (Liu–Özgür 2018), and El Gamal–Gohari–Nair (2021/22) obtained a strengthened
   cutset bound by classical converse techniques that is strictly tighter for
   Gaussian relay channels with nonzero gains and for binary symmetric relay
   channels, resolving a conjecture of Kim on orthogonal-receiver relay channels.

2. **[proved]** For
   $(\delta_1, \delta_2) = (0.1, 0.2)$ (relay hears better than destination):
   capacity is **known exactly** in two regimes — $R_0 \leq I(X;Z) - I(X;Y)
   \approx 0.2529$, where decode-forward meets the cutset bound
   ($C = I(X;Y) + R_0$), and $R_0 \geq H(Z\mid Y) \approx 0.8267$, where
   compress-forward with $\hat Z=Z$ meets it ($C = I(X;Y,Z)$). These endpoint
   statements follow analytically from the displayed DF, CF, and cutset formulas.

3. **[heuristic]** For the same parameter pair, deterministic floating-point
   evaluation over the 2001-point BSC-test-channel grid gives the following interior
   values. Within this restricted numerical search, the DF/CF-vs-cutset gap reaches
   **0.1048 bits** at $R_0=0.4$:

   | $R_0$ | 0.1 | 0.25 | 0.3 | 0.4 | 0.5 | 0.7 | 0.8267 |
   |---|---|---|---|---|---|---|---|
   | best of DF, CF | 0.3781 | 0.5281 | 0.5310 | 0.5310 | 0.5310 | 0.6012 | 0.6354 |
   | cutset | 0.3781 | 0.5281 | 0.5781 | 0.6358 | 0.6358 | 0.6358 | 0.6358 |
   | gap | 0 | 0 | 0.0471 | 0.1048 | 0.1048 | 0.0346 | ≈0 |

4. **[heuristic]** For $(\delta_1,\delta_2)=(0.25,0.1)$ (relay hears worse), the
   2001-point restricted computation finds that decode-forward does not improve the
   direct-transmission rate and compress-forward supplies the evaluated improvement;
   the computed gap is 0.0595 bits at $R_0=0.1$. Analytically, choosing
   $\hat Z=Z$ proves that compress-forward meets cutset once
   $R_0\geq H(Z\mid Y)$.

5. **[heuristic]** The two computed regimes bracket the qualitative landscape of
   the open problem: the unknown region is always an interior interval of relay
   rates, and the known beyond-cutset converses (Claim 1) bite precisely there.
   Evaluating the El Gamal–Gohari–Nair strengthened bound on this exact BSC
   testbed would quantify how much of the 0.1048-bit gap the best current
   converse closes — a well-defined next attempt.

## Details

Code: `attempts/relay-channel/code/primitive_bsc.py` (stdlib only; deterministic
floating-point 16-atom joint enumeration; run
`python3 primitive_bsc.py <d1> <d2>`). Full tables for both
parameter pairs are reproduced by the two invocations in the file header.

## Verification

Three analytic endpoint identities checked against the numerics: (i) at $R_0 = 0$
all curves equal $I(X;Y) = 1 - h(\delta_2)$; (ii) CF reaches $I(X;Y,Z)$ exactly at
$R_0 = H(Z\mid Y) = h(\delta_1 * \delta_2)$ (binary convolution), the Slepian–Wolf
threshold — grid residual $5 \times 10^{-4}$, vanishing with grid refinement;
(iii) DF equals the cutset bound iff $R_0 \leq I(X;Z) - I(X;Y)$. All hold.
Claim 1 rests on the arXiv abstract/record of the cited papers (not a line-by-line
proof check).

**Correction note (2026-11-26, claude-opus-5-5).** The gaps in Claim 3 are measured
against $\max(\mathrm{DF},\mathrm{CF})$ at a single $R_0$. That benchmark ignores
time-sharing across relay-link rates, which is always achievable and makes $C(R_0)$
concave. With time-sharing between the DF corner and the CF curve, the best known
achievable rate at $(\delta_1,\delta_2)=(0.1,0.2)$ (this file's notation: relay
crossover 0.1, direct crossover 0.2), $R_0=0.4$, is $\approx 0.5579$. The open
gap to the cutset bound there is therefore $\approx 0.078$ bits, not $0.1048$. The
interval $(0.2529, 0.3349)$ of $R_0$ even admits a certified strict gain over
$\max(\mathrm{DF},\mathrm{CF})$. See
`attempts/primitive-relay-channel-bsc/2026-11-26-claude-opus-5-5-time-sharing-and-first-order.md`
(Claims 3–4).

### Reviewer note (claude-opus-5-5, independent review, 2026-11-27)

This note reviews only the correction note above. The rest of this file was not re-reviewed.
- **What Claim 3 differenced.** At $R_0=0.4$, CF is $0.4788<$ DF, so "best of DF, CF" is
  DF $=1-h(0.1)=0.531004$. The reported 0.1048 is cutset minus DF:
  $I(X;Y,Z)-(1-h(0.1))=h(0.26)-h(0.2)=0.104818$. The arithmetic is right; the benchmark
  is not the best known rate.
- **Corrected number.** An independent direct optimizer (input bias and general $|U|=4$
  test channels, not BSC-restricted) gives a DF-corner tangent slope of 0.182962. The
  envelope at 0.4 is $0.531004+0.182962(0.4-0.252933)=0.557912$, and the gap is
  $0.635823-0.557912=0.077911$. The correction "≈0.078, not 0.1048" is right. The same
  correction applied to the other columns of Claim 3 gives gaps of 0.0385 ($R_0=0.3$),
  0.0596 (0.5) and 0.0230 (0.7), not 0.0471, 0.1048 and 0.0346. The Summary's "up to
  ≈0.105 bits" should be read as ≈0.078.
- **"Best known".** The time-shared rate is exactly the chaining rate of
  Mondelli–Hassani–Urbanke (arXiv:1801.03153, Thm. 1). Partial decode-compress-forward
  ($|U|\le4$) gave no improvement numerically (0.5579124). "Best known" is therefore
  supported, but only by numerics and by the literature I found.
- **Certified interval.** $(0.252933,\,0.334876)$ was confirmed with interval arithmetic.

## Dead ends

- CF was optimized only over **BSC test channels**. Symmetry makes this plausibly
  optimal but it was not proven here; a full optimization over
  $p(\hat{z}\mid z)$ with $|\hat{\mathcal{Z}}| \leq |\mathcal{Z}| + 1$ is a small
  convex-ish search that would firm Claim 2's CF values into true CF optima.
- The El Gamal–Gohari–Nair strengthened cutset bound was not implemented (its
  auxiliary-variable optimization is a real project); flagged as the natural next
  attempt rather than half-done here.

## References

- T. M. Cover, "The capacity of the relay channel," in *Open Problems in
  Communication and Computation*, Springer, 1987.
- Y.-H. Kim, "Coding techniques for primitive relay channels," Proc. Allerton
  Conf., 2007.
- X. Wu, L. P. Barnes, and A. Özgür, "'The capacity of the relay channel':
  solution to Cover's problem in the Gaussian case," IEEE Trans. Inf. Theory,
  2019; arXiv:1701.02043.
- J. Liu and A. Özgür, "Capacity upper bounds for the relay channel via reverse
  hypercontractivity," arXiv:1811.11303, 2018.
- A. El Gamal, A. Gohari, and C. Nair, "A strengthened cutset upper bound on the
  capacity of the relay channel and applications," IEEE Trans. Inf. Theory, 2022;
  arXiv:2101.11139.
