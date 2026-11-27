---
problem: marton-inner-bound-tightness
date: 2026-11-26
attempter: claude
model: claude-opus-5-5
type: survey
status: unverified
---

## Summary

The catalog's "What is known" says that no counterexample to Marton's inner bound is known for
any two-receiver DMBC. That is out of date. M. Huang, Y. Liu and Y. Liu,
"Sub-optimality of Marton's inner bound for the two-receiver broadcast channel"
(arXiv:2608.19869v1, 20 Aug 2026) [HLL], claim a finite DMBC $\tilde T$ with
$M_{\tilde T^{\otimes2}}>2M_{\tilde T}$. Here $M$ is the private-message Marton sum rate *with* the
common auxiliary $W$. Their numerics are certified with exact rationals and outward-rounded MPFR.

If HLL is correct, the frozen Lean `Statement` of this problem is **false**: we give the
deduction below. So, for that matter, is `InfoTheory.Problems.BroadcastChannel.Statement`.

We independently recomputed every explicit number in HLL's ternary base-channel certificate from
the paper's text: the one-letter optimizer value, the dual bound $UB(p^*)$, and the two-letter value.
We also ran a falsification search against their one-letter upper bound. Every recomputed value reproduces HLL's printed digits except one bound, (25), discussed
below. The matches cover the one-letter optimizer value, the two-letter component values and
mixture, and the explicit-instance bounds (40) and (42).

The falsification search found nothing above HLL's one-letter optimum. It covers all 81
deterministic maps $f:\{0,1\}^2\to\{0,1,2\}$ and the edge cases that HLL's cardinality
reduction leaves. The search *recovers* HLL's non-rectangular optimizer exactly.

One discrepancy turned up, in the safe direction. HLL's printed bound (25),
$UB(p^*)\le0.09165088339\ldots$, is exactly $5.000\times10^{-7}$ above the value at their own
optimizer, $0.09165038339\ldots$; their eq. (40) uses the printed value. So their stated gaps
are, if anything, understated: the fixed-input gap would be $3.83\times10^{-6}$ rather than
$2.83\times10^{-6}$ nats. Either the extra $5\times10^{-7}$ is deliberate certification slack
for the global maximum $B_T$, or it is a one-digit typo.

We also audited `martonCommonInnerBound`. It is the standard five-inequality region; time sharing
is absorbed in $U_0$, so it is convex; it is closed; and its $R_0=0$ slice is exactly the Core
`martonInnerBound`, which includes the superposition auxiliary. There is no trivial catalog error.
The only issue is that the problem is now claimed to be *resolved negatively*.

## Approach

Literature search (web) for post-2022 work on Marton optimality. We read HLL in full from the
arXiv PDF: the abstract, Secs. I–III, and Appendices A–E. We then re-implemented their explicit
checks from scratch (`code/hll_check.py`), using the channel, input law, dual parameters,
optimizer and two-letter rational table exactly as printed. HLL's GitHub code was not used.

## Claims

1. **[proved]** (literature record, primary source read) HLL's Theorem 5 asserts that there is a
   finite two-receiver DMBC $\tilde T$ with $M_{\tilde T^{\otimes 2}}>2M_{\tilde T}$. Hence the
   one-letter Marton region of $\tilde T$, with $W$ and with or without a common message, is
   strictly inside its capacity region. The construction:
   - **(a) Base channel.** A ternary base channel $T$ (eqs. (14)–(15)) has a *fixed-input* two-letter gain at
     $p^*$: $M_{T^{\otimes2}}(P^*)\ge0.1833045943$ nats, while
     $2M_T(p^*)\le2\,UB(p^*)\le0.1833017668$ nats.
   - **(b) Gradient shaping and constraint removal.** Their Thms. 2 and 4 append
     "common deterministic components", revealed to both receivers with small probability. This
     makes $p^*$ the global one-letter optimizer while keeping the gain.
   - **(c) Explicit instance.** Input alphabet $\{0,1,2\}\times[N]$ with $N=2^{2{,}000{,}000}$
     (finite but astronomically large), and gap $\ge1.88\times10^{-6}$ nats (their (43)).

   The acknowledgments state that C. Nair and A. Gohari verified the non-numerical aspects.
   As of 2026-11-26 we found no peer-reviewed version, so the result should be treated as
   **claimed, not yet refereed**.
2. **[sketch]** (deduction, conditional on HLL Thm. 5) `MartonInnerBoundTightness.Statement` is false.
   - *The capacity side.* $\tilde T$ has finite alphabets, so it is an instance
     `BroadcastChannel (Fin kX) (Fin kY₁) (Fin kY₂)`. By Marton's theorem applied to the
     super-channel $\tilde T^{\otimes2}$, every rate pair in Marton's region of $\tilde T^{\otimes2}$
     is achievable there. Halving the rates makes it achievable on $\tilde T$ at even
     blocklengths. Odd blocklengths are handled by padding one symbol and aiming at a rate pair
     slightly inside the region. So the closure `bcCommonCapacityRegion` contains points
     $(0,R_1,R_2)$ with $R_1+R_2=M_{\tilde T^{\otimes2}}/2$.
   - *The Marton side.* Every point of the pre-closure set of `martonCommonInnerBound` satisfies
     $r_0+r_1+r_2\le\min\{I(U_0;Y_1),I(U_0;Y_2)\}+I(U_1;Y_1|U_0)+I(U_2;Y_2|U_0)-I(U_1;U_2|U_0)\le M_{\tilde T}$.
     This follows from the third and fourth inequalities. The bound is a closed condition, so it
     survives the closure.
   - *Conclusion.* Since $M_{\tilde T^{\otimes2}}/2>M_{\tilde T}$, the two sets differ.

   The same argument with `bcCapacityRegion` and `martonInnerBound` refutes
   `BroadcastChannel.Statement`. Logs vs. nats is immaterial.
3. **[proved]** (formal audit) `martonCommonInnerBound` has three properties.
   - **(i) It matches the Liang–Kramer five-inequality region.** It is the five-inequality region
     of Liang–Kramer / El Gamal–Kim. By Liang–Kramer–Poor (2011) this equals the Gelfand–Pinsker
     form with $R_0\le\min\{I(W;Y),I(W;Z)\}$ used in HLL Thm. 1.
   - **(ii) Its pre-closure union is convex.** Time-share two distributions with an independent
     $Q$ and use $U_0'=(Q,U_0)$. Then $I(U_0'U_1;Y_1)\ge I(U_0U_1;Y_1|Q)$, each conditional term
     $I(\cdot;\cdot|U_0')$ is the exact $Q$-average, and $I(U_1;U_2|U_0')$ is the exact average. So each
     right-hand side is at least the average of the right-hand sides.
   - **(iii) Its $R_0=0$ slice is the Core `martonInnerBound`.** At $r_0=0$ the five inequalities
     become exactly the four inequalities of `martonInnerBound` with $(W,U,V)=(U_0,U_1,U_2)$; the
     fifth is implied.

   Neither region is trivially false. Both contain the superposition auxiliary, which matters
   because Gohari–El Gamal–Anantharam (IEEE TIT 2014, arXiv:1006.5166) show that Marton *without*
   it is suboptimal even for degraded BCs. A degraded-BC sanity check is in the companion
   `attempts/broadcast-channel/` file.
4. **[heuristic]** (independent numerical re-check of HLL's explicit numbers; not a proof)
   `code/hll_check.py` gives the following.
   - **(a) Input checks.** All six channel rows sum to exactly 1 as decimals. HLL's optimizer
     (19) induces exactly $p^*$, and $G_T$ there equals $-1.06471340944277385029\ldots$,
     matching (18) to every printed digit.
   - **(b) The two-letter value.** From the Appendix-A rational table (51 rows; each component
     sums to exactly $10^{12}$), we recompute $A_0,B_0,A_1,B_1$, which match (44) to all printed
     digits. The mixture is $\gamma=0.1833045943206552249018$, matching (46). This is the
     two-letter *lower* bound, and it is an exact evaluation of an explicit distribution, so
     this part is essentially a proof modulo floating-point. We used 50-digit mpmath, not
     interval arithmetic.
   - **(c) The one-letter value at their optimizer.** It is $0.09165038339135547467$. Their
     certified bound (25) is $5\times10^{-7}$ larger, consistent with slack or a typo; the safe
     direction.
   - **(d) Explicit instance.** With their rational $\lambda,\delta_0,\delta_1$, which sum to
     exactly 1, and $L=2\cdot10^6\ln2$, we reproduce (40) $=0.300841866099154\ldots$ using
     the printed (25), and (42) $=0.601685614323941\ldots$. Hence (43), gap
     $\ge1.88\times10^{-6}$ nats.
   - **(e) Falsification search.** It finds no $P_{UVX}$ with $G_T>F_T$:
     - random multistart over $|U|,|V|\le4$ with randomized $X$ reaches only $F_T-9.9\times10^{-5}$,
       a local optimum, illustrating HLL's remark that the optimum occupies a tiny region;
     - the structured search over all 81 deterministic maps on binary $U,V$, plus the
       $(U\text{ const},V=X)$ and $(U=X,V\text{ const})$ cases, returns exactly $F_T$, at the
       map $f=(0,1,2,0)$, which is HLL's.

   What this does **not** establish: a certified global maximum of $G_T$. Our search is a
   grid of step $1/60$ plus local polish, not interval branch-and-bound. It also does not
   re-prove the cardinality and determinism reductions or HLL Thms. 2 and 4.
5. **[conjectural]** What remains open after HLL is the binary-input case; HLL themselves end
   with "It remains interesting to see if Marton's inner bound is tight for binary input
   broadcast channels". The BSSC sum rate (`binary-skew-symmetric-bc`) is the sharpest instance:
   its certified window is $[0.361642884,\ 0.369297201]$ bits, see
   `attempts/binary-skew-symmetric-bc/2026-11-26-claude-opus-5-5-certified-bounds.md`.

## Details

**Proposed statement-fix text** (the Lean files were not edited, as the protocol requires).
HLL is a recent research result, not a trivial or classical fact, so this is not a "catalog error" in the
AGENTS.md sense. It does change what the frozen `Statement` *means*: its expected truth value
flips to `False`.

We recommend the following:
- *(a) This problem.* Keep the frozen `Statement` and mark the problem in Markdown as
  "claimed resolved (negatively) by arXiv:2608.19869, pending verification". A formal disproof
  would need a formalized Marton achievability theorem, which is far beyond the current
  `Bridge/` toolkit.
- *(b) Optionally, a new open problem.* The natural open successor is the binary-input
  restriction:
  ```
  def StatementBinary : Prop :=
    ∀ (kY₁ kY₂ : ℕ) (W : BroadcastChannel (Fin 2) (Fin kY₁) (Fin kY₂)),
      bcCommonCapacityRegion W = martonCommonInnerBound W
  ```
- *(c) The `broadcast-channel` problem.* That problem asks for a *single-letter characterization*.
  Its Lean proxy "Marton = capacity for all $W$" is refuted by HLL, while the Markdown question
  remains open, so the proxy needs a statement-fix PR. See the companion broadcast-channel attempt.

**Remaining citation nits (not errors).** The Markdown and the Lean docstring cite "El Gamal–Kim
Theorem 8.3" for the common-message region. We could not consult the book to confirm the number,
so this is unverified; it may be Theorem 8.4.

## Verification

`code/hll_check.py` (mpmath, 50 digits, exact decimal-to-rational inputs; scipy multistart).
Output of `python hll_check.py 40` (2026-11-26):
```
0. channel row sums (exact decimal arithmetic):
   row sum 1 == 1
   row sum 1 == 1
   row sum 1 == 1
   row sum 1 == 1
   row sum 1 == 1
   row sum 1 == 1
1. induced p_X = ['0.704504835923', '0.172563088231', '0.122932075846']  (p* = ['0.704504835923', '0.172563088231', '0.122932075846'] )
   G_T at (19)  = -1.064713409442773850294335   (HLL (18): -1.06471340944277385029...)
2. UB(p*) using F_T := G_T(19) = 0.09165038339135547467098   (HLL (25): <= 0.0916508833913554746710)
   I(U;Y)+I(V;Z)-I(U;V) at (19) = 0.09165038339135547467098
3. q=0: A_q = 0.183313856336049032166  B_q = 0.183296001454080700361
3. q=1: A_q = 0.1833008202506018554789  B_q = 0.1833080957271021625141
   mu*A0+(1-mu)A1 = 0.1833045943206552249018 ; mu*B0+(1-mu)B1 = 0.1833045943206552249018   (HLL (46): 0.183304594320655224901767...)
   two-letter value - 2*UB(p*) = 3.82753794428e-6 nats  (HLL: >= 2.8275e-6)
4. |U|=2 |V|=2: best G found over 40 starts = -1.064812657596898
4. |U|=2 |V|=3: best G found over 40 starts = -1.064812657968591
4. |U|=3 |V|=2: best G found over 40 starts = -1.064812657582755
4. |U|=3 |V|=3: best G found over 40 starts = -1.064812658541469
4. |U|=4 |V|=4: best G found over 40 starts = -1.064812657582757
   search max - F_T(19) = -9.925e-05  (positive => (25) would be refuted)
5. best over all 81 deterministic maps (|U|=|V|=2): -1.064713409442773  map f(00,01,10,11)=(0, 1, 2, 0)
5. U const, V=X: best G = -1.064812657582755
5. U=X, V const: best G = -1.064813096704839
   structured max - F_T(19) = 1.110e-15  (positive => (25) would be refuted)
6. lambda+delta0+delta1 = 1.0
   (40) with UB printed (25): M_T~ <= 0.30084186609915446254   (HLL: 0.30084186609915448)
   (40) with UB recomputed: M_T~ <= 0.3008413660992684699   (HLL: 0.30084186609915448)
   (42): M_T~^2 >= 0.60168561432394164363   (HLL: 0.60168561432394163)
   (43) with printed (40): gap >= 1.88212563268e-6
(section 6 was added after the main run and executed separately via explicit_instance(UB);
 the full script now prints it between sections 3 and 4)
```

## Dead ends

- We did not attempt to re-certify HLL's **one-letter upper bound** $UB(p^*)$. That needs a
  certified *global* maximization of their dual functional $G_T$ over $P_{UVX}$. HLL do it with
  interval arithmetic after cardinality reduction ($|U|+|V|\le|\mathcal X|+1$). Our multistart
  search can only falsify it, not confirm it. This is the single step a referee should re-certify
  independently, since the whole counterexample rests on a $2.8\times10^{-6}$-nat margin.
- We did not check HLL Thms. 2 and 4 (gradient shaping, constraint removal) beyond reading the
  proofs in Appendices C–E. They are short and looked correct to us. That is a reading, not a
  formal check; label it **[sketch]**.

## References

- M. Huang, Y. Liu, Y. Liu, "Sub-optimality of Marton's inner bound for the two-receiver
  broadcast channel," arXiv:2608.19869v1, 20 Aug 2026 (read in full).
- Y. Liu, M. Huang, "Counterexamples to the Markovity conjecture for the two-receiver broadcast
  channel," arXiv:2608.13170, 2026 (cited by HLL; not read).
- A. Gohari, Y. Liu, C. Nair, "A conjecture regarding the optimizers of Marton's inner bound for
  the two-receiver broadcast channel," ISIT 2025 (cited by HLL; not read).
- C. Nair, "On Marton's achievable region: local tensorization for product channels with a
  binary component," ITA 2020 (cited by HLL; not read).
- A. Gohari, A. El Gamal, V. Anantharam, "On Marton's inner bound for the general broadcast
  channel," IEEE Trans. Inf. Theory 60(7):3748–3762, 2014, arXiv:1006.5166 (abstract read).
- Y. Liang, G. Kramer, H. V. Poor, "On the equivalence of two achievable regions for the
  broadcast channel," IEEE Trans. Inf. Theory 57(1):95–100, 2011 (cited from memory for the
  equivalence of the two common-message forms; not re-read).
- Companion attempts: `attempts/binary-skew-symmetric-bc/2026-11-26-claude-opus-5-5-certified-bounds.md`,
  `attempts/broadcast-channel/2026-11-26-claude-opus-5-5-literature-and-formal-audit.md`.
