---
problem: deletion-channel
date: 2026-07-21
attempter: claude-scheduled
model: claude-fable-5
type: new-bound
status: unverified
---

## Summary

Sharpens the rigorous Fertonani-Duman marker-genie lower bounds on $C(d)$ from
`2026-07-19-claude-fable-5-finite-n-baseline.md` by optimizing over symmetric
first-order Markov block inputs (flip probability $\gamma$) with exact
$I(X^n;Y)$ computation up to $n = 18$, at $d \in \{0.05, 0.1, 0.2, 0.3\}$.
This improves the repo's best rigorous bounds at every one of the four $d$
— e.g. $C(0.1) \ge 0.5548$ (was $0.5494$) and $C(0.3) \ge 0.1873$ (was
$0.1677$) — and adds first in-repo bounds at $d = 0.05$ ($\ge 0.7243$) and
$d = 0.2$ ($\ge 0.3286$). **No published record is beaten**: all four values
remain below Drinea-Mitzenmacher, and Fertonani-Duman's own Table VI already
tabulates $0.724$ / $0.555$ at $d = 0.05$ / $0.1$ (optimized inputs,
$\ell = 17$), which our $n = 18$ Markov values tie at their reported
precision. "New bound" is claimed relative to this repository's baseline
only.

## Approach

The baseline's Claim 3 (= Fertonani-Duman eq. (39); Cheraghchi-Ribeiro survey
eqs. (12)-(13)) is valid for **any** fixed distribution $p$ on $\{0,1\}^n$
used i.i.d. across blocks:

$$C(d) \;\ge\; \frac{I_p(X^n;Y) - H(\mathrm{Bin}(n,1-d))}{n}.$$

The baseline evaluated it with i.i.d. Bern(1/2) inputs ($n = 18$) and
Blahut-Arimoto-optimized inputs ($n = 12$; memory-limited). The gap between
the two suggests better single-parameter input families at larger $n$: here
$p$ = symmetric first-order Markov path measure with flip probability
$\gamma$ (stationary start; $\gamma = 0.5$ recovers i.i.d.), which the
baseline's exact machinery (`exact_mi.py`) already supports. Two changes make
the sweep cheap: a single pass over inputs $x$ accumulates all $\gamma$
values at once (the $O(n 4^n)$ embedding-count DP is shared; each extra
$\gamma$ costs only $O(4^n)$), and $\gamma$ is optimized on a coarse grid at
$n = 12$, refined at $n = 14$/$16$, with only the ~optimal $\gamma$ per $d$
run at $n = 18$.

## Claims

1. **[proved]** (validity). The marker-genie inequality above holds verbatim
   for Markov-within-block inputs: the proof in the baseline (independent
   length-$n$ blocks, side information $B_i = |\tilde Y_i| \sim$ i.i.d.
   $\mathrm{Bin}(n,1-d)$, Dobrushin achievability for stationary ergodic
   inputs) places no constraint on the within-block distribution $p$. No new
   argument is needed.

2. **[proved]** (new in-repo bounds, exact to float64; $n = 18$,
   per-$d$ optimized $\gamma$):
   $$C(0.05) \ge 0.72432,\quad C(0.1) \ge 0.55476,\quad C(0.2) \ge 0.32856,\quad C(0.3) \ge 0.18732.$$
   Each value is $\frac1n[I_p(X^n;Y) - H(\mathrm{Bin}(n,1-d))]$ with
   $I_p$ an exact enumeration (no sampling, no optimization-convergence
   caveats; accumulated float64 rounding $< 10^{-9}$ bits) and the binomial
   entropy an exact 19-term sum. These beat the baseline's best rigorous
   values at both $d$ it covered ($0.5494$ at $d=0.1$ and $0.1677$ at
   $d=0.3$, BA-optimized inputs at $n=12$) and are the repo's first
   non-vacuous bounds at $d = 0.05$ and $0.2$.

3. **[proved]** (honest placement vs. literature). All four values are below
   the Drinea-Mitzenmacher lower bounds ($0.7283$, $0.5620$, $0.3467$,
   $0.2224$ — Mitzenmacher's 2009 survey, Table 1). Fertonani-Duman's Table
   VI already lists $\ell = 17$ *optimized-input* values $0.724$ ($d=0.05$)
   and $0.555$ ($d=0.1$); our $n=18$ Markov values are $0.72432$ / $0.55476$
   — the former prints above FD's $0.724$ but is **within their 3-decimal
   rounding** (their true value may be anywhere in $[0.7235, 0.7245]$), the
   latter $0.0002$ below $0.555$; both are ties at the precision FD report,
   obtained with a one-parameter input family instead of a
   $2^{17}$-dimensional optimization. At $d = 0.2$ and $0.3$ Fertonani-Duman
   plot but do not tabulate their bound (Fig. 8), so $0.32856$ and $0.18732$
   appear to be the sharpest *explicitly stated* values of this particular
   bound family at those $d$ — but they are not records, since
   Drinea-Mitzenmacher dominates. Nothing here is claimed to beat published
   work.

4. **[numerical]** (structure of the optimum). The optimal flip probability
   decreases with $d$: $\gamma^* \approx 0.47$ at $d=0.05$, $\approx 0.44$
   at $d=0.1$, $0.36$ at $d=0.2$, $\approx 0.28$ at $d=0.3$ (stable across
   $n = 12,14,16,18$ to within grid resolution $0.02$; interpolating with
   the baseline's $\gamma^* \approx 0.15$ at $d = 0.5$). The bound's
   $n$-increments at $d = 0.05$ are $+0.0019$, $+0.0009$, $+0.0007$ per
   $\Delta n = 2$ (grid-limited at the $10^{-4}$ level); at this pace the
   $0.0040$ gap to Drinea-Mitzenmacher's $0.7283$ needs $n$ well beyond
   exact enumeration's reach. Within this bound family, feasible $n$ will
   not overtake Drinea-Mitzenmacher at any of the four $d$ (see Dead ends).

## Details

### Best genie bound per $n$ (per-$d$ optimal $\gamma$ on the computed grids)

| $n$ | $d=0.05$ | $d=0.1$ | $d=0.2$ | $d=0.3$ |
|---|---|---|---|---|
| 12 | 0.72086 ($\gamma$=0.45) | 0.54843 ($\gamma$=0.45) | 0.31433 ($\gamma$=0.35) | 0.16465 ($\gamma$=0.30) |
| 14 | 0.72274 ($\gamma$=0.46) | 0.55131 ($\gamma$=0.44) | 0.32054 ($\gamma$=0.36) | 0.17442 ($\gamma$=0.28) |
| 16 | 0.72363 ($\gamma$=0.46) | 0.55325 ($\gamma$=0.44) | 0.32504 ($\gamma$=0.36) | 0.18165 ($\gamma$=0.28) |
| 18 | **0.72432** ($\gamma$=0.46) | **0.55476** ($\gamma$=0.44) | **0.32856** ($\gamma$=0.36) | **0.18732** ($\gamma$=0.28) |

Underlying exact values at $n = 18$ (bits; $H_b := H(\mathrm{Bin}(18,1-d))$
= 1.778715, 2.320478, 2.789750, 2.999763 for $d$ = 0.05, 0.1, 0.2, 0.3):

| $d$ | $\gamma^*$ | $\frac1n I_p(X^{18};Y)$ | $H_b/18$ | bound |
|---|---|---|---|---|
| 0.05 | 0.46 | 0.823141 | 0.098817 | 0.724324 |
| 0.1 | 0.44 | 0.683675 | 0.128915 | 0.554760 |
| 0.2 | 0.36 | 0.483548 | 0.154986 | 0.328562 |
| 0.3 | 0.28 | 0.353970 | 0.166654 | 0.187317 |

(Exact table values for all computed $(n, \gamma, d)$ are in
`code/markov_genie_results.json`; the $\gamma$ grids were
$\{0.15,\dots,0.5\}$ step $0.05$ at $n=12$, $\{0.26,\dots,0.5\}$ step $0.02$
at $n=14$/$16$, and $\{0.28, 0.30, 0.36, 0.44, 0.46\}$ at $n=18$.)

### Comparison table (baseline vs. this attempt vs. published)

| $d$ | baseline best (rigorous) | this attempt ($n=18$ Markov) | FD Table VI ($\ell=17$, opt. input) | DM lower bound (record among rigorous cited) |
|---|---|---|---|---|
| 0.05 | — (not computed) | **0.7243** | 0.724 | 0.7283 |
| 0.1 | 0.5494 (BA, $n=12$) | **0.5548** | 0.555 | 0.5620 |
| 0.2 | — (not computed) | **0.3286** | not tabulated | 0.3467 |
| 0.3 | 0.1677 (BA, $n=12$) | **0.1873** | not tabulated | 0.2224 |

Castiglione-Kavcic obtained higher *simulation-based* estimates with
order-3 Markov inputs at large $n$; per the Cheraghchi-Ribeiro survey these
"are not true lower bounds, in the sense that there is no rigorous proof."
The values here are exact finite computations with a proved inequality, i.e.
true lower bounds.

### Compute

Single machine, `nice -n 19`, ~6 min total: $n=12$ (8 $\gamma$, 0.3 s),
$n=14$ (13 $\gamma$, 3.8 s; fine grid 15 $\gamma$, 4.6 s), $n=16$
(10 $\gamma$, 34 s), $n=18$ (5 $\gamma$, 288 s). The multi-$\gamma$
single-pass trick makes a
$G$-point sweep cost $\approx (n+G)/n$ of one pass, so the sweep was
essentially free; $n = 19$ would have quadrupled cost past the compute
budget for a projected gain of $\lesssim 0.003$ at best (half the
$\Delta n = 2$ increments in the per-$n$ table).

## Verification

- `markov_genie.py` re-runs on every invocation: (a) `analyze_multi` vs.
  brute-force deletion-subset enumeration at $n \in \{3,6\}$, i.i.d. and
  Markov ($\gamma = 0.25$), agreement $< 10^{-10}$ bits; (b)
  `analyze_multi` at $\gamma = 0.5$ vs. the baseline's independently-written
  `analyze` (uniform) at $n = 10$, agreement $< 10^{-9}$; (c)
  $H(\mathrm{Bin}(1,p)) = h_2(p)$.
- Consistency with the baseline's published table: at $\gamma = 0.5$ our
  $n = 14$ values reproduce the baseline's i.i.d. column exactly
  (e.g. $0.694844$ at $d=0.1$, $0.325913$ at $d=0.3$).
- External anchors: our i.i.d. $n=18$ genie bound at $d = 0.1$ ($0.5468$,
  baseline) matches FD's tabulated $\ell = 17$ IUD value $0.546$; our
  optimized-$\gamma$ $n=18$ values land within $10^{-3}$ of FD's
  $\ell = 17$ fully-optimized-input values: $0.72432$ vs. their $0.724$
  (nominally above, but inside their 3-decimal rounding) and $0.55476$ vs.
  $0.555$ — as expected, since first-order Markov is a strict subfamily of
  what FD optimize over, while $n=18$ vs. $\ell=17$ nearly offsets that.
- The inequality chain itself (Claim 1) is the baseline's Claim 3, which was
  community-reviewed there; no step is new.
- Reproduce: `python3 code/markov_genie.py 18 0.28,0.3,0.36,0.44,0.46`
  (plus the smaller-$n$ grid runs listed above); results merge into
  `code/markov_genie_results.json`.

## Dead ends

1. **Beating Drinea-Mitzenmacher via larger $n$.** At $d = 0.05$ the gap is
   $0.7283 - 0.7243 = 0.0040$, but the bound's increments are $+0.0019$
   ($n\,12\!\to\!14$), $+0.0009$ ($14\!\to\!16$), $+0.0007$ ($16\!\to\!18$)
   (grid-limited at the $10^{-4}$ level); closing $0.0040$ at a
   sub-$10^{-3}$-per-step pace needs $n \gtrsim 30$, i.e. $\gtrsim 4^{12}$
   times the $n=18$ compute — out of reach for exact enumeration
   ($O(n 4^n)$). Same at the other three $d$: gaps to DM are $0.0072$,
   $0.0181$, $0.0351$ against increments of $\sim 0.001$-$0.006$ per
   $\Delta n = 2$. Note the $n \to \infty$ limit of the bound *is* the true
   first-order-Markov information rate (the genie penalty
   $H(\mathrm{Bin})/n \sim \frac{\log_2 n}{2n} \to 0$), so the family is not
   structurally capped below DM — but the route to it through exact
   finite-$n$ computation is; only smarter analysis (as in DM's run-length
   arguments) or non-rigorous simulation (Castiglione-Kavcic) reaches large
   effective $n$.
2. **Hoping Markov inputs add headroom beyond Fertonani-Duman's own
   program.** They do not at small $d$: FD's Table VI optimized-input values
   at $\ell = 17$ ($0.724$, $0.555$) already essentially equal our $n = 18$
   Markov values — the one-parameter family recovers, but cannot exceed,
   what full input optimization at comparable length gives. The honest gain
   over the *baseline* comes from reaching $n = 16$-$18$ with optimized
   inputs at all (the baseline's BA route was memory-capped at $n = 12$),
   not from Markov structure being special.
3. **Finer $\gamma$ refinement.** A $0.005$-grid pass at $n = 14$ around
   each optimum (15 extra $\gamma$ values, in
   `markov_genie_results.json`) improved the best bound by at most
   $2.2 \times 10^{-4}$ ($d=0.05$: $0.722954$ at $\gamma = 0.47$ vs.
   $0.722736$ at $0.46$) and by $< 3 \times 10^{-5}$ at the other three $d$
   ($\gamma^* = 0.435, 0.36, 0.285$). The per-$n$ table reports $0.02$-grid
   values for uniformity. Re-tuning at $n = 18$ would cost another full
   ~6-minute pass for a projected $\lesssim 2 \times 10^{-4}$ — dropped, so
   the $d = 0.05$ entry at $n=18$ may sit $\sim 2\times10^{-4}$ below the
   family optimum.
4. **Second-order Markov inputs at $n = 18$.** Not attempted: the natural
   next family (order-2/3 Markov, cf. Castiglione-Kavcic) would need its own
   sweep over a 2-3 parameter space at $O(n 4^n)$ per point; at this $n$ the
   headroom (distance to the FD-optimal input value) is $\lesssim 10^{-3}$,
   so the compute cannot pay for itself. The binding constraint is $n$, not
   input-family richness.

## References

- Prior attempt extended:
  `attempts/deletion-channel/2026-07-19-claude-fable-5-finite-n-baseline.md`
  (its Claim 3 is the inequality used; its recorded dead ends — the
  subadditivity trap, $d \ge 0.5$ vacuousness of this bound at feasible $n$
  — were taken as given and not revisited).
- D. Fertonani, T. M. Duman, "Novel bounds on the capacity of the binary
  deletion channel," IEEE Trans. Inf. Theory 56(6), 2010 (arXiv:0810.0785).
  Table VI (lower bounds; $0.724$ and $0.555$ at $d = 0.05, 0.1$ with
  optimized inputs, $\ell = 17$) fetched and read for this attempt.
- M. Mitzenmacher, "A survey of results for deletion channels and related
  synchronization channels," Probability Surveys 6, 2009. Table 1 (the
  Drinea-Mitzenmacher lower bounds $0.7283, 0.5620, 0.3467, 0.2224$ at
  $d = 0.05, 0.1, 0.2, 0.3$) fetched and read for this attempt.
- M. Cheraghchi, J. Ribeiro, "An overview of capacity results for
  synchronization channels," arXiv:1910.07199 — eqs. (12)-(13) (the marker
  bound), and the remark that the Castiglione-Kavcic order-3 Markov
  numbers are simulation-based, not rigorous lower bounds.
- J. Castiglione, A. Kavcic, "Trellis based lower bounds on capacities of
  channels with synchronization errors," ITW 2015 (as cited by
  Cheraghchi-Ribeiro; not independently fetched).
- R. L. Dobrushin, "Shannon's theorems for channels with synchronization
  errors," Probl. Inf. Transm., 1967 (achievability for stationary ergodic
  inputs).

**Novelty check:** searched Fertonani-Duman (full text, Tables V-VI),
Mitzenmacher's survey (Table 1), and Cheraghchi-Ribeiro (Section 3) for
tabulated rigorous lower bounds at these $d$. Conclusion stated in Claim 3:
nothing here beats a published number; the improvement is over this
repository's baseline, plus explicitly-stated values of the FD bound family
at $d = 0.2, 0.3$ where FD published only a figure. The `new-bound` type
refers to the in-repo baseline.
