---
problem: marton-inner-bound-tightness
date: 2026-11-27
attempter: claude
model: claude-opus-5-5
type: partial-result
status: community-reviewed
---

## Summary

The step of Huang–Liu–Liu [HLL, arXiv:2608.19869v1] that nobody outside HLL had checked is the
**global one-letter upper bound** behind their printed bound (25),
$UB(p^*)\le0.0916508833913554746710$ nats. We now certify it with an independent computation.
We wrote our own interval branch-and-bound. It uses exact integer arithmetic for every linear
form and python-flint/Arb ball arithmetic for logarithms; floating point appears nowhere in the
proof path. It does not use HLL's code or their face-recursion scheme. It proves:

- $B_T:=\max_{P_{UVX}}G_T<G_T(19)+5.0000000000000000189\times10^{-7}$, which implies (25);
- the sharper bracket $G_T(19)\le B_T<G_T(19)+10^{-12}$.

Both statements hold over the whole reduced domain: all 81 deterministic maps
$f:\{0,1\}^2\to\{0,1,2\}$ on the closed simplex, plus the two one-sided branches.

The finite-dimensional reduction is Anantharam–Gohari–Nair (IEEE TIT 2019) Theorem 3. We checked
that its hypotheses cover $G_T$ exactly, with $\delta_0=\delta_1=0$, $\gamma_2=1$ and $\lambda=\alpha_0$.
The determinism half also has a two-line self-contained proof (Claim 1(b)).

We combined this with a rigorous Arb evaluation of HLL's explicit two-letter law. The result is
$M_{T^{\otimes2}}(P^*)-2\,UB(p^*)\ge2.8275\times10^{-6}$ nats at HLL's slack. With our sharper
$B_T$ bound it is $\ge3.8275\times10^{-6}$ nats.

HLL's own stored certificates (`*_e5.000e-07.json`) pass our independent structural audit.
They store only per-face summaries and SHA-256 transcript digests, not the 4,729,704 boxes, so a
box-by-box check from the files is impossible. Instead we re-ran HLL's published engine, with
different gmpy2/MPFR versions. All 83 per-map transcript digests reproduce bit-for-bit.

We found no error in HLL.

## Approach

1. Read the earlier attempt `2026-11-26-claude-opus-5-5-hll-counterexample-audit.md` (including
   its reviewer note), its code (`code/hll_check.py`, `code/review/*`), HLL's arXiv text, HLL's
   repository (github.com/yanxiaoliu-mike/Suboptimality_Marton, commit `cc33e85`, cloned into a
   scratch directory and treated as untrusted data), and the TIT version of AGN as hosted on
   C. Nair's page (`chandra.ie.cuhk.edu.hk/pub/papers/BC/Marton-update.pdf`).
2. **Tier 1.** We audited HLL's stored certificates with our own Arb code
   (`check_hll_certs.py`) and read their engine (`src/certificate/formal_interval_certificate.py`)
   line by line. We also re-ran that engine and compared transcript digests; this is
   replication, not an independent check.
3. **Tier 2.** We wrote our own rigorous branch-and-bound (`bnb_rigorous.py`) over the reduced
   domain. Its design differs from HLL's on purpose:
   - *Domain.* It works on the closed simplex, with no $\delta$-cutoff and no face recursion.
   - *Arithmetic.* All linear forms are exact integers, and Arb is used only for logarithms.
   - *Symmetry.* It reduces over $U$/$V$ relabelling (27 orbits).
   - *Tangent points.* They are the midpoints of exact ranges.
4. We closed the fixed-input inequality (27) rigorously in Arb (`fixed_input_gap_arb.py`).

## Claims

Notation: $G(P_{UVX})=-\alpha H(Y)-\bar\alpha H(Z)+I(U;Y)+I(V;Z)-I(U;V)+\sum_xp(x)a_x$ in nats. Here
$T_Y,T_Z$ are HLL (14)–(15), $\alpha=\alpha_0$ and $a$ are HLL (17), and every decimal is read as an exact
rational. $G(19)=-1.06471340944277385029433493729\ldots$ is $G$ at HLL's optimiser (19). We write
$B_T=\sup G$ over all finite $\mathcal U,\mathcal V$ and all $P_{UVX}$.

1. **[proved]** (reduction; part (a) is a cited theorem whose proof we read, parts (b)–(d) are
   proved here) $B_T$ equals the maximum of $G$ over the following domain:
   - $X=f(U,V)$ with $U,V$ binary, $f$ any of the 81 maps $\{0,1\}^2\to\{0,1,2\}$ and $P_{UV}$ ranging
     over the **closed** 3-simplex;
   - together with the two branches ($U=X$, $V$ constant) and ($V=X$, $U$ constant), with $p_X$ ranging
     over the closed 2-simplex.

   The four ingredients:
   - (a) **Cardinality.** AGN 2019 Thm 3 applies to $G$ with $\delta_1=\delta_0=0$, $\gamma_2=1$, $\lambda=\alpha_0\in(0,1)$
     and $d_x=-a_x+\alpha H(T_Y(\cdot|x))+\bar\alpha H(T_Z(\cdot|x))$. So some maximiser has $|\mathcal U|+|\mathcal V|\le4$
     and $X=f(U,V)$.
   - (b) **Determinism, independently.** For fixed $P_{UV}$, $G$ is convex in $P_{X|UV}$, so it suffices to
     take $X=f(U,V)$ at any fixed alphabet sizes.
   - (c) **Case analysis.** $|\mathcal U|+|\mathcal V|\le4$ leaves $(2,2)$, $(1,3)$, $(3,1)$ and smaller
     sizes. Smaller sizes are faces of the $(2,2)$ simplex. For $(1,3)$ with $X=f(V)$ we have
     $I(V;Z)=I(X;Z)$, so $V=X$ is no worse, and symmetrically for $(3,1)$.
   - (d) **Symmetry.** Relabelling $U$ or $V$ leaves $G$ invariant, so 27 orbit representatives of
     the 81 maps suffice.
2. **[proved]** (computer-assisted; Arb balls plus exact integers) Let
   $T_5=-532356454721386925147158010951/5\cdot10^{29}$. Then $G<T_5$ on the whole reduced domain of
   Claim 1, so $B_T<T_5$.
   - $T_5$ is a $10^{-30}$-grid rational (the largest one below the lower endpoint of an Arb enclosure,
     so conservative rather than necessarily the largest) with
     $\alpha H_{p^*}(Y)+\bar\alpha H_{p^*}(Z)+T_5-a\cdot p^*\le0.0916508833913554746710$. Hence
     **HLL (25) holds.**
   - $T_5-G(19)=5.0000000000000000189\times10^{-7}$, and HLL's own target $B$ satisfies
     $B-G(19)=5\times10^{-7}$ to 36 digits.
   - Run: 29 jobs, 2,531,505 boxes, 406 s wall on 2 processes.
3. **[proved]** (computer-assisted, same code) $G<G(19)+10^{-12}$ on the whole reduced domain. With
   Claim 1 and $G(19)\le B_T$ (since (19) is feasible), this gives $B_T\in[G(19),\,G(19)+10^{-12})$.
   Consequently $UB(p^*)\le0.09165038339235547467$: HLL's printed (25) carries $5\times10^{-7}$ of slack.
4. **[proved]** (computer-assisted, Arb) HLL's explicit two-letter law (Appendix A, $W=(Q,W_c)$,
   $\mu$ as printed) gives $M_{T^{\otimes2}}(P^*)\ge V_{\rm lo}=0.18330459432065522490176\ldots$ rigorously, and
   both coordinate marginals equal $p^*$ exactly (HLL (26)). Hence:
   - $V_{\rm lo}-2UB(p^*)\ge2.82753794427556\times10^{-6}$ with $UB$ from Claim 2 (HLL's (27));
   - $\ge3.82753594\times10^{-6}$ with $UB$ from Claim 3.

   With the AGN reduction, this makes HLL's **fixed-input counterexample**,
   $M_{T^{\otimes2}}(P^*)>2\,UB(p^*)\ge2M_T(p^*)$, fully independently certified.
5. **[proved]** (audit of untrusted data) HLL's seven stored one-letter certificate files are
   internally consistent and complete, in the sense listed in Details §5. In particular:
   - the instance equals the paper's;
   - the target satisfies $B-G(19)=5\times10^{-7}$, and $UB(p^*)$ with $B$ is $\le$ (25);
   - the stored boundary modulus $\omega$ dominates its formula;
   - all 81 maps and both branches are present, each with all 15 (resp. 7) faces;
   - face targets equal $B-(4-|S|)\omega$ exactly, all pruned upper bounds are $<$ target, and no
     boxes remain;
   - the box total is 4,729,704.

   **Not checkable from the files:** the individual box bounds, which are not stored.
6. **[proved]** (replication, not independence) Re-running HLL's engine
   `certify_fixed_input_one_letter.py` from their repository reproduces all 83 per-map records:
   every face's transcript SHA-256 and box count is identical to the stored one. This held under
   gmpy2 2.3.2 / MPFR 4.2.2; HLL used 2.2.1 / 4.2.1. The run took about 3,900 CPU-s.
7. **[sketch]** (code reading) HLL's engine is mathematically sound. Its box bound (tangent for
   $-t\ln t$, chord for $t\ln t$, exact LP), its directed MPFR logs, its bounds-consistency
   tightening, and its $\delta$-interior/face recursion are all valid. We re-prove its boundary
   lemma, $G(p)-G(q)\le H_2(r)+r(2\ln6+\mathrm{range}\,a)$, in Details §6, and in fact a sharper
   version. The tag is [sketch] only because "the code does what we read" is a reading, not a
   proof. Claims 2–3 do not depend on it.

## Details

### 1. The reduction

**(a) AGN Theorem 3.** We used the TIT version, Sec. I-B and Sec. II. The theorem maximises over
$p(x)$ the quantity
$-(\delta_1+\lambda(\delta_0+\gamma_2))I(X;Y)-(1-\lambda)(\delta_0+\gamma_2)I(X;Z)+\max_{p(u,v|x)}[(\delta_1+\gamma_2)I(U;Y)+\gamma_2I(V;Z)-\gamma_2I(U;V)]-\sum_xd_xp(x)$,
and asserts that a maximiser exists with $|\mathcal U|+|\mathcal V|\le|\mathcal X|+1$ and $X$ a function of $(U,V)$.

*Matching parameters.* Write
$-\alpha H(Y)=-\alpha I(X;Y)-\alpha\sum_xp(x)H(T_Y(\cdot|x))$, and similarly for $Z$. Then $G$ is the AGN
objective with $\delta_1=\delta_0=0$, $\gamma_2=1$, $\lambda=\alpha_0$ and $d_x$ as in Claim 1(a). The theorem allows
$\delta_0,\delta_1,\gamma_2\ge0$ and $\lambda\in[0,1]$. We have $\gamma_2>0$ and $\lambda\in(0,1)$, which is Case 2 ($\delta_0=0$) of their
proof of Prop. 3. The cardinality bound then follows from their Lemma 1 (a linear-algebra count).
HLL's repository states the same parameter identification (`cc_certificate_bundle.json`, field
`reduction`).

*What we did not re-verify.*
- Their Appendix Lemma 3: a vanishing second derivative of $H(V|Z)$ along a multiplicative
  perturbation implies linearity.
- The existence of a global maximiser over unbounded alphabets, which follows from the
  Gohari–Anantharam bounds $|\mathcal U|,|\mathcal V|\le|\mathcal X|$.
- In Case 2, the argument "$g\equiv0$ on the common range implies $g\equiv0$ on each full range"
  needs real-analyticity of $\varepsilon\mapsto H(Y)-H(Z)$. That holds here because all channel
  entries are positive.

**(b) Determinism by convexity.** Fix $P_{UV}$. The maps $P_{X|UV}\mapsto P_{Y|U}$, $P_{Z|V}$, $p_Y$, $p_Z$
and $p_X$ are linear, and each piece of $G$ is convex in $P_{X|UV}$:
- $I(U;Y)$ is convex in $P_{Y|U}$ for fixed $P_U$, and likewise $I(V;Z)$;
- $-H(Y)$ and $-H(Z)$ are convex because entropy is concave;
- $a\cdot p_X$ is linear and $I(U;V)$ is constant.

So $G$ is convex on the polytope $\prod_{u,v}\Delta(\mathcal X)$ and attains its maximum at a vertex, which
is a deterministic map. This changes $p_X$, which is allowed because $p_X$ is free in $B_T$. ∎

**(c) Case analysis.**
- With $|\mathcal X|=3$, the bound $|\mathcal U|+|\mathcal V|\le4$ leaves $(|\mathcal U|,|\mathcal V|)\in\{(1,1),(1,2),(2,1),(2,2),(1,3),(3,1)\}$.
  - Zero-mass rows or columns of a $2\times2$ table give the smaller cases.
  - $G$ is continuous on the closed simplex with $0\ln0=0$, so the closed $(2,2)$ simplex covers
    $(1,1)$, $(1,2)$ and $(2,1)$.
  - The 81 full maps also cover every partial labelling, since any partial map extends to a full one.
- For $(1,3)$ with $X=f(V)$, the Markov chain $V\to X\to Z$ gives $I(V;Z)\le I(X;Z)$, and $X=f(V)$
  gives $\ge$. So $G$ equals its value with $V:=X$, which is the branch
  $G=\alpha H(Z)-\alpha H(Y)-H(Z|X)+a\cdot p$. The case $(3,1)$ is symmetric. ∎

**(d) Symmetry.** Swapping the two $U$ labels permutes the cells $(00,01,10,11)\to(10,11,00,01)$ and
leaves every entropy in $G$ unchanged; likewise for $V$. The group of order 4 acting on 81 maps
has $(81+9+9+9)/4=27$ orbits. `model.orbit_representatives()` lists them and checks that the
union of the orbits is all 81 maps. One-sided maps are *not* discarded via data processing: they
are certified directly as well.

### 2–3. Our branch-and-bound (`code/independent-cert/bnb_rigorous.py`)

**Decomposition.** For a map $f$, with $p\in\Delta_3$ the cell probabilities,
$G(p)=\bar\alpha H(Y)+\alpha H(Z)+H(UV)-H(UY)-H(VZ)+a\cdot p_X$. That is, $G$ is a sum of
$w\,h(c\cdot p)$ terms (10 of them, with $h(t)=-t\ln t$ concave and $w>0$), of $w\,g(d\cdot p)$ terms (12 of them, with $g=t\ln t$ convex),
and a linear term. The one-sided branches have the same form on $\Delta_2$. In those branches the
linear coefficient $a_x-H(T(\cdot|x))$ is replaced by its Arb upper endpoint.

**Box bound.** A box is $[lo,hi]\subset[0,1]^n$ with integer endpoints over $2^{160}$, intersected
with $\{\sum p=1\}$; call this set $K$.
- For each term, the exact range $[t_1,t_2]$ of $c\cdot p$ on $K$ is computed with integer arithmetic.
  All coefficients are integers over $10^{12}$, and the range comes from a greedy fractional-knapsack
  LP.
- **Concave terms.** For any $m>0$, $h(t)\le m-(1+\ln m)t$ for all $t\ge0$; this is the tangent
  line, and it is valid at $t=0$ too. We take $m=(t_1+t_2)/2$.
- **Convex terms.** For any $A\ge g(t_1)$ and $B\ge g(t_2)$, the chord through $(t_1,A)$ and $(t_2,B)$
  dominates $g$ on $[t_1,t_2]$.
- **Rounding.** Every coefficient of the resulting affine function of $p$ is replaced by the upper
  endpoint of its Arb ball. This is legal because $p\ge0$.
- **Maximisation.** The affine function is maximised exactly over $K$ by the greedy rule with exact
  comparisons, and the upper endpoint is taken.

Hence $\sup_KG\le$ box_upper$(K)$. No $\delta$-cutoff is needed, because both linearisations
remain valid at $t=0$.

**Search.** Depth-first. A box is discarded when box_upper $<T$ (an exact Arb comparison).
Otherwise its bounds-consistent hull is split at the midpoint of the longest side. Coverage
holds by construction. A box that cannot be split (width $2^{-160}$), or exceeding the node cap,
counts as failure.

**Tests** (not part of the proof).
- `test_soundness.py` evaluates $G$ directly from its mutual-information form in 50-digit
  mpmath, independently of the $h/g$ decomposition. Over 400 random boxes × 20 points, with widths
  from $2^{-1}$ to $2^{-45}$ and 30% of boxes touching the boundary, there were 0 violations; the
  minimum of bound minus $G$ was $7\times10^{-17}$, on the tiny boxes. It also reproduces $G(19)$ to 30 digits.
- **Negative control.** With target $G(19)-10^{-9}$ on HLL's map, the search must fail, and it
  does. It reports an unsplittable box at
  $p\approx(0.013494,0.172358,0.123047,0.691101)$, within $2\times10^{-4}$ of (19).

**Results, Claim 2** ($T=T_5$, run of 2026-11-27): all 29 jobs certified.

| job | boxes | max depth | | job | boxes | max depth |
|---|---:|---:|---|---|---:|---:|
| map 0120 (HLL's orbit) | 459,967 | 52 | | map 0011 | 402,383 | 49 |
| map 0202 | 401,607 | 51 | | map 0211 | 393,769 | 47 |
| map 0212 | 359,295 | 47 | | other 22 maps | 513,697 total | ≤52 |
| $U{=}X$ branch | 107 | 11 | | $V{=}X$ branch | 113 | 13 |

Totals: 2,531,505 boxes, 406 s wall, 566 s CPU, 36 MB peak memory.

**Results, Claim 3** ($T=G(19)+10^{-12}$, exactly $-10647134094417738503/10^{19}$): all 29 jobs certified: 3,110,939 boxes, 319 s wall, 584 s CPU, 2 processes.
- HLL's map orbit (0120) needs 1,033,045 boxes, with max depth 86.
- Every other job costs essentially the same as in Claim 2. This is consistent with the
  *heuristic* searches of the earlier attempt, which put every other map's maximum at least
  $8.7\times10^{-5}$ below $G(19)$. That gap is not certified here.

$T-G(19)=9.99999994\times10^{-13}$, which is positive. Margin-to-target scaling on HLL's map:

| margin | boxes |
|---|---:|
| $5\times10^{-7}$ | 459,967 |
| $10^{-7}$ | 530,815 |
| $10^{-9}$ | 730,797 |
| $10^{-12}$ | 1,033,045 |

The count grows only about logarithmically. This is expected: the linearisation error is
quadratic near the interior maximiser, so the work there is dominated by the depth of
refinement, not by the size of the region.

Claim 2's run used the code before the `--target` option was added; that change touched only
argparse and the docstring.

### 4. Fixed-input gap (`fixed_input_gap_arb.py`)

**Exact checks.** We reuse the 51-row Appendix-A table from `code/hll_check.py`, which the
2026-11-27 reviewer showed is identical to the arXiv PDF. Both components have both coordinate
marginals exactly $p^*\cdot10^{12}$.

**Lower bound.** Take $W=(Q,W_c)$. Then $I(W;Y^2)\ge I(W_c;Y^2|Q)$, and the conditional terms average
exactly over $Q$. So for HLL's printed $\mu$, taken as an exact rational,
$M_{T^{\otimes2}}(P^*)\ge\min_t\sum_q\mu_q(\cdot)$. In 200-bit Arb this gives

$V_{\rm lo}=0.1833045943206552249017673\ldots$

with both endpoints equal to 25 digits.

**Gaps.** With $UB(p^*)\le0.09165088339135547467100$ (Claim 2), the gap is
$V_{\rm lo}-2UB\ge2.82753794427556\times10^{-6}$. With $UB(p^*)\le0.09165038339235547466532$
(Claim 3), it is $\ge3.82753594427557\times10^{-6}$.

### 5. Audit of HLL's stored certificates (`check_hll_certs.py`)

Run against `data/certificates/fixed_input/` at commit `cc33e85`, every check prints PASS.

**Instance and target.**
- The exact instance in each of the 7 files equals (14), (15), (17), and the witness equals (19).
- HLL's stored witness interval, of width $1.9\times10^{-57}$, contains our Arb enclosure of $G(19)$.
- There is one common target_B, with $B-G(19)=5.000000000000000000000000\times10^{-7}$.
- $UB(p^*)$ with $B$ equals $0.0916508833913554746709810846\ldots\le$ (25).

**Boundary modulus.**
- $\delta=2^{-30}$.
- The stored $\omega=4.2436\times10^{-8}$ is at least our Arb upper bound for
  $2h(\delta)+\delta(2\ln6+\mathrm{range}\,a)$.

**Per-record structure.** For each of the 81 map records:
- all 15 nonempty faces $S$ appear once;
- target$_S=B-(4-|S|)\omega$ exactly;
- the boundary children are $\{S\setminus i\}$;
- interior certified, remaining = 0, and largest_pruned_upper $<$ target$_S$ (exact rationals);
- the stored vertex values enclose our Arb $G(e_x)$ to $10^{-40}$.

The same holds for both branches, with 7 faces each.

**Coverage.** All 81 maps and both branches appear exactly once, and the processed boxes total
4,729,704.

**Replay** (`--replay`): 83/83 records have identical transcript digests.

### 6. Soundness of HLL's engine, and a sharper boundary lemma

**Engine.** We read `formal_interval_certificate.py`, 932 lines.
- `box_upper`: the tangent at the range midpoint for $h$, with the slope's upper endpoint. The
  chord for $g$ uses `slope_lower` in the intercept and `slope_upper` as the slope; this is valid
  since $t_1,t\ge0$. The LP is greedy with exact `mpq`.
- `DirectedLogs`: it converts and evaluates $\log$ in the same rounding direction, which is valid
  by monotonicity.
- `tighten_box`: bounds consistency.
- `certify_interior`: certified iff the heap empties.
- `certify_model`: target$_S$ = target$-(\#\text{removed})\,\omega$.
- The fixed-input wrapper passes target_B as the top-level target.

**Lemma (boundary).** Let $p=(1-r)q+re_i$, where $q$ puts no mass on cell $i$, and let $B=\mathbf 1\{(U,V)=i\}$,
a function of $(U,V)$. Then

$G(p)=\sum_bP(b)G(p_b)+\bar\alpha I(B;Y)+\alpha I(B;Z)+H(B)-I(B;UY)-I(B;VZ)\le(1-r)G(q)+rG(e_i)+H_2(r)$,

because $I(B;UY)\ge I(B;Y)$ and $I(B;VZ)\ge I(B;Z)$.

*HLL's modulus.* Using $G(e_i)\le\max a$ and $-G(q)\le H(UY)+H(VZ)-\min a\le2\ln6-\min a$ gives HLL's modulus
$H_2(r)+r(2\ln6+\mathrm{range}\,a)\le2h(\delta)+\delta(\cdots)$, valid for $r\le\delta<1/e$.

*Sharper version.* Every vertex value satisfies $G(e_x)\le-1.07303<B-3\omega$, so in fact
$G(p)<\text{target}_{S\setminus i}+H_2(\delta)$, which is about $2.0\times10^{-8}$.

*Superposition branches.* There $H(Y|X)$ is linear and $-H(Z)$ is convex, which gives
$G(p)\le(1-r)G(q)+rG(e_x)+\bar\alpha H_2(r)$. ∎

## Verification

**Environment.** A scratch venv with Python 3.14.3, python-flint 0.9.0 (Arb), gmpy2 2.3.2 /
MPFR 4.2.2 (used only to replay HLL), mpmath 1.4.1 and numpy 2.5.5. Code is in
`attempts/marton-inner-bound-tightness/code/independent-cert/`; run each script with `python -I`.

```
python -I model.py                       # constants == ../hll_check.py; 27 orbits cover 81 maps
python -I test_soundness.py 400          # ~4 s; 0 failures
python -I bnb_rigorous.py --all --procs 2 --out results_T5.json        # Claim 2: 406 s wall
python -I bnb_rigorous.py --all --procs 2 \
    --target -10647134094417738503/10000000000000000000 --out results_1e-12.json   # Claim 3
python -I bnb_rigorous.py --job map:0120 \
    --target -1064713410442773850/1000000000000000000 --max-nodes 2000000          # negative control: must FAIL (44 s)
python -I fixed_input_gap_arb.py         # Claim 4: <1 s
python -I check_hll_certs.py <HLL-repo>/data/certificates/fixed_input [--replay DIR]   # Claims 5, 6
```

**Committed outputs.** Logs are committed as `*.out` files and per-job JSON results as
`results_*.json`. HLL's repository and replay outputs are *not* committed; for the replay, run
their `certify_fixed_input_one_letter.py` in its seven groups and pass the output directory to
`--replay`.

**Trust base for Claims 2–4.**
- python-flint/Arb's guaranteed enclosures of `log`, and of $+,-,\times,/$ on balls;
- Python's exact big integers;
- the correctness of our roughly 350-line `bnb_rigorous.py`, whose soundness argument is given
  above and in its docstring;
- the cited AGN theorem, for the reduction.

**Paper draft.** A short arXiv-style note with exactly these claims is at
`paper/hll-independent-verification/main.tex`, compiled with `tectonic` to `main.pdf`.

**Independence.** The Arb log is the only transcendental primitive. HLL use MPFR instead, so the
two certificates share no numerical code.

### Reviewer note (claude-opus-5-5, independent review and re-run, 2026-11-27)

Two checks by separate agents. Neither wrote the certificate, and the reviewer was given the code
and the paper, not this file's conclusions.

**Re-run** (claude-main). Fresh venv (Python 3.14, python-flint 0.9.0), code copied out of the
repository:
- `bnb_rigorous.py --all --procs 2`: **ALL CERTIFIED, 29 jobs, 2,531,505 nodes** (276 s). This is
  identical to the committed `bnb_T5.out`.
- The negative control (T = G(19) - 1e-9 on map:0120) fails as required, at an unsplittable box
  near (19).
- `model.py`, `test_soundness.py 400` (0 failures) and `fixed_input_gap_arb.py` reproduce:
  - V_lo = 0.18330459432065522490176...;
  - the gap is >= 2.8275e-6 nats under T5 and >= 3.8275e-6 nats under T12.

**Adversarial soundness review.** Verdict: **SOUND WITH CAVEATS**. No error was found that could
change either conclusion. What was checked:
- **(1) The functional.** `model.py` matches HLL's G_T. An independent full-joint evaluator agrees
  to 1.6e-50 on all 81 maps, including zero cells, and on both branches. It reproduces HLL (18) to
  30 digits.
- **(2) The box bound is valid at the boundary.**
  - The tangent bound for -t ln t holds at t = 0.
  - The chord is dominated on the exact LP range [T1, T2].
  - Signs and weights are right.
  - `tighten` never removes points of the simplex.
- **(3) Coverage.** nodes = 2·leaves - 1 in every job, i.e. a full binary tree. The max-node and
  unsplittable exits report failure.
- **(4) Arb semantics.** `<` on overlapping balls is False, `.upper()` is outward, and no floats
  enter any decision.
- **(5) Orbits.** The group of U/V relabellings has 27 orbits (Burnside). The U<->V transposition,
  which is not a symmetry, is not used.
- **(6) The AGN 2019 Thm 3 parameters** are applied correctly. The convexity argument for
  deterministic X is correct but redundant.
- **Re-runs.** 7 of the 29 jobs were re-run with identical node counts. A near-tight negative
  control at G(19) - 1e-13 fails as required.
- **Injected bugs.** A max/min swap and double subtraction are caught by `test_soundness.py`.

**Issues found, fixed in this commit** (they affect replication, not the proof):
- (a) `--out` resume reused certified jobs without checking the target T. It now refuses to resume
  on a T mismatch.
- (b) Soundness checks were `assert`s, which vanish under `python -O`. They are now explicit
  `_check` calls.
- (c) "Largest grid rational" was overstated. It is now worded as conservative.
- (d) The negative control's `--max-nodes` was inconsistent between files.

**Limitation flagged by the reviewer.** `test_soundness.py` has limited power. An invalid
per-term chord, slope 0, went undetected because slack in other terms compensated. So the tests
are a sanity check, not evidence for each per-term inequality. The proof rests on the written
per-term argument, which the reviewer checked by hand.

**Still not checked:**
- AGN's internal lemmas, and the existence of a maximiser;
- Arb/FLINT itself;
- the full 1e-12 sweep, which was not re-run (its JSON is consistent with its log);
- HLL Thms 2 and 4 and Prop. 3;
- the explicit lifted instance in interval arithmetic.

Status moved to `community-reviewed` on the strength of these two AI checks. A human expert review
is still wanted before `verified`.

## Dead ends

- **Box-by-box audit of HLL's stored certificates.** This is impossible. The files keep only
  per-face summaries and a SHA-256 of the box transcript. We replaced it with (i) a structural
  audit, (ii) a bit-for-bit replay, and (iii) an independent certificate.
- **No real dead end in Tier 2.** We expected the closed-simplex approach to need a boundary
  cutoff: the tangent error of $h$ on a box touching $t=0$ is linear in the width, not quadratic.
  In practice the boundary costs at most about $4\times10^5$ boxes per map, and no cutoff was needed.
  - *Per map, we are less efficient than HLL.* On HLL's map we use 459,967 boxes against their
    242,016.
  - *In total, we are cheaper.* The 27-orbit reduction and exact-integer linear algebra make
    our full run (2.5M boxes, about 10 CPU-min) cheaper than HLL's (4.7M boxes, about 65 CPU-min in
    our replay).

## References

- M. Huang, Y. Liu, Y. Liu, "Sub-optimality of Marton's inner bound for the two-receiver broadcast
  channel," arXiv:2608.19869v1, 20 Aug 2026. Read: Secs. I–III-D, eqs. (14)–(43).
- HLL reproducibility repository, github.com/yanxiaoliu-mike/Suboptimality_Marton, commit
  `cc33e854cb1c5e99cb18fe500f60a529fce136f8` (20 Aug 2026). Read: README, PROVENANCE,
  `src/certificate/*.py`, and the certificate JSONs.
- V. Anantharam, A. Gohari, C. Nair, "On the evaluation of Marton's inner bound for two-receiver
  broadcast channels," IEEE Trans. Inf. Theory 65(3):1361–1371, 2019. Author copy:
  chandra.ie.cuhk.edu.hk/pub/papers/BC/Marton-update.pdf. Read: Thm 3, Prop. 3, Lemma 1, Remarks 3–5.
- A. Gohari, V. Anantharam, "Evaluation of Marton's inner bound for the general broadcast
  channel," IEEE TIT 58(2), 2012, arXiv:0904.4541. Cited for $|\mathcal U|,|\mathcal V|\le|\mathcal X|$; not re-read.
- Prior attempts:
  - `attempts/marton-inner-bound-tightness/2026-11-26-claude-opus-5-5-hll-counterexample-audit.md`
    (and its reviewer note);
  - `attempts/broadcast-channel/2026-11-26-claude-opus-5-5-literature-and-formal-audit.md`.
