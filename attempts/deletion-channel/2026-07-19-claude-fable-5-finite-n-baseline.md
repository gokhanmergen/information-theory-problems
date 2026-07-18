---
problem: deletion-channel
date: 2026-07-19
attempter: claude
model: claude-fable-5
type: numerical-evidence
status: unverified
---

## Summary

Exact (no sampling) computation of the finite-blocklength mutual information
rate $\frac1n I(X^n;Y)$ of the binary deletion channel for i.i.d. Bern(1/2)
inputs, all $n \le 18$ and $d \in \{0.1, 0.3, 0.5, 0.7, 0.9\}$, plus
Blahut-Arimoto evaluation of $C_n(d) = \frac1n \max_p I(X^n;Y)$ with certified
duality gaps for $n \le 12$, and first-order Markov inputs at $d=0.5$. The
i.i.d. sequence $\frac1n I$ is strictly decreasing in $n$ at every computed
$d$; it is **not** a lower bound on $C$ (concrete witness below), but two
rigorous families of bounds are extracted: $C \le C_n$ (upper) and the
Fertonani-Duman marker-genie lower bound $C \ge C_n - \frac1n H(\mathrm{Bin}(n,1-d))$.
Everything here reproduces or is dominated by known results (Fertonani-Duman
2010 reached $\ell = 17$ with the same machinery); the value of this attempt is
a reproducible in-repo baseline, the exact i.i.d. table itself, and a careful
record of what finite-$n$ numbers do and do not bound.

## Approach

The channel law factorizes through embedding counts: for $x \in \{0,1\}^n$ and
a candidate output $y$ of length $m \le n$,

$$P(y \mid x) = N(x,y)\, d^{\,n-m} (1-d)^m,$$

where $N(x,y)$ is the number of ways to delete $n-m$ positions of $x$ so that
$y$ remains (the number of embeddings of $y$ into $x$ as a subsequence),
computable by the standard DP $f(i,y) = f(i-1,y) + \mathbf{1}[y_{\text{last}} = x_i]\, f(i-1, y_{\text{minus last}})$.
The DP is vectorized over all $2^m$ strings $y$ of each length at once, and the
$\log c_m$ terms of $H(Y)$ and $H(Y|X)$ cancel, leaving

$$I(X^n;Y) = \sum_{m=0}^n c_m \Big[ \sum_x w(x) S_m(x) - \sum_{y \in \{0,1\}^m} S^w_m[y] \log_2 S^w_m[y] \Big],$$

with $c_m = d^{n-m}(1-d)^m$, $S_m(x) = \sum_y N(x,y)\log_2 N(x,y)$,
$S^w_m[y] = \sum_x w(x) N(x,y)$, and $w$ the input distribution
(i.i.d. uniform or Markov). Bitwise-complement symmetry halves the input loop.
Total cost $O(4^n \cdot n)$ time, $O(2^n)$ memory: $n = 18$ takes ~2 minutes.
For $C_n$ the full $2^n \times (2^{n+1}-1)$ transition matrix is built and
Blahut-Arimoto is run; at every iterate the dual certificate
$\max_x D(P(\cdot|x)\|q)$ gives a rigorous upper bound on $n\,C_n$ regardless
of convergence.

## Claims

1. **[proved]** (exact values, i.i.d. inputs). For i.i.d. Bern(1/2) inputs the
   values of $\frac1n I(X^n;Y)$ in the table below are exact up to float64
   rounding (absolute error $< 10^{-9}$ bits; see Verification). At every
   computed $d$, the sequence is strictly decreasing over $n = 1,\dots,18$
   (the strictness for all $n$ beyond 18 is observed, not proved).

2. **[proved]** (subadditivity; what the numbers bound). With i.i.d. inputs,
   $a_n := I(X^n;Y)$ is subadditive: $a_{n+m} \le a_n + a_m$. Hence by Fekete
   the i.i.d.-input information rate
   $I_{\mathrm{iid}}(d) := \lim_n a_n/n = \inf_n a_n/n$ exists and every
   finite-$n$ value $a_n/n$ is an **upper bound on $I_{\mathrm{iid}}(d)$**
   (which in turn satisfies $I_{\mathrm{iid}}(d) \le C(d)$). The finite-$n$
   value $a_n/n$ is **not** a lower bound on $C(d)$: at $d = 0.5$,
   $a_4/4 = 0.264151$, which exceeds the published upper bound
   $C(0.5) \le 0.212$ (Fertonani-Duman 2010, Table IV). Nor is it an upper
   bound on $C(d)$ without further argument. Both directions of naive reading
   are therefore wrong in general.

3. **[proved]** (rigorous lower bounds on $C$ via the marker genie, after
   Fertonani-Duman). For every $n$ and every input process assigning an
   arbitrary fixed distribution $p$ to each $n$-block independently,
   $$C(d) \;\ge\; \frac{I_p(X^n;Y) - H(\mathrm{Bin}(n,1-d))}{n}.$$
   With i.i.d. Bern(1/2) inputs at $n=18$ this gives
   $C(0.1) \ge 0.5468$ and $C(0.3) \ge 0.1363$ (the bound is negative, hence
   vacuous, for $d \ge 0.5$). These beat the closed-form bounds cited in the
   problem file — $(1-d)/9$ and $0.1221(1-d)$ — at $d = 0.1$ and $0.3$, but
   are *not new*: they are below Drinea-Mitzenmacher's $0.5620$ / $0.2224$,
   and Fertonani-Duman's Table VI already lists $0.546$ at $d=0.1$ for
   uniform inputs at $\ell = 17$ (our $n=18$ value $0.5468$ is the same bound
   one step further, a consistency check).

4. **[proved]** (rigorous upper bounds on $C$). $n C_n$ is subadditive, so
   $C(d) = \inf_n C_n(d) \le C_n(d)$ (Dobrushin; Kanoria-Montanari; Dalai
   ISIT 2011, Lemma 1). Blahut-Arimoto with the dual certificate gives, at
   $n = 12$: $C \le 0.7154,\ 0.3929,\ 0.2346,\ 0.1417,\ 0.0630$ at
   $d = 0.1, 0.3, 0.5, 0.7, 0.9$. These are weaker than Fertonani-Duman's published
   $\ell=17$ values ($0.689, 0.362, 0.212, 0.126, 0.049$ at
   $d = 0.1, 0.3, 0.5, 0.7, 0.9$) — same method, smaller $n$ — and are
   included as an internal consistency anchor, not as new bounds.

5. **[numerical]** (Markov inputs help at $d=0.5$). For symmetric first-order
   Markov inputs with flip probability $\gamma$, at $d = 0.5$, $n = 14$:
   $\frac1n I$ rises from $0.13871$ (i.i.d., $\gamma=0.5$) to $0.22192$ at
   $\gamma = 0.15$ (best on our grid $\{0.1, 0.15, 0.2, 0.25, 0.3, 0.4, 0.5\}$)
   — a 60% improvement, consistent with the known phenomenon that
   longer-run inputs are better for deletions. Note $0.22192$ again exceeds
   the known upper bound $C(0.5) \le 0.212$: finite-$n$ Markov rates are not
   achievable-rate claims either.

6. **[heuristic]** (extrapolation of the i.i.d. rate). The increments
   $a_n - a_{n-1}$ at $n = 18$ are $0.6038, 0.2190, 0.0678, 0.0169, 0.0018$
   for $d = 0.1, 0.3, 0.5, 0.7, 0.9$ and are still slowly drifting (not
   monotone in $n$ at $d=0.9$). Rigorously $I_{\mathrm{iid}}(0.5) \in
   [-0.0506, 0.1234] \cap [0,\infty)$ from Claims 2-3 applied to the i.i.d.
   sequence itself; heuristically the increment trend suggests
   $I_{\mathrm{iid}}(0.5) \approx 0.06$-$0.07$, well below the best known
   lower bound $C(0.5) \ge 0.1019$ achieved with run-length-structured
   inputs — i.i.d. inputs are genuinely bad for this channel at moderate $d$.

## Details

### Exact i.i.d. Bern(1/2) table: $\frac1n I(X^n;Y)$ (bits/input symbol)

| $n$ | $d=0.1$ | $d=0.3$ | $d=0.5$ | $d=0.7$ | $d=0.9$ |
|---|---|---|---|---|---|
| 1 | 0.900000 | 0.700000 | 0.500000 | 0.300000 | 0.100000 |
| 2 | 0.855000 | 0.595000 | 0.375000 | 0.195000 | 0.055000 |
| 3 | 0.824515 | 0.530868 | 0.306986 | 0.144868 | 0.036515 |
| 4 | 0.801162 | 0.486206 | 0.264151 | 0.116419 | 0.027059 |
| 5 | 0.782294 | 0.452862 | 0.234635 | 0.098329 | 0.021508 |
| 6 | 0.766567 | 0.426841 | 0.213001 | 0.085869 | 0.017925 |
| 7 | 0.753178 | 0.405886 | 0.196411 | 0.076772 | 0.015443 |
| 8 | 0.741595 | 0.388603 | 0.183243 | 0.069833 | 0.013632 |
| 9 | 0.731451 | 0.374075 | 0.172504 | 0.064356 | 0.012254 |
| 10 | 0.722477 | 0.361673 | 0.163553 | 0.059916 | 0.011171 |
| 11 | 0.714468 | 0.350946 | 0.155961 | 0.056237 | 0.010297 |
| 12 | 0.707271 | 0.341566 | 0.149425 | 0.053134 | 0.009576 |
| 13 | 0.700762 | 0.333285 | 0.143728 | 0.050476 | 0.008971 |
| 14 | 0.694844 | 0.325913 | 0.138710 | 0.048171 | 0.008456 |
| 15 | 0.689435 | 0.319302 | 0.134250 | 0.046150 | 0.008011 |
| 16 | 0.684472 | 0.313336 | 0.130255 | 0.044362 | 0.007623 |
| 17 | 0.679900 | 0.307920 | 0.126650 | 0.042765 | 0.007281 |
| 18 | 0.675672 | 0.302979 | 0.123378 | 0.041330 | 0.006977 |

Strictly decreasing in $n$ down every column. Subadditivity
$a_{n+m} \le a_n + a_m$ was checked on all 765 computed triples
$(n, m, d)$ with $n+m \le 18$: no violations.

### Proof of Claim 2 (subadditivity)

Split $X^{n+m} = (X_1, X_2)$ into independent blocks with outputs
$Y_1, Y_2$ of the two independent sub-channels; the full output is the
concatenation $Y = Y_1 \circ Y_2$, a deterministic function of $(Y_1,Y_2)$.
Data processing gives $I(X;Y) \le I(X; Y_1, Y_2)$, and since
$(X_1,Y_1) \perp (X_2,Y_2)$,
$I(X;Y_1,Y_2) = H(Y_1Y_2) - H(Y_1|X_1) - H(Y_2|X_2) \le I(X_1;Y_1) + I(X_2;Y_2)$.
Fekete's lemma then gives $\lim a_n/n = \inf a_n/n$. The same argument with
$\max_p$ shows $n C_n$ is subadditive, hence $C_n \ge \inf_k C_k = C$ (the
identification of $\inf C_k$ with the operational capacity is Dobrushin's
theorem; see Dalai 2011, Lemma 1, for this exact statement). The witness in
Claim 2 ($a_4/4 = 0.264151 > 0.212 \ge C(0.5)$) shows the i.i.d. finite-$n$
rate can strictly exceed capacity, because a length-4 code used once has no
synchronization cost across blocks; the cost appears only when blocks are
concatenated without markers.

### Proof of Claim 3 (marker-genie lower bound)

Take $k$ independent blocks of length $n$, each with input distribution $p$,
total input $X$, block outputs $\tilde Y_i$, and $Y = \tilde Y_1 \circ \cdots
\circ \tilde Y_k$. Let $B = (|\tilde Y_1|, \dots, |\tilde Y_{k-1}|)$. Given
$(Y, B)$ one recovers all $\tilde Y_i$, and conversely, so
$$I(X; \tilde Y_1 \dots \tilde Y_k) = I(X; Y, B) \le I(X;Y) + H(B) = I(X;Y) + (k-1) H(\mathrm{Bin}(n, 1-d)),$$
using independence of the $B_i \sim \mathrm{Bin}(n,1-d)$. The left side is
$k\, I_p(X^n;Y)$ by block independence. Dividing by $kn$ and letting
$k \to \infty$, the i.i.d.-across-blocks process achieves rate at least
$\frac1n [I_p(X^n;Y) - H(\mathrm{Bin}(n,1-d))]$ over the deletion channel,
and this is a lower bound on $C(d)$ (achievability for stationary ergodic
input processes on this channel is Dobrushin's theorem). This is exactly
Fertonani-Duman's marker construction (their eq. (39); survey form
$C_\ell \ge C \ge C_\ell - \frac1\ell H(V_1)$ with
$V_1 \sim \mathrm{Bin}(\ell, 1-d)$), with $H(\mathrm{Bin})$ replacing the
cruder $\log_2(n+1)$ of Dalai's Lemma 1.

Values of the bound with i.i.d. Bern(1/2) inputs at $n = 18$
($H(\mathrm{Bin}(18, 1-d)) = 2.3205,\ 2.9998,\ 3.1316,\ 2.9998,\ 2.3205$
bits for $d = 0.1, 0.3, 0.5, 0.7, 0.9$):

| $d$ | $C \ge$ (iid, $n=18$) | $C \ge$ (BA-optimized, $n=12$) | best known lower (DM) | $0.1221(1-d)$ | $(1-d)/9$ |
|---|---|---|---|---|---|
| 0.1 | **0.5468** | **0.5494** | 0.5620 | 0.1099 | 0.1000 |
| 0.3 | **0.1363** | **0.1677** | 0.2224 | 0.0855 | 0.0778 |
| 0.5 | vacuous ($-0.0506$) | vacuous ($-0.0021$) | 0.1019 | 0.0611 | 0.0556 |
| 0.7 | vacuous ($-0.1253$) | vacuous ($-0.0840$) | 0.0453 | 0.0366 | 0.0333 |
| 0.9 | vacuous ($-0.1219$) | vacuous ($-0.1030$) | 0.0124 | 0.0122 | 0.0111 |

### Claim 4 ($C_n$ upper bounds via Blahut-Arimoto)

For any output distribution $q$, $\;n C_n \le \max_x D(P(\cdot|x) \| q)$
(capacity duality / minimax redundancy), so every BA iterate certifies a
rigorous upper bound irrespective of convergence; the primal value
$I(p_t)$ certifies a lower bound on $n C_n$. Upper bounds $C \le C_n \le$:

| $n$ | $d=0.1$ | $d=0.3$ | $d=0.5$ | $d=0.7$ | $d=0.9$ |
|---|---|---|---|---|---|
| 10 | 0.7301 | 0.4108 | 0.2477 | 0.1505 | 0.0671 |
| 11 | 0.7223 | 0.4013 | 0.2407 | 0.1454 | 0.0649 |
| 12 | 0.7154 | 0.3929 | 0.2346 | 0.1417 | 0.0630 |

At $d \in \{0.1, 0.3\}$ BA converged to certified duality gap $< 10^{-7}$;
at $d \in \{0.5, 0.7, 0.9\}$ it hit the 3000-iteration cap with certified gap
$\le 5.5 \times 10^{-4}$ — the upper bounds above are rigorous regardless
(dual certificate), and the corresponding $C_n$ lower estimates used in the
marker bound are at most that much below the true $C_n$.

Comparison: Fertonani-Duman 2010 (Table IV) already published the stronger
$\ell = 17$ values $0.689, 0.362, 0.212, 0.126, 0.049$; the recent
parallelized-BA work (arXiv:2604.05867) pushes further and yields
$C \le 0.3578(1-d)$ for $d \ge 0.64$. Our $n=12$ values are consistent with,
and dominated by, both — as expected since $C_n$ decreases in $n$ along the
subadditive sequence.

### Claim 5 (Markov inputs at $d = 0.5$), exact values of $\frac1n I$

| $n$ | $\gamma=0.1$ | $0.15$ | $0.2$ | $0.25$ | $0.3$ | $0.4$ | $0.5$ (iid) |
|---|---|---|---|---|---|---|---|
| 8 | 0.25314 | 0.26384 | 0.26322 | 0.25594 | 0.24463 | 0.21564 | 0.18324 |
| 10 | 0.23597 | 0.24600 | 0.24447 | 0.23642 | 0.22456 | 0.19529 | 0.16355 |
| 12 | 0.22320 | 0.23254 | 0.23033 | 0.22177 | 0.20962 | 0.18041 | 0.14942 |
| 14 | 0.21319 | 0.22192 | 0.21918 | 0.21028 | 0.19798 | 0.16896 | 0.13871 |

The optimum on the grid sits at $\gamma \approx 0.15$ for every computed $n$
(mean run length $\approx 6.7$), and the relative improvement over i.i.d.
grows with $n$ (44% at $n=8$, 60% at $n=14$).

### Numerical precision

All quantities are finite sums with exact integer combinatorial weights
($N(x,y) \le \binom{18}{9} = 48620$, within exact float64 range) evaluated in
float64; entropy sums have $\le 2^{19}$ terms, so accumulated rounding is
$< 10^{-9}$ bits. "Exact" throughout means exact enumeration, not interval
arithmetic.

## Verification

- DP channel law vs. brute-force enumeration of all $2^n$ deletion subsets:
  agreement to $< 10^{-10}$ bits for $n \in \{2,3,5,6\}$, $d \in \{0.1,0.5,0.9\}$,
  both i.i.d. and Markov ($\gamma = 0.3$) inputs (asserted at the start of
  `exact_mi.py main()` on every run).
- Analytic check $I(X^1;Y) = 1-d$ for all five $d$: passes to $10^{-12}$.
- $\sum_y P(y|x) = 1$ asserted for every row of the BA transition matrix.
- Subadditivity holds on all 765 computed $(n,m,d)$ triples.
- External anchor: our $n=18$ i.i.d. marker bound at $d=0.1$ (0.5468) matches
  Fertonani-Duman's published $\ell=17$ IUD value (0.546); our $C_n$ uppers
  lie above their $\ell=17$ values as they must.
- Code: `attempts/deletion-channel/code/exact_mi.py` (i.i.d. + Markov tables,
  `results.json`), `code/ba_bounds.py` ($C_n$, `ba_results.json`),
  `code/summarize.py` (derived tables). Python 3 + numpy only.
  `python3 exact_mi.py 18` reproduces everything i.i.d./Markov (~4 min);
  `python3 ba_bounds.py 12` reproduces the $C_n$ bounds.

## Dead ends

1. **Hoping the i.i.d. finite-$n$ rate lower-bounds $C$ via superadditivity.**
   It does not: with i.i.d. inputs $a_n$ is *sub*additive (concatenation
   destroys block boundaries; the genie inequality runs the wrong way), so
   $a_n/n$ approaches $I_{\mathrm{iid}}$ from above and can exceed $C$
   — witnessed concretely by $a_4/4 = 0.2642 > 0.212 \ge C(0.5)$. The only
   rigorous route from finite-$n$ i.i.d. numbers to a lower bound on $C$ is
   the marker-genie penalty $-H(\mathrm{Bin}(n,1-d))/n$, and paying it makes
   the bound vacuous for $d \ge 0.5$ at every $n \le 18$: the penalty decays
   like $\frac{1}{2n}\log_2 n$ while the available rate at $d \ge 0.5$ is
   $\lesssim 0.12$, so $n$ in the several hundreds would be needed — far
   beyond exact enumeration ($O(4^n)$).
2. **Pushing $n$ past 18.** Cost quadruples per increment ($n=18$: 131 s;
   $n = 22$ would be ~9 h and, for the $P(y)$ accumulator, $2^{23}$ floats —
   feasible but pointless: the numbers move by $< 0.005$/step and no bound
   changes character). For $C_n$, the transition matrix at $n = 13$ already
   needs > 1 GB; Fertonani-Duman reached $\ell = 17$ in 2010 with the same
   method and arXiv:2604.05867 (2026) has parallelized it further, so more
   compute here duplicates known results.
3. **BA underflow.** Blahut-Arimoto drives some input weights below
   $10^{-308}$, making some $q(y)$ underflow to exactly 0 and poisoning
   $D(P\|q)$ with NaN. Fixed by clamping $q$ at $10^{-300}$ and renormalizing
   — legitimate because the dual certificate holds for *any* probability
   vector $q$. (First run produced silent NaNs; results were discarded and
   recomputed.)
4. **Reading Markov finite-$n$ rates as achievable rates.** At $d=0.5$ they
   exceed the known capacity upper bound for all $n \le 14$ computed, so any
   such reading is unsound; they only indicate the direction of input
   optimization (toward longer runs), consistent with the run-length
   literature.

## References

- Prior attempts consulted: none (this is the first attempt on
  `deletion-channel`).
- R. L. Dobrushin, "Shannon's theorems for channels with synchronization
  errors," Probl. Inf. Transm., 1967.
- D. Fertonani, T. M. Duman, "Novel bounds on the capacity of the binary
  deletion channel," IEEE Trans. Inf. Theory 56(6), 2010 (arXiv:0810.0785).
  Tables IV (upper bounds; 0.212 at $d=0.5$) and VI (marker lower bounds;
  0.546 at $d=0.1$, $\ell=17$, IUD inputs) used above.
- S. Diggavi, M. Mitzenmacher, H. Pfister, "Capacity upper bounds for the
  deletion channel," ISIT 2007 — Table I tabulates the Drinea-Mitzenmacher
  lower bounds (0.5620, 0.2224, 0.1019, 0.04532, 0.01238 at
  $d = 0.1, 0.3, 0.5, 0.7, 0.9$).
- M. Dalai, "A new bound on the capacity of the binary deletion channel with
  high deletion probabilities," ISIT 2011 — Lemma 1 ($C = \inf_n C_n$,
  $C \ge C_n - \log(n+1)/n$).
- Y. Kanoria, A. Montanari, IEEE T-IT 2013 (subadditivity of $nC_n$).
- M. Cheraghchi, J. Ribeiro, "An overview of capacity results for
  synchronization channels," arXiv:1910.07199 — eq. (16) is the
  $H(\mathrm{Bin})$ form of the marker bound used in Claim 3.
- I. Rubinstein, R. Con, arXiv:2305.07156 — $C > 0.1221(1-d)$;
  $C < 0.3745(1-d)$ for $d \ge 0.68$.
- arXiv:2604.05867 (2026) — parallelized Blahut-Arimoto;
  $C \le 0.3578(1-d)$ for $d \ge 0.64$.
- M. Mitzenmacher, "A survey of results for deletion channels and related
  synchronization channels," Probab. Surveys, 2009.

**Novelty check:** searched the papers above (fetched and read
Fertonani-Duman 0810.0785, Dalai ISIT 2011, DMP ISIT 2007, Cheraghchi-Ribeiro
1910.07199, Rubinstein-Con abstract, 2604.05867 abstract) — every bound
produced here is an instance of the Fertonani-Duman finite-length program and
is dominated by their $\ell = 17$ numbers or successors. No novelty is
claimed; the exact i.i.d. $\frac1n I$ table to $n=18$ and the Markov grid are
provided as reusable baseline data.
