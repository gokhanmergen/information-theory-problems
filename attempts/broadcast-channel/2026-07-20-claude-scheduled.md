---
problem: broadcast-channel
date: 2026-07-20
attempter: claude-scheduled
model: claude-fable-5
type: numerical-evidence
status: unverified
---

## Summary

First (to our knowledge) numerical evaluation of both Gohari–Nair (2022)
auxiliary-receiver outer bounds — Theorem 7 (the "J version" of the UV bound)
and Theorem 8 (the two-auxiliary-receiver bound) — on the BSSC private-message
sum rate, executing the next step flagged by
`2026-07-18-claude-fable-5-bssc-bounds.md`. Both implementations provably
reduce to the UV bound at their trivial auxiliary-receiver settings and
reproduce the UV sum-rate value $0.3725562$ there to $10^{-7}$. **Outcome
(negative but informative): across every auxiliary-receiver channel scanned
(9 for Theorem 8, 6 for Theorem 7) and at the auxiliary cardinalities tried,
no configuration produced a sum-rate bound below the UV value** — every usable
Theorem 7 estimate lands exactly at $0.3725562$ and every nontrivial Theorem 8
configuration is strictly looser ($\geq 0.5$). The BSSC sum-capacity window
$[0.3616428,\ 0.3725562]$ is left unchanged by this evaluation; where an
improvement would have to come from (if anywhere) is localized in Dead ends.

## Approach

**Source.** A. Gohari and C. Nair, "Outer bounds for multiuser settings: the
auxiliary receiver approach," IEEE Trans. Inf. Theory 68(2):701–736, 2022. No
arXiv posting was found (searched for the title and authors); the author-hosted
final PDF at `chandra.ie.cuhk.edu.hk/pub/papers/NIT/Auxiliary-Receiver.pdf`
was used, and all equations were transcribed from the rendered pages (pp.
17–18 for Theorem 7, p. 23 for Theorem 8), not from lossy text extraction.

**Theorem 7** (J version of the UV outer bound; outputs $Y,Z$, sender $X$):
for any achievable $(R_0,R_1,R_2)$ there is a $p(x)$ such that *for every*
auxiliary channel $T_{J|X,Y,Z}$ there exist auxiliaries with joint
$p_{U,V,W,X}\,p_{\tilde W,\tilde U,\tilde V|X}\,p_{\hat W,\hat U,\hat V|X}\,
T_{Y,Z|X}\,T_{J|X,Y,Z}$ satisfying nine rate constraints (18a)–(18i) — of
which (18b), (18e), (18i) are exactly the UV constraints and (18c), (18d),
(18f), (18g), (18h) are new, $J$-dependent ones — together with three
equality constraints (19a)–(19c) of Csiszár-sum type, e.g. (19a):
$[I(\tilde W;Z)-I(\tilde W;J)] + [I(\hat W;J)-I(\hat W;Y)] = I(W;Z)-I(W;Y)$,
and constraints (20a)–(20c), e.g. (20a):
$0 \le I(X;Z|\tilde U,\tilde W)-I(X;J|\tilde U,\tilde W) \le
I(\tilde V;Z|\tilde W)-I(\tilde V;J|\tilde W)$ and (20c):
$I(V;Z|W)+I(X;Y|V,W) = I(U;Y|W)+I(X;Z|U,W)$. Cardinality caps: the three
$W$-type variables $\le |\mathcal X|+6 = 8$, the six $U/V$-type $\le
|\mathcal X|+1 = 3$. The full expressions are reproduced in the code
docstrings.

**Theorem 8** (two auxiliary receivers, $J$ given to the $Y$-receiver and
$\hat J$ to the $Z$-receiver): for *any* $T_{J,\hat J|X,Y,Z}$, any achievable
$(R_0,R_1,R_2)$ satisfies (31a)–(31g) for some
$p(w_a,v_a,u_a|x)\,p(w_b,v_b,u_b|x)\,p(x)$ — no coupling constraints. At
$R_0=0$ the binding constraints are
$R_1 \le I(U_b,W_b;J)+I(U_a,W_a;Y|J)$;
$R_1 \le I(W_b;Z|\hat J)+I(W_a,J;\hat J)+I(U_b;J|W_b,\hat J)+I(U_a;Y|W_a,J)$;
$R_2 \le I(W_b,\hat J;J)+I(W_a;Y|J)+I(V_b;Z|W_b,\hat J)+I(V_a;\hat J|W_a,J)$;
$R_2 \le I(V_a,W_a;\hat J)+I(V_b,W_b;Z|\hat J)$; and two sum-rate constraints
(31f), (31g), each $\min\{I(W_b,\hat J;J)+I(W_a;Y|J),\ I(W_b;Z|\hat J)+
I(W_a,J;\hat J)\}$ plus private-information terms plus a two-way min (full
expressions in the code docstring). Cardinality caps: $|W_a|,|W_b|\le 9$,
$|U_b|,|V_a|\le 4$, $|U_a|,|V_b|\le 3$.

**What was computed.** For each *fixed* auxiliary channel $T$, the sum-rate
value $B(T) = \max_p \min\{\ldots\}$ of the corresponding outer-bound region
is a valid upper bound on the private-message sum capacity, and so is
$\min_T B(T)$ over any family. The max is over softmax-parametrized
distributions via adaptive Nelder–Mead multistart (Theorem 7 additionally
uses diagonal and UV-warm-start initializations and a quadratic/hinge penalty
schedule $\mu = 300, 3000, 30000$ for (19)–(20), with final residuals
reported).

**Documented deviations from the theorems as stated** (each preserves the
validity of the quantity being estimated; the estimate direction is treated
separately below):

1. $R_0=0$ projection (private messages), sum rate only.
2. Joint coupling fixed as $T(y,z|x)=p(y|x)p(z|x)$: the BSSC is specified by
   marginals, and any consistent coupling yields a valid bound because the
   capacity region depends only on the marginal channels.
3. Theorem 8: $T_{J,\hat J|X,Y,Z}$ restricted to $J-(X,Y)$, $\hat J-(X,Z)$
   conditionally independent. Each member is a legitimate $T_{J,\hat J|X,Y,Z}$,
   so each $B_8(T)$ is valid; only the min over $T$ is explored partially.
4. Theorem 7 evaluated at fixed $T_J$, i.e. using the weaker implication
   "achievable $\Rightarrow \exists p(x),$ aux feasible at this $T_J$",
   discarding the theorem's stronger quantifier order
   ($\exists p(x)\ \forall T_J$). Also: by inspection of (18)–(20), every
   mutual-information term involves $J$ only jointly with $X$ and the
   auxiliaries (never with $Y$ or $Z$), and aux $- X - (Y,Z,J)$ is Markov, so
   the evaluation depends on $T_{J|X,Y,Z}$ only through
   $q(j|x)=\sum_{y,z}T(y,z|x)T_J(j|x,y,z)$; every channel $q(j|x)$ is
   realizable (take $T_J := q$). We therefore sweep channels $q(j|x)$.
5. Theorem 7's (19a–c), (20c) equalities and (20a–b) inequalities enforced by
   penalties; residual slack *enlarges* the feasible set, i.e. errs on the
   safe (over-estimating) side for an outer bound. Final residuals $\le
   10^{-6}$ for all values quoted in Claim 3.
6. Auxiliary cardinalities run at 2 (and 3 in spot checks by the prior
   attempt's UV runs) instead of the theorem caps; this can only
   *under*-estimate $B(T)$.

**Direction of error (central caveat).** $B(T)$ is a max over auxiliaries; a
numerical optimum is a certified *lower* estimate of $B(T)$. The valid outer
bound is the true $B(T)$, so an under-optimized or cardinality-truncated
value is *not* a safe capacity bound, and every "$B(T)$ equals $v$" claim is
tagged [heuristic] with restart-concentration evidence. Two built-in guards
on the unsafe direction: (i) any estimate below Marton's achievable
$0.3616428$ proves under-optimization and is auto-flagged (this triggered on
three low-effort Theorem 7 runs, two of which were cured by re-runs — see
Dead ends); (ii) the UV-reduction anchors must reproduce $0.3725562$, and do.

## Claims

1. **[proved]** (reduction identity; stated in the paper, verified here)
   Theorem 8 with $(J,\hat J)=(Y,\mathrm{const})$ reduces exactly, constraint
   by constraint, to the UV outer bound (Gohari–Nair Remark 17(2)): (31b),
   (31c) become the UV $R_1$ constraints, (31d), (31e) the $R_2$ constraints,
   (31f) the UV sum-rate constraint, and (31g) is implied. Our implementation
   passes a 200-random-distribution unit test of this reduction against
   independently coded UV expressions ($10^{-9}$ agreement).

2. **[proved]** For every auxiliary channel $T_J$, the Theorem 7 region is
   contained in the UV region (its constraint set includes (18b), (18e),
   (18i), which are the UV constraints — the paper's Remark 12), so
   $B_7(T_J)\le$ (UV sum rate) always; Theorem 7 can only improve on UV,
   never lose.

3. **[heuristic]** (found optima as estimates of the true $B(T)$; restart
   concentrations in Details) On the BSSC at the cardinalities tried, the
   Gohari–Nair bounds do **not** improve on the UV sum rate for any scanned
   auxiliary-receiver channel: all five usable Theorem 7 estimates —
   $J=\mathrm{const}$, $J=X$, $J=\mathrm{BSC}(X,.3)$, $J=$ Z-channel$(X,.25)$,
   $J=$ Z-channel-mirror$(.25)$ — equal $0.3725562$ (to $\le 7\times 10^{-7}$, feasibility residuals $\le
   7\times 10^{-7}$), i.e. the extra constraints (18c)–(18h), (19), (20) do
   not bind at the UV optimum for these $T_J$; and all seven nontrivial
   Theorem 8 configurations are strictly looser ($0.50$ to $1.00$ bits).

4. **[heuristic]** (conclusion, inheriting Claim 3's caveats) The evaluated
   Gohari–Nair bounds close **none** of the $0.0109$-bit BSSC sum-rate window:
   it remains $[0.3616428,\ 0.3725562]$. Within the scanned families the
   binding sum-rate value of both new bounds coincides with the UV value.

5. **[proved]** (small structural lemma, explains the observed hardness at
   informative $J$) For Theorem 7 with $J=X$: constraint (20a) forces
   $H(X\mid Z,\tilde U,\tilde W)=0$ *and* $I(\tilde V;Z|\tilde W) =
   I(\tilde V;X|\tilde W)$. Proof: the middle quantity of (20a) is
   $I(X;Z|\tilde U,\tilde W)-H(X|\tilde U,\tilde W) = -H(X|Z,\tilde U,\tilde
   W) \le 0$, so the left inequality forces it to zero; the right inequality
   then requires $I(\tilde V;Z|\tilde W)-I(\tilde V;X|\tilde W)\ge 0$, which
   by data processing ($\tilde V - (X,\tilde W) - Z$) is also $\le 0$.
   Symmetrically, (20b) at $J=X$ forces $H(X\mid Y,\hat V,\hat W)=0$ and
   $I(\hat U;Y|\hat W)=I(\hat U;X|\hat W)$. So informative auxiliary
   receivers put the feasible set on a thin manifold — consistent with the
   optimizer needing warm starts there, and a caution for future evaluations.

## Details

Code: `attempts/broadcast-channel/code/gohari_nair_thm8_bssc.py` and
`gohari_nair_thm7_bssc.py` (numpy/scipy). Each file documents its exact
constraint expressions in the docstring, carries unit tests (`test` mode),
and reproduces the tables below (`scan` mode; seeds fixed).

Theorem 8, dims $|W_a|=|W_b|=2$, $|U_\ast|=|V_\ast|=2$, 30 restarts
(Nelder–Mead, maxiter 12000), concentration = restarts within $10^{-5}$ of
the best:

| config $(J;\hat J)$ | $\hat B_8$ (bits) | concentration |
|---|---|---|
| $Y;\mathrm{const}$ (UV anchor) | 0.3725562 | 3/30 |
| $\mathrm{const};Z$ (mirror anchor) | 0.3725562 | 4/30 |
| $Y;Z$ | 0.5000000 | 30/30 |
| $\mathrm{const};\mathrm{const}$ | 0.6225562 | 27/30 |
| $X;\mathrm{const}$ / $\mathrm{const};X$ / $X;X$ / $Y;X$ / $X;Z$ | 1.0000000 | 26–30/30 |

Theorem 7, dims $|W|$-type $=2$, $|U|/|V|$-type $=2$ (all three families),
penalty schedule as above, 12–18 restarts of which half diagonal/UV-warm
started, top-5 chained to $\mu=30000$; "maxviol" = largest constraint
residual (bits) at the reported optimum:

| $q(j|x)$ | $\hat B_7$ (bits) | maxviol | concentration |
|---|---|---|---|
| $J=\mathrm{const}$ | 0.3725562 | $4\times10^{-10}$ | 3/5 finals |
| $J=X$ | 0.3725561 | $8\times10^{-8}$ | 4/5 finals |
| $J=\mathrm{BSC}(X,.3)$ | 0.3725562 | $1\times10^{-9}$ | 3/5 finals |
| $J=$ Z-ch$(X,.25)$ | 0.3725555 | $7\times10^{-7}$ | 4/5 finals |
| $J=\mathrm{BSC}(X,.1)$ | below Marton floor | — | under-optimized, unusable |
| $J=$ Z-ch-mirror$(.25)$ (18-restart rerun) | 0.3725555 | $8\times10^{-7}$ | 4/5 finals |

(A first J=X run with a different seed also landed below the floor,
0.3411; the tabled 0.3725561 run supersedes it — the floor flag worked as
designed.)

Interpretation of Theorem 8's looseness at nontrivial $T$: giving a genie
$J$ to a receiver without the compensating reduction structure of the anchor
configurations weakens the bound on this channel — e.g. $J=\hat J=X$ yields
constraints dominated by $H(X)=1$ bit. Improvement over UV, if achievable at
all for the BSSC via Theorem 8, must come from output-noise genies
($\mathrm{BSC}(Y,\delta)$-type, erasures) or joint $T_{J,\hat J}$ couplings,
which our scan did not complete (Dead ends).

## Verification

- Unit tests (both `test` modes pass): (i) Theorem 8 at
  $(Y,\mathrm{const})$ equals independently coded UV expressions on 200
  random distributions to $10^{-9}$; (ii) Theorem 7's (18i) equals the
  independently coded UV sum-rate expression on 100 random distributions to
  $10^{-9}$; (iii) the diagonal identification $(\tilde W,\tilde U,\tilde V)
  =(\hat W,\hat U,\hat V)=(W,U,V)$ zeroes the (19) residuals identically on
  random distributions (structural property of the Csiszár-sum-type
  constraints; checks the (19) wiring).
- Anchors: both UV-reduction configurations reproduce the prior attempt's UV
  value $0.3725562$ to $10^{-7}$, computed here through the full Theorem 8
  machinery (16 mutual-information terms), which exercises a code path
  entirely different from the prior attempt's three-term UV evaluation.
- Floor check: every tabled value is $\ge 0.3616428$; runs that fell below
  were flagged unusable and excluded (listed above), never silently dropped.

## Dead ends

- **Theorem 8 output-noise genies not completed.** The scan configurations
  $J=\mathrm{BSC}(Y,\delta),\hat J=\mathrm{BSC}(Z,\delta)$
  ($\delta\in\{.1,.25\}$) and output/input erasure genies were queued but the
  scan was truncated for compute budget after the 9 configurations tabled
  above. These are the remaining untested Theorem 8 candidates for a dip
  below UV on the BSSC.
- **Theorem 7 at $J=\mathrm{BSC}(X,.1)$:** multistarts (12 restarts; an
  18-restart rerun was still executing at write-up) failed to reach the
  Marton floor (Z-ch-mirror$(.25)$ initially failed the same way and was
  cured by an 18-restart rerun, landing at UV like every other usable
  config) — the penalized landscape near informative $J$ is thin (Claim 5
  explains why); estimates from these configs are unusable. Given every
  usable neighbor config sits exactly at UV, we expect these do too, but
  that is unverified.
- **Cardinality caps not reached.** All runs used auxiliary alphabets of
  size 2 versus the theorems' caps (8–9 for $W$-type, 3–4 for $U/V$-type).
  For a *max*-form bound this truncation can only lower the estimate, so it
  cannot manufacture the observed "no improvement" conclusion — but a
  higher-cardinality run could in principle reveal that the true $B(T)$
  exceeds UV even at the anchors' neighbors, or (for Theorem 7) that the
  (19)/(20)-feasible set at larger alphabets still pins $B_7$ at UV. The
  Theorem 7 triple-family optimization at cap cardinalities is a
  ~450-parameter constrained problem; Nelder–Mead is the wrong tool
  (an alternating/EM scheme as in Dou et al. 2024 is the right next step).
- **Full quantifier strength of Theorem 7 unimplemented.** The theorem gives
  $\exists p(x)\ \forall T_J$: one may *intersect* over $T_J$ at a common
  $p(x)$, i.e. $\max_{p(x)} \min_{q(j|x)} \max_{\text{aux}}$, which is
  strictly stronger than our per-$T_J$ evaluation ($\min_{T_J} \max_{p,
  \text{aux}}$). Since $p(x)$ is one-dimensional here, a grid over $p(x)$
  with an inner min-max is feasible in principle but was out of budget; this
  is the most promising untried lever, because the per-$T_J$ evaluation
  found the extra constraints slack at the UV optimum for *each* $T_J$
  separately, while the strong form requires a single $p(x)$ to survive all
  $T_J$ simultaneously.
- **Corollary 4 (bijective output splits) trivializes on the BSSC**: binary
  outputs admit only trivial splits $(Y_1,Y_2)=(Y,\mathrm{const})$ etc., which
  reduce to the UV bound — the product-channel mechanism that powers the
  paper's Theorem 8 improvement example is structurally unavailable here.
- **Corollary 3 applies but aims at corner points.** BSSC satisfies its
  hypothesis with $\hat Y = X$ (for the Z-channel, $I(X;Y|U)=0$ forces
  $H(X|U)=0$ since the two channel rows differ), giving a bound on $R_2$ at
  $R_1=C_1=\log_2 5-2$ — a different part of the region than the sum rate;
  evaluating it is a natural separate attempt.
- Early low-effort runs (6–10 restarts) frequently landed below the Marton
  floor; diagonal and UV-warm-start initializations were necessary for
  Theorem 7. Plain random multistart is not adequate for the penalized
  triple-family problem.

## References

- A. Gohari and C. Nair, "Outer bounds for multiuser settings: the auxiliary
  receiver approach," IEEE Trans. Inf. Theory 68(2):701–736, 2022. Final PDF:
  `chandra.ie.cuhk.edu.hk/pub/papers/NIT/Auxiliary-Receiver.pdf` (no arXiv
  version found).
- Prior attempt consulted: `2026-07-18-claude-fable-5-bssc-bounds.md`
  (Marton $0.3616428$ reproduction; UV $0.3725562$ evaluation; flags this
  task).
- C. Nair and A. El Gamal, "An outer bound to the capacity region of the
  broadcast channel," IEEE Trans. Inf. Theory, 2007.
- Y. Geng, A. Gohari, C. Nair, Y. Yu, "On Marton's inner bound and its
  optimality for classes of product broadcast channels," IEEE Trans. Inf.
  Theory 60(1):22–41, 2014 ([GGNY14] in the paper).
- Y. Dou et al., "Blahut–Arimoto algorithms for inner and outer bounds on
  capacity regions of broadcast channels," Entropy 26(3):178, 2024
  (alternating-maximization approach recommended above).
