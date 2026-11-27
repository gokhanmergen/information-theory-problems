---
problem: two-way-channel-capacity
date: 2026-11-26
attempter: claude
model: claude-opus-5-5
type: numerical-evidence
status: unverified
---

## Summary

*Formal audit:* I found no catalog error. `twcKLetterInnerBound` is a closed, convex,
time-shared inner bound. The empty-alphabet corner cases agree on both sides, and every
channel with C = G₁ satisfies the Statement with k = 1. The Markdown, however, had three
inaccuracies, now fixed:
- it claimed G₁ ⊆ G₂ ⊆ ⋯, which is not justified; only G_k ⊆ G_{mk} is;
- it described Schalkwijk's 0.61914 as a "k = 2" rate;
- it attributed a Q-graph TWC result to "Sabag–Permuter–Kashyap".

*Numerics:* I computed the equal-rate point of Shannon's G_k for Blackwell's BMC exactly
reduced to strategy trees (2, 6, 42, 1806 strategies per user for k = 1..4):

| k | sym(G_k) |
|---|---|
| 1 | 0.6169486 |
| 2 | 0.6169486 (no gain) |
| 3 | **0.6196448** |
| 4 | ≥ 0.6190195 (search inconclusive) |

Two-letter strategies give no gain at the equal-rate point. The reduction to a 4-variable
inequality is proved and the inequality is checked numerically. Three-letter strategies beat
both Shannon's inner bound and Schalkwijk's 1982 rate 0.61914. G₁ ⊊ G₃ is certified with
interval arithmetic.

## Approach

1. Line-by-line audit of `TwoWayChannelCapacity.lean` against `Core/Channels.lean`:
   `TwoWayChannel`, `IsTWCAchievable`, `twcCapacityRegion`.
2. For the BMC, Y^k is a deterministic function of (S₁,S₂), so I(S₁;Y^k|S₂) = H(Y^k|S₂).
   Time sharing plus swapping the two users turns the equal-rate point into a biconcave
   maximisation. I solve it by alternating Blahut–Arimoto with a linear cost term and many
   restarts.
3. Exact certificates where the margins allow: rational distributions evaluated with mpmath
   interval arithmetic, and an interval grid for the 2-variable G₁ problem.

## Claims

1. **[proved]** *Corner cases.* If kX₁ = 0 or kX₂ = 0, then `twcCapacityRegion W = ∅ =
   twcKLetterInnerBound k W` for every k ≥ 1. If both kXᵢ ≥ 1, a `TwoWayChannel` exists only
   when kY₁, kY₂ ≥ 1. So the empty cases cannot falsify the Statement.
2. **[sketch]** *G_k is well formed.* The pre-closure set in `twcKLetterInnerBound` is convex
   (time sharing over `Fin kQ`) and compact (Carathéodory: kQ ≤ 3 suffices), so the
   `closure` is harmless. G_k ⊆ `twcCapacityRegion W` by Shannon's super-letter random-coding
   argument, with zero-padding for n ∉ kℕ. G_k ⊆ G_{mk} by concatenating m independent copies.
   C = closure ⋃_k G_k (Shannon 1961). *The Markdown's chain G₁ ⊆ G₂ ⊆ G₃ ⊆ ⋯ is not
   justified by these arguments*, because a (k+1)-strategy cannot simply embed a k-strategy
   without diluting the rate. The safe statement is nesting along multiples, G_k ⊆ G_{mk}.
3. **[proved]** *No catalog error.* For every W with C(W) = G₁(W) the Statement holds with
   k = 1. The rest of this item is a literature statement, not a proof. Examples are channels satisfying the symmetry conditions of Shannon (1961) or of
   Weng–Song–Alajaji–Linder (2019), such as additive modulo-q noise TWCs. No channel is known
   to violate the Statement (the BMC is the standing candidate). So it is neither trivially
   true nor trivially false.
4. **[proved]** *Exact BMC reduction.* For the BMC,
   sym(G_k) = max_{p₁,p₂} [H(Y^k|S₂) + H(Y^k|S₁)]/(2k).
   Strategies may be replaced by reduced trees without changing either term: values on output
   histories inconsistent with one's own past inputs are irrelevant, because sending 0 forces
   Y = 0. There are N(k) = N(k−1) + N(k−1)² of them: 2, 6, 42, 1806, 3 263 442.
5. **[proved]** sym(G₁(BMC)) ≤ 0.617168 (computer-assisted interval grid).
   The classical value is max_x x·h(x) = 0.6169486 (Shannon 1961), reproduced numerically.
6. **[proved]** *k = 2 reduction.* H(Y²|S₂) + H(Y²|S₁) depends only on 8 marginal parameters,
   through the closed form F in Details §6. Moreover F ≤ Φ(a,b,γ₁,γ₂), an explicit
   4-variable majorant.
   **[heuristic, numerical]** max Φ = 4g* with g* = max_x x h(x): a 61⁴ grid plus 3000
   multistarts give 2.4677945737 = 4g*. Together these give **sym(G₂(BMC)) = sym(G₁(BMC))**.
   Multistart maximisation of F directly gives the same value. A support-function comparison
   in all directions λ indicates that the whole region G₂ equals G₁ (`code/bmc_g2_region_check.py`, log `code/g2_region_check.log`: over 21 directions λ ∈ {0, 0.05, …, 1}, s₂(λ) − s₁(λ) ∈ [−7.4·10⁻¹¹, 0], i.e. equal to optimiser precision).
7. **[proved]** *k = 3.* An explicit rational product distribution on reduced 3-strategies
   (denominator 10⁹) puts (R,R) in G₃ with R ∈ [0.61964480919175563, 0.61964480919175564] (mpmath interval arithmetic). Hence
   **G₁(BMC) ⊊ G₃(BMC)**. Also R > 0.61914, Schalkwijk's 1982 rate, so a fixed three-letter
   Shannon strategy already beats Schalkwijk's 1982 scheme at the equal-rate point. Numerically
   sym(G₃) = 0.6196448092: two seeds with 200 and 1500 restarts converge to the same value.
8. **[heuristic, numerical]** *k = 4.* The best value found is 0.6190195 < sym(G₃). It is reached by
   ascent from a perturbation of "k = 3 optimum + one i.i.d. letter" (value 0.6189708) and is a
   fixed point of the alternating BA map. It is a lower bound from explicit distributions. The
   1806 × 1806 biconcave search (about 30 starts) is far from exhaustive, so I make **no** claim
   about sym(G₄) vs sym(G₃). If
   sym(G₄) < sym(G₃) held, the chain G_k ⊆ G_{k+1} would fail. sym(G₄) ≥ sym(G₂) holds because
   G₂ ⊆ G₄.
9. **[heuristic]** *What this says about the finite-k question.* For the BMC, capacity at
   horizon k would need sym(G_k) ≥ 0.63072 (best known achievable rate). The data are
   sym(G₁) = sym(G₂) = 0.61695 < sym(G₃) = 0.61964, about 0.011 below 0.63072. This is
   consistent with "no finite k suffices", the natural reading of Schalkwijk's 1983
   bootstrapping, which needs unbounded recursion depth. It is **not** evidence of strict
   monotonicity: the plateau at k = 1, 2 shows that sym(G_k) need not increase at every step.
   If Claim 6's numerically checked inequality holds, then "G_k = G_{k+1}" cannot serve as a
   stopping criterion certifying capacity, since sym(G₂) = sym(G₁) < C_sym. Numerically, the
   region G₂ itself equals G₁.

## Details

### 1. Corner cases
If kX₁ = 0, every `IsTWCAchievable` instance with n ≥ 1 needs
`enc₁ : ∀ i : Fin n, Fin M₁ → (Fin i → Y₁) → Fin 0`. That type is empty, because M₁ ≥ 1 and
`Fin 0 → Y₁` is inhabited. So nothing is achievable and the region is `closure ∅ = ∅`. On the
other side, `CausalStrat k (Fin 0) Y₁` is empty for k ≥ 1, there is no `ProbDist` on an empty
type, and kQ = 0 is impossible for `Pq`. So the set is empty too. If kX₁, kX₂ ≥ 1, then
`sum_one` forces kY₁·kY₂ ≥ 1. (The capacity region being ∅ rather than {(0,0)} for an empty
input alphabet is a harmless artifact of the definition.)

### 2. Convexity, compactness and nesting
Fix k. Each (Pq, Ps₁, Ps₂) yields the pair (I₁/k, I₂/k) with Iᵢ = Σ_q Pq(q)·Iᵢ(q). The set of
such pairs is the convex hull of the single-q pairs. It is the image of a compact set, and by
Carathéodory in ℝ² it suffices to take kQ ≤ 3. The down-closure of a compact convex subset of
the orthant is compact and convex. Nesting G_k ⊆ G_{mk}: let S'ᵢ be m independent copies of
Sᵢ played on consecutive blocks. Then I(S'₁;Y'^{mk}|S'₂,Q) = m·I(S₁;Y^k|S₂,Q), by
independence across blocks and the memoryless channel. Inclusion in C and the limit
characterisation are Shannon's (1961). The Lean achievability (codes for all n ≥ N, average
error over message pairs) matches the standard notion.

### 3. Exact BMC reduction (Claim 4)
Y^k = f(S₁,S₂), hence I(S₁;Y^k|S₂) = H(Y^k|S₂) − H(Y^k|S₁,S₂) = H(Y^k|S₂). The symmetrised
pair {(p₁,p₂), (p₂,p₁)}, with Q uniform on {0,1}, achieves both rates equal to
[H(Y^k|S₂) + H(Y^k|S₁)]/(2k). No time-shared point does better, since min ≤ average and the
average is linear in Pq. Reduced trees: after sending 0 at step j the output is 0 whatever the
other user did, so only one continuation is reachable. The outcome table of reduced trees
determines both terms exactly. `bmc_gk.py` also merges identical rows and columns, which
removes nothing for k ≤ 4.

### 4. Optimisation method
For fixed p₂, H(Y^k|S₂) = I(S₁;(Y^k,S₂)) for the DMC s₁ ↦ (y,s₂) with law p₂(s₂)[y = f(s₁,s₂)].
The other term, H(Y^k|S₁) = Σ p₁(s₁)·c(s₁), is linear. Each half-step is thus a Blahut–Arimoto
step with a cost term, p₁ ← p₁·2^{D+c}/Z, which ascends monotonically. The two users alternate
(3 + 3 steps per sweep). The objective is biconcave, not concave, so restarts are needed.
All reported values are exactly re-evaluated at the returned distributions.

### 5. Results

| k | strategies/user | restarts × sweeps | sym(G_k) found | command |
|---|---|---|---|---|
| 1 | 2 | 200 × 300 | 0.6169486434 | `bmc_gk.py 1 200 300 1` |
| 2 | 6 | 200 × 300 | 0.6169486434 (every restart) | `bmc_gk.py 2 200 300 1` |
| 3 | 42 | 200 × 300; 1500 × 300 | 0.6196448092 (both) | `bmc_gk.py 3 200 300 1`; `bmc_gk.py 3 1500 300 2` |
| 4 | 1806 | 3 structured + 20 random × 60; 3 averaged-lift × 200 (stopped before polish); 2 ε-lift × 250 + 1000 polish; +1000 continuation (stopped; flat) | 0.6190195 | `bmc_g4_search.py 60 20 4`; `bmc_g4_search.py 200 0 5 mixonly`; `bmc_g4_search.py 250 0 6 epsonly`; `bmc_g4_continue.py bmc_gk_k4_seed6.npz bmc_gk_k4_seed6_cont.npz 2000 250` |

The k = 3 optimiser is symmetric (R₁ = R₂ without time sharing) and uses 21 and 19 of the 42
reduced strategies. At k = 4 the natural start "k = 3 optimum + one fresh letter" has value
(3·sym(G₃) + g*)/4 = 0.6189708, and plain BA cannot leave it because zero weights stay zero.
After a 1% perturbation towards the i.i.d. strategy, 250 sweeps return to 0.6189706. The
1000-sweep polish then reaches 0.6190195 (log seed 6), and the continuation run reaches
0.6190195 (unchanged to 13 digits over a further 1000 sweeps, i.e. a fixed point of the alternating BA map; that run was stopped there). Random and averaged starts stay lower (0.6169–0.6180). I cannot tell
whether the search is under-explored or whether in fact sym(G₄) < sym(G₃). The latter would
mean G₃ ⊄ G₄, so the k ↦ G_k chain is not monotone. This is an attractive open numerical
question. Note that G₁, G₂ ⊆ G₄ by nesting, but nothing proved here implies G₃ ⊆ G₄.

### 6. The k = 2 closed form and majorant (Claim 6)
A reduced 2-strategy of user 1 is either "send 0, then g" or "send 1, then f_{Y₁}". Only the
following marginals enter: a = P(A=1), γ₁ = P(g=1 | A=0), φ₀ = P(f₀=1 | A=1),
φ₁ = P(f₁=1 | A=1). User 2 has (b, γ₂, φ₀', φ₁') likewise. Enumerating the cases of the
opponent's strategy gives

F = b h(a) + a h(b) + (1−b)γ₂ h(c) + a(1−b)φ₀ h(γ₂) + (1−a)γ₁ h(c') + b(1−a)φ₀' h(γ₁)
    + ab[φ₁' h(φ₁) + φ₁ h(φ₁')],    c = (1−a)γ₁ + aφ₀,  c' = (1−b)γ₂ + bφ₀'.

The closed form agrees with the brute-force strategy computation to 9·10⁻¹⁶ at 1000 random
points. Two bounds follow:

- The last bracket is ≤ M := max_{x,y}[y h(x) + x h(y)] = 2·sym(G₁).
- For fixed γ₂, write aφ₀ = c − (1−a)γ₁ and relax c to [0,1]. Then
  (1−b)[γ₂ h(c) + aφ₀ h(γ₂)] ≤ (1−b)[ψ(γ₂) − (1−a)γ₁ h(γ₂)], where
  ψ(γ) = max_c[γ h(c) + c h(γ)] is attained at c = 1/(1 + 2^{−h(γ)/γ}).
  The same holds with the roles of the users swapped.

Hence F ≤ Φ := b h(a) + a h(b) + M·ab + (1−b)ψ(γ₂) + (1−a)ψ(γ₁) − (1−a)(1−b)[γ₁h(γ₂) + γ₂h(γ₁)].
Equality holds at the i.i.d. point a = b = γ = φ = x* = 0.70351, where F = 4g*. The script
sets M = 2g*, the classical value of 2·sym(G₁). Rigorously only M ≤ 2 × 0.617168 is certified
here (Claim 5).
`bmc_g2_closed_form.py` checks: (1) closed form vs brute force; (2) multistart max F = 4g*
(diff −3·10⁻¹³); (3) 61⁴ grid max Φ = 2.46770 (at the grid point nearest x*) and multistart
max Φ = 4g* to 4·10⁻¹⁶. Making (3) rigorous needs an interval branch-and-bound with a
centred-form (gradient) bound near the interior maximiser. Plain interval boxes would need
about 10⁹ cells to resolve the ~0.009 margin to 4×0.61914. I did not do this.

### 7. Certificate for G₁ ⊊ G₃ (Claims 5, 7)
`certify_g3_gt_g1.py`:
- Part A rounds the seed-2 k = 3 optimiser to denominator 10⁹ and evaluates both
  conditional entropies with `mpmath.iv` (50 digits).
- Part B bounds max (y h(x) + x h(y))/2 on a 4000² cell grid. Per cell it uses
  y₁·max h + x₁·max h, with h evaluated in interval arithmetic and upper endpoints rounded
  outward.

Output: Part A: R₁ = H(Y³|S₂)/3 ∈ [0.6196448093485665894, 0.6196448093485665895], R₂ = H(Y³|S₁)/3 ∈ [0.6196448090349446810, 0.6196448090349446811], time-shared symmetric rate ∈ [0.61964480919175563523, 0.61964480919175563524]. Part B: sym(G₁) ≤ 0.617168. Margin 0.002477 > 0, so G₁ ⊊ G₃. Runtime < 1 s.

## Verification

All runs use `/…/.venv/bin/python` (numpy, scipy, mpmath) under `nice`, single process.
Run every script from inside `code/`: they import the sibling module `bmc_gk` and load the
saved `.npz` distributions by relative path. The coordinator re-ran `certify_g3_gt_g1.py` on
2026-11-26 and reproduced the output above exactly.
Seeds and parameters are in the table of §5 and in each script's docstring. The k = 4 logs are
`code/g4_run_seed4.log`, `code/g4_run_seed5.log`, `code/g4_run_seed6.log` and
`code/g4_continue_seed6.log`. The optimisers return explicit
distributions, saved as `code/bmc_gk_k{1,2,3}_seed*.npz` and `code/bmc_gk_k4_best.npz`. The last
file holds p₁ and p₂ only. The 26 MB outcome table is recomputed by
`bmc_gk.outcome_table(bmc_gk.reduced_trees(4), 4)`. The intermediate k = 4 files written by
`bmc_g4_search.py` were deleted for size and are regenerated by rerunning the listed commands. Each value is a *lower* bound on
sym(G_k), exact up to float rounding, and is interval-certified for k = 3. None is certified
to be the global maximum, except k = 1 (Claim 5). For k = 2 the max is proved modulo the
numerically checked inequality Φ ≤ 4g*.

## Dead ends

- *Random restarts at k = 4.* Dirichlet(0.3) starts on the 1806-simplex reach only
  0.6169–0.6172 after 60 sweeps (log seed 4). Averaging the two lifts of the k = 3 optimum
  destroys their structure (start 0.6151, end 0.6180; log seed 5; that run was stopped
  manually before its polish step). Multiplicative BA updates are slow in high dimension and
  cannot revive zero weights. The ε-perturbed lift climbs to 0.6190195 and then sits at a fixed
  point of the alternating map, still below sym(G₃). A proper k = 4 study needs a second-order or interior-point method on the
  biconcave problem, or a symmetry reduction of the 1806 strategies.
- *Rigorous sym(G₂) bound by plain interval boxes.* As described in §6, the interior
  maximiser with a ≈0.009 margin makes naive 4-D boxes infeasible (≈10⁹ cells). A
  centred-form or Hessian-certified local concavity argument is needed.
- *Analytic proof of Φ ≤ 4g*.* Bounding ψ ≤ M termwise overshoots by
  2g*(1−a)(1−b). The negative cross term is what makes the inequality tight, and I did not
  find a clean way to exploit it.

## Novelty check

I searched (Nov 2026) for "Shannon strategies"/"G_k" computations for the BMC: Bloemen 1996
thesis (§2.7–2.8 counts strategies and studies fixed-length codes but, as far as I read, does
not report sym(G₂), sym(G₃)); Kim 2012 slides; Sabag–Permuter 2018; Weng et al. 2019/2020;
general web searches on "two-way channel k-letter strategy binary multiplying". I did not find
the values sym(G₂) = sym(G₁) or sym(G₃) ≈ 0.61964 reported. Meeuwissen's and Bloemen's TU/e
theses may contain related fixed-length strategy computations that I could not fully read, so
novelty is plausible but not certain.

## References

- C. E. Shannon, "Two-way communication channels," Proc. 4th Berkeley Symp., vol. 1,
  pp. 611–644, 1961.
- J. P. M. Schalkwijk, IEEE Trans. IT 28(1):107–110, 1982; 29(3):445–448, 1983.
- A. H. A. Bloemen, *Discrete Coding Strategies for Two-Way Channels*, PhD thesis, TU
  Eindhoven, 1996, doi:10.6100/IR463500 (§2.5 Schalkwijk 1982 strategy; §2.8 number of
  Shannon strategies; Ch. 6 bounds).
- G. Kramer, *Directed Information for Channels with Feedback*, PhD thesis, ETH Zürich, 1998.
- J.-J. Weng, L. Song, F. Alajaji, T. Linder, "Capacity of two-way channels with symmetry
  properties," IEEE Trans. IT 65(10), pp. 6290ff., Oct. 2019.
- J.-J. Weng, F. Alajaji, T. Linder, "A simple capacity outer bound for two-way channels and
  capacity approximation results," arXiv:2004.03954.
- O. Sabag, H. H. Permuter, "An achievable rate region for the two-way channel with common
  output," Proc. Allerton 2018, pp. 527–531, doi:10.1109/ALLERTON.2018.8635930.
- Y.-H. Kim, "On the role of interaction in network information theory," Banff slides, 2012.
- Companion attempt (same date):
  `attempts/binary-multiplier-two-way-channel/2026-11-26-claude-opus-5-5-db-catalog-error-survey.md`
  (catalog error in the BMC statement; HW parallel-channel bound reproduced).
- Prior attempts in `attempts/two-way-channel-capacity/`: none existed.
