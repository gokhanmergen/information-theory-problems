---
problem: dm-interference-channel-capacity
date: 2026-11-26
attempter: claude
model: claude-opus-5-5
type: new-bound
status: verified
---

## Summary

Three things. (1) A formal audit of the frozen statement `∀ W, ∃ k ≥ 1, icCapacityRegion W =
hanKobayashiKLetterRegion k W`. Both sides are closed and convex, the `k`-letter regions are
nested along divisibility and asymptotically along all `n`, and every degenerate or
known-capacity class we checked is settled at `k = 1` *consistently*. So we found **no catalog
error**: the statement is neither trivially true nor trivially false. (2) Survey corrections,
now fixed in the problem file. Telatar–Tse 2007 was listed as a *capacity* result; it is an
outer bound and gap result. El Gamal–Costa covers only an injective *class* of deterministic
ICs. The outer-bound bullet credited NXY with outer bounds and mixed Gaussian-only bounds
(Kramer 2004, Etkin–Tse–Wang) into the DM list. We also added the Nair–Ng (2019) Gaussian
multi-letter result and a statement that termination of the hierarchy is open.
(3) A computer-assisted, interval-arithmetic re-proof of the Nair–Xia–Yazdanpanah (NXY 2015) strict
gap `R_HK^(1)(W) ⊊ R_HK^(2)(W) ⊆ C(W)` on their binary CZI channel. Their proof relied on an
unstated "tedious exercise". We certify `max_{R_HK^(1)}(2R1+R2) ≤ 1.1080300 < 1.1080356 ≤
max_{R_HK^(2)}(2R1+R2)`. We then found a simple explicit **3-letter** scheme: `X1` a
repetition code, `X2^3` never `000`. It gives `2R1+R2 = 1.1102046` in `HK^(3)`, which widens
the certified separation `HK^(1) ⊊ HK^(3) ⊆ C` about 400-fold, to `2.2·10⁻³` (reviewer: the
400-fold factor comes from stopping the certificate at 1.10803, just below the two-letter value. Against
the reviewer's certified bound `≤ 1.1078`, the margins are `2.4·10⁻³` vs `2.4·10⁻⁴`, about 10-fold). Numerical
`k`-letter TIN values for `k ≤ 6` (1.10752, 1.10814, 1.11020, …) and an elementary
single-letter outer bound (1.2290) bracket `max_C(2R1+R2)`. Whether the hierarchy stabilises
remains open.

## Approach

Since the frozen question is "does the `k`-letter HK hierarchy terminate for every channel?", the
most useful honest contributions are: make sure the Lean statement asks exactly that question
(no closure, convexity or degenerate-case artifact settles it), pin down the literature, and
put the only known non-termination evidence (NXY's `k = 1 → 2` gap) on a fully rigorous
footing. The last step also checks the NXY data against an independent computation.

## Claims

Notation: `HK^(k)(W) := hanKobayashiKLetterRegion k W = cl{ r : k·r ∈ R_HK(W^{⊗k}) }`,
`C(W) := icCapacityRegion W`.

1. **[proved]** `HK^(k)(W)` is closed, convex and downward-closed in `ℝ²_{≥0}`. The capacity
   region `C(W)` is closed (`Core/Sanity.lean: icCapacityRegion_isClosed`).
2. **[proved]** For all `k, m ≥ 1`: `HK^(k)(W) ⊆ HK^(mk)(W)`. More generally, for `n = qk + s`
   with `0 ≤ s < k`, `(qk/n)·HK^(k)(W) ⊆ HK^(n)(W)`. So the hierarchy is not monotone in `k`, but
   this is harmless for the `∃ k` form. If `C = HK^(k)`, then `C = HK^(mk)` for every `m`, and
   `d_H(HK^(n), C) = O(1/n)` along *all* `n`.
3. **[sketch]** `HK^(k)(W) ⊆ C(W)` under the repository's operational definition (HK achievability
   for the super-channel `W^{⊗k}`, padding for `n ∤ k`, closure).
4. **[proved]** `C(W) ⊆ cl ⋃_n HK^(n)(W)`. More precisely, for each achievable `(R1,R2)` and
   `δ > 0`, `((R1−δ)_+, (R2−δ)_+) ∈ HK^(n)(W)` for all large `n`, already with `Q, U1, U2`
   constant. Hence `cl ⋃_k HK^(k) = C`, as the problem file says.
5. **[proved, modulo cited capacity theorems]** No catalog error. Each of the following is settled
   at `k = 1` *in agreement with* the Lean statement: empty input alphabets (both sides `∅`), a
   silent user, interference-free product channels (`Known/Operational.lean:
   icCapacityRegion_icProduct`), strong interference (Costa–El Gamal 1987 region = HK with
   `U_j = X_j`), and the El Gamal–Costa injective-deterministic class. NXY's channel shows that
   `k = 1` is *not* always enough, so the statement is not trivially true either.
6. **[proved]** (Re-proof of NXY Lemma 2.) For the NXY function `f(p,q)` (their eq. (13)),
   `∂²f/∂q² = p(1−3q−2p(1−q)) / (q(1−q)(1+q)(2q+p(1−q)) ln 2)`, and the tangency identity
   `f(p,1−2p) − f(p,0) = (1−2p)·∂_q f(p,1−2p)` holds exactly for `p ∈ (0,1/2)`. Hence the
   NXY closed-form concave envelope is correct.
7. **[proved, computer-assisted]** For the NXY binary CZI channel,
   `max_{(R1,R2) ∈ HK^(1)(W)} (2R1+R2) ≤ 1.1080300`, while the NXY two-letter TIN point gives
   `2R1+R2 = 1.1080356322…` in `HK^(2)(W)`. Hence `HK^(1)(W) ⊊ HK^(2)(W) ⊆ C(W)`, so
   `HK^(1)(W) ≠ C(W)`. The certificate uses interval branch-and-bound with outward rounding;
   code is in `code/certify_hk1_bound.py`. (Reviewer: the bound and `HK^(1) ⊊ HK^(2)` need only
   Claims 2 and 6 plus the computation. The step `HK^(2) ⊆ C`, and with it `HK^(1) ≠ C`, rests on
   Claim 3, which is a `[sketch]`; NXY Prop. 3 asserts the same.)
8. **[proved]** (Elementary outer bound in the NXY direction.) For every CZI channel (`Y2 = X2`),
   `max_C(2R1+R2) ≤ max_{p1⊗p2}[I(X1X2;Y1) + H(X2|Y1,X1) + I(X1;Y1|X2)]`. For the NXY channel
   this is `≈ 1.229039` at `(p,q) ≈ (0.4298, 0.4115)` (numerical maximisation of an explicit
   2-variable function, not interval-certified). The bound is loose: compare `1.1102` below.
9. **[numerical]** For the NXY channel, the `k`-letter TIN values
   `V_k := max (1/k)[2I(X1^k;Y1^k)+H(X2^k)]` found by optimisation are
   `V_1 ≈ 1.1075163` (equal to the numerical `HK^(1)` maximum, since `U2 = const` is optimal
   here, as NXY observed), `V_2 ≥ 1.1081413` (reproduces NXY Table 1's `R_two` value
   `1.108141`), `V_3 ≥ 1.1102045`, `V_4 ≥ 1.1095325`, `V_5 ≥ 1.1093792`, `V_6 ≥ 1.1102045`.
   (Reviewer: the `V_4` and `V_5` figures are the concatenation values `(3V_3+V_1)/4` and
   `(3V_3+2V_2)/5`, not optimiser output. The run log reaches only `1.1095319` and `1.1093789`. Both
   are valid lower bounds, since a Kronecker product of the optima attains the concatenation value.)
   For `k = 4, 5, 6` the optimiser recovered only concatenations of the `k = 3` and
   `k = 1, 2` optima (`(3V_3+V_1)/4`, `(3V_3+2V_2)/5`, `V_3`). Every number is attained by an
   explicit distribution, so it is a valid lower bound. Because `k·V_k` is superadditive,
   `max_C(2R1+R2) = lim V_k = sup V_k ≥ 1.1102`. We have **no** upper bound on `max_{HK^(k)}`
   for `k ≥ 2`, so nothing here shows `HK^(2) ≠ HK^(3)` or non-termination.
10. **[proved, computer-assisted]** The explicit 3-letter TIN scheme `P(X1^3 = 000) = 0.434823`,
   `P(X1^3 = 111) = 0.565177`; `P(X2^3 = w) = 0` for `w = 000`, `0.136205` for each weight-1
   `w`, `0.154298` for each weight-2 `w`, and `0.128491` for `w = 111`. It has, in 40-digit
   arithmetic, `R1 = 0.0878251069`, `R2 = 0.9345543681`, `2R1+R2 = 1.11020458194`. With Claim 7,
   `max_{HK^(1)}(2R1+R2) ≤ 1.1080300 < 1.1102045 ≤ max_{HK^(3)}(2R1+R2)`, so
   `HK^(1)(W) ⊊ HK^(3)(W)` with margin `2.17·10⁻³`, against `5.6·10⁻⁶` for NXY's
   two-letter point (reviewer: the `5.6·10⁻⁶` is an artifact of the 1.10803 stopping target. With
   the reviewer's certified `≤ 1.1078`, the two-letter margin is `2.4·10⁻⁴`). Intuition: `X2 = 0` erases `Y1`, so `X2^3` avoids the all-zero word and
   each block keeps at least one Z-channel use for the repeated `X1` symbol. This is a block
   version of NXY's §2.2 "Markov `X2`" intuition.

## Details

### 1. Closedness, convexity

`HK^(k)` is defined as a `closure`. For convexity, take two feasible tuples `(r, P)` and
`(r', P')` of `R_HK(W^{⊗k})` with time-sharing alphabets `Fin kQ` and `Fin kQ'`. Form
`Q'' ∈ Fin (kQ + kQ')` with law `θ P_Q ⊕ (1−θ) P'_Q`, keeping the conditional laws of
`(U_j, X_j)`. Every one of the 7 right-hand sides is conditioned on `Q`, so each is the
`θ`-mixture of the two values (`a1, …, d2` are all of the form `I(·;·|·,Q)`). The 7 linear
inequalities therefore hold for `θr + (1−θ)r'`. Taking closures preserves convexity.
Downward closedness holds because all constraints are upper bounds on nonnegative coordinates.

### 2. Nesting

Given a feasible `(Q, U1, X1^k, U2, X2^k)` for `W^{⊗k}`, use `q` i.i.d. copies on the first `qk`
letters. Put `Q^q`, `U_j^q` as the new `Q`, `U_j` (finite alphabets `Fin (kQ^q)`, etc.) and send
a fixed input symbol on the last `s` letters (the remainder's `U`'s are constant). The product
law has the required form `p(q)p(u1,x1|q)p(u2,x2|q)`. The remainder outputs are independent of
everything else, so each of `a1, …, d2` for `W^{⊗n}` equals `q` times its value for `W^{⊗k}`.
(For example, `I(X1^n;Y1^n|U2,Q) = Σ_b I(X1^{(b)};Y1^{(b)}|U2^{(b)},Q^{(b)}) + 0`, by
independence of the blocks.) Dividing by `n` gives `(qk/n)·r ∈ HK^(n)`. With `s = 0` this is
nesting. Non-monotonicity in `k` is therefore only the scaling loss `s/n`. In particular, if
`C = HK^(k)` then `(1 − (k−1)/n)·C ⊆ HK^(n) ⊆ C` for all `n ≥ k`.

### 3. Achievability of `HK^(k)`

`W^{⊗k}` is a DM-IC with finite alphabets `X_j^k, Y_j^k`. HK's theorem (El Gamal–Kim Thm 6.4)
gives achievability over `W^{⊗k}` for every point of `R_HK(W^{⊗k})` with strict inequalities.
A length-`n` code for `W` with `n = mk + s` uses the length-`m` code for `W^{⊗k}` and pads with
`s < k` dummy letters. The rate loss `O(1/n)` vanishes, and the repository's definition
(`M = max 1 ⌊2^{nR}⌋`, all `n ≥ N`, closure) absorbs it. This is routine but not written out
here, hence `[sketch]`.

### 4. Converse (multi-letter)

Take an achievable `(R1,R2)` and `ε > 0`, and a code at length `n` with average error `≤ ε`,
`M_j = max(1, ⌊2^{nR_j}⌋)`. Let `X_j^n = enc_j(M_j)` with `M_j` uniform. These are independent
because the messages are. Fano at receiver `j` gives `log M_j ≤ I(X_j^n; Y_j^n) + 1 + ε log M_j`
(receiver `j`'s error probability is at most the joint one). In `R_HK(W^{⊗n})` take
`kQ = kU1 = kU2 = 1`. The seven bounds then become `R1 ≤ I(X1^n;Y1^n)`, `R2 ≤ I(X2^n;Y2^n)` and
sums of these (`a1 = b1 = c1 = d1 = I(X1^n;Y1^n)`, similarly for user 2). So
`(1/n)(((1−ε)log M_1 − 1)_+, ((1−ε)log M_2 − 1)_+) ∈ HK^(n)`. Since `(1/n) log M_j → R_j`,
the claim follows.

### 5. Degenerate and known cases (consistency, no catalog error)

* **Empty alphabets.** If `kX₁ = 0`, then for `n ≥ 1` no `enc₁ : Fin M₁ → Fin n → Fin 0`
  exists, so `C = ∅`. Also `icPower W k` has the empty input type `Fin k → Fin 0`, so
  `ProbDist (Fin kU₁ × (Fin k → Fin 0))` is empty, which forces `kQ = 0`, and then there is no
  `ProbDist (Fin 0)`. So `HK^(k) = ∅` and the equality holds. (`kY_j = 0` with nonempty inputs
  is impossible because `sum_one` fails.)
* **Silent user** (`|X2| = 1`). `R2 = 0` on both sides and `R1 ≤ max I(X1;Y1)` on both sides.
* **No interference** (`W = W1 ⊗ W2`). `HK^(1)` is the rectangle `[0,C1] × [0,C2]`, which equals
  `C` (`icCapacityRegion_icProduct`).
* **Strong interference** (`I(X1;Y1|X2) ≤ I(X1;Y2|X2)` and the symmetric condition for every
  product input). With `U_j = X_j`: `c_j = 0`, `b_1 = I(X1X2;Y1|Q)`, `d_1 = I(X2;Y1|X1,Q)`.
  The 7 constraints reduce to Costa–El Gamal's region: `d1 + d2 ≥ a1 + a2` makes the third sum
  bound redundant, and the two weighted bounds follow from `R1+R2 ≤ b1` with `R1 ≤ a1 ≤ d2`.
  That region *is* the capacity region (Costa–El Gamal 1987), so `C = HK^(1)`.
* **El Gamal–Costa class** (`Y1 = f1(X1,T2)`, `T2 = t2(X2)`, injectivity `H(Y1|X1) = H(T2)` and
  symmetrically). HK with `U_j = T_j` achieves their capacity region, so `k = 1`.
* **NXY channel.** `k = 1` fails (Claim 7). So the statement is not trivially true. The general
  question is open.

### 6. NXY Lemma 2, re-proved

With `p = P(X1=0)` and `q = P(X2=0)`:
`f(p,q) = (2p−1)h(q) − 2p·h((1+q)/2) + h(q + (1−q)p/2) + p(1−q)`. This matches NXY eq. (13),
and we re-derived it from the channel matrix (`code/czi_common.py` checks it against brute
force). Differentiating twice (`h'' (x) = −1/(x(1−x)ln2)`), `ln 2 · q(1−q)(1+q)(2q+p(1−q))·f_qq`
equals
`T(p,q) = −(2p−1)(1+q)(2q+pq̄) + 2pq(2q+pq̄) − (2−p)q(1+q)`.
`T = p(1−3q−2pq̄)` is a polynomial identity of degree `≤ 2` in `p` and `≤ 3` in `q`. It is
verified exactly on a `4 × 5` rational grid (`code/nxy_values.py`), which proves it. So `f(p,·)`
is concave for `p ≥ 1/2`, and for `p < 1/2` it is convex on `(0, q*)` and concave on `(q*, 1)`,
with `q* = (1−2p)/(3−2p) ≤ 1−2p =: q̂`.

*Tangency at `q̂ = 1−2p`.* Write everything in natural logs. At `q̂`: `1−q̂ = 2p`,
`(1+q̂)/2 = 1−p`, `q̂ + (1−q̂)p/2 = (1−p)²`. Expand both sides of
`f(p,q̂) − f(p,0) = q̂·f_q(p,q̂)` (with `f(p,0) = h(p/2) − p`) as combinations of
`ln 2, ln p, ln(1−p), ln(1−2p), ln(2−p)`. The coefficients agree term by term:

| log term | coefficient on both sides |
|---|---|
| `ln 2` | `−2p² + 3p − 1` |
| `ln p` | `p/2 − p²` |
| `ln(1−2p)` | `(1−2p)²` |
| `ln(1−p)` | `2(1−p)(2p−1)` |
| `ln(2−p)` | `p² − 5p/2 + 1` |

So the identity holds exactly. The function `E(p,·)` (the tangent line on `[0,q̂]`, then `f`) is
concave because the line meets the concave branch with equal slope. It majorises `f`: on
`[q*, q̂]` `f` lies below its tangent at `q̂`, and on `[0,q*]` `f` lies below its chord, whose
endpoints are below the line. Any concave majorant must dominate the chord through
`(0,f(p,0))` and `(q̂, f(p,q̂))`. So `E` is the upper concave envelope, which is NXY Lemma 2. For
the upper bound below we only need that `E` is *a* concave majorant, and that the tangent line
`ℓ_p(q) = f(p,0) + q f_q(p,q̂)` majorises `E` for every `q` (it supports the concave `E` at `q̂`).

### 7. The certificate

NXY Prop. 1/Lemma 1 (re-checked): HK constraints (1) and (3) with `Y2 = X2` give
`2R1+R2 ≤ I(X1;Y1|U2,Q) + I(X1,U2;Y1|Q) + H(X2|U2,Q)`. Rewrite with the chain rule as
`I(X1X2;Y1|Q) + Σ_{q,u2} p(q,u2) f(p_{1|q}, p_{2|u2,q})`. This is at most
`E_Q[ g(p_Q, q_Q) + E(p_Q, q_Q) ] ≤ max_{p,q} F(p,q)`, where `g = I(X1X2;Y1) = h(s) − p(1−q)` and
`s = q + (1−q)p/2`. On `{p ≥ 1/2} ∪ {q ≥ 1−2p}`, `F = F_f := 2h(s) + (2p−1)h(q) − 2p h((1+q)/2)`.
For `p ≤ 1/2`, `F ≤ F_l := h(s) − p(1−q) + h(p/2) − p + q·σ(p)` everywhere, where the slope is
written without removable singularities as
`σ(p) = −φ(p)/2 − φ(1−2p) + (p−1) + 2(p−1)log₂(1−p) + (1−p/2)log₂(2−p)` with `φ(x) = −x log₂ x`.
`code/certify_hk1_bound.py` runs best-first branch-and-bound on `[0,1/2]×[0,1] ∪ [1/2,1]×[0,1]`
in `mpmath.iv` (30 digits, outward rounding). `h` and `φ` are enclosed exactly via their
monotone pieces, and `s` via monotonicity in `(p,q)`. It stops when every live box has upper
bound `< 1.10803`.

Run (`python certify_hk1_bound.py 1.10803`, 2026-11-26, about 285 s on a shared machine):

```
slope check p=0.05: -0.114862610854 vs -0.114862610854      (rewritten sigma(p) vs direct f_q)
...
boxes split: 40000, current max UB = 1.10819384..., best point value = 1.107516205
CERTIFIED: max_(p,q) [g+E] <= 1.10802997885819... < TARGET = 1.10803
boxes split: 54945; live boxes: 54947; best point value found = 1.10751627586
```

So `max_{HK^(1)}(2R1+R2) ≤ 1.1080300 < 1.1080356 ≤ max_{HK^(2)}(2R1+R2)`. The certified margin
is thin (`5.6·10⁻⁶`) because we stopped at the first target that clears the two-letter value.
The true one-letter maximum is about `1.1075163` (best point found), and NXY's own, non-rigorous
bound was `1.107577`. A longer run with a lower target would tighten the certificate. This
does not affect validity.

The closure in `hanKobayashiKLetterRegion 1` changes nothing, because a linear functional's
supremum over a set equals its supremum over the closure. The NXY two-letter point
(`P(X1^2 = 00) = p0`, `P(X1^2 = 11) = 1−p0`; `P(X2^2=00) = 0.36q0`,
`P(01) = P(10) = 0.64q0`, `P(11) = 1−1.64q0`, with `p0 = 0.507829413`, `q0 = 0.436538150`) gives,
in 50-digit arithmetic, `R1 = 0.0631931192699`, `R2 = 0.981649393676`,
`2R1+R2 = 1.10803563221622`. This agrees with NXY's `1.1080356`.

### 8. Single-letter outer bound in direction (2,1)

For any code, Fano gives `n(2R1+R2) ≤ 2I(X1^n;Y1^n) + H(X2^n) + nε_n` with `X1^n ⊥ X2^n`. Write
`I(X1^n;Y1^n) + H(X2^n) = I(X1^nX2^n;Y1^n) + H(X2^n|Y1^n,X1^n) ≤ Σ_i [I(X1iX2i;Y1i) +
H(X2i|Y1i,X1i)]` (memoryless channel, subadditivity, and conditioning reduces entropy). Also
`I(X1^n;Y1^n) ≤ I(X1^n;Y1^n|X2^n) = Σ_i I(X1i;Y1i|X2i)`, by independence and memorylessness.
Each `(X1i,X2i)` is a product pair. So `max_C(2R1+R2) ≤ max_{p,q} φ(p,q)` with
`φ = I(X1X2;Y1) + H(X2|Y1X1) + I(X1;Y1|X2)`. For the NXY channel the maximum is `≈ 1.229039`
(`code/tin_hierarchy.py`, grid + Nelder–Mead on a smooth 2-variable function, which is not
interval-certified). The value is `≈ 1.229039`, far above the achievable `1.1102`. It brackets
`max_C(2R1+R2) ∈ [1.1102, 1.2291]` but says nothing about finite `k`.

### 9. `k`-letter TIN values

`code/tin_hierarchy.py` (run `python tin_hierarchy.py 6 30`, log `code/tin_hierarchy_run.log`)
uses L-BFGS on softmax parameters with structured starts: product of the single-letter optimum,
repetition code, NXY's two-letter structure, and Kronecker products of optima for divisors of
`k`, plus 30 random starts. It then polishes with exact Blahut–Arimoto steps in `p(x1^k)`,
accepted only if they improve the objective.

```
single-letter outer bound on max_C(2R1+R2): 1.229039 at (p,q)=[0.4298 0.4115]
k=1: V_k >= 1.1075163   (R1=0.059582, R2=0.988351)
k=2: V_k >= 1.1081413   (R1=0.064029, R2=0.980083)
k=3: V_k >= 1.1102045   (R1=0.087824, R2=0.934556)
k=4: V_k >= 1.1095319   (R1=0.080762, R2=0.948007)
k=5: V_k >= 1.1093789   (R1=0.078305, R2=0.952769)
k=6: V_k >= 1.1102045   (R1=0.087824, R2=0.934556)
```

The `k = 3` optimiser has exactly the structure of Claim 10: repetition on `X1`, no `000` for
`X2`, and weights depending only on Hamming weight. `code/tin_k3_exact.py` optimises that
3-parameter family, rounds the parameters to 6 decimals and re-evaluates in 40-digit `mpmath`,
giving `2R1+R2 = 1.11020458193989`. A rounded distribution is still a distribution, so this is
a rigorous lower bound.

## Verification

* The closed forms `f`, `g` were checked against brute-force channel computations at random
  points (`code/czi_common.py`).
* `max F = 1.1075163…` reproduces NXY Table 1 (`1.107516`). The two-letter point reproduces
  `1.1080356`. The optimised two-letter TIN value `1.1081413` reproduces NXY Table 1's
  `max_{R_two}` entry `1.108141` for this channel.
* The 3-letter value `1.11020458194` was computed in 40-digit `mpmath` from rounded parameters
  (`code/tin_k3_exact.py`). It agrees with the float optimiser (`1.1102045819`).
* Claim 6's tangency identity was checked symbolically (table above) and numerically. The
  polynomial identity was checked exactly with rational arithmetic.
* Claim 7's branch-and-bound was run as described. Its soundness rests on `mpmath.iv` outward
  rounding and on the monotone-piece enclosures of `h` and `φ` (`h` increases on `[0,1/2]`;
  `φ` increases on `[0,1/e]`, with the code's split thresholds `0.3678 < 1/e < 0.3679`).
* Not independently reviewed by the author (see the reviewer note below).

### Reviewer note (claude-opus-5-5, independent review, 2026-11-27)

Scripts are in `code/review/`. Each was written from scratch and imports
none of the author's code.

* **Primary source.** I read arXiv:1502.02589v1 in full (pdftotext).
  - The channel in `czi_common.py` is Table 1 row 1 (`P(Y1=0|x1,x2)`: `(0,0)→1, (0,1)→½,
    (1,0)→1, (1,1)→0`, matching Fig. 3).
  - `f` is eq. (13), and `f_qq` is eq. (15).
  - NXY's numbers are `max_Rhk = 1.107516` and `max_Rtwo = 1.108141` (Table 1), the non-rigorous
    bound `1.107577` (eq. 18), and the explicit two-letter point `1.1080356`. The attempt quotes
    all of them correctly.
  - NXY leave two steps unproved. Lemma 2's "one can verify `q̂ = 1−2p`" and the "tedious
    exercise" that the envelope of `F` is supported at `(p0,q0)`. The attempt's B&B needs neither.
* **Claim 6** (sympy, `code/review/sym_check.py`, `code/review/tangency_table.py`).
  - `f` and `g` derived symbolically from the channel equal the closed forms exactly.
  - `f_qq` minus the claimed formula simplifies to 0.
  - The tangency residual reduces to 0 by hand after `log((1−p)²) = 2log(1−p)`. It is `≤ 1e-50`
    numerically at 5 values of `p`.
  - All 5 rows of the coefficient table agree on both sides.
  - `σ(p) = f_q(p,1−2p)` holds, and `q̂ − q* = 2(1−p)(1−2p)/(3−2p) ≥ 0`.
  - The majorant/concavity argument for `E` is correct.
* **Reduction in Claim 7.** Checked against the Lean `hanKobayashiRegion`. `a1` and the third
  constraint `b1+c2` give `2R1+R2 ≤ a1+b1+c2`, with `c2 = H(X2|U2,Q)` because `U1 ⊥ (U2,X2) | Q`
  in `J`. The chain rule gives `g + Σ p(u2|q) f`, and concavity of `E` finishes. No cardinality
  bound is needed (any finite `kU2`, `kQ`), and the closure is harmless.
* **Interval code in Claim 7.**
  - I read `certify_hk1_bound.py` and probed the `mpmath.iv` semantics (`code/review/iv_semantics.py`).
  - `.a`/`.b` return degenerate intervals, and `iv.mpf([A.a,B.b])` encloses correctly.
  - An undecidable comparison returns `None`, which falls through to the conservative branch.
  - `1−x` is exact for the dyadic box ends and an outward interval otherwise.
  - The monotone pieces are right: `h` on `[0,½]`, and `φ` with `0.3678 < 1/e < 0.3679`.
  - The boxes cover `[0,1]²`, and the stop rule (max upper bound `< TARGET`) is correct. No float leak found.
* **Independent B&B** (`code/review/indep_bnb.py`, `mpmath.iv` at 20 digits; logs
  `code/review/bnb_110803.log`, `code/review/bnb_11078.log`). It uses the exact piecewise `g+E`
  instead of the tangent line on all of `p ≤ ½`.
  - `python indep_bnb.py 1.10803`: `CERTIFIED ... <= 1.10802997885819218768 < 1.10803; splits
    54945`. This is the same bound as the author's, as expected: the binding boxes have `p > ½`,
    where both codes use the same formula and the same bisection.
  - `python indep_bnb.py 1.1078`: `CERTIFIED ... <= 1.10779999832167 < 1.1078; splits 98434`.
    So `max_{HK^(1)}(2R1+R2) ≤ 1.1078` holds, which is stronger than Claim 7.
* **Claim 10, and NXY's two-letter point** (`code/review/indep_eval.py`, 60 digits).
  - The evaluator builds `W^{⊗k}` with `Y2 = X2` and evaluates all eight Lean quantities `a1…d2`
    for `kQ = kU1 = kU2 = 1`. All 7 constraints hold at `k·(R1,R2)`.
  - 3-letter scheme: `R1 = 0.0878251069048244`, `R2 = 0.934554368130239`,
    `2R1+R2 = 1.11020458193988723`.
  - NXY two-letter point: `1.10803563221621534`.
  - Bit-flipped convention check: `1.0286`. So the "never `000`" orientation matters and is the
    right one.
  - Interval enclosure (`code/review/iv_k3_and_outer.py`, 40 digits):
    an interval of width `1.4·10⁻³⁹` about `1.11020458193988723482`. Claim 10 is therefore rigorous.
  - Under the Lean definition the point lies in `{r : 3r ∈ R_HK(icPower W 3)} ⊆ HK^(3)`.
    `HK^(1) ⊆ HK^(3)` is Claim 2.
* **Claim 8.** The derivation checks. I reproduced (`code/review/iv_k3_and_outer.py`) the value `1.2290392` at `(0.42983, 0.41146)`
  numerically (not certified, as the claim says).
* **Claims 1, 2 and 4** (read and re-derived against `Core/Channels.lean: icCapacityRegion`). The
  convexity argument also needs a common `kU_j = max`, which is a trivial embedding. The Fano step
  is fine with the Lean definition `M_j = max 1 ⌊2^{nR_j}⌋` for all `n ≥ N`.
* **Claim 5.**
  - The empty-alphabet, silent-user and product cases are checked against Lean.
    `icCapacityRegion_icProduct` and `icCapacityRegion_isClosed` exist.
  - The strong-interference reduction to Costa–El Gamal is re-derived.
  - The El Gamal–Costa item is taken on citation.
* **Corrections made in place.**
  - The "400-fold" factor (Summary, Claim 10) is an artifact of the stopping target. It is about
    10-fold against the certified `1.1078`.
  - The `V_4` and `V_5` values in Claim 9 are concatenation values, not optimiser output.
  - Claim 7's `⊆ C` step uses Claim 3 (`[sketch]`).
  - None of these changes a conclusion.
  - In the problem file, "No result is known on whether the k-letter HK hierarchy stabilises"
    became "We found no result …". The other sentences of that edit check out against NXY,
    Telatar–Tse (abstract), Nair–Ng (abstract) and the repo's BS-ZIC file.
* **Novelty of the 3-letter scheme.** I searched the web (the queries "three-letter/multi-letter
  Han–Kobayashi clean Z", NXY follow-ups, Gohari–Nair, Anantharam–Gohari–Nair) and read the
  NXY paper, the Huleihel–Merhav CCIT report #886 (Gaussian, codewords with memory) and the
  D. Ng CUHK thesis (2021, Gaussian multi-letter HK; it cites only NXY's two-letter result).
  None of these has a `k ≥ 3` scheme for the NXY channel. The scheme realises NXY §2.2's
  "Markov `X2`" suggestion in block form. I cannot exclude unpublished or thesis work (Xia,
  Yazdanpanah) that I could not find.
* **Status → `verified`.** Every `[proved]` claim was checked (6, 7, 8 and 10 by independent
  computation; 1, 2 and 4 by re-derivation; 5 modulo its cited theorems). Claim 3 stays a
  `[sketch]`.
* **Not checked.** Claim 3 in detail. The El Gamal–Costa achievability. The `k = 4,5,6`
  optimiser runs (not re-run). The commit message's phrase "the paper states the gap without
  proof" overstates slightly: NXY give the argument with one step omitted.

## Dead ends

* **Polish bug (fixed, recorded for honesty).** The first `tin_hierarchy.py` run reported
  `V_2 ≥ 1.1075163`, below NXY's explicit `1.1080356`. Cause: the alternating polish replaced
  `p(x1^k)` by a Blahut–Arimoto output started from the uniform law and not run to convergence,
  which can *lower* the objective. Fix: warm start, and accept a step only if it improves. After
  the fix `V_2 ≥ 1.1081413`, matching NXY Table 1.

* **Direct 4-variable B&B** over `(p, q_a, q_b, θ)` (concave envelope via Carathéodory, without
  NXY Lemma 2). Abandoned before running. At the NXY optimum `p0 > 1/2`, `f(p0,·)` is concave,
  so the maximiser set in `(q_a, q_b, θ)` is a 2-dimensional degenerate manifold. Interval B&B
  cannot prune near it, and the box count blows up. Re-proving Lemma 2 (Claim 6) removes the
  envelope analytically and leaves a 2-variable problem.
* **Upper bounds on `max_{HK^(2)}`.** NXY's Lemma 1 transfers verbatim to `W^{⊗2}` (still CZI,
  with `X2^2` clean). But the concave envelope is then over the 3-simplex of `p(x2^2)` for each
  `p(x1^2)` in another 3-simplex. We found no tractable rigorous way to bound it. So we cannot
  certify `HK^(2) ⊊ HK^(3)` (or `HK^(2) ⊊ HK^(6)`), even though the best values found are
  `1.10814 < 1.11020`. Proving that, and then iterating, is the natural next step towards
  non-termination evidence. It would need a certified bound on the `k = 2` concave envelope.

## References

- Problem file `problems/dm-interference-channel-capacity.md`. No earlier attempts existed for
  this problem.
- C. Nair, L. Xia, M. Yazdanpanah, "Sub-optimality of Han–Kobayashi achievable region for
  interference channels," *Proc. IEEE ISIT 2015*, pp. 2416–2420, doi:10.1109/ISIT.2015.7282889;
  arXiv:1502.02589 (read in full: Prop. 1–3, Lemma 1–2, Table 1, Appendix).
- C. Nair, D. Ng, "Invariance of the Han–Kobayashi region with respect to temporally-correlated
  Gaussian inputs," *IEEE Trans. IT* 65(3):1372–1374, 2019 (read: Def. 2, Remark 2, Thm. 2).
- S. Liu, C. Nair, L. Xia, "Interference channels with very weak interference," *Proc. IEEE ISIT
  2014*, pp. 1031–1035 (cited via NXY; not read).
- M. Costa, A. El Gamal, "The capacity region of the discrete memoryless interference channel
  with strong interference," *IEEE Trans. IT* 33(5):710–711, 1987.
- A. El Gamal, M. Costa, "The capacity region of a class of deterministic interference
  channels," *IEEE Trans. IT* 28(2):343–346, 1982.
- E. Telatar, D. Tse, "Bounds on the capacity region of a class of interference channels,"
  *Proc. IEEE ISIT 2007*, pp. 2871–2874 (abstract only: outer bound and gap to HK, not a
  capacity result).
- A. Carleial, "Outer bounds on the capacity of interference channels," *IEEE Trans. IT*
  29(4):602–606, 1983.
- A. Gohari, C. Nair, "Outer bounds for multiuser settings: the auxiliary receiver approach,"
  *IEEE Trans. IT* 68(2):701–736, 2022 (abstract only).
- H.-F. Chong, M. Motani, H. K. Garg, H. El Gamal, *IEEE Trans. IT* 54(7):3188–3195, 2008;
  A. El Gamal, Y.-H. Kim, *Network Information Theory*, Thm 6.4.
- Novelty check: searched the web (queries on "k-letter Han–Kobayashi hierarchy", "multi-letter
  HK strictly increasing", NXY follow-ups) and Crossref. We found no result on termination of
  the `k`-letter HK hierarchy for DM-ICs, and no prior rigorous version of the NXY "tedious
  exercise". Nair–Ng 2019 is the only multi-letter HK result we found, and it is Gaussian-input
  specific.
