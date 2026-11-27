---
problem: mac-with-feedback
date: 2026-11-26
attempter: claude
model: claude-opus-5-5
type: partial-result
status: unverified
---

## Summary

Three things. (1) A formal audit of the frozen statement `∀ W, ∃ k ≥ 1,
macFeedbackCapacityRegion W = coverLeungKLetterRegion k W`. Both sides are closed and convex.
`R_CL^(k)` is nested along divisibility, and up to an `O(1/n)` scaling along all `n`. The
closure of the union equals `C_FB`; we give an elementary Fano proof, not needing Kramer's
directed-information theorem. Every degenerate or known class we checked (empty alphabets,
constant channel, silent user, feedback-useless channels, Willems' class including the binary
adder MAC) is settled at `k = 1` *consistently*. **No catalog error.** (2) Survey fixes: the
Venkataramanan–Pradhan page numbers were wrong, and `R_CL^(k)` is Kramer's (1998) "generalized
Cover–Leung region". Both are fixed in the problem file. (3) A new, computer-assisted strict
inclusion `R_CL^(1)(W) ⊊ R_CL^(2)(W)` for an explicit binary DM-MAC: the Bross–Lapidoth binary
MAC at `q = 1/2`, i.e. `Y = X_J` with `J` uniform on `{1,2}` and unknown to everyone. Its
max sum-rate jumps from `≤ 0.5789491` (certified, `k = 1`; true value about `0.57651`) to
`≥ 0.5843216` (explicit 2-step strategies, `k = 2`). So the finite-`k` hierarchy is genuinely
non-trivial on finite alphabets, and, with the standard achievability of Claim 3, Cover–Leung
is not the feedback capacity region of this channel.

## Approach

The frozen question is whether the `k`-letter Cover–Leung (CL) hierarchy terminates for every
finite-alphabet MAC. Before attacking it we checked that the Lean objects ask exactly that
question. Then we looked for the smallest rigorous fact about the hierarchy itself. The only
published finite-`k` data we found are Kramer's `M = 2` evaluations on the Gaussian MAC, as
reported by VP 2011, §IV-B, and those are outside the finite-alphabet scope. A clean,
certified `k = 1 → 2` jump on a binary MAC is the MAC-FB analogue of the NXY `k = 1 → 2` gap for
the interference channel.

## Claims

Notation: `R^(k) := coverLeungKLetterRegion k W`, `C_FB := macFeedbackCapacityRegion W`.

1. **[proved]** `R^(k)` is closed, convex and downward-closed in `ℝ²_{≥0}`.
2. **[proved]** For `n = qk + s` with `0 ≤ s < k`: `(qk/n)·R^(k) ⊆ R^(n)`. In particular
   `R^(k) ⊆ R^(mk)`.
3. **[sketch]** `R^(k) ⊆ C_FB` under the repository's operational definition. This is CL's
   theorem applied to the super-channel `(S1,S2) ↦ Y^k` with finite strategy alphabets, plus
   padding.
4. **[proved]** If `(R1,R2)` is operationally achievable, then for every `δ > 0` and all large
   `n`, `((R1−δ)_+, (R2−δ)_+) ∈ R^(n)`, already with `U` constant. Hence
   `cl ⋃_k R^(k) = C_FB`.
5. **[sketch]** (Proved from Claims 1, 2 and 4, plus the `[sketch]` Claim 3.) `C_FB` is convex. `Statement(W)` holds iff `C_FB ⊆ R^(k)` for some
   `k`. If it holds with `k`, it holds with every multiple of `k`, and then
   `(1 − (k−1)/n)·C_FB ⊆ R^(n) ⊆ C_FB` for all `n ≥ k`. So the non-monotonicity of
   `k ↦ R^(k)` is harmless for the `∃ k` form.
6. **[proved, modulo the cited capacity theorems]** No catalog error. `Statement(W)` holds with
   `k = 1` for: empty input alphabets (both sides `∅`); constant channels (`{(0,0)}`); a silent
   second user (`[0,C(V)] × {0}`, using the point-to-point feedback converse); any `W` for which
   feedback does not enlarge the no-feedback region (since `CL ⊇` Ahlswede–Liao); and Willems'
   class `X1 = φ(Y, X2)` (Willems 1982), which includes the binary adder MAC. It *fails* at
   `k = 1` for the channel of Claim 8, so it is not trivially true.
7. **[sketch]** `R^(k)` equals Kramer's generalized CL region with `M = k` (thesis §§5.3–5.4, as
   described in VP 2011, §IV-B, Fact 22). Under `S1 ⊥ S2 | U`,
   `I(S1;Y^k|S2,U) = I(X1^k → Y^k ‖ X2^k | U)` and `I(S1S2;Y^k) = I(X1^kX2^k → Y^k)`, and random
   strategies realise exactly the causally conditioned input laws.
8. **[proved, computer-assisted]** Let `W_{1/2}` be the binary MAC with
   `P(Y=1|x1,x2) = (x1+x2)/2`. Then
   `max_{R^(1)}(R1+R2) ≤ UB1 := 0.5789491 < LB2 := 0.5843216 ≤ max_{R^(2)}(R1+R2)`. Hence
   `R^(1)(W_{1/2}) ⊊ R^(2)(W_{1/2})`. Combined with Claim 3 (`R^(2) ⊆ C_FB`, standard CL
   achievability on the super-channel), Cover–Leung is strictly suboptimal for `W_{1/2}`, and
   `Statement(W_{1/2})` fails at `k = 1`.
9. **[numerical]** For the same family `W_q` (Bross–Lapidoth's binary reduction of the Poisson
   MAC), numerical optimisation also gives a `k = 2` sum-rate above the best `k = 1` value found
   at `q = 0.4` (`0.3664908` vs `0.3658759`). At `q = 0.25` we found no gain (`≤ 5·10⁻⁶`).
   None of this is certified, except that the `k = 2` numbers are explicit achievable points.
10. **[heuristic]** On whether the hierarchy terminates, we have no evidence for finite
    alphabets either way. The only finite-`M` data point for a channel with known capacity is
    Gaussian: Kramer's `M = 2` at SNR 10 gives `1.2566` against Ozarow's `1.2847`, as reported by
    VP. That is consistent with, but no evidence of, non-termination.

## Details

### 1. Closed, convex, downward-closed

`R^(k)` is a `closure` by definition. For convexity, take feasible `(r, P)` and `(r', P')` with
auxiliary alphabets `Fin kU` and `Fin kU'`. Put `U'' ∈ Fin (kU + kU')` with law
`θ P_U ⊕ (1−θ) P'_U`, keeping the strategy kernels. Conditional independence `S1 ⊥ S2 | U''`
is preserved. `I(S1;Y^k|S2,U'')` and `I(S2;Y^k|S1,U'')` are exact `θ`-mixtures. `I(S1S2;Y^k)`
is concave in the law of `(S1,S2)` for the fixed super-channel
`V(y^k|s1,s2) = ∏_i W(y_i|s1_i(y^{i−1}), s2_i(y^{i−1}))`, so it is at least the mixture of
the two values. Hence `θr + (1−θ)r'` is feasible.

### 2. Nesting and scaling

Given feasible `(U, S1, S2)` for horizon `k`, take `q` i.i.d. copies
`(U^{(b)}, S1^{(b)}, S2^{(b)})`, `b = 1..q`. Define the horizon-`n` strategy that runs
`S_j^{(b)}` on letters `(b−1)k+1, …, bk`, *feeding it only the outputs of its own sub-block*
(this is a legal element of `MACFeedbackStrat n`, since it is a function of a prefix of
`y^{i−1}`). It sends a fixed symbol on the last `s` letters. With `U := (U^{(1)},…,U^{(q)})`
(finite) the joint law has the required product form. The sub-blocks are independent, and the
last `s` outputs are independent of everything. Each of the three information quantities is
therefore exactly `q` times its horizon-`k` value, so `(qk/n)·r ∈ R^(n)`. Note that `R^(n)` is
downward-closed, so scaling towards the origin stays inside.

### 3. Achievability

`V` above is a DM-MAC with finite input alphabets (`|S_j| = |X_j|^{(|Y|^k−1)/(|Y|−1)}`). Its
uses are memoryless across super-letters, and both encoders observe every past super-output.
CL's theorem (El Gamal–Kim §17.2) gives every rate pair strictly inside the CL region of `V`.
Dividing by `k`, and padding blocklengths `n ≢ 0 (mod k)` with `< k` dummy letters, yields
achievability of the interior of `R^(k)`. The closure in `macFeedbackCapacityRegion` absorbs the
rest. The CL block-Markov argument is standard and is not repeated, hence `[sketch]`.

### 4. Converse (multi-letter, elementary)

Fix an achievable `(R1,R2)`, `δ > 0` and `ε ∈ (0,1)`. For large `n` there is a code with
`M_j = max(1, ⌊2^{nR_j}⌋)` and average error `≤ ε`. Let `M_j` be independent and uniform, and
let `S_j := (i, y^{i−1}) ↦ enc_j i M_j y^{i−1}` be the strategy of the encoder for message
`M_j`. So `S1 ⊥ S2`, and `Y^n` depends on the messages only through `(S1,S2)` via `V`. Fano
gives `H(M1M2|Y^n) ≤ 1 + ε log(M1M2)`. Then

* `log M1 = I(M1;Y^n|M2) + H(M1|Y^n M2) ≤ I(S1;Y^n|S2) + 1 + ε log(M1M2)`. Here
  `I(M1;Y^n|M2) = H(Y^n|M2) − H(Y^n|S1S2)` and `H(Y^n|M2) ≤ H(Y^n|S2)`, because `S2` is a
  function of `M2`.
* The same holds for user 2, and `log(M1M2) ≤ I(S1S2;Y^n) + 1 + ε log(M1M2)`.

With `U` constant (`kU = 1`), the pair
`r_j = (1/n)(log M_j − 1 − ε log(M1M2))_+` satisfies all three constraints of `R^(n)`.
For the sum, `r1 + r2 ≤ (1/n)(log M1M2 − 1 − ε log(M1M2))`. Since `(1/n)log M_j → R_j`,
choosing `ε` small and `n` large gives `r ≥ (R − δ)_+` coordinatewise, and downward-closedness
finishes the proof. Kramer's theorem is the sharper statement that one may restrict to the
directed-information form. For the converse half `C_FB ⊆ cl ⋃_k R^(k)` of the equality
that the problem file attributes to Kramer, the elementary argument suffices. The other half is
Claim 3.

### 5. Consequences

`⋃_k R^(k)` is a directed union of convex sets (`R^(k), R^(m) ⊆ R^(km)`), hence convex. Its
closure `C_FB` is therefore convex. If `C_FB = R^(k)`, then Claim 2 gives
`(1−(k−1)/n)·C_FB ⊆ R^(n) ⊆ C_FB` for `n ≥ k`. Conversely `C_FB ⊆ R^(k)` together with Claim 3
gives equality. A channel for which `R^(n)` approaches `C_FB` more slowly than `O(1/n)` along
some subsequence would therefore *disprove* the statement. This is a possible line of attack,
which we did not pursue.

### 6. Degenerate and known classes

* *Empty `X1`* (`kX₁ = 0`). For `n ≥ 1` there is no `enc₁ i : Fin M₁ → (Fin i → Y) → Fin 0`,
  so `C_FB = ∅` (this agrees with the `Known/Operational.lean` header). Also
  `MACFeedbackStrat k (Fin 0) Y` is empty for `k ≥ 1`: at `i = 0` the domain `Fin 0 → Y` is
  inhabited. So no `ProbDist` on it exists, `Ps₁` forces `kU = 0`, and then there is no
  `ProbDist (Fin 0)`. Both sides are `∅`.
* *Constant channel.* All information terms vanish: `{(0,0)} = {(0,0)}`.
* *Silent user 2* (`macIgnoringSecond V`). `R2 ≤ I(X2;Y|X1,U) = 0` and
  `R1 ≤ I(X1;Y|U) ≤ C(V)`, with equality attained. So `R^(1) = [0,C(V)]×{0} = C_FB`. The
  upper inclusion uses the point-to-point feedback converse, as noted in
  `Known/Operational.lean`.
* *Feedback-useless channels.* `R^(1) ⊇` Ahlswede–Liao region: take `U = Q`, and use
  `I(X1X2;Y) ≥ I(X1X2;Y|Q)`. So if `C_FB = C_noFB` then `R^(1) = C_FB`.
* *Willems' class* (`X1` a function of `(Y, X2)`, e.g. `Y = X1+X2`). Willems (1982) proves
  `C_FB = CL = R^(1)`, with the same closed region (unbounded `kU` does not matter).

### 7. Identification with Kramer's generalized CL region

Assume `S1 ⊥ S2 | U` and `X_{j,i} = S_{j,i}(Y^{i−1})`. Then
`I(S1;Y^k|S2,U) = Σ_i [H(Y_i|Y^{i−1},S2,U) − H(Y_i|X_{1i},X_{2i})]`. The posterior
`p(s1 | y^{i−1}, s2, u) ∝ p(s1|u) ∏_{j<i} W(y_j | s1_j(y^{j−1}), x_{2j})` depends on `s2` only
through `x2^{i−1}`. Hence `H(Y_i|Y^{i−1},S2,U) = H(Y_i|Y^{i−1},X2^i,U)`, and the sum is
`I(X1^k → Y^k ‖ X2^k | U)`. The sum term is `I(X1^kX2^k → Y^k)`. Conversely, a causally
conditioned law `∏_i p(x_{ji}|x_j^{i−1}, y^{i−1}, u)` is realised by drawing the strategy's value
at each node `y^{i−1}` from that kernel, evaluated at the strategy's own past outputs. This is the
code-tree argument. We could not access Kramer's thesis, so the match is to VP's restatement.

### 8. The certified jump on `W_{1/2}`

**Channel.** `W_q`: `P(Y=1|x1,x2) = q(x1+x2)`. This is Bross–Lapidoth's binary reduction of the
Poisson MAC, as described in VP §IV-C. At `q = 1/2`, `Y = X_J` with `J ~ Unif{1,2}` independent
of everything: the receiver sees the input of a uniformly chosen user, and nobody learns `J`.
`W_{1/2}` is not in Willems' class: from `X2 = 0, Y = 0` one cannot tell `X1`. For reference,
the max sum-rate without feedback is `0.5` (uniform inputs), and the cooperative bound
`max_{p(x1,x2)} I(X1X2;Y)` is `1` (`X1 = X2`).

**Lower bound at `k = 2`.** `code/opt_cl.py` (soft-min continuation, `|U| = 4`, random starts)
found a distribution with `p(u) ≈ (0.540, 0.230, 0.230)` on three atoms. Writing a 2-step
strategy as `x0|f(0)f(1)` (first input, then second input as a function of `y1`), for `u = 0`:
user 1 uses `0|11 (.410), 0|01 (.269), 1|00 (.254), 1|01 (.068)` and user 2 uses
`0|00 (.412), 0|10 (.267), 1|11 (.254), 1|10 (.067)`. The other two atoms are mirror images of
each other. So the second inputs are genuinely feedback-dependent ("copy `y1`" / "negate `y1`"),
correlated through the common feedback symbol rather than through `U` alone. The saved
distribution (`code/opt_q0.5.npz`) is renormalised exactly and evaluated in 40-digit arithmetic
(`code/certify_gap.py`):
`A1/2 = 0.292180722684`, `A2/2 = 0.292140853262`, `B/2 = 0.584335271754`, so
**`LB2 := min(A1+A2, B)/2 = 0.58432157594618 ≤ max_{R^(2)}(R1+R2)`**.

**Upper bound at `k = 1` (duality certificate).** For `α ∈ [0,1]`, a table `L(x1,x2)` and an
output pmf `r`, suppose `ψ(p1,p2) := I(X1;Y|X2)+I(X2;Y|X1) ≤ Σ p1(x1)p2(x2)L(x1,x2)` for *all*
product inputs. Then every CL distribution satisfies:
`min(A,B) ≤ αA + (1−α)B` with `A = A1+A2`;
`A = Σ_u p(u)ψ(p_{1|u},p_{2|u}) ≤ ⟨p̄, L⟩` with `p̄ = Σ_u p(u)p_{1|u}⊗p_{2|u}`;
and `B = I(X1X2;Y) = Σ_x p̄(x)D(W_x‖p̄W) ≤ Σ_x p̄(x)D(W_x‖r)`.
Hence **`max_{R^(1)}(R1+R2) ≤ max_x [αL(x) + (1−α)D(W_x‖r)]`**. Taking closures does not change
a supremum. This is weak duality for `max min(A,B) = min_α max(αA+(1−α)B)`, which is exact
because `{(A,B)}` is convex up to domination; the bound loses nothing in principle. (Exactness
is not needed for the certificate.) We found
`(α, L, r)` by an LP on a `161²` grid of product inputs, alternated with an `r`-update:
`α = 0.605`, `L = (L00, L01, L10, L11) = (0.30004610530312337, 0.9529406263243592,
0.9529406263243592, 0.3000500233786525)`, `r = (0.4999989600880894, 0.5000010399119106)`.
The grid LP value is `0.57652908`. Then `ψ ≤ L + ε` with `ε = 4·10⁻³` was **verified on all of
`[0,1]²`** by interval bisection (`cert_cl1.verify_majorization`). The final maximum was
evaluated in interval arithmetic:

```
$ python certify_gap.py 0.5 4e-3          (log: code/certify_gap_q0.5.log)
q=0.5: k=2 point: A1/2=0.292180722684, A2/2=0.292140853262, B/2=0.584335271754
   => sum-rate of R_CL^(2) >= 0.58432157594618  (40-digit arithmetic)
   LP (grid) bound for k=1: 0.57652908 at alpha=0.6050, ...
   CERTIFIED k=1 sum-rate <= 0.578949078927469...  (psi <= L + 0.004 verified on [0,1]^2, 93967 boxes) [239s]
   numerical k=1 optimum found: 0.5765051813
RESULT: certified gap  0.584321575946 - 0.578949078927 = 0.0053725  (STRICT INCLUSION R_CL^(1) < R_CL^(2) CERTIFIED)
```

So **`UB1 = 0.5789491`**.

The numerical `k = 1` optimum found by local search is `0.57650518`, attained at `U` uniform on
two atoms with `P(X1=0|u) = P(X2=0|u) ∈ {0.304, 0.696}`. The certified bound is looser only
because of the slack `αε ≈ 2.4·10⁻³`, which we chose for speed.

**Conclusion.** `max_{R^(1)}(R1+R2) ≤ UB1 < LB2 ≤ max_{R^(2)}(R1+R2)`, so
`R^(1)(W_{1/2}) ⊊ R^(2)(W_{1/2})`. By Claim 3, `R^(2) ⊆ C_FB`, so Cover–Leung is strictly
suboptimal for `W_{1/2}`, and `Statement(W_{1/2})` cannot hold with `k = 1`. Since `R^(1)` is
convex and closed, the sum-rate gap also gives an explicit separating line, `R1+R2 = UB1`.

### 9. Other channels (numerical only)

`code/opt_cl.py` uses the same method for other `q`. Logs: `code/opt_q*.log`, and
`code/explore.log` for the first pass.

| channel | no-FB sum cap. | CL `k=1` (best found) | CL `k=2` (explicit point) | coop. bound |
|---|---|---|---|---|
| `W_{0.25}` | 0.179103 | 0.2037924 | ≥ 0.2037969 (gain `5·10⁻⁶`, within optimiser noise) | 0.321928 |
| `W_{0.40}` | 0.325232 | 0.3658759 | ≥ 0.3664908 (gain `6.1·10⁻⁴`) | 0.618231 |
| `W_{0.50}` | 0.500000 | 0.5765052 | ≥ 0.5843216 (gain `7.8·10⁻³`; certified gap `5.4·10⁻³`) | 1.000000 |
| noisy adder, `ε=0.1` | 1.095839 | 1.162236 | ≥ 1.162523 | 1.164936 |
| noisy adder, `ε=0.3` | 0.620846 | 0.661472 | ≥ 0.662125 | 0.663034 |

The `k = 1` column is a local-search value, not certified, except at `q = 1/2` (Claim 8).
So for `q = 0.4` the apparent gain is numerical evidence only: the `k = 2` number is a
rigorous achievable value, but `0.3658759` is not a certified upper bound. The gain shrinks
quickly as `q` decreases. We found none at `q = 0.25`, though the `k = 2` optimiser may simply
have failed there. This is consistent with the intuition that within-block adaptation pays
most when single outputs are most informative about the input pair.

## Verification

* The `k = 2` information quantities were computed by two independent code paths, and they
  agree to `10⁻¹⁵`: the vectorised `mac_cl.cl_quantities`, and the literal Lean formulas
  `condMutualInfo = H(XZ)+H(YZ)−H(XYZ)−H(Z)` on the full joint table `J(u,s1,s2,y²)` of
  `coverLeungKLetterRegion` (`code/check_lean_formula.py`). A third path,
  `code/certify_gap.py`, recomputes them in 40-digit `mpmath` from the exactly renormalised
  saved distribution. That 40-digit value is the one quoted as `LB2`.
* The `k = 1` bound is a weak-duality certificate. Its only non-trivial input is the
  majorisation `ψ ≤ L + ε` (`ε = 4·10⁻³`) on `[0,1]²`. This is checked by interval bisection in
  `mpmath.iv`, using concavity-based enclosures of `a ↦ H(a w0 + (1−a) w1)`: the endpoint
  minimum for the lower bound, and endpoint tangent lines for the upper bound. The final
  `max_x[α(L(x)+ε) + (1−α)D(W_x‖r)]` is evaluated in interval arithmetic.
* The numerical `k = 1` optimum found by local search (`0.5765052`) lies below the certified
  `UB1`, as it must.
* Not independently reviewed. The audit claims (1–7) are pen-and-paper.

## Dead ends

* **Random-start optimisation of `R^(2)`.** In a first exploratory pass (`code/explore.py`,
  6 random starts, `β = 200` soft-min), the `k = 2` optimiser for `q = 0.10` and `q = 0.25`
  returned sum-rates *below* the `k = 1` optimum. That is impossible, since
  `R^(1) ⊆ R^(2)`. It was an optimisation failure: the soft-min with fixed `β` biases the
  objective by up to `ln 2/β`, and the landscape over `≥ 50` softmax parameters is rugged. Fix:
  `β`-continuation `10² → 10³ → 10⁴` and warm starts from the `k = 1` optimum embedded as
  feedback-ignoring product strategies (`code/opt_cl.py`). From the embedded start the
  optimiser only crawls (`+8·10⁻⁶` at `q = 1/2`). The large gain came from random starts, which
  find genuinely feedback-dependent second-step maps. **So none of our numerical `k = 2` values
  should be read as the true `max_{R^(2)}`; they are lower bounds.**
* **Noisy adder MACs** (`Y = X1+X2` through a ternary symmetric channel). In `explore.py`, CL
  at `k = 1` is already within `3·10⁻³` of the cooperative bound `max I(X1X2;Y)`, so a
  `k = 2` gain, if any, is at most that. We found `≤ 7·10⁻⁴`, which we did not pursue or
  certify. Note that the noiseless adder is in Willems' class.
* **Upper bounds on `max_{R^(2)}`.** The duality certificate of Claim 8 extends verbatim to
  `k = 2` (replace `ψ` by `I(S1;Y²|S2)+I(S2;Y²|S1)` on product strategy laws). But the
  majorisation must then be certified over a product of two 7-simplices (`|S_j| = 8`), which is
  hopeless for interval branch-and-bound. So we cannot show `R^(2) ⊊ R^(4)` or anything about
  larger `k`.
* **Attempted disproof idea** (not pursued to a result). Claim 5 shows that `Statement(W)`
  forces `d_H(R^(n), C_FB) = O(1/n)`. Proving a slower rate for an explicit channel would need
  a converse that matches `C_FB`, which is unavailable for any non-Willems DM-MAC. Dependence
  balance bounds are not known to be tight there.

## References

- Problem file `problems/mac-with-feedback.md`; no earlier attempts existed for this problem.
- R. Venkataramanan, S. S. Pradhan, "A new achievable rate region for the multiple-access
  channel with noiseless feedback," *IEEE Trans. IT* 57(12):8038–8054, 2011; arXiv:0901.1892.
  We read §IV via ar5iv: examples, Kramer `M = 2` comparison, Fact 22, and the BL-error remark.
- G. Kramer, *Directed Information for Channels with Feedback*, PhD thesis, ETH Zurich, 1998
  (**not accessed**; §§5.3–5.4 content taken from VP's description); G. Kramer, "Capacity
  results for the discrete memoryless network," *IEEE Trans. IT* 49(1):4–21, 2003.
- T. M. Cover, C. S. K. Leung, *IEEE Trans. IT* 27(3):292–298, 1981; F. M. J. Willems,
  *IEEE Trans. IT* 28(1):93–95, 1982; L. H. Ozarow, *IEEE Trans. IT* 30(4):623–629, 1984;
  N. T. Gaarder, J. K. Wolf, *IEEE Trans. IT* 21(1):100–102, 1975.
- S. I. Bross, A. Lapidoth, *IEEE Trans. IT* 51(3):811–833, 2005 (not accessed; the binary
  channel is taken from VP §IV-C).
- A. P. Hekstra, F. M. J. Willems, *IEEE Trans. IT* 35(1):44–53, 1989; R. Tandon, S. Ulukus,
  *IEEE Trans. IT* 55(10):4494–4507, 2009 (cited, not used).
- H. H. Permuter, T. Weissman, J. Chen, *IEEE Trans. IT* 55(6):2455–2477, 2009;
  A. Anastasopoulos, S. S. Pradhan, *Proc. ISIT 2020*, pp. 2085–2090 (arXiv:2001.03807,
  abstract read); D. Vasal, arXiv:2202.02320 (abstract seen via search snippet only).
- A. El Gamal, Y.-H. Kim, *Network Information Theory*, §17.2 (Cover–Leung theorem).
- **Novelty check.** We ran web searches for: multi-letter or code-tree improvements of
  Cover–Leung; the VP and BL examples; computability or single-letterization of MAC-FB capacity
  in 2015–2026 (Anastasopoulos–Pradhan, Vasal, and Boche–Schaefer–Poor computability work,
  which concerns finite-state channels, not the DM-MAC-FB); and k-letter hierarchies. We also
  queried Crossref for bibliographic data. We found no statement that the `M = 2` generalized CL
  region strictly contains CL for a *finite-alphabet* MAC. Kramer's thesis, which we could not
  read, evaluated `M = 2` "for a few examples" (VP). VP name only the Gaussian MAC in that
  comparison, but **the thesis may contain a discrete example**. So Claim 8 should be regarded
  as new only in its certified form for `W_{1/2}`. CL's suboptimality for this channel family
  is consistent with VP's strict improvement for `q → 0`. At `q = 1/2` we know of no prior
  statement.
