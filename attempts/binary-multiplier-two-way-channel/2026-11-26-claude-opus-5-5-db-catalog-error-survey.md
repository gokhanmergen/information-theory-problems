---
problem: binary-multiplier-two-way-channel
date: 2026-11-26
attempter: claude
model: claude-opus-5-5
type: survey
status: unverified
---

## Summary

**Catalog error.** The Lean functional `bmcDependenceBalanceBound` is the *plain*
Hekstra–Willems dependence-balance (DB) bound. For the BMC this bound is vacuous: it equals
Shannon's outer bound, log₂φ ≈ 0.694242, and not 0.64628 (Claims 1–2, proved). Because
C_sym(BMC) ≤ 0.64891 (Zhang–Berger–Schalkwijk 1986), the frozen `Statement` is **false** by
a known result. The value 0.64628 comes from Hekstra and Willems' DB bound *with an adaptive
parallel channel*. I reconstruct that bound from Bloemen's 1996 thesis, reduce it to a closed
form (Claim 4, proved), and reproduce 0.64628 numerically: the primal value is 0.6462832 and
the Lagrangian dual value is 0.6462831 (Claim 5). I propose a corrected Lean statement built
on that closed form. The literature section is updated: the best lower bound is 0.63072
(Schalkwijk–Meeuwissen–Bloemen 1995), not 0.63056, and I found no improvement on either side
up to Nov 2026.

## Approach

1. Audit the Lean definitions against the Markdown and against the literature.
2. Evaluate the Lean DB functional exactly. For deterministic single-output channels the DB
   constraint simplifies to an entropy inequality, and this shows at once that it is inactive
   for the BMC.
3. Find out which bound actually gives 0.64628. Kim (2012) credits it to "DB bound + channel
   augmentation". Tandon–Ulukus (2007) credit it to the "parallel channel extension". Bloemen's
   1996 TU/e thesis (Thm 6.3, Table 6.2) states the parallel channel explicitly. Reproduce the
   number from that statement.
4. Literature sweep for 1990–2026 improvements on the lower and upper bounds.

## Claims

1. **[proved]** For any channel whose output is a deterministic function Y = f(X₁,X₂), and
   any p(z,x₁,x₂):
   I(X₁;X₂|Z) − I(X₁;X₂|Y,Z) = H(Y|Z) − H(Y|X₁,Z) − H(Y|X₂,Z).
   So for the BMC the DB constraint is H(Y|Z) ≤ I(X₁;Y|X₂,Z) + I(X₂;Y|X₁,Z). Since
   H(Y|Z) ≤ 1, the constraint holds automatically whenever the two rate terms sum to at least
   1 bit, and in particular at every symmetric rate ≥ 1/2.
2. **[proved]** `bmcDependenceBalanceBound = log₂((1+√5)/2) ≈ 0.6942419136`, which is
   Shannon's outer-bound value. The "≈ 0.64628" in the Lean docstring and in the Markdown is
   wrong for this functional. Bloemen (1996, §6.4.2) already observed in substance that the
   plain DB constraint "does not sharpen the Shannon outer bound in case of a BMC".
3. **[proved, given the published converse of Zhang–Berger–Schalkwijk 1986]** The frozen
   `InfoTheory.Problems.BinaryMultiplierTwoWayChannel.Statement` is false:
   `bmcSymmetricCapacity ≤ 0.64891 < 0.69424 ≤ bmcDependenceBalanceBound`. Under AGENTS.md
   this is a catalog error, and a corrected statement is proposed below.
4. **[proved]** Take Hekstra and Willems' adaptive parallel channel for the BMC (Bloemen 1996,
   Table 6.2). Its auxiliary output B satisfies I(X₁;X₂|Y,B,U) ≡ 0, so the DB constraint forces
   X₁ ⊥ X₂ | U. The bound then has an explicit closed form in (w_u, α_u, β_u). The formula is
   in Details §4.
5. **[heuristic, numerical]** The closed form of Claim 4 evaluates to 0.6462832 (explicit
   parameters, |U| = 3; the same value for |U| = 4, 5, 6). A grid-based Lagrangian dual gives
   0.6462831. This reproduces Hekstra–Willems' 0.64628 to all published digits, which confirms
   the reconstruction and the corrected definition. The dual is evaluated on a 2001² grid
   without interval control, so the upper side is not rigorous.
6. **[survey]** As of Nov 2026 the best known bounds are
   **0.63072 ≤ C_sym(BMC) ≤ 0.64628**. The lower bound is Schalkwijk–Meeuwissen–Bloemen (1995).
   The upper bound is Hekstra–Willems (1989) with the parallel channel. Tandon–Ulukus (2007)
   proved that HW's choice is optimal among binary adaptive parallel channels. I found no later
   improvement on either side; the searches are listed under Novelty check.

## Details

### 1. The DB constraint for deterministic single-output channels

Two applications of the chain rule give I(X₁;X₂|Y,Z) = I(X₁;X₂|Z) + I(X₁;Y|X₂,Z) − I(X₁;Y|Z),
so I(X₁;X₂|Z) − I(X₁;X₂|Y,Z) = I(X₁;Y|Z) − I(X₁;Y|X₂,Z). With Y = f(X₁,X₂) we have
H(Y|X₁,X₂,Z) = 0. Hence I(X₁;Y|Z) = H(Y|Z) − H(Y|X₁,Z) and I(X₁;Y|X₂,Z) = H(Y|X₂,Z), which is
the identity. The rate terms are I(X₁;Y|X₂,Z) = H(Y|X₂,Z) and I(X₂;Y|X₁,Z) = H(Y|X₁,Z). The
constraint is therefore H(Y|Z) ≤ I₁ + I₂, and H(Y|Z) ≤ log₂|𝒴| = 1. ∎

### 2. Value of the Lean functional

*Lower bound.* Take kZ = 1 and Shannon's outer-bound optimiser
p₀₀ = 0, p₀₁ = p₁₀ = (5−√5)/10, p₁₁ = 1/√5 (the probabilities sum to 1). Then
P(X₂=1) = (5+√5)/10 and P(X₁=1 | X₂=1) = 2√5/(5+√5) = (√5−1)/2 = 1/φ. Using
1/φ + 1/φ² = 1 and 1/φ² = 2 − φ, we get h(1/φ) = log₂φ·(1/φ + 2/φ²) = (3−φ)·log₂φ. Hence
H(Y|X₂) = (5+√5)/10 · (3−φ) · log₂φ = log₂φ, because (5+√5)(5−√5)/20 = 1 and 3 − φ = (5−√5)/2.
By symmetry H(Y|X₁) = log₂φ. The sum is 2·log₂φ ≈ 1.388 ≥ 1 ≥ H(Y), so DB holds by Claim 1.
So log₂φ belongs to the set. In 60-digit arithmetic, `code/db_vacuous.py` evaluates the Lean
`condMutualInfo` formula and gives I(X₁;X₂) = 0.15625 ≤ I(X₁;X₂|Y) = 0.55279, with both rate
terms equal to log₂φ to 60 digits.

*Upper bound.* For any (kZ, P), min(I₁,I₂) ≤ ½(I₁+I₂) = Σ_z P(z)·½[H(Y|X₂,Z=z) + H(Y|X₁,Z=z)].
It suffices to show ½[H(Y|X₁) + H(Y|X₂)] ≤ log₂φ for every p(x₁,x₂). Write a = P(X₁=1),
b = P(X₂=1), c = p₁₁. Then H(Y|X₁) = Φ(a,c) := a·h(c/a). This is the perspective of h, so it
is jointly concave, and it is nondecreasing in a, since ∂Φ/∂a = −log₂(1 − c/a) ≥ 0. Feasibility
(p₀₀ ≥ 0) requires a + b ≤ 1 + c. Therefore
½[Φ(a,c) + Φ(b,c)] ≤ Φ((a+b)/2, c) ≤ Φ((1+c)/2, c) = h(t)/(2−t), where t = 2c/(1+c) ∈ [0,1].
By concavity, h lies below its tangent at t₀ = 1/φ. Since h'(1/φ) = log₂((1−t₀)/t₀) = −log₂φ,
for all t we get h(t) ≤ (3−φ)·log₂φ − log₂φ·(t − φ + 1) = log₂φ·(2 − t). So h(t)/(2−t) ≤ log₂φ.
Every element of the set is therefore ≤ log₂φ. The set is bounded above and contains log₂φ,
so `sSup = log₂φ`. ∎

### 3. Why the Statement is false

`bmcSymmetricCapacity` is the equal-rate point of `twcCapacityRegion binaryMultiplyingChannel`.
That region is built from average-error codes for all large n, with adaptive encoders
`enc₁ i m₁ (y₁ history)`, which is the standard operational notion. Every Lean-achievable pair
is achievable in the standard sense, so the published converses apply:
C_sym ≤ 0.64891 (ZBS 1986) and C_sym ≤ 0.64628 (HW 1989). Both are < log₂φ, so
`Statement : bmcSymmetricCapacity = bmcDependenceBalanceBound` is false. A Lean
`statement_false` would need a formal converse (Fano plus the ZBS or HW argument), which is not
in `Known/` or `Bridge/` today. That is the honest gap between "settled by a known fact" and
"machine-checked".

### 4. The Hekstra–Willems parallel-channel bound in closed form

I could not access HW 1989 itself. The statement below is taken from Bloemen's thesis
(Thm 6.3 and Table 6.2, Sec. 6.4.3). Tandon's 2010 thesis, Sec. 2.5, gives the same adaptive
form for the MAC with feedback.

C(TWC) ⊆ {(R₁,R₂) : R₁ ≤ min[I(X₁;YB|X₂U), I(X₁;Y|X₂)], R₂ ≤ min[I(X₂;YB|X₁U), I(X₂;Y|X₁)],
I(X₁;X₂|U) ≤ I(X₁;X₂|Y,B,U)}. Here p = p(u,x₁,x₂)·p(y|x₁,x₂)·p_B(b|x₁,x₂,y), the channel p_B
may depend on p(x₁,x₂|u), and |U| ≤ |X₁||X₂| + 2. For the BMC the parallel channel is:

| (x₁,x₂,y) | P(B=0) | P(B=1) |
|---|---|---|
| (0,0,0) | p | 1−p |
| (0,1,0) | 0 | 1 |
| (1,0,0) | 1 | 0 |
| (1,1,1) | B = ∗ (constant) | |

*I(X₁;X₂|Y,B,U) = 0.* Given Y = 1, both inputs are 1. Given Y = 0 and B = 1, X₁ = 0. Given
Y = 0 and B = 0, X₂ = 0. So DB forces I(X₁;X₂|U) = 0. Let α = P(X₁=1|u), β = P(X₂=1|u), and
h = binary entropy. Then

- I(X₁;YB|X₂,u) = β·h(α) + (1−β)·[h((1−α)(1−p)) − (1−α)·h(p)],
- I(X₂;YB|X₁,u) = α·h(β) + (1−α)·[h((1−β)p) − (1−β)·h(p)].

The leak terms are the brackets. Setting the derivative of the leak sum in p to zero gives
p = α(1−β)/((1−α)β + α(1−β)). This is Bloemen's eq. (6.58) up to the B-label convention. The
U-free terms are I(X₁;Y|X₂) = P₂·h(P₁₁/P₂) and I(X₂;Y|X₁) = P₁·h(P₁₁/P₁) for the mixture,
where P₁ = Σw·α, P₂ = Σw·β and P₁₁ = Σw·αβ. ∎

### 5. Numerics for the HW bound

`code/hw_parallel_bound.py 4 60 1` runs SLSQP with an epigraph variable and 60 random restarts
for each |U|:

| \|U\| | value | optimiser (w; α; β) |
|---|---|---|
| 1 | 0.6169486 | Shannon inner bound, α = β = 0.70351 |
| 2 | 0.6458869 | (½,½); (0.8635, 0.5408); (0.5408, 0.8635) |
| 3 | **0.6462832** | (0.16437, 0.67127, 0.16437); (0.96851, 0.71026, 0.39818); (0.39818, 0.71026, 0.96851) |
| 4, 5, 6 | 0.6462832 | same support |

At the optimum all four terms are equal. `code/hw_dual_check.py` computes
min over λ and t₀ of the grid maximum of λ/2·(r₁+r₂) + (1−λ)/2·(tangent planes of the concave
U-free terms). It returns 0.6462831 at λ = 0.2906, t₀ = 0.6635, so the primal–dual gap is at
grid resolution. Hekstra–Willems' published value is 0.64628.

### 6. Literature status (what the Markdown should say)

| bound | value | source |
|---|---|---|
| Shannon inner (independent inputs) | 0.61695 (P(X=1) = 0.70351) | Shannon 1961 |
| Hagelbarger strategy | 4/7 = 0.5714 (uniform); 0.59305 optimised | Shannon 1961; Bloemen 1996 §1 |
| Schalkwijk 1982 | 0.61914 | IEEE TIT 28(1) |
| Schalkwijk 1983 (bootstrapping / Slepian–Wolf) | 0.63056 (0.6305552557) | IEEE TIT 29(3); rigorous proof Tolhuizen 1985 |
| Schalkwijk 1990, 1991 | 0.6305552986, 0.6305552995 | BeNeLux Symp. 1990; ISIT 1991 (via Bloemen 1996, eq. 6.1) |
| Schalkwijk–Meeuwissen–Bloemen | **0.63072** | Tijdschr. NERG 60(3) 1995; ISIT 1995 Whistler; Bloemen 1996 eq. (6.42) |
| Ardestanizadeh, directed-information inner bound | 0.6191 | UCSD PhD thesis (as reported by Kim 2012) |
| Sabag–Permuter, graph-based single-letter region | > 0.61695 (beats Shannon inner) | Allerton 2018 |
| Shannon outer | log₂φ = 0.69424 | Shannon 1961 |
| plain DB (the Lean functional) | log₂φ = 0.69424 (vacuous) | this file; Bloemen 1996 §6.4.2 |
| Zhang–Berger–Schalkwijk | 0.64891 | IEEE TIT 32(3) 1986 |
| HW DB + adaptive parallel channel | **0.64628** | IEEE TIT 35(1) 1989; optimal among binary adaptive parallel channels (Tandon–Ulukus 2007) |

The Markdown's line "Subsequent refinements (Meeuwissen 1998; Kramer 1998; Chaaban–Sezgin)
slightly improved … 0.63056–0.6307" is inaccurate. The 0.63072 improvement is due to
Schalkwijk, Meeuwissen and Bloemen (1995). I found no BMC rate improvement attributed to Kramer
1998 or to Chaaban–Sezgin.

### Catalog error and proposed corrected statement

**Error.** `bmcDependenceBalanceBound` (the plain DB functional) equals log₂φ (Claim 2), so
`Statement` asserts C_sym = log₂φ, which is refuted by ZBS 1986 and HW 1989. Proposed fix: keep
`bmcSymmetricCapacity` and replace the bound by the HW parallel-channel bound in the closed
form of Claim 4. This needs only `binaryEntropy` and finite sums. Proposed text, for a
statement-fix PR (not applied here):

```lean
/-- Leak-minimising crossover of the Hekstra–Willems adaptive parallel channel for the BMC
    (Bloemen 1996, Table 6.2 / eq. (6.58)); `α = P(X₁=1|u)`, `β = P(X₂=1|u)`.
    (Lean's `x / 0 = 0` only fires at α = β ∈ {0,1}, where the leak vanishes for every p.) -/
noncomputable def hwCrossover (α β : ℝ) : ℝ :=
  α * (1 - β) / ((1 - α) * β + α * (1 - β))

/-- Hekstra–Willems (1989) dependence-balance bound with adaptive parallel channel, for the
    equal-rate point of the BMC, in closed form (the DB constraint forces `X₁ ⊥ X₂ | U`).
    Evaluates to ≈ 0.64628 bits. -/
noncomputable def bmcHWParallelChannelBound : ℝ :=
  sSup { r : ℝ | ∃ (k : ℕ) (w α β : Fin k → ℝ),
    (∀ u, 0 ≤ w u) ∧ (∑ u, w u) = 1 ∧
    (∀ u, 0 ≤ α u ∧ α u ≤ 1) ∧ (∀ u, 0 ≤ β u ∧ β u ≤ 1) ∧
    let p : Fin k → ℝ := fun u => hwCrossover (α u) (β u)
    let r₁ := ∑ u, w u * (β u * binaryEntropy (α u) + (1 - β u) *
      (binaryEntropy ((1 - α u) * (1 - p u)) - (1 - α u) * binaryEntropy (p u)))
    let r₂ := ∑ u, w u * (α u * binaryEntropy (β u) + (1 - α u) *
      (binaryEntropy ((1 - β u) * p u) - (1 - β u) * binaryEntropy (p u)))
    let P₁ := ∑ u, w u * α u
    let P₂ := ∑ u, w u * β u
    let P₁₁ := ∑ u, w u * (α u * β u)
    r = min (min r₁ (P₂ * binaryEntropy (P₁₁ / P₂)))
            (min r₂ (P₁ * binaryEntropy (P₁₁ / P₁))) }

def Statement : Prop :=
  bmcSymmetricCapacity = bmcHWParallelChannelBound
```

A second, more literal option keeps an explicit auxiliary output `B` with the adaptive kernel
of Table 6.2 and the DB inequality `I(X₁;X₂|U) ≤ I(X₁;X₂|Y,B,U)`. It is equivalent by Claim 4
but needs conditional marginals inside the kernel. A certificate for the fixed statement could
prove `bmcHWParallelChannelBound ≥ 0.6462` from the explicit |U| = 3 point of Details §5 using
interval bounds on `binaryEntropy`. The upper side (≤ 0.6463) needs the dual argument made
rigorous.

## Verification

- Claim 2: `code/db_vacuous.py` (mpmath, 60 digits) evaluates the exact Lean `condMutualInfo`
  formula at kZ = 1 and p*. A 400×400×400 grid scan of
  max ½[H(Y|X₁)+H(Y|X₂)] returns 0.694239 against log₂φ = 0.694242. Runtime < 1 s.
- Claim 5: `code/hw_parallel_bound.py 4 60 1` (seed 1, 60 SLSQP restarts per |U|, about 2 min).
  The |U| = 5, 6 runs used 40 restarts each, seed 7, and gave 0.6462831536849.
  `code/hw_dual_check.py` (2001² grid, about 3 min) gives dual 0.6462831.
- Literature: the statements attributed to Bloemen (1996) were read in the thesis PDF from
  TU/e Pure; the Tandon–Ulukus (2007) abstract was read on the Univ. of Arizona portal; Kim's
  2012 Banff slides and Tandon's 2010 thesis were read in full text; Willems' July 2026 CUHK
  slides were read in full text. I could **not** access HW 1989, ZBS 1986, SMB 1995 or
  Ardestanizadeh's thesis directly; their numbers are quoted as reported by the sources above.

## Dead ends

- *Plain DB as stated in the catalog.* The Shannon outer-bound optimiser already satisfies the
  constraint: I(X₁;X₂) = 0.156 < I(X₁;X₂|Y) = 0.553. The plain DB bound therefore cannot
  improve log₂φ for the BMC, for any auxiliary Z. The obstruction is that conditioning on Y = 0
  makes the inputs perfectly anti-correlated, so a lot of dependence is "produced" without being
  usable. Willems' July 2026 slides (slide 34) print "0.64628" directly under the plain DB
  theorem. That is a presentational shortcut, and Bloemen §6.4.2 is explicit that the plain
  bound gives nothing here.
- I did not attempt a rigorous (interval) certification of the HW dual upper bound. The value
  0.64628 is a published result and was not the point of the audit.

## Novelty check

Claims 1–2 are elementary, and Claim 2 is stated in words in Bloemen (1996, §6.4.2); they are
not new. The new points in this file are three: (i) the catalog's Lean functional is exactly
the vacuous bound, which makes the frozen statement false; (ii) the closed-form reduction of
the HW parallel-channel bound (Claim 4), which I have not seen written in this form in the
sources I could read; (iii) its independent numerical reproduction. Searches (Nov 2026):
"binary multiplying channel" with 0.64628, 0.63072, "dependence balance", "parallel channel",
"directed information", "Q-graph"; Hekstra–Willems abstract; Tandon–Ulukus; Gohari–Kramer
arXiv:2009.14814; Sabag–Permuter; Weng–Alajaji–Linder. None of these reports a bound below
0.64628 or above 0.63072. Gohari and Kramer (Remark 15 and the conclusion of arXiv:2009.14814)
list adaptive auxiliary receivers as an open direction for strengthening DB bounds. That is
the most natural route to a better converse.

## References

- C. E. Shannon, "Two-way communication channels," Proc. 4th Berkeley Symp., vol. 1,
  pp. 611–644, 1961.
- J. P. M. Schalkwijk, IEEE Trans. IT 28(1):107–110, 1982; IEEE Trans. IT 29(3):445–448, 1983;
  "Another 0.63056," Proc. 11th BeNeLux Symp. Inf. Theory, pp. 155–161, 1990; "Extending the
  achievable rate region of the binary multiplying channel," Proc. ISIT, p. 302, Budapest, 1991.
- L. Tolhuizen, "Discrete coding for the BMC, based on Schalkwijk's strategy," Proc. 6th
  BeNeLux Symp. Inf. Theory, pp. 207–212, 1985.
- J. P. M. Schalkwijk, H. B. Meeuwissen, A. H. A. Bloemen, "New results on a fundamental
  problem in network information theory," Tijdschrift van het NERG 60(3), 1995; and
  H. B. Meeuwissen, J. P. M. Schalkwijk, A. H. A. Bloemen, "Extension of the achievable rate
  region of Schalkwijk's 1983 coding strategy for the binary multiplying channel," Proc. IEEE
  ISIT, Whistler, 1995 (equal-rate point 0.63072).
- A. H. A. Bloemen, *Discrete Coding Strategies for Two-Way Channels*, PhD thesis, TU
  Eindhoven, 1996, doi:10.6100/IR463500. §6.4 (ZBS, plain DB is vacuous for the BMC, Thm 6.3
  and Table 6.2: HW parallel channel; Table 6.3: bounds).
- Z. Zhang, T. Berger, J. P. M. Schalkwijk, IEEE Trans. IT 32(3):383–386, 1986.
- A. P. Hekstra, F. M. J. Willems, "Dependence balance bounds for single-output two-way
  channels," IEEE Trans. IT 35(1):44–53, 1989 (not accessed directly).
- R. Tandon, S. Ulukus, "On dependence balance bounds for two way channels," Proc. 41st
  Asilomar Conf., pp. 868–872, 2007, doi:10.1109/ACSSC.2007.4487342 (abstract read).
- R. Tandon, *Capacity Bounds for Multi-User Channels with Feedback, Relaying and
  Cooperation*, PhD thesis, Univ. of Maryland, 2010, Sec. 2.5.
- Y.-H. Kim, "On the role of interaction in network information theory," slides, Banff,
  Jan. 2012 (BMC slide: "DB bound + channel augmentation (Hekstra–Willems): C_sym ≤ 0.6463";
  Ardestanizadeh 0.6191).
- O. Sabag, H. H. Permuter, "An achievable rate region for the two-way channel with common
  output," Proc. Allerton 2018, pp. 527–531, doi:10.1109/ALLERTON.2018.8635930 (abstract read).
- A. Gohari, G. Kramer, "Dependence balance and capacity bounds for multiterminal
  communication and wiretap channels," arXiv:2009.14814 (v4).
- F. M. J. Willems, "Single-output two-way channels and the dependence balance bound,"
  lecture slides, CUHK, 6–7 July 2026.
- Prior attempts in `attempts/binary-multiplier-two-way-channel/`: none existed.
