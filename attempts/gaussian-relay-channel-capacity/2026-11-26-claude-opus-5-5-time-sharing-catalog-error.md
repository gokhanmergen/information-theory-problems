---
problem: gaussian-relay-channel-capacity
date: 2026-11-26
attempter: claude
model: claude-opus-5-5
type: partial-result
status: unverified
---

## Summary

**The frozen Lean `Statement` is false, and the reason was already known in 2006. That makes it
a catalog error.** `gaussianHybridDFCFRate` is the Gaussian hybrid DF/CF rate with *no
time-sharing*. The formal operational model allows bursty signalling (a per-codeword source
constraint and a per-message *expected* relay constraint), so any rate of the form
λ·R(P₁/λ, P₂/λ) is achievable. Lemma 1 below shows that when g₁₂² ≤ g₁₃² the formal hybrid
rate is *exactly* the closed-form Gaussian compress-forward (CF) rate. El Gamal–Mohseni–Zahedi
(EMZ 2006, eq. (8)) noted that this rate is not concave in P and improved it by bursting.
Exact integer arithmetic certifies, at unit gains with P₁ = 10⁻³ and P₂ = 10⁻¹:

  C_Gauss ≥ (1/200)·log₂(333/280) = 0.0012505 > 0.0007864 = ½·log₂(551601/551000) = R_hyb  (ratio 1.59).

A second certificate uses only the *point-to-point* AWGN coding theorem and no relay coding
theorem. At unit gains with P₁ = P₂ = 1/10, EMZ's block-length-2 linear relaying scheme
(their Example 1) achieves 0.088283 > 0.073779 = R_hyb. The same scheme also beats the obvious
repair: we prove that the **upper concave envelope** of R_hyb over power allocations is at most
0.77135·t along P₁ = P₂ = t, while bursty linear relaying achieves 0.88283·t for every
t ∈ (0, 1/10]. Any repair of the form "capacity = (Gaussian hybrid, possibly time-shared)" is
therefore known to be false. We propose how to re-pose the entry below.

## Approach

1. Audit `IsGaussianRelayAchievable` to see which strategies it admits.
2. Evaluate `gaussianHybridDFCFRate` *exactly* where possible. We first tried a branch-and-bound
   over (α, β, γ, θ, c). A monotonicity argument (Lemma 1) collapses the whole supremum to the
   closed-form CF rate when g₁₂² ≤ g₁₃², so no branch-and-bound is needed.
3. Compare with published achievable rates that the hybrid formula does not contain:
   time-shared CF (EMZ eq. (8)) and EMZ Example 1 linear relaying.
4. For the repaired statement (concave envelope), prove a global supporting line for R_CF and
   compare it with bursty linear relaying.

Notation: C(s) = ½·log₂(1+s), m = 1/(2 ln 2), s₁₂ = g₁₂²P₁, s₁₃ = g₁₃²P₁, s₂₃ = g₂₃²P₂,
R_CF := C(s₁₃ + s₁₂s₂₃/(1+s₁₂+s₁₃+s₂₃)). C_Gauss is `gaussianRelayCapacity` and R_hyb is
`gaussianHybridDFCFRate` (identified with its real value when finite).

## Claims

1. **[proved]** *(Model audit + burst lemma.)* In `IsGaussianRelayAchievable` the source
   constraint holds per codeword and the relay constraint is a per-message expectation over the
   relay noise. The relay is strictly causal and measurable. Consequently, if every R' < R₀ is
   achievable at powers (P₁/λ, P₂/λ) for some λ ∈ (0,1], then every R < λR₀ is achievable at
   (P₁, P₂). EMZ 2006 (Sec. 2, code definition "as in" Cover–El Gamal 1979) use a stricter
   model: the source constraint per codeword and relay power bounded for *every* y₁ⁿ. Their
   codes are therefore admissible here, and their achievability results carry over.
2. **[proved]** *(Lemma 1.)* If g₁₂² ≤ g₁₃² and P₁, P₂ ≥ 0, then
   `gaussianHybridDFCFRate g₁₂ g₁₃ g₂₃ P₁ P₂ = ENNReal.ofReal R_CF`.
3. **[proved]**, modulo the Gaussian CF achievability theorem (EMZ eq. (7); Cover–El Gamal 1979
   Thm 6 extended to AWGN). At (g₁₂,g₁₃,g₂₃,P₁,P₂) = (1,1,1,10⁻³,10⁻¹):
   C_Gauss ≥ (1/200)log₂(333/280) ≈ 0.00125048 > ½log₂(551601/551000) ≈ 0.00078638 = R_hyb.
   At the coordinator's point (1,1,3,1/20,1/20) with λ = 3/10:
   C_Gauss ≥ (3/20)log₂(64/51) ≈ 0.0491362 > ½log₂(33/31) ≈ 0.0450989 = R_hyb.
   **Hence `¬ Statement`.**
4. **[proved]**, with the same dependence. For all gains with 0 < g₁₂² ≤ g₁₃² and g₂₃ ≠ 0, and
   every direction (p₁, p₂) > 0 with 2g₁₂²g₂₃²p₂ > g₁₃⁴p₁, there is t₀ > 0 such that
   C_Gauss(tp₁, tp₂) > R_hyb(tp₁, tp₂) for all 0 < t < t₀. With unit gains this covers
   P₁ = P₂ = t (numerically, for t < 0.1104).
5. **[proved]**, modulo only Shannon's AWGN coding theorem with a per-codeword power constraint
   (Cover–Thomas Thm 9.1.1). At unit gains with P₁ = P₂ = 1/10, EMZ Example 1 with β = 2/3 is
   admissible in the formal model and achieves
   r_L = ¼·log₂(1 + SNR) ∈ [0.0882828331677, 0.0882828331678]. This exceeds
   R_hyb = ½log₂(72/65) ≈ 0.0737786. This gives a second, relay-coding-free refutation of the
   Statement.
6. **[proved]** *(Supporting line.)* For unit gains and all x₁, x₂ ≥ 0,
   R_hyb(x₁, x₂) = R_CF(x₁, x₂) ≤ x₁/(2 ln 2) + x₂/20. Hence the upper concave envelope
   conc R_hyb(P₁,P₂) := sup{Σwᵢ R_hyb(P₁ᵢ,P₂ᵢ) : wᵢ ≥ 0, Σwᵢ = 1, ΣwᵢP₁ᵢ ≤ P₁, ΣwᵢP₂ᵢ ≤ P₂}
   satisfies conc R_hyb(t,t) ≤ (m + 1/20)·t ≈ 0.7713475·t for all t ≥ 0.
7. **[proved]**, modulo the AWGN coding theorem. For every t ∈ (0, 1/10],
   C_Gauss(1,1,1,t,t) ≥ 10·r_L·t ≈ 0.8828283·t > 0.7713476·t ≥ conc R_hyb(t,t). So the
   minimal repair "capacity = concave envelope of the hybrid rate" is also false.
8. **[heuristic]** *(Numerical, multistart local search.)* Consider Gaussian CF with a *coded*
   time-sharing variable Q, where each rate constraint is averaged over Q separately (El
   Gamal–Kim form). At unit gains and P₁ = P₂ = t → 0, its slope is ≈ 0.781. That is above the
   naive envelope but well below 0.8828. The Q-repair is therefore very likely also beaten by
   EMZ Example 1 at low SNR. Not certified: the search is not global, and the DF parts of the
   hybrid were not included in the Q-version.
9. **[conjectural]** *(Corrected statement.)* No statement of the form
   "C_Gauss = (single-letter Gaussian DF/CF/hybrid rate, with or without time-sharing)" is a
   faithful *open* problem: by Claims 3, 5, 7 and 8 the answer is known to be (or is very
   likely) negative. A faithful replacement must ask about a quantity whose value is genuinely
   unknown. See "Proposed corrected Statement" for concrete Lean text.

## Details

### 1. Audit of `IsGaussianRelayAchievable` and the burst lemma

From `lean/InfoTheory/Problems/GaussianRelayChannelCapacity.lean`:

* **Source:** `∀ m, ∑ i, (enc m i)^2 ≤ n * P₁`. This is per codeword, and silent symbols
  contribute 0.
* **Relay:** `∀ m, ∫⁻ zr, ofReal((∏ᵢ φ(zrᵢ)) · ∑ᵢ (relay i (yr|_{<i}))²) ≤ ofReal(n P₂)`, where
  φ = `gaussianPdf1D 1` is the N(0,1) density. This is the expected relay energy for message m
  over the relay noise. It is *weaker* than the "for all y₁ⁿ" constraint of EMZ 2006 (Sec. 2)
  and admits linear relaying, whose output is unbounded.
* **Causality:** `relay i : (Fin i.1 → ℝ) → ℝ` is applied to `yr` at indices j < i, so the relay
  is strictly causal. `relay i` and `dec` are required to be measurable.
* **Error:** average over messages. Codes are required for **every** n ≥ N, with
  M = max(1, ⌊2^{nR}⌋).

*Burst lemma (proof).* Fix R < λR₀ and pick R' ∈ (R/λ, R₀), so R' is achievable at
(P₁/λ, P₂/λ). Given n, set k = ⌊λn⌋. For n large, k ≥ N'(ε) and kR' ≥ (λn−1)R' ≥ nR. Take the
length-k inner code with M' = max(1, ⌊2^{kR'}⌋) ≥ M messages. Keep the M messages with the
smallest conditional error; their average error is ≤ ε. Map the inner decoder's other outputs
to a fixed kept message. On symbols 1..k use the inner encoder and relay functions; the relay
at time i ≤ k reads only coordinates < i. On symbols k+1..n send 0 from both nodes. Source
energy ≤ k·P₁/λ ≤ nP₁. Expected relay energy ≤ kP₂/λ ≤ nP₂: by Tonelli, the integrand depends
only on the first k noise coordinates, and the others integrate to 1. The error integral
reduces to the inner one in the same way. Everything is a composition of the inner measurable
maps with coordinate projections. ∎

The same argument shows C_Gauss(P₁,P₂) ≥ λ·C_Gauss(P₁/λ, P₂/λ).

### 2. Proof of Lemma 1

Take any feasible (α, β, γ, θ, c, R₁, R₂). Let A, B₁, B₂, S be the right-hand sides of the four
constraints. Then R₁ + R₂ ≤ A + min(B₁, B₂), with:

* A = C(s₁₂β/(1+s₁₂γ)) ≤ C(s₁₂(1−γ)/(1+s₁₂γ)) = C(s₁₂) − C(γs₁₂), because β ≤ 1−α−γ ≤ 1−γ;
* B₂ ≤ C(a+d) − C(c), with a = γs₁₃, b = γs₁₂, d = s₂₃ (bound 1−θ ≤ 1), and B₁ = C(a + bc/(1+c)).

On c ≥ 0, B₁ is increasing and C(a+d) − C(c) is decreasing, with B₁(0) ≤ C(a+d). So
min(B₁, B₂) ≤ max_c min(…) = value at the crossing c* = d/(1+a+b), which is
C(a + bd/(1+a+b+d)). Hence R₁ + R₂ ≤ F(γ), where

  F(γ) = C(s₁₂) + ½log₂[ (1+γs₁₃)/(1+γs₁₂) + γ²s₁₂s₂₃ / ((1+γs₁₂)·D(γ)) ],  D(γ) = 1 + γ(s₁₂+s₁₃) + s₂₃.

If s₁₂ ≤ s₁₃, both summands inside the log are nondecreasing in γ:

* the first has derivative (s₁₃−s₁₂)/(1+γs₁₂)² ≥ 0;
* the second has logarithmic derivative 2/γ − (s₁₂+s₁₃)/D − s₁₂/(1+γs₁₂) > 2/γ − 1/γ − 1/γ = 0.

So sup F = F(1) = R_CF. The value R_CF is attained by α = β = θ = 0, γ = 1,
c = s₂₃/(1+s₁₂+s₁₃), R₁ = 0, R₂ = R_CF: all four constraints hold, the second and third with
equality, and S coincides with B₂ because α = θ = 0. The `sSup` over `{ofReal(R₁+R₂)}` is
therefore `ofReal R_CF`. ∎

`numerics.py N1` cross-checks Lemma 1 against brute-force optimisation of the Lean formula at 8
random points with g₁₂ < g₁₃; the differences are ≤ 1e-14. It also shows that the hybrid is
*strictly* larger than CF at 3 random points with g₁₂ > g₁₃, so Lemma 1 does not extend to that
case.

### 3. Certificate A (bursty CF)

Achievability theorem used: for every P, P₂ > 0, every rate below R_CF(P, P₂) is achievable on
the AWGN relay channel. Sources: EMZ 2006 eq. (7), in their normalisation g₁₃ = 1, a = g₁₂,
b = g₂₃, γP = P₂, N = 1; it is obtained there from Cover–El Gamal 1979 Thm 6 with jointly
Gaussian (X, X₁, Ŷ₁). Their codes satisfy the stricter "for all y₁ⁿ" relay constraint. With
Claim 1 this gives C_Gauss(P₁,P₂) ≥ λR_CF(P₁/λ, P₂/λ), which is EMZ eq. (8) verbatim.

*Headline point* (1,1,1,10⁻³,10⁻¹), λ = 1/100. By Lemma 1 R_hyb = ½log₂ F_h with
F_h = 1 + 10⁻³ + 10⁻⁴/1.102 = 551601/551000. The burst powers (10⁻¹, 10) give
F_b = 1 + 1/10 + 1/11.2 = 333/280. The claim λ·½log₂F_b > ½log₂F_h is equivalent to
333·551000¹⁰⁰ > 280·551601¹⁰⁰, which is checked in exact integers (`certify_catalog_error.py`, A1).
Values: 0.00125047675 vs 0.00078637676.

*Coordinator point* (1,1,3,1/20,1/20), λ = 3/10. F_h = 33/31 and F_b = 64/51; the claim is
equivalent to F_b³ > F_h¹⁰ (A2). Values: 0.0491362 vs 0.0450989. This confirms the
coordinator's Nelder–Mead numbers. At that point the hybrid optimum is pure CF (γ = 1), as
Lemma 1 predicts.

### 4. Proof of Claim 4

Fix λ ∈ (0,1) and let a = g₁₃²p₁, b = g₁₂²p₁, d = g₂₃²p₂. Then
ρ(t) := R_CF(tp) = m·ln(1 + x(t)) with x(t) = at + bd·t²/(1+(a+b+d)t). This is smooth near
t = 0, with x(0) = 0, x'(0) = a and x''(0) = 2bd, so ρ''(0) = m(2bd − a²).

Let φ(t) = λρ(t/λ) − ρ(t). Then φ(0) = φ'(0) = 0 and φ''(0) = (1/λ − 1)·m(2bd − a²) > 0. Since
φ'' is continuous, φ > 0 on some interval (0, t₀). By Claim 1 and the CF theorem,
C_Gauss(tp) ≥ λρ(t/λ) > ρ(t) = R_hyb(tp), using Lemma 1. ∎

At unit gains with P₁ = P₂ = P, numerics (`numerics.py N2`) put the largest P at which some
burst helps at P* ≈ 0.1104. The relative gain there is small, e.g. 2.2% at P = 10⁻³.

### 5. EMZ Example 1 in the formal model (Claim 5)

Let n' = ⌊n/2⌋, and let u(m) ∈ ℝ^{n'} be a codeword of a point-to-point AWGN code with
‖u(m)‖² ≤ n'·2βP₁. In super-symbol j (times 2j−1 and 2j):

* the source sends x_{2j−1} = u_j and x_{2j} = √((1−β)/β)·u_j;
* the relay sends 0 at time 2j−1 and d·y_{r,2j−1} at time 2j, with d² = 2P₂/(2g₁₂²βP₁+1);
* the last symbol, when n is odd, is silent.

The relay is strictly causal and linear, hence measurable.

*Power.* Source energy = ‖u‖²/β ≤ 2n'P₁ ≤ nP₁. Expected relay energy for message m is
d²(g₁₂²‖u(m)‖² + n') ≤ 2n'P₂ ≤ nP₂. Note this is a *per-message* bound, as the Lean model
requires; it holds because the codeword energy is controlled per codeword.

*Channel.* With unit gains, y_{2j−1} = u_j + z and y_{2j} = c·u_j + d·z_r + z', where
c = √((1−β)/β) + d. Maximal-ratio combining (a linear map) gives a scalar AWGN channel with
SNR = 2βP₁·(1 + c²/(1+d²)). The decoder is MRC followed by the AWGN decoder. By the AWGN coding
theorem every rate < ½log₂(1+SNR) per super-symbol is achievable, i.e. < r_L = ¼log₂(1+SNR)
per channel use. This is EMZ eq. (15).

At P₁ = P₂ = 1/10 and β = 2/3: d² = 3/17, c = 1/√2 + √(3/17), and
SNR ∈ [0.277330032922, 0.277330032923] in interval arithmetic (B1). The check
1 + SNR > (72/65)² is equivalent to r_L > R_hyb.

### 6. Supporting line for R_CF, unit gains (Claim 6)

Let y = x₁x₂/(1+2x₁+x₂). Then

  R_CF = m·ln(1+x₁+y) ≤ m·ln(1+x₁) + m·y/(1+x₁).

Write m·y/(1+x₁) = K·x₂/(D+x₂) with K = m x₁/(1+x₁) and D = 1+2x₁. A one-line computation
(substitute u = D + x₂ and minimise KD/u + μ₂u over u ≥ D) gives

  sup_{x₂≥0} [K x₂/(D+x₂) − μ₂x₂] = (√K − √(μ₂D))₊².

So R_CF − m x₁ − μ₂x₂ ≤ Φ(x₁) := (√K − √(μ₂D))₊² − m(x₁ − ln(1+x₁)), and it suffices to show
Φ ≤ 0 on [0, ∞). Take μ₂ = 1/20. The positive part vanishes iff
q(x) = 2μ₂x² + (3μ₂ − m)x + μ₂ ≥ 0. The function q is a convex quadratic with q(0.08) > 0,
q(6) > 0 and its vertex in (0.08, 6), so Φ ≤ 0 off [0.08, 6] (check B2a). On [0.08, 6],
interval branch-and-bound proves Φ ≤ 0 (B2b). It uses the upper bound
(√K(u) − √(μ₂D(l)))₊² − m(l − ln(1+l)) on each [l, u], which is valid because K, D and
x − ln(1+x) are increasing. It needs 14 leaf intervals, and the largest leaf bound is −2.97e-4.

Because R_hyb = R_CF at all power pairs for unit gains (Lemma 1), any convex combination
satisfies Σwᵢ R_hyb(xᵢ) ≤ Σwᵢ(m x₁ᵢ + x₂ᵢ/20) ≤ m P₁ + P₂/20. ∎

The value 1/20 is a convenient choice. The best μ₂ for this relaxation is ≈ 0.0392, giving
slope 0.7606. A grid dual on R_CF itself gives ≈ 0.758 (`numerics.py N3`).

### 7. Separation (Claim 7)

For t ∈ (0, 1/10], burst the Claim-5 code from powers (1/10, 1/10) with λ = 10t (Claim 1). This
gives C_Gauss(1,1,1,t,t) ≥ 10t·r_L. Check B3 gives 10·r_L > 0.88282833 > 0.77134753 ≥ m + 1/20,
rigorously. ∎

Even without bursting, at t = 1/10 we get 0.088283 > 0.077135 ≥ conc R_hyb(1/10, 1/10).

### 8. Coded time-sharing (Claim 8)

`numerics.py N4` maximises, as t → 0, the CF rate with constraints averaged over Q:
R ≤ Σwᵢ C(aᵢ + aᵢcᵢ/(1+cᵢ)) and R ≤ Σwᵢ[C(aᵢ+bᵢ) − C(cᵢ)], subject to Σwᵢaᵢ ≤ 1 and
Σwᵢbᵢ ≤ 1. Results: |Q| = 1 gives 0.7379 (= single-burst CF), |Q| = 2 gives 0.7806, and
|Q| = 3 gives 0.7793 (a local optimum).

The |Q| = 2 optimum is a "listen, then talk" structure. In a short slot the relay compresses
finely (c ≈ 2.5) while almost silent. In a long low-power slot it forwards the description.
This exceeds the naive-envelope bound 0.7713, so the Q-repair is a genuinely different
quantity. It is still far below Example 1's 0.8828.

### Low-SNR slopes (numerical summary, unit gains, powers (t, κt), t → 0)

| κ | envelope of R_CF (grid dual) | single-burst CF | single-burst EMZ Ex. 1 |
|---|---|---|---|
| 0.1 | 0.7231 | 0.7210 | 0.7521 |
| 1 | 0.7579 | 0.7371 | 0.8844 |
| 10 | 0.9977 | 0.9972 | 1.1289 |
| 100 | 1.2614 | 1.2612 | 1.3158 |
| 1000 | 1.3805 | 1.3798 | 1.3986 |

(Direct-link slope 0.7213; cutset slope 1.4427.) The grid dual enforces the constraints only at
grid points, so it is a *lower* estimate of the true envelope slope. Only the κ = 1 row is
certified (Claims 6–7, with the rigorous bound 0.7713).

## Novelty check

Sources consulted:

* The EMZ 2006 full text: the Stanford-hosted preprint
  `isl.stanford.edu/users/abbas/group/sina/WWW/papers/relay_7.pdf`, read in full via pdftotext.
* The arXiv abstracts of Zhang–Jiang–Cui (arXiv:1003.0735), Kosut–Effros–Langberg
  (arXiv:2401.15495) and Wu–Özgür (arXiv:1510.04007).
* Search snippets for El Gamal–Gohari–Nair (arXiv:2101.11139).
* Web searches on "time-sharing compress-forward Gaussian relay", "minimum energy per bit
  Gaussian relay channel", and "capacity per unit cost relay channel".

What is **already known**:

* EMZ 2006 state that the Gaussian side-information (CF) rate is "not a concave function of P"
  and give the bursty bound (their eq. (8)), for exactly this full-duplex model. They also give
  Theorem 2 (CF with a time-sharing variable Q).
* EMZ Example 1 and Fig. 3 (a = 1, √γ·b = 2) show block-length-2 linear relaying beating both
  the generalized block-Markov rate and the Gaussian CF rate. Their Sec. 5.1 says Example 1 with
  time-sharing "usually" has lower minimum energy-per-bit than the side-information scheme.
* Zhang–Jiang–Cui 2010 (abstract) study time-sharing CF at low SNR.
* Kosut–Effros–Langberg 2024 (abstract) report rank-1 linear relaying beating "2-dimensional"
  schemes such as Example 1.

So the *phenomena* are known. As far as I can tell the following are new, though small:

* Lemma 1, the exact identity R_hyb = R_CF for g₁₂² ≤ g₁₃². I did not find it in EMZ, who
  compare against the generalized block-Markov bound, not against the Thm-7 hybrid.
* The check against the exact Lean definitions.
* The exact and interval certificates.
* The certified refutation of the concave-envelope repair.

None of this is claimed as a contribution to the capacity question itself.

## Proposed corrected Statement

**Diagnosis.** The current `Statement` asks whether C_Gauss equals a specific single-letter
Gaussian achievable rate. Its answer is "no", for reasons in the 2006 literature. Its "natural"
repairs fail as well:

* **S1 (concave envelope; refuted by Claim 7):**

```lean
noncomputable def gaussianHybridEnvelope (g₁₂ g₁₃ g₂₃ P₁ P₂ : ℝ) : ℝ≥0∞ :=
  sSup { r | ∃ (k : ℕ) (w p₁ p₂ : Fin k → ℝ),
      (∀ i, 0 ≤ w i ∧ 0 ≤ p₁ i ∧ 0 ≤ p₂ i) ∧ ∑ i, w i = 1 ∧
      ∑ i, w i * p₁ i ≤ P₁ ∧ ∑ i, w i * p₂ i ≤ P₂ ∧
      r = ∑ i, ENNReal.ofReal (w i) * gaussianHybridDFCFRate g₁₂ g₁₃ g₂₃ (p₁ i) (p₂ i) }
-- Statement_S1 : ∀ g₁₂ g₁₃ g₂₃ P₁ P₂, 0 < P₁ → 0 < P₂ →
--   gaussianRelayCapacity g₁₂ g₁₃ g₂₃ P₁ P₂ = gaussianHybridEnvelope g₁₂ g₁₃ g₂₃ P₁ P₂
-- FALSE at (1,1,1,t,t) for every t ∈ (0, 1/10]  (Claims 6–7).
```

* **S2 (coded time-sharing Q inside the hybrid):** very likely false for the same reason
  (Claim 8, heuristic).

**Recommendation.**

* **(a)** Record the present Statement as a catalog error. It is settled negatively by EMZ 2006
  eq. (8) together with Lemma 1, or by EMZ Example 1 together with the AWGN coding theorem. A
  Lean `statement_false` certificate needs either Gaussian CF achievability or point-to-point
  AWGN achievability. `Known/GaussianChannel.lean` currently has only the converse and a
  BPSK/BSC positive-rate result. Hard-decision BPSK is too weak for Claim 5 (see Dead ends).
  A finely quantised BPSK version of Example 1, combined with the DMC coding theorem in
  `Bridge`, should suffice: unquantised BPSK already reaches slope ≈ 0.884. I did not check
  this (heuristic).
* **(b)** Re-pose the open entry around a quantity whose value is genuinely unknown. One
  candidate that is faithful to the "exact capacity" spirit and expressible with the existing
  `gaussianRelayCapacity` is the low-SNR slope (minimum energy-per-bit) of the symmetric
  channel:

```lean
/-- Is the cutset low-SNR slope 1/ln 2 (in bits per unit power) achieved by the unit-gain
    Gaussian relay channel with equal powers? Known: liminf ≥ 0.8828 (EMZ Ex. 1 + bursting,
    certified in attempts/gaussian-relay-channel-capacity/), limsup ≤ 1/ln 2 (cutset). -/
def Statement : Prop :=
  Filter.Tendsto (fun P : ℝ => gaussianRelayCapacity 1 1 1 P P / ENNReal.ofReal P)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds (ENNReal.ofReal (1 / Real.log 2)))
```

  Caveat: EMZ 2006 and Kosut–Effros–Langberg 2024 treat the minimum energy-per-bit as open.
  I could **not** confirm that no converse strictly below the cutset slope is known; EGN 2022's
  strengthened bound might give one. Maintainers should verify before adopting this.
  Alternatively, keep a "does scheme X achieve capacity?" entry only for a scheme class that is
  not already beaten by a published scheme.

## Verification

* `code/certify_catalog_error.py` takes under 1 s and prints PASS/FAIL. It covers A1 and A2
  (exact integers), B1 (interval r_L vs R_hyb), B2a/B2b (supporting line: exact sign checks
  plus interval branch-and-bound) and B3 (slope separation). All pass with mpmath 60-digit
  interval arithmetic.
* `code/numerics.py` is non-rigorous and takes about 2 min. It covers N1 (Lemma 1 vs
  brute-force optimisation of the Lean formula), N2 (symmetric threshold), N3 (slope table),
  N4 (coded time-sharing) and N5 (BPSK variants of Example 1).
* The analytic parts (burst lemma, Lemma 1, Claim 4, the reduction in §6) are proved in this
  file and have not been independently reviewed. No Lean was written, per coordinator
  instructions.

## Dead ends

* **Branch-and-bound over (α,β,γ,θ,c)** was planned first. It is superseded by Lemma 1 for
  g₁₂² ≤ g₁₃². For g₁₂² > g₁₃², Lemma 1 fails (N1 shows hybrid > CF), and a certificate there
  would need the 4-D branch-and-bound. Not pursued, because one counterexample suffices.
* **Cutset-type upper bounds on R_hyb cannot certify the gap.** At the headline point, the
  broadcast cut C(s₁₂+s₁₃) = 0.001441 exceeds the bursty CF value 0.001250. The hybrid's
  internal compression constraint has to be used, which is what Lemma 1 does.
* **Naive concave envelope as the catalog repair** is refuted by Claims 6–7. The coded
  time-sharing (Q) repair is very likely refuted too (Claim 8).
* **Numerical pitfall.** A first run of the Q-slope search returned the cutset slope 1.4427.
  This was an artefact of evaluating log₂(1+a) for a ≈ 1e-16, where rounding doubles the value.
  Using `log1p` fixes it. Any low-SNR optimiser over this family must use `log1p`.
* **Hard-decision BPSK route to a Lean disproof** (reusing the BPSK→BSC reduction in
  `Known/GaussianChannel.lean`) fails numerically (`numerics.py N5`, diagonal grid search).
  Example 1 with hard-decision BPSK has slope at most ≈ 0.602, below the direct-link slope
  0.7213, and on the grid it never exceeds R_CF (max difference −2.4e-4). Unquantised BPSK
  (binary-input AWGN) gives slope ≈ 0.884, essentially the Gaussian 0.8849. So a
  *finely quantised* BPSK version plus the DMC coding theorem should be enough for a Lean
  `statement_false` (heuristic; not checked).

## References

- Prior attempts consulted: `attempts/relay-channel/*`, for format and EGN-evaluation
  conventions; their machinery is for the discrete primitive relay channel and is not used
  here. No earlier attempts exist for this problem.
- T. M. Cover and A. El Gamal, "Capacity theorems for the relay channel," IEEE Trans. IT 25(5),
  572–584, 1979 (Thm 6: compress-forward; Thm 7: hybrid). Not re-read; cited via EMZ.
- A. El Gamal, M. Mohseni, S. Zahedi, "Bounds on capacity and minimum energy-per-bit for AWGN
  relay channels," IEEE Trans. IT 52(4), 1545–1561, 2006. Preprint read in full. Used: Sec. 2
  (code definition, power constraints), eqs. (6)–(8), Theorem 2, Example 1 / eq. (15), Fig. 3,
  Sec. 5.1.
- L. Zhang, J. Jiang, S. Cui, "Compress-and-forward performance in low-SNR relay channels,"
  arXiv:1003.0735, 2010 (abstract only).
- O. Kosut, M. Effros, M. Langberg, "Nobody expects a differential equation: minimum
  energy-per-bit for the Gaussian relay channel with rank-1 linear relaying," arXiv:2401.15495,
  2024 (abstract only).
- A. El Gamal, A. Gohari, C. Nair, "A strengthened cutset upper bound on the capacity of the
  relay channel and applications," IEEE Trans. IT 68(7), 2022; arXiv:2101.11139 (search
  snippets only).
- T. M. Cover and J. A. Thomas, *Elements of Information Theory*, 2nd ed., Thm 9.1.1 (AWGN
  coding theorem).
- A. El Gamal and Y.-H. Kim, *Network Information Theory*, Cambridge, 2011, Ch. 16 (CF with
  time-sharing; Gaussian relay). Cited from memory for the Q-form only, not used in any proof.
