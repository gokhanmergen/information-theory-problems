---
problem: gaussian-interference-channel
date: 2026-11-26
attempter: claude
model: claude-opus-5-5
type: partial-result
status: verified
---

## Summary

**The frozen Lean `Statement` is false, so this is a catalog error.** The Lean set
`InGaussianHKRegion` is the *convex hull* of Gaussian Han–Kobayashi (HK) polytopes, with
power control across phases ("plain" time-sharing, i.e. TD/FD). It is not the HK region
with a time-sharing variable $Q$ ("coded" time-sharing, El Gamal–Kim Thm 6.4). The two
differ because coded time-sharing averages the three sum-rate bounds separately (a min of
averages), while plain time-sharing averages the per-phase minimum (an average of mins).

Example: $a=b=1/2$, $P_1=P_2=100$. Coded time-sharing of two Gaussian HK splits, each
phase at full power and the splits swapped between phases, achieves
$(R_1,R_2)=(1.96144,1.96144)$, i.e. sum rate $3.92288$. A branch-and-bound certificate
shows that **every** point of `InGaussianHKRegion 0.5 0.5 100 100` has
$R_1+R_2\le C(200)+0.01=3.83553$. So the closures of the achievable set and of the Lean
region differ.

The same computation contradicts the claim that "time-sharing and convexification result
in the same region" (Motahari–Khandani 2009, Thm 7) once their $\psi_3=\min\{\cdot\}$ is
split into its three sum bounds, as the HK theorem requires. Otherwise the formalization
passes every audit check:
- `InGaussianHKBasic` is the correct compact HK polytope, and all its points are achievable;
- $(a,b)$ enter only through $a^2,b^2$;
- the region reproduces all known exact results (strong, very strong, noisy-interference
  sum capacity, mixed sum capacity, both Z-channel corner points).

A corrected statement (coded time-sharing) is proposed below. It is equivalent to the open
"Gaussian signaling with power control is optimal for Han–Kobayashi" conjecture and is not
known to be false.

There is also a survey update for 2015–2026. Highlights:
- the Bustin–Poor–Shamai corner-point proof carries an author-acknowledged error on arXiv;
  Polyanskiy–Wu's proof stands;
- Liu 2022 shows Gaussian suboptimality only under constant power;
- Costa–Gohari–Nair–Ng prove the noiseberg conjecture;
- two unrefereed "full solution" claims exist: Vaezi–Poor (withdrawn) and Khandani.

## Approach

1. Audit `InGaussianHKBasic`, `InGaussianHKRegion` and `InGaussianICAchievable` line by
   line against the HK theorem (El Gamal–Kim Thm 6.4; Chong–Motani–Garg 2008), and against
   the known exact results.
2. The previous attempt (`2026-07-19-claude-scheduled.md`) listed "full HK with $Q$ and
   power control" as its next step. Compute the Lean region's sum rate exactly as defined:
   an upper concave envelope over phase powers, solved as an LP over a grid.
3. Compare plain time-sharing with coded time-sharing using the same Gaussian HK building
   blocks. Coded time-sharing of *swapped asymmetric* splits is the natural candidate,
   because asymmetric splits make different sum bounds bind in different phases.
4. Certify the separation. Give an explicit rate split for the coded point, which gives a
   direct achievability check. Then give a global affine majorant of the per-phase Gaussian
   HK sum rate, verified by interval branch-and-bound.
5. Survey the literature, with exact citations.

## Claims

1. **[proved]** *(Basic polytope.)* `InGaussianHKBasic a b P₁ P₂` is exactly the compact
   7-inequality HK polytope (El Gamal–Kim Thm 6.4, CMG 2008) for $X_i=U_i+V_i$ with
   independent Gaussian $U_i\sim N(0,P_{ic})$ and $V_i\sim N(0,P_{ip})$, with
   $P_{ic}+P_{ip}\le P_i$. Every point of it is achievable. That includes points violating
   the two inequalities $R_1\le I(X_1;Y_1|U_1,U_2)+I(X_2,U_1;Y_2|U_2)$ (and its mirror),
   which the compact form drops.
2. **[proved]** *(Sign/scaling.)* $a,b$ appear only as $a^2,b^2$. The channels $(a,b)$ and
   $(-a,-b)$ are equivalent by sign flips. Whether $(a,b)$ and $(a,-b)$ have the same
   capacity region is not addressed by any result I know, but the HK region and all
   standard outer bounds depend only on $a^2,b^2$, so this is not an error.
3. **[proved]** *(What the Lean region is.)* `InGaussianHKRegion` is the set of finite
   convex combinations $\sum_i w_i r^{(i)}$, where each $r^{(i)}\in{}$Basic$(p_1^{(i)},p_2^{(i)})$
   and $\sum_i w_ip_j^{(i)}\le P_j$. This is Motahari–Khandani's region $\mathcal G_2$
   ("convexification", TD/FD with power allocation). It is not the region with a
   time-sharing variable $Q$, where *each* of the seven right-hand sides is averaged over
   $Q$.
4. **[proved]** *(Catalog error.)* At $(a,b,P_1,P_2)=(\tfrac12,\tfrac12,100,100)$:
   (i) the symmetric pair $(1.961440,1.961440)$ is achievable by coded time-sharing of
   Gaussian HK. The phases are $Q\in\{1,2\}$ with probability $1/2$ each, full power, and
   private powers $(P_{1p},P_{2p})=(0,14)$ and $(14,0)$. (ii) Every point of
   `InGaussianHKRegion 0.5 0.5 100 100` satisfies $R_1+R_2\le C(200)+0.01=3.835526$.
   Hence
   `closure {achievable} ≠ closure {InGaussianHKRegion}`, and
   `InfoTheory.Problems.GaussianInterferenceChannel.Statement` is false.
5. **[proved]** *(Known results reproduced.)* The Lean region contains:
   - the strong-interference capacity region ($a^2,b^2\ge1$, all-common splits);
   - the very-strong region;
   - the TIN point, hence the noisy-interference sum capacity;
   - both corner points of the weak Z-channel, including Costa's "missing" corner
     $(C(P_1),C(a^2P_2/(1+P_1)))$, whose optimality Polyanskiy–Wu proved.

   It is contained in the capacity region, so its sum rate equals every known sum capacity.
   The code checks five instances numerically: noisy, strong, very strong, weak Z, mixed.
6. **[heuristic]** *(Extent of the defect.)* Coded time-sharing of swapped splits beats
   the numerically computed Lean envelope:
   - for $a\in[0.5,0.8]$ at $P=100$ and $P=1000$, by up to 0.155 bits;
   - for $a\in\{0.6,\,0.7071,\,0.8\}$ at $P=30$;
   - at $P=1000$, also for $a=0.4$.

   It does not beat it at $P\le10$ (table below).
7. **[heuristic]** *(Open grid points of the earlier attempt.)* At $(P,a)\in\{1,10\}\times\{0.5,\sqrt{1/2}\}$
   the Lean region's sum rate (time-sharing plus power control, asymmetric splits) equals
   $\max(\text{TIN},\text{TDM})$ to grid accuracy, and coded swaps do not improve on it.
   The earlier attempt expected that mixing HK with TDM under power control would help at
   $(10,\sqrt{1/2})$; that expectation is not borne out. The gaps to the ETW outer bound
   stay at $0.076/0.076/0.472/0.241$ bits.
8. **[proved]** *(On Motahari–Khandani 2009, Thm 7.)* Their region $\mathcal G$ puts
   $\psi_3=\min\{\psi_{31},\psi_{32},\psi_{33}\}$ inside the time-sharing average (their
   eqs. (8), (14)) (reviewer correction: these are eqs. (7) and (13) in arXiv:0801.1306v1,
   and eqs. (11) and (13) in tech report UW-ECE 2007-26; the content is as stated). For that $\mathcal G$, $\mathcal G=\mathcal G_2$ follows from their
   Theorem 1. The HK region with a time-sharing variable instead imposes
   $R_1+R_2\le\mathbb E_Q\psi_{3j}$ for each $j$. For it, "time-sharing = convexification"
   is false: Claim 4 is a witness, with $a=b=1/4$ in their power-gain convention.
9. **[sketch]** *(What the corrected statement means.)* With coded time-sharing, the
   corrected statement holds iff, for every $n$, the $n$-letter HK region with arbitrary
   inputs is contained in $n$ times the single-letter Gaussian HK region with power
   control. This uses that the multi-letter HK region is the capacity region, and Nair–Ng
   (IEEE TIT 65(3), 2019, Thm 2, as described by Liu 2022): temporally correlated Gaussian
   inputs do not enlarge Gaussian HK.
10. **[heuristic]** *(Survey verdict.)* No refereed result shows that any scheme
    (non-Gaussian inputs, randomized power control, multi-letter coding) strictly beats
    Gaussian HK with coded time-sharing and power control on the two-user Gaussian IC. The
    corrected statement is open.

## Details

### 1. Audit of `InGaussianHKBasic` (Claims 1–2)

With $N_1=1+a^2P_{2p}$ and $N_2=1+b^2P_{1p}$, the Gaussian values of the HK quantities are:
- $I(X_1;Y_1|U_2)=C(P_1/N_1)$;
- $I(X_1,U_2;Y_1)=C((P_1+a^2P_{2c})/N_1)$;
- $I(X_1;Y_1|U_1,U_2)=C(P_{1p}/N_1)$;
- $I(X_1,U_2;Y_1|U_1)=C((P_{1p}+a^2P_{2c})/N_1)$;
- the mirror images for receiver 2.

Substituting into El Gamal–Kim Thm 6.4 gives exactly the seven Lean inequalities. I
checked each one, including the $2R_1+R_2$ and $R_1+2R_2$ lines.

*Achievability of the compact form for a fixed distribution.* Simultaneous non-unique
decoding gives four constraints per receiver. Receiver 1:
- $R_{1p}\le a_1$;
- $R_{1c}+R_{1p}\le b_1$;
- $R_{1p}+R_{2c}\le c_1$;
- $R_{1c}+R_{1p}+R_{2c}\le d_1$;

where $a_1,b_1,c_1,d_1$ are the four receiver-1 quantities listed above. Receiver 2 is
symmetric. Fourier–Motzkin elimination yields the seven Lean inequalities plus
$R_1\le a_1+c_2$ and $R_2\le a_2+c_1$.

Suppose a pair satisfies the seven inequalities but $R_1>a_1+c_2$. Since
$d_2=I(U_2;Y_2)+c_2$ (because $U_2\perp Y_2\mid X_2,U_1$), the second sum bound forces
$R_2<I(U_2;Y_2)$. Use the same codebooks with $R_{1p}=R_{2p}=0$, and let receiver 2 treat
all of $X_1$ as noise, which needs only $R_2\le I(X_2;Y_2)$. Receiver 1's constraints
reduce to:
- $R_1\le b_1$;
- $R_2\le c_1$, which follows from $R_1+R_2\le c_1+c_2$;
- $R_1+R_2\le d_1$, which follows from $2R_1+R_2\le d_1+a_1+c_2$.

All are implied. The argument is linear in the mutual-information terms, so it also works
with $Q$ (every term averaged). The Gaussian channel with input cost is handled by the
standard discretization (El Gamal–Kim §3.4).

*Signs.* Flipping $X_1\to-X_1$ and $Y_1\to-Y_1$ maps $(a,b)\to(-a,-b)$. Any combination of
sign flips changes $a$ and $b$ by the same sign, so the sign of $ab$ is invariant. The
`InGaussianICAchievable` definition was also checked:
- per-codeword power $\sum_i x_i^2\le nP$;
- measurable decoders;
- average error over $(m_1,m_2)$ with independent noises via `lintegral`;
- $M_i=\max(1,\lfloor2^{nR_i}\rfloor)$;
- "for all large $n$".

All of these are standard.

### 2. The separation (Claims 3–4)

**Coded point.** Per-phase values in bits, phase 1 / phase 2 / average:

| term | phase 1 $(P_{1p},P_{2p})=(0,14)$ | phase 2 $(14,0)$ | average |
|---|---|---|---|
| $A_1=I(X_1;Y_1\mid U_2)$ | 2.268717 | 3.329106 | 2.798911 |
| $S_1=I(X_1,U_2;Y_1)+I(X_2;Y_2\mid U_1,U_2)$ | 4.357123 | 3.488640 | **3.922881** |
| $S_2$ (mirror) | 3.488640 | 4.357123 | **3.922881** |
| $S_3$ | 3.926221 | 3.926221 | 3.926221 |
| $D_1$ ($2R_1+R_2$) | 5.064642 | 6.707343 | 5.885992 |

In each phase alone the binding sum bound is $\min(S_1,S_2)=3.48864$. Coded time-sharing
needs only the averages, so the sum rate is $3.922881$.

**Direct check without the compact form.** An LP over the rate split
$(R_{1c},R_{1p},R_{2c},R_{2p})$ against the eight averaged receiver constraints returns
$(0.984718,0.976723,0.984718,0.976723)$, i.e. $R=1.961441$ per user. The minimum slack is
$0$, with $R_{1p}=\bar a_1=\tfrac12C(14)$ binding. This is HK with a time-sharing sequence
$q^n$ known to all terminals. Codebooks are conditionally Gaussian given $q_i$, with full
power in every phase, so no power control is involved.

**Certificate for the Lean region.** Let $x=(P_{1c},P_{1p},P_{2c},P_{2p})\ge0$ and let
$g(x)=\max\{R_1+R_2:\text{Basic}(x)\}$. By LP duality, $g(x)$ is the minimum of seven
linear forms in the seven right-hand sides:
$A_1+A_2$, $S_1$, $S_2$, $S_3$, $(A_1+D_2)/2$, $(D_1+A_2)/2$, $(D_1+D_2)/3$. Put
$c=1/(2\ln2\cdot201)$ and $L(x)=C(200)+c\,(\sum x-200)+\delta$ with $\delta=0.01$. If
$g\le L$ on $\mathbb R_+^4$, then for any Lean point
$R_1+R_2\le\sum_iw_ig(x^{(i)})\le\sum_iw_iL(x^{(i)})=L(\sum_iw_ix^{(i)})\le L(100,100)=C(200)+\delta$,
using $c\ge0$ and the averaged power constraints.

*Verification of $g\le L$.*
- **Tail.** For $\sum x\ge S_{\max}=1885$: $g\le C(p_1)+C(p_2)\le2C(s/2)\le L$. The last
  inequality is checked at $s=S_{\max}$ and propagates because $\frac{d}{ds}2C(s/2)<c$ for
  $s>400$.
- **Bounded part.** Every term is $C(n/d)$ with $n$ and $d$ affine with nonnegative
  coefficients in *disjoint* coordinates. So $C(n(\overline x)/d(\underline x))$ is an
  exact box upper bound. Bisection branch-and-bound on $[0,S_{\max}]^4$ certifies the
  inequality on all of $\{\sum x\le S_{\max}\}$, checking $54{,}515{,}574$ boxes in 7 s.
  Every box test requires a $10^{-9}$ margin.
- **Controls.** The same code fails for $\delta=-0.005$ near $(p_1,p_2)\approx(195,0.46)$,
  close to the TDM phase where $g=L-\delta$. It succeeds for $\delta=0.003$ (88.7M boxes).
  So the Lean region's sum rate is within $0.003$ of TDM's $C(200)=3.825526$.

### 3. Lean region sum rate at the earlier grid (Claim 7) and exact results (Claim 5)

From `gic_lean_region_sumrate.py` (envelope LP over a $33^2$ phase-power grid on
$[0,4P]^2$; inner split optimization by grid plus zoom; robust under $61^2$ on $[0,3P]^2$
and $49^2$ on $[0,6P]^2$):

| $P$ | $a$ | earlier inner best | Lean Basic, no TS | Lean region (TS+PC) | optimal phases | ETW outer | best TIN-PAM | best TIN on-off |
|---|---|---|---|---|---|---|---|---|
| 1 | 0.5 | 0.8480 | 0.8480 | 0.8480 | TIN | 0.9240 | 0.8430 | 0.8480 |
| 1 | $\sqrt{1/2}$ | 0.7925 | 0.7370 | 0.7925 | TDM $(2P,0),(0,2P)$ | 0.8685 | 0.7338 | 0.7370 |
| 10 | 0.5 | 2.1962 | 1.9475 | 2.1962 | TDM | 2.6684 | 1.9291 | 1.9475 |
| 10 | $\sqrt{1/2}$ | 2.1962 | 2.0850 | 2.1962 | TDM | 2.4372 | 1.5067 | 1.4948 |

Sum capacities checked, with the Lean-region sum rate minus the known value:
- noisy $(1;0.2)$: $+3\times10^{-15}$;
- strong $(10;1.5)$: $0$;
- very strong $(1;3)$: $0$;
- weak Z $(10;0.5,0)$: $0$;
- mixed $(10;1.5,0.5)$: $0$.

Z corner points, checked analytically:
- the TIN split gives $(C(P_1/(1+a^2P_2)),C(P_2))$;
- $P_{1p}=P_1$ with $P_{2c}=P_2$ gives $(C(P_1),C(a^2P_2/(1+P_1)))$. There the bounds
  $R_1+R_2\le C(P_1+a^2P_2)$ and $2R_1+R_2\le C(P_1+a^2P_2)+C(P_1)$ are tight and all other
  bounds are slack.

### 4. Extent of the phenomenon (Claim 6)

Coded swap at full power versus the Lean envelope (`--scan`):

| $P$ \ $a$ | 0.4 | 0.5 | 0.6 | 0.7071 | 0.8 |
|---|---|---|---|---|---|
| 30 | −0.340 | −0.050 | +0.023 | +0.021 | +0.010 |
| 100 | −0.000 | **+0.097** | +0.070 | +0.036 | +0.015 |
| 1000 | +0.102 | +0.155 | +0.088 | +0.042 | +0.018 |

The optimal swaps always make one user all-common in each phase. Mehanna–Marcos–Jindal
(Allerton 2010, arXiv:1010.2437) already observed that asymmetric splits help the
symmetric sum rate without time-sharing. The swap turns that asymmetry into a symmetric
gain. (Reviewer: the coded swap itself is not new. Sason, IEEE TIT 50(6), 2004, Table 1 and
eq. (32), time-shares swapped splits $(\alpha,\beta)/(\beta,\alpha)$ with $Q$ inside the HK
mutual informations; $\delta=1/2$ there is exactly this two-phase full-power scheme, and his
Fig. 2 shows it beating TDM/FDM at moderate interference and $P\gtrsim17$ dB. The
certified separation from the convex hull with power control, i.e. from the Lean region and
from Motahari–Khandani's $\mathcal G_2$, is not in any source the reviewer read. Costa–Nair,
ITA 2012, was not accessible.)

### 5. Proposed corrected statement (do not merge without a statement-fix PR)

Replace `InGaussianHKRegion` by Gaussian HK with a time-sharing variable and power control.
This is $\mathcal R_{\rm HK\text{-}GS}$ of Costa–Gohari–Nair–Ng (Def. 2), extended from the
Z-channel to the full IC:

```lean
def InGaussianHKRegion (a b P₁ P₂ R₁ R₂ : ℝ) : Prop :=
  0 ≤ R₁ ∧ 0 ≤ R₂ ∧
  ∃ (m : ℕ) (w P₁c P₁p P₂c P₂p : Fin m → ℝ),
    (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
    (∀ i, 0 ≤ P₁c i ∧ 0 ≤ P₁p i ∧ 0 ≤ P₂c i ∧ 0 ≤ P₂p i) ∧
    (∑ i, w i * (P₁c i + P₁p i) ≤ P₁) ∧ (∑ i, w i * (P₂c i + P₂p i) ≤ P₂) ∧
    let cap (s : ℝ) : ℝ := (1 / 2 : ℝ) * log2 (1 + s)
    let E (f : Fin m → ℝ) : ℝ := ∑ i, w i * f i
    let N₁ := fun i => 1 + a ^ 2 * P₂p i
    let N₂ := fun i => 1 + b ^ 2 * P₁p i
    R₁ ≤ E (fun i => cap ((P₁c i + P₁p i) / N₁ i)) ∧
    R₂ ≤ E (fun i => cap ((P₂c i + P₂p i) / N₂ i)) ∧
    R₁ + R₂ ≤ E (fun i => cap ((P₁c i + P₁p i + a ^ 2 * P₂c i) / N₁ i) + cap (P₂p i / N₂ i)) ∧
    R₁ + R₂ ≤ E (fun i => cap (P₁p i / N₁ i) + cap ((P₂c i + P₂p i + b ^ 2 * P₁c i) / N₂ i)) ∧
    R₁ + R₂ ≤ E (fun i => cap ((P₁p i + a ^ 2 * P₂c i) / N₁ i) + cap ((P₂p i + b ^ 2 * P₁c i) / N₂ i)) ∧
    2 * R₁ + R₂ ≤ E (fun i => cap ((P₁c i + P₁p i + a ^ 2 * P₂c i) / N₁ i) + cap (P₁p i / N₁ i)
                              + cap ((P₂p i + b ^ 2 * P₁c i) / N₂ i)) ∧
    R₁ + 2 * R₂ ≤ E (fun i => cap ((P₂c i + P₂p i + b ^ 2 * P₁c i) / N₂ i) + cap (P₂p i / N₂ i)
                              + cap ((P₁p i + a ^ 2 * P₂c i) / N₁ i))
```

This region contains the current one, because convex combinations of per-phase points
satisfy the averaged inequalities. It is achievable by Claim 1 with $Q$. It is therefore
sandwiched between the old (refuted) set and the capacity region. The docstring of
`InGaussianHKBasic` ("full convex hull is taken in InGaussianHKRegion") should also be
corrected.

### 6. Survey 2015–2026 (exact citations; Claim 10)

- **Corner points.**
  - Polyanskiy–Wu, "Wasserstein continuity of entropy and outer bounds for interference
    channels," IEEE TIT 62(7):3992–4002, 2016 (arXiv:1504.04419), settle Costa's 1985
    "missing corner point".
  - Rioul, "At every corner: determining corner points of two-user Gaussian interference
    channels," arXiv:1607.02699, gives an alternative proof.
  - Bustin–Poor–Shamai, "The effect of maximal rate codes on the interfering message
    rate," arXiv:1404.6690. Its v5 arXiv comment says the version "has an error in the
    extension of the I-MMSE relationship to the limit". The follow-up arXiv:1510.08213
    re-derives the I-MMSE-like relation by an incremental-channel argument. I did not check
    whether it repairs the corner-point proof.
  - Sason, arXiv:1306.4934, gives bounds on corner points.
  - The *slope* at Costa's corner point is still open (Gohari–Nair–Ng, ISIT 2021;
    Liu 2022, Thm 8 and Conjecture 2).
- **Gaussian optimality inside HK.**
  - Nair–Ng, "Invariance of the Han–Kobayashi region with respect to temporally-correlated
    Gaussian inputs," IEEE TIT 65(3):1372–1374, 2019.
  - Costa–Nair–Ng–Wang, "On the structure of certain non-convex functionals and the
    Gaussian Z-interference channel," ISIT 2020, pp. 1522–1527: a conjecture that would
    imply Gaussian optimality of HK for the Z-IC.
  - J. Liu, "Stability of the Gaussian stationary point in the Han–Kobayashi region for
    Z-interference channels," arXiv:2209.00163, 2022. Counterexamples to that conjecture.
    Gaussian signaling is suboptimal for HK *under constant power control* (Thm 4). The
    counterexamples do not extend to variable power control (§VI). Amended conjecture
    (Conjecture 2).
  - Costa–Gohari–Nair–Ng, "A proof of the noiseberg conjecture for the Gaussian
    Z-interference channel," ISIT 2023. They prove that Costa's noiseberg scheme attains the
    concave envelope of HK with Gaussian signaling. They say an earlier claimed proof
    (Zhao–Zhu–Chen, ISIT 2012) has a gap, and they state a refined Gaussian-optimality
    conjecture. They write that it "is
    still unknown whether the HK achievable region (restricted to Gaussian inputs and
    allowing for power control) represents the capacity region".
  - Beigi–Liu–Nair–Yazdanpanah, ISIT 2016; Costa–Nair, ITA 2016 and ITA 2012 (time-sharing
    between Gaussian distributions strictly helps the symmetric sum rate; I could not access
    it to check whether its time-sharing is coded); Costa–Nair–Ng, ITA 2017; Nair–Ng,
    ITA 2018; W. H. Ng, PhD thesis, CUHK 2021.
- **Non-Gaussian inputs.**
  - Abbe–Zheng, "A coordinate system for Gaussian networks," IEEE TIT 58(2):721–733, 2012:
    non-Gaussian ensembles beat Gaussian ones for TIN-type rates (constant power).
  - Dytso–Tuninetti–Devroye, "Interference as noise: friend or foe?" arXiv:1506.02597
    (IEEE TIT 2016): TIN without time-sharing, with mixed discrete+Gaussian inputs, is
    within a constant or $O(\log\log)$ gap and gDoF-optimal (abstract-level check).

  Neither claims to beat Gaussian HK with time-sharing and power control.
- **Outer bounds.**
  - Nam, arXiv:1506.03324: new moderate-interference outer bounds. The symmetric real
    capacity is pinned to within 0.104 bit for $g^2\in(\max(0.086,P^{-1/3}),1)$, and at
    high SNR to within 0.1 bit of a Gaussian HK scheme with time-sharing.
  - Gohari–Nair, "Outer bounds for multiuser settings: the auxiliary receiver approach,"
    IEEE TIT 68(2):701–736, 2022.
- **DM case.** Nair–Xia–Yazdanpanah, ISIT 2015, pp. 2416–2420 (arXiv:1502.02589): HK is
  strictly suboptimal for some DM ICs.
- **Unrefereed or withdrawn full-solution claims** (not counted as known results):
  - Vaezi–Poor, arXiv:1509.02953, *withdrawn* ("a flaw in the proof of the outer bound");
  - Khandani, arXiv:2011.12981 (2020) and arXiv:2501.14941 (2025, v4), claiming Gaussian
    HK optimality for the weak IC.
- **Time-sharing vs convexification.** Motahari–Khandani, "Capacity bounds for the Gaussian
  interference channel," IEEE TIT 55(2):620–643, 2009 (tech. report UW-ECE 2007-26 read).
  See Claim 8.

## Verification

- `code/gic_coded_vs_plain_timesharing.py`:
  - PART 1: exact closed forms, with the rate-split LP cross-checking the compact form to
    $10^{-6}$;
  - PART 2: branch-and-bound, 7 s;
  - `--scan`: the Claim 6 table.
- `code/gic_lean_region_sumrate.py`: Claim 5 and Claim 7 tables, ~40 s. Built-in asserts:
  Basic with all-private power equals TIN; Basic with all-common power under strong
  interference equals the MAC-intersection sum; the Lean-region sum rate equals each of five
  known sum capacities.
- The box upper bound agrees exactly with an independent HiGHS LP on 3000 degenerate boxes.
  Random sampling (200k points) gives $\max(g-L)=-0.0515$ for $\delta=0$, consistent with
  TDM being the maximizer.
- Floating point: IEEE double with a $10^{-9}$ margin per box test. No directed rounding,
  so the certificate is computer-assisted at double precision.
- Not verified: the ETW outer-bound formula inherited from the earlier attempt (still
  flagged there). It is used only for context in Claim 7.

### Reviewer note (claude-opus-5-5, independent review, 2026-11-27)

**Verdict.** The headline claim holds: the frozen `Statement` is false. I checked every
`[proved]` claim (1–5 and 8) myself and re-certified the separation with independent,
outward-rounded code, so the status is now `verified`. The rigorous upper-bound certificate
is committed as `code/reviewer_bnb_rigorous.py` (run `python reviewer_bnb_rigorous.py 0.003`:
88,659,404 boxes, about 17 s, prints "Lean-region sum rate <= C(200) + DELTA <= 3.82852584559").
The coordinator re-ran it and re-read its soundness argument (weak-duality forms, disjoint
numerator/denominator coordinates, `nextafter` rounding, the e^t lower bound by squarings, and
the tail s ≥ SMAX ≥ 401, where L − 2C(s/2) is nondecreasing). My other scripts stayed outside
the repo (scratch); the method is described below so it can be redone.

- **Lean reading (Claim 3).**
  - `Statement`: for all a, b and all P₁, P₂ > 0, the closure of `InGaussianICAchievable`
    equals the closure of `InGaussianHKRegion`. The achievability definition uses a
    per-codeword power constraint Σx² ≤ nP.
  - `InGaussianHKRegion`: finite convex combinations of `InGaussianHKBasic` points. Phase
    powers are free except for Σwᵢpⱼᵢ ≤ Pⱼ, and there is no Q inside the bounds.
  - A Basic split with P₁c+P₁p < p₁ is a phase with less power, so the set equals
    Motahari–Khandani's G₂.
  - Core: `log2 = log/log 2`, and `gaussianPdf1D 1` is the N(0,1) density.
- **Claim 1.** I re-derived all 7 right-hand sides from conditional variances; they match
  El Gamal–Kim Thm 6.4 term by term. The argument for the two dropped inequalities is
  sound: d₂ = I(U₂;Y₂)+c₂ since U₂–(X₂,U₁)–Y₂, and both cannot fail at once since S₃ = c₁+c₂.
- **Claim 4(i).** My own mpmath code computed the MIs from variance ratios.
  - Averaged (A₁,A₂,S₁,S₂,S₃,D₁,D₂) = (2.798911, 2.798911, 3.922881, 3.922881, 3.926221,
    5.885992, 5.885992).
  - Exact vertex enumeration gives max R₁+R₂ = 3.92288136.
  - The split (R₁c,R₁p) = (0.984718, 0.976723) per user meets all 8 averaged
    simultaneous-decoding constraints, with min slack 0.
  - Both users use power 100 in both phases, so there is no power control; the
    per-codeword constraint holds after the usual ε back-off.
  - Gaussian HK-with-Q achievability (El Gamal–Kim Thm 6.4 plus discretization) is cited,
    not re-proved. A finer split (0, 14.13) gives 3.9234.
- **Claim 4(ii), the key step.** This bound is neither a grid search nor a Lipschitz bound.
  It is a Lagrangian bound:
  - R₁+R₂ ≤ Σwᵢg(xᵢ) ≤ ΣwᵢL(xᵢ) ≤ L(P,P), with L affine and increasing. This holds for any
    number of phases and any power control.
  - Note: with power control, the hull's sum rate is a concave envelope over phase powers,
    not the best single fixed-power region. TDM's C(200) = 3.8255 beats every single split
    (best 3.8106).
  - g = min of the 7 weak-duality forms; D₁ ≥ S₁ and D₂ ≥ S₂, so the list is complete.
  - The box bounds are exact, because numerators and denominators use disjoint coordinates.
  - The tail argument is analytic.

  My branch-and-bound tests the product form Π(1+rⱼ) ≤ E(s_lo)^m, where
  E(s) = 2^{2L} = 201·e^{(s−200)/201}·4^δ.
  - Every IEEE operation is pushed outward with `nextafter`.
  - e^t is bounded below by (1+t/2²⁴)^{2²⁴}, computed with 24 downward-rounded squarings.
  - The constants and the tail come from `mpmath.iv`. No libm call enters a box test.

  Results:

  | δ | outcome | boxes |
  |---|---|---|
  | 0.09 | certified | 4.92M |
  | 0.05 | certified | 11.3M |
  | 0.01 | certified | 54.5M (author: 54.5M) |
  | 0.003 | certified | 88.7M |
  | 0 | fails, as it must (TDM phase: g = L−δ) | — |
  | −0.005 | fails, as it must | — |

  Rigorously, then, the Lean sum rate is ≤ C(200)+0.003 = 3.828526 < 3.922881. 3000
  Nelder–Mead starts give sup(g−L|δ=0) = 0 at the single-user point, so the Lean sum rate
  is very likely exactly C(200) (heuristic).
- **Claim 5.** Checked analytically:
  - strong (S₃ ≥ S₁ when b² ≥ 1), very strong, TIN, and both Z corners;
  - mixed, MK Thm 10: the split "user 1 all-common, user 2 all-private" gives exactly
    C(P₂)+min{C(P₁/(1+a²P₂)), C(b²P₁/(1+P₂))}.
- **Claim 8.** I read arXiv:0801.1306v1 §II-C/D and tech report 2007-26.
  - Ψ contains ψ₃ = min, and G averages Ψ.
  - Thm 7 follows from Thm 1 plus the unique-minimizer property. I checked
    σ_{G₀}(1,1) = ψ₃ for weak interference (A₁+A₂ ≥ S₃ and A₁+D₂ ≥ S₂+S₃).
  - Equation numbers are corrected in place.
- **Claim 6 (heuristic).** My own 801² coded-swap grid gives:
  - P=1000, a=0.5: 5.6379, against TDM 5.4833 (+0.155);
  - P=1000, a=0.4: 5.7286, against the best single split 5.6253 (+0.103).

  These are consistent with the table. The "excess" column still rests on a grid estimate,
  so the `[heuristic]` label is right.
- **Novelty.** The coded swap is Sason 2004 (Table 1, δ=1/2); credit is added in §4.
  - Costa–Gohari–Nair–Ng (noiseberg paper, Introduction) confirm that time-sharing between
    Gaussian HK schemes strictly helps (their refs: Costa ITA 2011, Costa–Nair ITA 2012).
  - Costa–Nair–Ng (ITA 2017, Remark 1) credit Costa 1985 for using Q for power control.
  - No source I read states the separation from G₂.
  - Missing from the survey: Huleihel–Merhav, arXiv:1508.05726 (codewords with memory),
    which Costa–Nair–Ng's Remark 1 disputes.
- **Survey spot checks.**
  - arXiv:1404.6690 v5 (2018) is a *withdrawal*; its comment cites the I-MMSE limit error.
  - arXiv:1509.02953 v2 is withdrawn, as stated.
  - Khandani arXiv:2501.14941 is now at v14 (2026-11-02). Its claim that the envelope is
    reached with at most 2 phases, one of them single-user, was not checked against this
    witness.
- **Corrected statement (§5).** It matches Costa–Gohari–Nair–Ng Def. 2 (Q inside every
  mutual information, E X² ≤ P) extended to two-sided interference. Its 7 averaged
  right-hand sides match Basic. Not typechecked: there is no Lean build in this worktree.
- **Not checked:** Claims 7 and 9 in detail; the ETW formula; Nam; Liu's theorem numbers;
  Nair–Ng; Costa–Nair ITA 2012 (inaccessible).

## Dead ends

- **Non-Gaussian TIN probes at the open grid points.** Uniform $M$-PAM ($M\le16$) and
  randomized on–off Gaussian inputs, each treating interference as noise, never beat the
  Lean region (table, last two columns). At $(10,\sqrt{1/2})$ they are far below it
  (1.51 vs 2.20). Such simple non-Gaussian schemes give no route to refuting even the
  corrected statement.
- **Coded time-sharing at low SNR.** At $P\in\{1,3,10\}$ the swap trick never beats TDM or
  TIN (scan: excess $\le0$). The defect is a high-SNR, moderately-weak-interference effect.
- **A first coded-vs-plain optimizer** (random starts plus Nelder–Mead over 2-phase
  parameters) was too weak: it often returned values below the plain-TS envelope. I replaced
  it with the structured swap family and the exact LP dual-form evaluation.
- **Motahari–Khandani Thm 7 initially suggested** that coded time-sharing equals
  convexification for weak GICs, which would have made the Lean region correct. Reading
  their definitions (eq. (8): $\psi_3=\min$, then eq. (14); reviewer: eqs. (7), (13) in
arXiv:0801.1306v1) shows their $\mathcal G$ is not
  the HK region with $Q$.
- **Not tried:** HK with *randomized* power control, where $Q$ carries information
  (Hajek–Pursley style; EGN used it for the Gaussian primitive relay). It is non-Gaussian
  and is the most natural candidate against the corrected statement.

## References

- Prior attempt consulted: `2026-07-19-claude-scheduled.md`. This attempt extends its
  Dead-ends item "full HK with time-sharing variable $Q$ … and the convex hull across
  schemes".
- A. El Gamal, Y.-H. Kim, *Network Information Theory*, CUP 2011, Thm 6.4 (via the
  CMG/Kobayashi–Han compact form; book text not accessed). H.-F. Chong, M. Motani,
  H. K. Garg, H. El Gamal, "On the Han–Kobayashi region for the interference channel,"
  IEEE TIT 54(7), 2008.
- A. S. Motahari, A. K. Khandani, IEEE TIT 55(2):620–643, 2009; tech. report UW-ECE
  #2007-26 (read: §II-D, §II-E, Thm 7).
- O. Mehanna, J. Marcos, N. Jindal, Allerton 2010, arXiv:1010.2437.
- All survey items as cited in Details §6, plus Sato (IEEE TIT 1981), Carleial (1975),
  Han–Kobayashi (1981), Etkin–Tse–Wang (2008), Shang–Kramer–Chen / Motahari–Khandani /
  Annapureddy–Veeravalli (2009), Sason (IEEE TIT 50(6), 2004), Costa (IEEE TIT 31(5), 1985).
- Code: `code/gic_lean_region_sumrate.py`, `code/gic_coded_vs_plain_timesharing.py`.
