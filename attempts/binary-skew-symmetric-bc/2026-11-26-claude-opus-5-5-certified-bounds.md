---
problem: binary-skew-symmetric-bc
date: 2026-11-26
attempter: claude
model: claude-opus-5-5
type: new-bound
status: unverified
---

## Summary

The BSSC sum-capacity window is now **certified** as
$0.361642884 \le C_{\mathrm{sum}}(W_{\mathrm{BSSC}}) \le 0.369297201$ bits, down from the
uncertified $[0.3616428,\ 0.3725562]$ recorded so far. The window shrinks from $0.0109$ to
$0.0076543$ bits. The upper bound comes from the two-auxiliary-receiver sum-rate bound of Gohari–Liu–Nair, and the
weaker certified value $0.369317310$ from Geng's one-auxiliary-receiver bound (ISIT 2025).
This file gives self-contained proofs of the two bounds in concave-envelope form and checks
their values with outward-rounded interval arithmetic plus exact rational hulls.

The literature check also turned up two corrections to the problem file:

- The first BSSC improvement over UV is due to Geng (ISIT 2025) and Gohari–Liu–Nair. Gohari–Nair (2022) did not
  evaluate the BSSC; its strict improvements are on other channels.
- Both published BSSC numbers are about $10^{-6}$ too low, at the very auxiliary channels the
  authors report. We give rigorous lower bounds on the values of their formulas at their parameters.

The Marton value $0.3616428$ is certified from below by an explicit randomized-time-division distribution.

## Approach

1. **Literature pin-down.** We read Gohari–Nair (2022) from the author-hosted PDF and searched it for the BSSC. Their strict
   improvements over UV are the erasure-Blackwell corner point (their Sec. 4.2 and Remark 13)
   and product channels (via [GGNY14]); no BSSC value appears. The BSSC improvements were
   traced to two later sources:
   - Y. Geng, "A simple auxiliary receiver outer bound for broadcast channels," ISIT 2025.
     We could not access it directly; its BSSC evaluation is quoted in GLN below.
   - A. Gohari, Y. Liu, C. Nair, "A two auxiliary receiver outer bound to the capacity region
     of a two-receiver discrete memoryless broadcast channel" [GLN]. This is an author-hosted
     manuscript (`chandra.ie.cuhk.edu.hk/pub/papers/BC/GK-outer.pdf`, read 2026-11-26), with no arXiv
     version found. It cites ISIT 2025 papers, so it dates from 2025 or later.
   GLN Sec. III-A reports Geng's value $0.369316568803963$ at the auxiliary channel
   $J=\mathrm{BSC}(0.189986556858845)$. GLN Sec. IV reports their own $0.369296340638082$, at an
   explicit pair $(G,K)$.
2. **Self-contained bounds.** We re-derive, for private messages, the two sum-rate bounds that
   produce those numbers (Lemmas A and B). The derivations use Fano, the Csiszár-sum telescoping
   identity and a time-sharing variable. The auxiliary-receiver terms close up because each
   "extra" term has a definite sign.
3. **Certification.** For binary input the bounds are explicit functions of $t=P(X=1)$ built
   from nested upper concave envelopes on $[0,1]$. We majorize each envelope rigorously
   (see the code docstring) and reduce the max over $t$ to $t=\tfrac12$ by concavity plus skew
   symmetry (Lemma C).

Notation (bits): $t=P(X=1)$; receiver $Y$ is the Z-channel ($0\to0$, $1\to$ Unif), receiver $Z$
is its mirror. Then
$I_Y(t)=h(t/2)-t$ and $I_Z(t)=h(\tfrac{1-t}{2})-(1-t)$. An auxiliary receiver $J$ with
$a_x=P(J{=}0\mid X{=}x)$ has
$I_J(t)=h(a_0+(a_1-a_0)t)-(1-t)h(a_0)-t\,h(a_1)$.
$\mathcal C[\cdot]$ denotes the upper concave envelope on $[0,1]$.

## Claims

1. **[proved]** (literature record, primary sources read) The problem file's sentence
   "Gohari and Nair (2022) … proved a strictly tighter upper bound on the BSSC sum-rate than the
   UV outer bound" is misattributed. Gohari–Nair (2022) contains no BSSC evaluation. The first BSSC
   sum-rate improvement over UV is Geng's (ISIT 2025): $\approx 0.369316568803963$ at
   $J=\mathrm{BSC}(0.18998\ldots)$, using a bound that GLN Prop. 1 shows is implied, for each
   fixed $J$, by Gohari–Nair Theorem 7. GLN then improved this to $\approx 0.369296340638082$.
   GLN call the improvement "small". It is larger for other skew-symmetric channels: see their
   Sec. IV-A (crossover 0.9) and Fig. 3.
2. **[proved]** (Lemma A, the J-bound sum rate.) For every auxiliary channel $T_{J|X}$, every
   achievable private-message pair satisfies
   $R_1+R_2\le \max_t F_J(t)$, where
   $$F_J=\tfrac12 I_Y+\tfrac12 I_Z+\mathcal C\big[\mathcal C[I_J-I_Y]+\tfrac12(I_Y-I_J)\big]
   +\mathcal C\big[\mathcal C[I_J-I_Z]+\tfrac12(I_Z-I_J)\big].$$
   This is Geng's Theorem 1 at $\mu=1,\sigma=1,\gamma=\tfrac12$, i.e. GLN eq. (15).
3. **[proved]** (Lemma B, the GK sum rate.) For every pair of auxiliary channels $T_{G|X},T_{K|X}$,
   $R_1+R_2\le\max_t F_{GK}(t)$, where
   $$F_{GK}=\tfrac12 I_Y+\tfrac12 I_Z+\mathcal C\big[\tfrac12(I_Y-I_G)+\mathcal C[I_G-I_Y]\big]
   +\mathcal C\big[\tfrac12(I_Z-I_K)+\mathcal C[I_K-I_Z]\big]+\tfrac12\mathcal C[I_G-I_K]+\tfrac12\mathcal C[I_K-I_G].$$
   This is GLN eq. (16), derived there from their Theorem 7 (13c) and (13e); we re-derive it below.
4. **[proved]** (Lemma C.) If $J$ is a BSC, or $K$ is the skew mirror of $G$
   ($K(k|x)=G(1-k|1-x)$), then $F_J$ (resp. $F_{GK}$) is concave and satisfies $F(t)=F(1-t)$.
   Hence $\max_t F=F(\tfrac12)$.
5. **[proved]** (computer-assisted; interval arithmetic plus exact rational hulls, code below)
   - (a) $F_J(\tfrac12)\le 0.369317310$ for $J=\mathrm{BSC}(\alpha)$, with $\alpha$ the 64-bit dyadic
     rational nearest $0.189953475893$.
   - (b) $F_{GK}(\tfrac12)\le 0.369297201$ for $G=(a_0,a_1)$ the 64-bit dyadics nearest
     $(0.17311456,\ 0.79310944)$, paired with receiver $Y$, and $K$ its skew mirror.
   - (c) the UV envelope form $\tfrac12I_Y+\tfrac12I_Z+\tfrac12\mathcal C[I_Y-I_Z]+\tfrac12\mathcal C[I_Z-I_Y]$
     at $\tfrac12$ is $\le 0.372556252$.

   With Claims 2–4: **$C_{\mathrm{sum}}(W_{\mathrm{BSSC}})\le 0.369297201$ bits.** Also, by (c), the
   catalog's UV number $0.37256$ is now a certified upper bound rather than a numerical estimate.
6. **[proved]** (computer-assisted) The Lean-region point with $W\sim$ Unif$\{0,1\}$ is explicit:
   - given $W{=}0$: $X\sim\mathrm{Bern}(a)$, $U=X$, $V=0$;
   - given $W{=}1$: $X\sim\mathrm{Bern}(1-a)$, $U=0$, $V=X$;
   - $a$ the 64-bit dyadic nearest $0.1584357$.

   This point lies in `martonInnerBound binarySkewSymmetricBC` with $R_1=R_2=S/2$, where
   $S=h(\tfrac14)+\tfrac12h(\tfrac a2)-\tfrac12h(\tfrac{1-a}2)-a\ge 0.361642884421$. Hence
   `bsscMartonSumRate` $\ge 0.361642884$ and $C_{\mathrm{sum}}\ge0.361642884$, by Marton's theorem.
   The matching upper bound `bsscMartonSumRate` $=0.3616428\ldots$ is the Nair–Wang–Geng /
   Geng–Jog–Nair–Wang theorem; it is not re-proved here.
7. **[proved]** (computer-assisted lower bounds on the published formulas at the published parameters)
   - At GLN's quoted $J=\mathrm{BSC}(0.189986556858845)$, $F_J(\tfrac12)\ge 0.369317326769$.
     That is $7.6\times10^{-7}$ above the quoted $0.369316568803963$.
   - At GLN's quoted $(G,K)$, $F_{GK}(\tfrac12)\ge 0.369297253624$.
     That is $9.1\times10^{-7}$ above the quoted $0.369296340638082$.

   So both published 15-digit values understate their own formulas at the stated parameters.
   This is harmless to the qualitative conclusions, but matters for anyone citing the digits.
   **[heuristic]** The likely cause is coarse-grid envelope evaluation:
   - with a uniform grid our evaluator gives $0.3693145$ (201 points) and $0.3693169$ (501 points)
     for $F_J$, bracketing the published value;
   - the converged value is $0.36931732823$.
8. **[heuristic]** (numerical optimization, not certified as a global optimum)
   - Over all binary $J$ (asymmetric, and with $\gamma$ free), $\min F_J(\tfrac12)\approx0.369317306$
     at $J\approx\mathrm{BSC}(0.18995)$; asymmetry does not help.
   - Over skew-symmetric binary pairs $(G,K)$, $\min F_{GK}(\tfrac12)\approx0.3692971967$ at
     $G\approx(0.17311,0.79311)$.
   - Ternary auxiliary receivers, i.e. ternary $G$ with $K$ its mirror, give no improvement
     beyond grid resolution ($\le10^{-9}$). Optimizing from four starts drives the third output
     to probability $\lesssim10^{-3}$ and returns $0.3692971955$, against $0.3692971962$ for
     binary on the same grid.
   - All of these numbers come from `code/bssc_float_explore.py` (modes `optJ`, `optGK`,
     `ternary`, `grid`).

## Details

**Proof of Lemma A.** Take a code with independent uniform $M_1,M_2$, inputs $X^n$, and outputs
$Y^n,Z^n$. Let $J^n$ be the output of the memoryless channel $T_{J|X}$ applied to $X^n$, and
write $\epsilon_n\to0$.

*Step 1 (Fano and independence).* Fano gives
$n(R_1+R_2-\epsilon_n)\le I(M_1;Y^n)+I(M_2;Z^n)$. Since $M_1\perp M_2$,
$$I(M_1;J^n)+I(M_2;J^n)\le I(M_1;J^n)+I(M_2;J^n|M_1)=I(M_1M_2;J^n)\le I(X^n;J^n),$$
so
$$n(R_1+R_2-\epsilon_n)\le I(X^n;J^n)+[I(M_1;Y^n)-I(M_1;J^n)]+[I(M_2;Z^n)-I(M_2;J^n)].$$

*Step 2 (single-letter terms).* Set $\hat W_i=(Y^{i-1},J_{i+1}^n)$ and
$\tilde W_i=(Z^{i-1},J_{i+1}^n)$. Then:
- (i) $I(X^n;J^n)=\sum_i I(X_i;J_i)-\sum_i I(J_i;J^{i-1})$, by memorylessness.
- (ii) Csiszár-sum telescoping gives
  $I(M_1;Y^n)-I(M_1;J^n)=\sum_i[I(M_1;Y_i|\hat W_i)-I(M_1;J_i|\hat W_i)]$, and likewise for
  $M_2$ with $(Z,\tilde W)$.
- (iii) The same telescoping without a message gives
  $\sum_i[I(\hat W_i;Y_i)-I(\hat W_i;J_i)]=\sum_iI(Y_i;Y^{i-1})-\sum_iI(J_i;J^{i-1})$, using
  $\sum_iI(J_i;J_{i+1}^n)=\sum_iI(J_i;J^{i-1})$. Hence
  $-\sum_i I(J_i;J^{i-1})\le\sum_i[I(\hat W_i;Y_i)-I(\hat W_i;J_i)]$, and likewise with $(Z,\tilde W)$.

*Step 3 (time sharing).* Let $Q$ be uniform on $[n]$ and set $\hat W=(\hat W_Q,Q)$,
$\tilde W=(\tilde W_Q,Q)$, $\hat U=M_1$, $\tilde V=M_2$. Then
$I(X_Q;J_Q|Q)=I(X;J)-I(Q;J)$, and
$I(\hat W_Q;Y|Q)-I(\hat W_Q;J|Q)=I(\hat W;Y)-I(\hat W;J)-I(Q;Y)+I(Q;J)$.
The extra term $-I(Q;Y)$ is $\le0$. This gives the two constraints
- (8c) $R_1+R_2\le I(X;J)+I(\hat U\hat W;Y)-I(\hat U\hat W;J)+I(\tilde V;Z|\tilde W)-I(\tilde V;J|\tilde W)$;
- (8d) $R_1+R_2\le I(X;J)+I(\hat U;Y|\hat W)-I(\hat U;J|\hat W)+I(\tilde V\tilde W;Z)-I(\tilde V\tilde W;J)$.

Here $(\hat U,\hat W)-X-(Y,J)$ and $(\tilde V,\tilde W)-X-(Z,J)$ are Markov, and $X\sim p$ is the
code's average input distribution.

*Step 4 (envelopes).* Average (8c) and (8d). Write each $I(\cdot;Y|\cdot)$ through the
conditional input laws $p_{X|\hat w}$ and $p_{X|\hat u\hat w}$; this is legitimate by the Markov chains. The $\hat U$-part becomes
$$\tfrac12(I_Y-I_J)(p)+\mathbb E_{\hat W}\Big[\tfrac12(I_Y-I_J)(p_{X|\hat W})
+\mathbb E_{\hat U|\hat W}(I_J-I_Y)(p_{X|\hat U\hat W})\Big]
\le\tfrac12(I_Y-I_J)(p)+\mathcal C\big[\tfrac12(I_Y-I_J)+\mathcal C[I_J-I_Y]\big](p).$$
The $\tilde V$-part is the same with $Z$. Adding $I_J(p)$ gives $R_1+R_2\le F_J(p)\le\max_tF_J$. $\square$

**Proof of Lemma B.** Generate $(G^n,K^n)$ memorylessly from $X^n$.

- *Constraint (m).* Write $I(M_1;Y^n)=[I(M_1;Y^n)-I(M_1;G^n)]+[I(M_1;G^n)-I(M_1;K^n)]+I(M_1;K^n)$.
  Then use $I(M_1;K^n)+I(M_2;Z^n)\le I(X^n;K^n)+[I(M_2;Z^n)-I(M_2;K^n)]$, as in Step 1.
  Single-letterize with the hybrids:
  - $W_{a,i}=(Y^{i-1},G_{i+1}^n)$, unconditional form;
  - $(G^{i-1},K_{i+1}^n)$, unconditional form;
  - $W_{c,i}=(Z^{i-1},K_{i+1}^n)$, conditional form.

  The leftover chain terms are $(\Sigma_G-\Sigma_Y)+(\Sigma_K-\Sigma_G)-\Sigma_K=-\Sigma_Y\le0$,
  where $\Sigma_A:=\sum_iI(A_i;A^{i-1})$. The leftover time-sharing terms are $-I(Q;Y)\le0$. Result:
  $$R_1+R_2\le I(U_aW_a;Y)-I(U_aW_a;G)+I(U_bW_b;G)-I(U_bW_b;K)+I(X;K)+I(V_c;Z|W_c)-I(V_c;K|W_c).$$
- *Constraint (o).* This is the mirror image: $M_2$ goes $Z\to K\to G$ and ends with $I(X^n;G^n)$,
  and $M_1$'s term $[I(M_1;Y^n)-I(M_1;G^n)]$ is taken in conditional form with the same $W_a$.
  The $(Z,K)$ term is taken in unconditional form with the same $W_c$. The leftovers are $-\Sigma_Z-I(Q;Z)\le0$. Result:
  $$R_1+R_2\le I(V_cW_c;Z)-I(V_cW_c;K)+I(V_bW_b;K)-I(V_bW_b;G)+I(X;G)+I(U_a;Y|W_a)-I(U_a;G|W_a).$$

  These are GLN (19m) and (19o) at $R_0=0$, which we checked term by term.
- *Envelopes.* Average (m) and (o).
  - The $a$- and $c$-parts are handled exactly as in Lemma A, with $J\to G$ and $J\to K$
    respectively. This works because both constraints use the *same* $(U_a,W_a)$ and $(V_c,W_c)$.
  - The $b$-parts satisfy $\tfrac12[I(U_bW_b;G)-I(U_bW_b;K)]\le\tfrac12(I_G-I_K)+\tfrac12\mathcal C[I_K-I_G]$,
    and symmetrically for the $V_b$ term.
  - The linear terms sum to $\tfrac12I_Y+\tfrac12I_Z$. $\square$

**Proof of Lemma C.**
- *Concavity.* $F$ is a nonnegative combination of $I_Y$ and $I_Z$ (both concave in the input
  law) plus concave envelopes.
- *Symmetry.* The map $t\mapsto1-t$ gives $I_Y(1-t)=I_Z(t)$. For a BSC, $I_J(1-t)=I_J(t)$; for the
  skew mirror, $I_K(t)=I_G(1-t)$. Envelopes commute with the affine map $t\mapsto 1-t$, so the
  $Y$-envelope term at $1-t$ equals the $Z$-envelope term at $t$, and
  $\mathcal C[I_G-I_K](1-t)=\mathcal C[I_K-I_G](t)$.
- *Conclusion.* A concave function that is symmetric about $\tfrac12$ attains its maximum at $\tfrac12$. $\square$

**Certification method (Claim 5, 7; `code/bssc_certify.py`).** All arithmetic is either
outward-rounded `mpmath.iv` at 120 bits or exact `fractions.Fraction`. Every stored value is
rounded outward to $2^{-140}$, with an extra $10^{-30}$ margin.

- *Grid.* Rational grid: $t_k=\sin^2(\pi k/2K)$ rounded to $2^{-64}$, symmetrized, plus 60
  geometric nodes toward each endpoint; $K=8000$ gives 8121 nodes.
- *Majorizing $\mathcal C[f]$.*
  - Node values $\overline{f}(t_k)$ come from interval enclosures.
  - On each cell take the smaller of two raises. The first is the interpolation error
    $\frac{w^2}{8}\max(0,-\inf f'')$, with $\inf f''$ from an interval enclosure of
    $f''=\sum c\,\beta^2h''$, where $h''(s)=-1/(\ln2\,s(1-s))$. The second is a crude cell
    supremum from monotone pieces of $h$; it is used next to $t=0,1$, where $f''$ is unbounded.
  - Raise the nodes so that the piecewise-linear interpolant dominates $f$ cell by cell.
  - Take the exact rational upper hull. It is concave, majorizes $f$, and so majorizes $\mathcal C[f]$.
- *Nested envelopes $\mathcal C[\mathcal C[f]+g]$.* The inner hull is linear on every cell, so the
  same procedure applies with $g''$.
- *Lower bounds (Claim 7).* The hull of points on or below a graph minorizes its envelope, so
  exact hulls of lower node values give rigorous minorants.

The heuristic numbers in Claims 7–8 come from the separate floating-point evaluator
`code/bssc_float_explore.py` (scipy Qhull envelopes; modes `values`, `grid`, `optJ`, `optGK`,
`ternary`).

The output of `python bssc_certify.py 8000 marton uv j gk jlow gklow`, run with environment
`BSSC_ALPHA=0.189953475893 BSSC_G0=0.17311456 BSSC_G1=0.79310944`, is reproduced verbatim in
**Verification**.

## Verification

Run 2026-11-26 (`nice`, single process, about 4 min):
```
grid nodes: 8121
Marton RTD sum rate at a = 0.158435700 (exact rational 2854123837928735/18014398509481984):  >= 0.361642884421
UV  sum-rate envelope form (18):  <= 0.372556251547   [30s]
J-bound (Geng Thm 1, sigma=1,gamma=1/2), J=BSC(0.189953475893000): <= 0.369317309574   [105s]
J-bound value at Geng's published J=BSC(0.189986556858845) is >= 0.369317326769   [127s]
GK-bound value at GLN's published (G,K) is >= 0.369297253624   [161s]
GK-bound (16), G=(0.173114560000000, 0.793109440000000), K=mirror: <= 0.369297200757   [259s]
```
Consistency checks:
- **Grid convergence.** At $K=400$ the same run gives looser but valid bounds:
  $0.3725582$ (UV), $0.3693186$ (J), $0.3692991$ (GK). Every certified upper value lies above the
  converged numerical value of the same formula: UV $0.372556248918$; J $0.369317305975$;
  GK $0.36929719668$. The gaps are $2.6\times10^{-9}$, $3.6\times10^{-9}$ and $4.1\times10^{-9}$ respectively.
- **Independent cross-checks.** A separate floating-point evaluator (scipy Qhull envelopes on a
  $\sin^2$ grid) reproduces the earlier UV value $0.3725562$ of
  `attempts/broadcast-channel/2026-07-18-claude-fable-5-bssc-bounds.md`. It also reproduces the
  Marton RTD value $0.3616428844$ through GLN's envelope form (17), i.e. with the $\mathcal C$
  restored, which the PDF text extraction drops.
- **Sanity.** All certified quantities obey Marton $<$ GK $<$ J $<$ UV $<$ $\log_2$-trivial bounds.
- **Status.** Not independently reviewed yet. Promotion to `verified` needs an independent re-run
  of `code/bssc_certify.py`, and ideally an independent re-implementation of the majorant
  construction.

## Dead ends

- **Chains of auxiliary receivers on the "b" leg do not help.** Replacing the single $G\to K$
  step by $G=A_1\to A_2\to\cdots\to A_m=K$ (each step single-letterized like the $b$-term)
  turns $\tfrac12\mathcal C[I_K-I_G]$ into $\tfrac12\sum_i\mathcal C[I_{A_{i+1}}-I_{A_i}]$.
  By subadditivity of $\mathcal C$, that sum is $\ge\tfrac12\mathcal C[I_K-I_G]$. **[proved]**
  (one line). Hence any improvement must come from a different single-letterization, not from
  longer chains of this type.
- **Other averages of GLN's sum-rate constraints.** Averaging (13d) and (13f) instead of (13c)
  and (13e) gives the same $a$/$c$ envelopes. The $b$ terms become
  $\tfrac12\mathcal C[(I_K-I_G)+\mathcal C[I_G-I_K]]+\tfrac12\mathcal C[(I_G-I_K)+\mathcal C[I_K-I_G]]$,
  which is pointwise $\ge\tfrac12\mathcal C[I_G-I_K]+\tfrac12\mathcal C[I_K-I_G]$. So that
  combination is never better. **[sketch]**
- **The earlier Theorem-7 scan** (`attempts/broadcast-channel/2026-07-20-claude-scheduled.md`)
  concluded that Gohari–Nair's bounds close none of the window. That conclusion is superseded:
  - GLN Prop. 1 shows Theorem 7 implies Geng's bound for each fixed $J$, so Theorem 7 at
    $J=\mathrm{BSC}(0.19)$ is $\le F_J(\tfrac12)\approx0.369317$.
  - The scan's $J$ list (const, $X$, BSC(0.1), BSC(0.3), Z-channels) missed the narrow basin
    around BSC(0.19). At BSC(0.3) and BSC(0.1), $F_J$ is $0.504$ and $0.531$, far above UV.
    Their Theorem-7 values there equal UV only because the UV constraints are part of Theorem 7.
  - This is not a contradiction, just an unlucky grid.
- **Ternary auxiliary receivers in the GK bound.** These collapse to the binary optimum
  numerically (Claim 8). This agrees with GLN's report that ternary $J$ did not improve Geng's
  bound. We did not try ternary pairs without the mirror constraint, or ternary $J$ in Lemma A.
- **Using GLN's 15-digit values as certified bounds.** This fails because of Claim 7; we quote
  our certified values instead.

## References

- A. Gohari and C. Nair, "Outer bounds for multiuser settings: the auxiliary receiver
  approach," IEEE Trans. Inf. Theory 68(2):701–736, 2022 (author PDF
  `chandra.ie.cuhk.edu.hk/pub/papers/NIT/Auxiliary-Receiver.pdf`; Sec. 4.2, Remark 13, final
  remarks read).
- Y. Geng, "A simple auxiliary receiver outer bound for broadcast channels," Proc. IEEE ISIT
  2025, pp. 1–6. Not accessed; its Theorem 1 and BSSC value are quoted from [GLN].
- A. Gohari, Y. Liu, C. Nair, "A two auxiliary receiver outer bound to the capacity region of a
  two-receiver discrete memoryless broadcast channel," manuscript, author-hosted PDF
  `chandra.ie.cuhk.edu.hk/pub/papers/BC/GK-outer.pdf` [GLN]. Theorems 3–7, eqs. (15)–(18),
  Sec. IV and Appendices A–B were read.
- Y. Geng, V. Jog, C. Nair, Z. V. Wang, "An information inequality and evaluation of Marton's
  inner bound for binary input broadcast channels," IEEE Trans. Inf. Theory 59(7):4095–4105,
  2013 (journal version of Nair–Wang–Geng ISIT 2010, arXiv:1001.1468).
- M. Huang, Y. Liu, Y. Liu, "Sub-optimality of Marton's inner bound for the two-receiver
  broadcast channel," arXiv:2608.19869 (2026). This is the source for the multi-letter history
  quoted in the problem-file edit; see `attempts/marton-inner-bound-tightness/`.
- Prior attempts: `attempts/broadcast-channel/2026-07-18-claude-fable-5-bssc-bounds.md` and
  `attempts/broadcast-channel/2026-07-20-claude-scheduled.md`.
