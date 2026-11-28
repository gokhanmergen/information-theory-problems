---
problem: binary-skew-symmetric-bc
date: 2026-11-27
attempter: claude
model: claude-opus-5-5
type: numerical-evidence
status: unverified
---

## Summary

We asked whether the Huang–Liu–Liu (HLL, arXiv:2608.19869) mechanism for beating one-letter
Marton can work with a **binary input**, and in particular on the BSSC. There are five findings.

- **BSSC reduction.** "Two-letter Marton does not beat one-letter Marton on the BSSC" follows
  from one finite-dimensional inequality at the single dual point $(\alpha,a)=(\tfrac12,0)$:
  $B_{T\otimes T}(\tfrac12,0)\le 2B_T(\tfrac12,0)$. This is a sufficient condition, and an
  approximate version $B_{T\otimes T}\le2B_T+\varepsilon$ bounds any gain by $\varepsilon$. The dual point is *exactly* tight for
  one-letter Marton: $h(\tfrac14)+B_T(\tfrac12,0)$ equals the randomized-time-division sum rate
  identically, not just numerically. After the Anantharam–Gohari–Nair cardinality reduction the
  inequality is a maximization over 430+430 explicit deterministic maps on 5-simplices, plus
  two 3-simplex branches. This is an instance of AGN 2019's Lemma 2 criterion (credited below).
  **[proved]**, given cited theorems.
- **Numerics.** A heavy multistart search over all those maps finds $B_{T\otimes T}(\tfrac12,0)=2B_T(\tfrac12,0)$
  to $10^{-15}$, attained only at product, Markov distributions. The best non-product local
  optimum is $4.25\times10^{-3}$ bits lower. We also find no non-additivity
  - at 26 other dual points $(\alpha,a)$ for the BSSC;
  - on 152 random binary-input channels with output sizes up to 3, plus 44 random channels at
    "tied" dual points (the randomized-time-division regime);
  - in a direct search of the two-letter Marton functional with $W$, seeded and unseeded.

  **[heuristic]** (numerical). It agrees with AGN 2019's report that "rather exhaustive"
  two-letter searches on binary-input, binary-output channels found no improvement.
- **Obstruction for HLL's conversion with binary input.** HLL's constraint-removal step makes
  $p^*$ optimal with shaping components of weight $O(1/\log N)\to0$, via an input-side label
  $K\in[N]$. With binary input, every component's fixed-input Marton function is concave and
  lies between $0$ and $h(p)$, so its slopes are bounded by $S(p)=h(p)/\min(p,1-p)$. Any
  binary-input (output-side-only) shaping therefore needs weight at least $s/(s+S(p^*))$,
  bounded away from 0 **[proved]** (Claims 6–7). So the vanishing-weight limit of HLL's Thm 4
  is unavailable. Whether some non-vanishing-weight shaping could still preserve a gain is not
  settled **[heuristic]** (Claim 8).
  - The seed of HLL's construction, a non-Markov one-letter optimizer, cannot occur for binary
    input **[proved]**, by AGN (Claim 9b).
  - For skew-symmetric channels no shaping is needed at all **[proved]** (Claim 9a).
- **Computer-assisted two-letter bound for the BSSC.** A DC branch-and-bound over every map
  class certifies $B_{T\otimes T}(\tfrac12,0)\le2B_T(\tfrac12,0)+0.01$. It runs in float64 with
  an explicit rounding margin, which is why it is tagged **[sketch]** rather than interval-rigorous
  (Claim 10). Hence the **two-letter Marton sum rate of the BSSC is at most $0.36664$ bits per
  letter**, strictly below the certified outer bound $0.369297$. Two-letter Marton cannot close
  the BSSC window, and any two-letter gain is at most $0.005$ bits per letter. Pushing
  $\varepsilon$ toward 0 is out of reach with this bound (Dead end 1).

## Approach

1. Read HLL in full (arXiv PDF) and the prior attempts (`2026-11-26-claude-opus-5-5-certified-bounds.md`,
   `attempts/marton-inner-bound-tightness/2026-11-26-claude-opus-5-5-hll-counterexample-audit.md`
   and its code). Then a literature check of the binary-input Marton papers (primary PDFs; see
   Novelty check).
2. Work entirely with the **dual functional** of Gohari–Liu–Nair / HLL:
   $$G_T(P_{UVX};\alpha,a)=-\alpha H(Y)-\bar\alpha H(Z)+I(U;Y)+I(V;Z)-I(U;V)+\textstyle\sum_x p(x)a_x,
   \qquad B_T(\alpha,a)=\max_{P_{UVX}}G_T .$$
   For binary input, $B_T$ is a 1-D maximization. For $T\otimes T$ (4-ary input) it is a finite
   family of 5-dimensional maximizations. The two-letter question is then whether
   $B_{T\otimes T}(\alpha,a\oplus a)>2B_T(\alpha,a)$, where $(a\oplus a)(x_1,x_2)=a_{x_1}+a_{x_2}$.
   A gain requires this "dual non-additivity" (Claim 2), and for the BSSC one point suffices (Claim 3).
3. Numerical search for dual non-additivity (BSSC, then random binary-input channels), plus a
   direct search of the two-letter Marton functional as an independent cross-check.
4. Analyse each step of HLL's conversion (Thm 2 gradient shaping, Prop 3 receiver-revealed
   mixtures, Thm 4 constraint removal) under the constraint that the input stays binary.

Notation: bits throughout; $p=P(X{=}1)$; $h$ is binary entropy; $\bar\alpha=1-\alpha$.
For a BC $C$ and $P_{WUVX}$,
$L^{\alpha}_C(P)=\alpha I(W;Y)+\bar\alpha I(W;Z)+I(U;Y|W)+I(V;Z|W)-I(U;V|W)$ and
$M_C(P)=\min\{I(W;Y),I(W;Z)\}+I(U;Y|W)+I(V;Z|W)-I(U;V|W)=\min_\alpha L^\alpha_C(P)$.
Write $\ell^\alpha_C(p)=\max_{P_{WUV|X}}L^\alpha_C$, $m_C(p)=\max_{P_{WUV|X}}M_C$ (the
fixed-input Marton sum rate), and
$UB^{\alpha,a}_C(p)=\alpha H_p(Y)+\bar\alpha H_p(Z)+B_C(\alpha,a)-a\cdot p$ (HLL (23)).
HLL's (24) gives $L^\alpha_C(P)\le UB^{\alpha,a}_C(p_X)$ for all $P$, all $a$ and any finite $C$.
(HLL's labelling of $\alpha$ in (3) vs (24) is swapped; we use one convention throughout.)

## Claims

1. **[proved]** (literature record; primary sources read, see Novelty check) Status of
   multi-letter Marton for binary input and the BSSC:
   - (a) Anantharam–Gohari–Nair (IEEE TIT 65(3), 2019), §II-C, already formulate the two-letter
     test for products of binary-input BCs in dual form (their Lemma 2 and eq. (28)). They
     reduce the right-hand side to $|U|+|V|\le5$ with $X_1X_2=f(U,V)$, the cases
     $(|U|,|V|)=(2,3),(3,2)$ being the nontrivial ones. They report: "Despite extensive
     simulations on binary input broadcast channels we were unable to find channels for which
     the two-letter region strictly improved on the single-letter region". Also: "At least when all outputs
     of both broadcast channels are binary valued, we believe that we performed a rather
     exhaustive and intensive search, yet we were unable to find any such instance."
     They do not name the BSSC or report its numbers.
   - (b) Geng–Gohari–Nair–Yu (ITA 2011), Thm 3: the two-letter randomized-time-division
     $\lambda$-sum rate factorizes, so RTD-type schemes cannot show a two-letter gain.
   - (c) Nair (ITA 2020), Prop. 2.6 / Remark 2.7: for a product channel with a binary component,
     the product of one-letter maximizers is a *local* maximizer of the two-letter dual. Nair
     adds: "it is not known whether there are other non-trivial local maximizers". The global
     statement, which would settle the binary case, is open.
   - (d) We found **no publication reporting an explicit two-letter Marton computation for the
     BSSC**; the BSSC's binary outputs place it in the class AGN say they searched.
     Gohari–Liu–Nair (ISIT 2025; extended version on Nair's page) state Conjectures 1
     (additivity of the dual) and 2 (Markovity), and for binary input only remark that
     Markovity holds trivially.
2. **[proved]** (dual criterion; for finite $T$ this is the sum-rate case of AGN 2019 Lemma 2,
   restated for HLL's fixed-input notion) Let $T$ be any finite BC, $p\in\Delta(\mathcal X)$,
   and $(\alpha,a)$ with $B_{T\otimes T}(\alpha,a\oplus a)=2B_T(\alpha,a)$. Then every $P$ on
   $\mathcal X^2$ whose two input marginals average to $p$ satisfies
   $M_{T\otimes T}(P)\le 2\,UB^{\alpha,a}_T(p)$. In particular, if dual additivity holds at a
   pair with $UB^{\alpha,a}_T(p)=m_T(p)$, there is no fixed-input two-letter gain at $p$ in HLL's
   sense (their eq. (5)).
3. **[proved]** (BSSC reduction; uses Claim 2's argument, GJNW 2013 Thm 1 or AGN 2019 Thm 3, and
   Marton achievability) For the BSSC $T$:
   - (a) $B_T(\tfrac12,0)=\max_{q\in[0,1]}\big[\tfrac12h(\tfrac q2)-\tfrac12h(\tfrac{1-q}2)-q\big]
     =-0.449635240037\ldots$;
   - (b) $h(\tfrac14)+B_T(\tfrac12,0)=\max_a\big[h(\tfrac14)+\tfrac12h(\tfrac a2)-\tfrac12h(\tfrac{1-a}2)-a\big]
     =0.361642884422\ldots$, which is exactly the RTD Marton sum rate $M_T$;
   - (c) for every $n$ and every $P$ on $\{0,1\}^n$:
     $M_{T^{\otimes n}}(P)\le n\,h(\tfrac14)+B_{T^{\otimes n}}(\tfrac12,0)$.

   Hence $B_{T\otimes T}(\tfrac12,0)\le2B_T(\tfrac12,0)+\varepsilon$ implies
   $M_{T\otimes T}\le 2M_T+\varepsilon$. Equality would give: **two-letter Marton equals
   one-letter Marton on the BSSC**. By AGN 2019 Thm 3,
   $B_{T\otimes T}(\tfrac12,0)$ is the maximum of $G$ over
   - $X_1X_2=f(U,V)$ with $(|U|,|V|)\in\{(2,3),(3,2)\}$ and all maps $f$ (430 classes each up to
     relabelling $U$ and $V$ symbols); and
   - the two branches $U=X_1X_2$, $V$ const, and its mirror.
4. **[heuristic]** (numerical; code `code/multiletter/`) For the BSSC:
   - (a) The best value found over all 860 map classes and both branches is
     $B_{T\otimes T}(\tfrac12,0)\ge 2B_T(\tfrac12,0)+O(10^{-15})$, with no value above
     $2B_T+9\times10^{-16}$. Setup: 256 starts × 3000 mirror-ascent iterations per class, plus
     L-BFGS polish of the 25 best classes in each family.
     - 66 of the 862 classes attain $2B_T$ to within $10^{-10}$.
     - A separate run (32 starts × 2000 iterations, seed 5) checked the structure at all 64
       classes within $10^{-7}$:
       - the maximizers have $I(X_1;X_2)\le4.4\times10^{-16}$ (product inputs) and
         $I(U;V|X_1X_2)\le4.4\times10^{-16}$ (Markov);
       - their input marginals are $(P(X_1{=}1),P(X_2{=}1))=(q^*,1-q^*)$ or $(1-q^*,q^*)$, with
         $q^*=0.15843$, the one-letter optimizer;
       - so one letter sits on the $U=X$ branch and the other on the mirror $V=X$ branch.
     - Every other class stays at least $4.248\times10^{-3}$ bits below $2B_T$. The five best
       such classes all tie at this value, e.g. $f=(1,2,3;1,2,3)$, which does not depend on
       $U$. This bears on Nair's open question (ITA 2020) about other local maximizers: in our
       search, none comes within $4\times10^{-3}$ of the product value.
   - (b) On 26 further dual points $(\alpha,a_1)$, with $\alpha\in\{0.1,0.25,0.4,0.5,0.6,0.75,0.9\}$
     and $a_1\in[-1,1]$ (logs `out/bssc_scan*`), the maximum of $B_2-2B_1$ found is
     $6.7\times10^{-16}$.
   - (c) Direct maximization of the two-letter form $L^{1/2}$ with $W$ and stochastic $X$,
     using no cardinality reduction and no minimax:
     - *Unseeded multistart*, with $|W|,|U|,|V|=(2,4,4)$, $(3,3,3)$ and $(4,4,4)$ and 300, 300
       and 150 starts respectively, never exceeds $2M_T=0.7232858$. But it **also never
       reaches** $2M_T$: best values 0.69696, 0.68942 and 0.68664. So it is weak evidence; the
       landscape is badly multimodal for unstructured local search.
     - *Seeded*: 200 starts from the product of the two one-letter RTD optimizers
       ($|W|=|U|=|V|=4$), perturbed in softmax coordinates with $\sigma\in\{0.05,0.2,0.5,1,2\}$.
       All return to $\le2M_T$, with maximum $2M_T-2.1\times10^{-9}$, i.e. optimizer
       tolerance. For $\sigma\le1$ all 160 return to within $10^{-6}$ of $2M_T$. This is a
       numerical neighbourhood check consistent with Nair's local tensorization.

   This is evidence, not proof, that two-letter Marton = one-letter Marton on the BSSC. It
   agrees with AGN's report (Claim 1a).
5. **[heuristic]** (numerical) Random binary-input channels: $2\times k_Y$ and $2\times k_Z$ with
   $k\in\{2,3\}$, rows Dirichlet with concentration in $\{0.3,1,3\}$, and with probability
   1/3 a zeroed entry (Z-like rows).
   - (a) 152 channels at random dual points ($\alpha\sim U(0.05,0.95)$, $a_1\sim N(0,1)$).
   - (b) 44 channels at *tied* dual points, where both one-letter branches ($U=X$ and $V=X$)
     attain $B_1$. This is the randomized-time-division regime where the BSSC optimum lives.
     Only about 1 in 20 random (channel, $\alpha$) pairs has such a point, so they were found by
     resampling.

   No trial shows $B_2-2B_1>10^{-9}$. The maximum found is $3.1\times10^{-15}$ in (a) and
   $1.8\times10^{-15}$ in (b). This is a small sample next to AGN's reported searches; its value is that it
   is reproducible and includes ternary outputs.
6. **[proved]** (bounded slopes) Let $C$ be any BC with binary input (arbitrary finite outputs).
   For every $\alpha$, the functions $m_C$ and $\ell^\alpha_C$ are concave on $[0,1]$ and satisfy
   $0\le m_C(p)\le\ell^\alpha_C(p)\le I_p(X;YZ)\le h(p)$. Hence every supergradient at
   $p\in(0,1)$ lies in $[-h(p)/(1-p),\,h(p)/p]$, so its absolute value is at most
   $S(p):=h(p)/\min(p,1-p)$.
7. **[proved]** (binary-input shaping has non-vanishing weight) Let $T'=\lambda T\oplus(1-\lambda)C$
   be a receiver-revealed mixture (HLL Prop. 3 style) of binary-input BCs on the *same*
   binary input. Here $C$ may itself be a mixture, and any extra receiver outputs are allowed.
   Then:
   - $\ell^\alpha_{T'}\le\lambda\ell^\alpha_T+(1-\lambda)\ell^\alpha_C$;
   - if a concave $f$ with $s:=\operatorname{dist}(0,\partial f(p^*))>0$ is used as the base
     majorant (as $f=UB$ is in HLL (12), (50)), then $p^*$ maximizes the shaped majorant
     $\lambda f+(1-\lambda)\varphi$ (for any concave $0\le\varphi\le h$, e.g. $\varphi=\ell^\alpha_C$) only if
     $$1-\lambda\ \ge\ \frac{s}{s+S(p^*)} .$$

   In HLL's Thm 2 / Thm 4 the shaping weight is $1-\lambda_L=O(1/L)\to0$. That relies on
   $h_2(p_i)+p_iL$ having slope $L+O(1)\to\infty$, which requires the input-side label $K\in[N]$.
   No binary-input construction, in particular none that adds components only on the output
   side, can reproduce the limit $1-\lambda\to0$.
8. **[heuristic]** (why this kills HLL's Thm 4 limit, not just its proof) With $1-\lambda$
   bounded below, the loss terms in HLL's (53) no longer vanish. Their analogue for a
   binary-input component is the difference between its one-letter value at $p^*$ and half its
   two-letter contribution under the base witness $P^*$. For the conversion to survive, these
   loss terms must be below the fixed-input gain (about $3\times10^{-6}$ nats in HLL's ternary
   example) divided by $1-\lambda$. HLL's components are loss-free up to $\delta h_2$ only
   because $K$ is independent of $P^*$ and invisible to $T$. A binary-input component sees the
   same $X^2$ law as $T$, with auxiliaries tuned to $T$. We could not turn this into a theorem
   (Dead ends).
9. **[proved]** (when no shaping is needed; seed of HLL absent for binary input)
   - (a) If $T$ is skew-symmetric, i.e. invariant under $x\mapsto1-x$ together with swapping
     the receivers (the BSSC is), then $m_T(p)=m_T(1-p)$. With concavity this gives
     $\max_pm_T=m_T(\tfrac12)$. So a fixed-input gain at $p=\tfrac12$ is already an
     unconstrained gain $M_{T\otimes T}>2M_T$: for the BSSC, constraint removal is unnecessary.
   - (b) For binary input, $B_T(\alpha,a)$ is attained with $U$ or $V$ constant (AGN Thm 3:
     $|U|+|V|\le3$ and $X=f(U,V)$), so the optimizers of the one-letter dual are Markov. HLL's
     discovery chain was: non-Markov one-letter optimizer ⟶ failure of local tensorization ⟶
     non-additivity ⟶ fixed-input gain ⟶ unconstrained gain. For binary input its first link
     cannot occur, and its second is excluded by Nair's Prop. 2.6. So a binary counterexample
     would need a two-letter dual value above $2B_T$ at distributions outside some
     neighbourhood of the product maximizers.
10. **[sketch]** (computer-assisted two-letter bound for the BSSC; float64, not interval
    arithmetic) $B_{T\otimes T}(\tfrac12,0)\le2B_T(\tfrac12,0)+0.01+10^{-9}$. Hence, by Claim 3,
    $$\tfrac12M_{T\otimes T}\le M_T+0.0050000006\le0.36664289\ \text{bits}.$$
    So the two-letter Marton sum rate of the BSSC is certified below the certified outer bound
    $0.369297201$: two-letter Marton cannot close the window, and any two-letter gain is at most
    $0.005$ bits per letter.
    - *Method:* a simplicial branch-and-bound (`bnb_dc.py`) over every one of the 860 map classes
      and both branches of Claim 3, covering each 5-simplex (resp. 3-simplex) completely. It uses a
      DC bound valid on every simplex (Details).
    - *Effort:* all 862 problems PROVED with no abort, using $2.317\times10^9$ simplices in total.
      The hardest classes, `23:022133` (the product-optimum class) and `23:011233`, took
      $3.15\times10^7$ simplices each. Wall time was about 35 min on 4 cores. Logs
      `out/bnb_eps0.01_shard*of4.txt`.
    - *Why only a sketch:* the arithmetic is float64 with a fixed margin of $10^{-9}$ against an
      a-priori rounding budget of order $10^{-11}$ (Details), not outward-rounded interval
      arithmetic. The result also rests on AGN 2019 Thm 3 (cited).
    - *Upgrade path:* re-running the same leaves in interval arithmetic would make this
      `[proved]`. This is routine but costs far more CPU in mpmath.

## Details

**Proof of Claim 2.** Fix $P=P_{WUVX_1X_2}$ with input marginals $P_1,P_2$ and $\tfrac12(P_1+P_2)=p$.
1. $M_{T\otimes T}(P)\le L^\alpha_{T\otimes T}(P)$, because $M=\min_tL^t$.
2. HLL (24) applied to the channel $T\otimes T$ with cost $a\oplus a$ gives
   $L^\alpha_{T\otimes T}(P)\le\alpha H(Y_1Y_2)+\bar\alpha H(Z_1Z_2)+B_{T\otimes T}(\alpha,a\oplus a)-a\cdot P_1-a\cdot P_2$.
3. Use $H(Y_1Y_2)\le H(Y_1)+H(Y_2)$, the same for $Z$, and the assumption $B_{T\otimes T}=2B_T$.
   The right side is then at most $UB^{\alpha,a}_T(P_1)+UB^{\alpha,a}_T(P_2)$.
4. $UB^{\alpha,a}_T$ is concave (entropy is concave and the rest is affine), so this is
   $\le2UB^{\alpha,a}_T(p)$. $\square$

The pair attaining $UB=m_T(p)$ exists under GGNY's max–min theorem plus envelope duality,
$\mathcal C[\varphi](p)=\inf_a\{\max_q(\varphi(q)+a\cdot q)-a\cdot p\}$ (AGN (10)). For the BSSC
we do not need this: Claim 3(b) exhibits the pair directly.

**Proof of Claim 3.**
- (a) By GJNW Thm 1 (pointwise in $p_X$): $\max_{U,V|X}[I(U;Y)+I(V;Z)-I(U;V)]=\max\{I_Y(q),I_Z(q)\}$
  for binary $X$. Equivalently, AGN Thm 3 gives $|U|+|V|\le3$ with $X=f(U,V)$, i.e.
  ($U=X$, $V$ const) or the mirror. So $B_T(\alpha,a)=\max_q\max\{\psi_Y,\psi_Z\}$ with
  $\psi_Y(q)=-\alpha H_Y(q)-\bar\alpha H_Z(q)+I_Y(q)+a\cdot(1-q,q)$, and $\psi_Z$ the same with
  $I_Z$.
  - For the BSSC: $H_Y(q)=h(q/2)$, $H_Z(q)=h(\tfrac{1-q}2)$, $I_Y=h(q/2)-q$, $I_Z=h(\tfrac{1-q}2)-(1-q)$.
  - At $(\tfrac12,0)$, $\psi_Y(q)=\tfrac12h(\tfrac q2)-\tfrac12h(\tfrac{1-q}2)-q$ and $\psi_Z(q)=\psi_Y(1-q)$.
    This gives (a).
- (b) $UB^{1/2,0}(\tfrac12)=\tfrac12h(\tfrac14)+\tfrac12h(\tfrac14)+B_T(\tfrac12,0)$, and the
  bracket in (a) at $q=a$ is exactly the RTD sum rate $S(a)$ of the previous attempt's Claim 6
  minus $h(\tfrac14)$. The maximum over $a$ is the RTD sum rate, which is achievable. For the
  upper bound, every $P$ satisfies
  $M_T(P)\le L^{1/2}_T(P)\le UB^{1/2,0}(p_X)=\tfrac12h(\tfrac p2)+\tfrac12h(\tfrac{1-p}2)+B_T(\tfrac12,0)\le h(\tfrac14)+B_T(\tfrac12,0)$
  (HLL (24), then concavity and symmetry about $\tfrac12$). Combined with the RTD lower bound,
  this reproves $M_T=0.3616428844\ldots$ (known: GJNW), with no minimax needed.
- (c) Apply HLL (24) to $T^{\otimes n}$, with $q_i$ the marginal of $X_i$:
  $M(P)\le\tfrac12H(Y^n)+\tfrac12H(Z^n)+B_{T^{\otimes n}}(\tfrac12,0)
  \le\sum_i\tfrac12[h(\tfrac{q_i}2)+h(\tfrac{1-q_i}2)]+B_{T^{\otimes n}}$.
  Each summand is at most $h(\tfrac14)$. $\square$

Cardinality: AGN Thm 3 is stated for $\max_{p(x)}\{\ldots+\max_{p(u,v|x)}[(\delta_1+\gamma_2)I(U;Y)+\gamma_2I(V;Z)-\gamma_2I(U;V)]-\sum d_xp(x)\}$.
With $\delta_0=\delta_1=0$, $\gamma_2=1$ and $\lambda=\alpha$, the terms $-\alpha I(X;Y)-\bar\alpha I(X;Z)$
differ from $-\alpha H(Y)-\bar\alpha H(Z)$ by terms linear in $p(x)$, which are absorbed into
$d$. So it covers $B_{T\otimes T}(\alpha,a\oplus a)$ with $|\mathcal X|=4$. (AGN Remark 9ff.
make the same reduction for products of binary-input channels.)

**Proof of Claim 6.**
- *Nonnegativity:* take constant auxiliaries.
- $m_C\le\ell^\alpha_C$, because $M=\min_tL^t$.
- $L^\alpha_C(P)\le I(X;YZ)$. Bound $\alpha I(W;Y)+\bar\alpha I(W;Z)$ by the larger of the two;
  say it is $I(W;Y)$. Then
  $I(V;Z|W)-I(U;V|W)\le I(V;ZU|W)-I(U;V|W)=I(V;Z|UW)$, so
  $L\le I(W;YZ)+I(U;YZ|W)+I(V;YZ|UW)=I(WUV;YZ)\le I(X;YZ)\le h(p)$.
  The case $I(W;Z)$ is symmetric, using $I(U;Y|VW)$.
- *Concavity:* HLL Lemma 6 for $m_C$. The same time-sharing argument, $W'=(Q,W_Q)$ and
  $I(W';Y)\ge$ the average, gives concavity of $\ell^\alpha_C$.
- *Slopes:* for a concave $\varphi$ with $0\le\varphi\le h$ and supergradient $g$ at $p$,
  - $\varphi(1)\le\varphi(p)+g(1-p)$ gives $g\ge-h(p)/(1-p)$;
  - $\varphi(0)\le\varphi(p)-gp$ gives $g\le h(p)/p$. $\square$

**Proof of Claim 7.**
- The receiver-revealed state $Q$ is independent of $(W,U,V,X)$ and seen by both receivers, so
  each mutual-information term of $L^\alpha_{T'}$ splits exactly as $\lambda(\cdot)_T+(1-\lambda)(\cdot)_C$.
  This is HLL App. D without the min. Maximizing over $P_{WUV|X}$ at fixed $p$ gives the
  inequality.
- On $[0,1]$, the superdifferential of a finite concave function at an interior point is an
  interval. Since $0\notin\partial f(p^*)$, all its elements have one sign and modulus $\ge s$.
- $p^*$ maximizes the concave $\Phi=\lambda f+(1-\lambda)\varphi$ iff
  $0\in\partial\Phi(p^*)=\lambda\partial f(p^*)+(1-\lambda)\partial\varphi(p^*)$.
- By Claim 6, $|g'|\le S(p^*)$ on $\partial\varphi(p^*)$. So $0=\lambda g+(1-\lambda)g'$
  forces $\lambda s\le(1-\lambda)S(p^*)$. $\square$

For HLL's own component $G_i$, the function $h_2(p_i)+p_iL$ exceeds $h(p)$ as soon as $L>0$.
It needs $H(G_i)$ up to $p_i\log N$, i.e. input entropy beyond one bit. This is exactly what an
output-side-only modification of a binary-input channel cannot supply.

**Claim 9(a).** Let $\sigma$ relabel $x\mapsto1-x$ and swap the receivers, with $(W,U,V)\mapsto(W,V,U)$.
This maps feasible distributions with marginal $p$ to feasible distributions with marginal
$1-p$ for $\sigma T=T$, and it preserves $M$, since $M$ is symmetric under $(U,Y)\leftrightarrow(V,Z)$.
Therefore $m_T(p)=m_T(1-p)$, and concavity puts the maximum at $\tfrac12$. If $P$ has average
marginal $\tfrac12$ and $M_{T\otimes T}(P)>2m_T(\tfrac12)=2M_T$, that is already an unconstrained
two-letter gain.

**Claim 10: the DC bound and its rounding budget.** For a map class, $G(P)=c(P)+k(P)$ with
$c=\tfrac12H(Y^2)+\tfrac12H(Z^2)+H(U,V)$ and $k=-H(U,Y^2)-H(V,Z^2)$. Each is an entropy of a
linear image of $P$, so $c$ is concave and $k$ convex; for the branches,
$c=\tfrac12H(Z^2)-E\,H(Z^2|x)$ and $k=-\tfrac12H(Y^2)$, or the mirror.

*Bound on a simplex.* Let $S=\operatorname{conv}\{v_0,\dots,v_d\}$ be full-dimensional in the
probability simplex, and let $x_0$ be its centroid, which is interior, so $\nabla c(x_0)$ is
finite. For $x=\sum_i\lambda_iv_i\in S$:
- $c(x)\le\ell(x):=c(x_0)+\nabla c(x_0)\cdot(x-x_0)$, by concavity;
- $k(x)\le\sum_i\lambda_ik(v_i)$, by convexity;
- $\ell$ is affine.

Hence $G(x)\le\sum_i\lambda_i[\ell(v_i)+k(v_i)]\le\max_i[\ell(v_i)+k(v_i)]=:UB(S)$.

*Algorithm.* Start from the whole simplex. Discard $S$ iff $UB(S)+10^{-9}\le2b_1+\varepsilon$;
otherwise bisect its longest edge. The constant parts $-1/\ln2$ of the entropy gradients cancel
because $\sum_j(x-x_0)_j=0$. Here $b_1$ is the float value of $\psi_Y$ at the computed
maximizer, which is $\le B_T(\tfrac12,0)+10^{-15}$. Termination with every leaf discarded proves
$\max G\le2B_T+\varepsilon+10^{-9}+2\cdot10^{-15}$ on that class, up to rounding.

*Rounding budget.* $UB(S)$ is a sum of at most about 60 terms:
- entropies of 4- to 12-point distributions, magnitude $\le4$;
- gradient terms $|\log_2 p|\cdot|v-x_0|_1$, with $|v-x_0|_1\le2$.

We did not log the smallest centroid probability. The code clips probabilities at $10^{-300}$
inside logarithms, so $|\log_2p|\le997$. The clip would make the tangent plane wrong if it
were ever active, but that would need a simplex of diameter about $10^{-300}$, and simplices are
discarded at diameters many orders larger.

Each term carries a few ulps of relative error, so even in this worst case the total is
$\lesssim60\cdot2000\cdot2^{-50}\approx10^{-10}$, below the margin $10^{-9}$. At realistic
depths it is about $10^{-12}$. This estimate is exactly the step a fully rigorous version would
replace by outward rounding, which is why Claim 10 is tagged `[sketch]`.

*Checks.*
- `bnb_validity_test.py`: on $2\times10^6$ random sub-simplices with radii in $[10^{-4},1]$ and
  random interior points, $G(x)-UB(S)\le-1.3\times10^{-7}$ over 25 problems. Concavity of $c$
  and convexity of $k$ also hold along random segments.
- Negative controls (`out/bnb_negative_control.txt`): with a target $10^{-3}$ below the true
  maximum (product class), or $10^{-4}$ below a branch maximum, the B&B never terminates
  "PROVED". It aborts at the cap, as it must.

**Numerical method (Claims 4, 5).**
- `ml_core.py`:
  - $B_1$ by a 200,001-point grid plus golden section on each branch;
  - the two-letter dual $G=\bar\alpha H(Y^2)+\alpha H(Z^2)-H(U,Y^2)-H(V,Z^2)+H(U,V)+E\,a(X)$,
    an identity that follows from $I(U;Y)=H(Y)-H(UY)+H(U)$, with analytic gradient;
  - batched exponentiated-gradient (mirror) ascent on the simplex, over all canonical maps at
    once, with Dirichlet starts of concentration $\{0.2,0.5,1,3\}$;
  - L-BFGS polish in softmax coordinates.
- *Map enumeration:* all $4^6$ maps $f:[2]\times[3]\to\{0,1\}^2$ modulo the $2!\cdot3!$
  relabellings, giving 430 classes; likewise 430 for $[3]\times[2]$. Degenerate maps are kept;
  they represent faces.
- *Branches:* $(U=X^2,V\text{ const})$ and mirror, by Nelder–Mead on the 3-simplex.
- *Gradient check:* finite differences agree to $10^{-6}$.
- *One-letter reduction check* (`check_one_letter.py`): on 40 random channels, brute-force
  stochastic $|U|=|V|=3$ never exceeds $B_1$; the maximum excess is $+1.1\times10^{-16}$.

## Verification

All runs used `OMP_NUM_THREADS=1` and `nice`. The Python was 3.14 with numpy 2.5.5, scipy 1.18.1
and mpmath 1.4.1; mpmath is unused here. Commands, run from `code/multiletter/`:

```
python check_one_letter.py 40 3                  # Claim 3(a) sanity: max(brute - B1) = +1.110e-16
python bssc_two_letter.py center 256 3000 1      # Claim 4(a)                 (~25 min)
python bssc_optimizer_structure.py 32 2000 5     # Claim 4(a), structure      (~4 min)
python bssc_two_letter.py scan 32 1500 2         # Claim 4(b): first 10 rows, then stopped (slow)
python bssc_two_letter.py scan 16 800 3 0.25,0.4,0.5,0.6,0.75,0.9 -0.5,0,0.5   # Claim 4(b)
python direct_marton.py 300 5 2 4 4              # Claim 4(c), unseeded
python direct_marton.py 300 6 3 3 3
python direct_marton.py 150 7 4 4 4
python direct_marton.py seeded 40 3              # Claim 4(c), seeded at the product RTD optimum
python random_search.py 180 11 24 1000           # Claim 5(a)  (stopped after 20 trials each;
python random_search.py 180 12 24 1000           #   earlier code version, polish of 4 maps)
python random_search.py 400 21 16 800            # Claim 5(a)  (stopped after 56 trials each)
python random_search.py 400 22 16 800
python random_search.py 400 31 16 800 tied       # Claim 5(b)  (stopped, see logs)
python random_search.py 400 32 16 800 tied
python random_search.py 400 33 16 800 tied
python bnb_validity_test.py 20000 1              # Claim 10: DC-bound validity
python bnb_dc.py negctl                          # Claim 10: negative controls
for k in 0 1 2 3; do python bnb_dc.py 0.01 4e8 $k/4; done   # Claim 10 (4 shards run in parallel)
python bnb_dc.py proto                           # Dead end 1, cost data
```

Key outputs (full logs in `code/multiletter/out/`):

```
[bssc_center_256x3000_seed1.txt]
B_1(1/2,0) = -0.449635240037178 at q = 0.1584349713 (UX);  2 B_1 = -0.899270480074356
best value found  B_2 >= -0.899270480074355   (B_2 - 2B_1 = 8.882e-16)
map classes attaining 2B_1 (within 1e-10): 66 of 862
best map classes NOT attaining 2B_1:
   23 f=[1, 2, 3, 1, 2, 3]  value - 2B_1 = -4.248004e-03      (4 more classes at the same value)
[bssc_optimizer_structure_32x2000_seed5.txt]
near-optimal classes: 64 ; max I(X1;X2) = 4.44e-16 ; max I(U;V|X) = 4.44e-16
   (all 64 with marginals (P(X1=1), P(X2=1)) = (0.15843, 0.84157) or (0.84157, 0.15843))
[bssc_scan*]  27 dual points incl. (1/2,0): max (B_2 found - 2 B_1) = 6.661e-16
[direct_*]    unseeded best L_1/2 = 0.696961 (2,4,4), 0.689417 (3,3,3), 0.686640 (4,4,4)
              vs 2 M_T = 0.723286;  seeded: overall max L_1/2 - 2M1 = -2.149e-09
[random_seed1*/2*]  152 trials, max (B_2 found - 2 B_1) = +3.109e-15, no FLAG
[random_tied_seed3*]  44 tied trials (seeds 31-33), max (B_2 found - 2 B_1) = +1.776e-15, no FLAG
[bnb_eps0.01_shard{0,1,2,3}of4.txt]  each ends "SHARD RESULT: ALL PROVED"; 216+216+215+215 = 862
              problems (860 map classes + 2 branches), 0 ABORT, total simplices 2,316,557,204
[bnb_validity_test.txt]   max G(x) - UB(S) = -1.276e-07 ; max concavity/convexity violation = -8.095e-08
[bnb_negative_control.txt] targets below attained values: ABORT (as required)
```

What the computations do **not** establish:
- They give no upper bound on $B_{T\otimes T}$. Multistart can miss a narrow basin; in HLL's
  ternary example, a step-1/30 grid missed the witness basin. Our starts are random and
  include sparse Dirichlet draws, but there is no coverage guarantee.
- The random-channel sample is small compared with AGN's reported searches.
- Not independently reviewed.

## Dead ends

1. **Pushing the Claim 10 certificate to $\varepsilon\to0$** (i.e. proving two-letter Marton =
   one-letter Marton on the BSSC by the same DC branch-and-bound).
   - *Cost data for the hardest class*, the one carrying the product optimum
     $f=\begin{psmallmatrix}0&2&2\\1&3&3\end{psmallmatrix}$ (`out/bnb_proto.txt`,
     `out/bnb_product_map_large.txt`):

     | $\varepsilon$ (bits) | simplices |
     |---|---|
     | 0.1 | $9.2\times10^5$ |
     | 0.03 | $6.7\times10^6$ |
     | 0.015 | $1.85\times10^7$ |
     | 0.01 | $3.15\times10^7$ (inside the Claim 10 run) |

     The empirical cost grows like $\varepsilon^{-1.6}$ to $\varepsilon^{-1.7}$ per hard class,
     and 66 classes are hard.
   - *Obstruction:* the optimum $2B_T$ is attained, on a positive-dimensional set (flat
     directions from splitting a $V$-symbol) in 66 classes. Any first-order bound has excess of
     order $\text{diam}^2$, or diam × log near faces, at the maximizers. So the B&B can only
     prove $2B_T+\varepsilon$, never $2B_T$ itself, and its cost diverges as $\varepsilon\to0$.
   - *What would close it:* a quantitative second-order (local-concavity) bound in a
     neighbourhood of the product manifold, for instance a quantitative version of Nair's local
     tensorization, combined with this B&B outside the neighbourhood. We did not attempt that.
2. **Direct two-letter Marton search with HLL's alphabet sizes** ($|W|=2$, $|U|=|V|=4$).
   - *Result:* it peaks at about 0.6970 bits, well below $2M_T=0.7233$.
   - *Obstruction:* the product of two RTD schemes needs $W=(W_1,W_2)$, i.e. $|W|=4$. With
     $|W|=2$ it is not representable. HLL's sizes are tuned to their ternary witness. Direct
     search without the dual is also far less reliable than the dual search.
3. **Output-side-only version of HLL's constraint removal** (Claims 6–8).
   - *Obstruction:* this is impossible with vanishing weight; precisely, $1-\lambda\ge s/(s+S(p^*))$.
   - *What we could not prove:* that *every* binary-input shaping must destroy a given
     fixed-input gain. That would need the two-letter losses of the shaping components under
     $P^*$ to be bounded below in terms of their slope. We see no reason for a uniform bound,
     and we do not claim one.
4. **Looking for HLL's seed in binary input.** Non-Markov dual optimizers cannot occur at one
   letter (Claim 9b). At two letters ($T\otimes T$ is 4-ary) they could exist in principle, but
   every two-letter optimizer we found is a product distribution, hence Markov.

## Novelty check

- *Where we looked:* HLL (full text); Liu–Huang arXiv:2608.13170; Gohari–Liu–Nair (ISIT 2025,
  extended PDF `Mar-Con.pdf` on Nair's page); Anantharam–Gohari–Nair TIT 2019
  (`Marton-update.pdf`) and ISIT 2013; Geng–Jog–Nair–Wang TIT 2013 and arXiv:1001.1468;
  Geng–Gohari–Nair–Yu ITA 2011 and TIT 2014 (arXiv:1105.5438); Gohari–Nair–Anantharam
  arXiv:1202.0898; Nair ITA 2020 (`loc-ten-bin.pdf`); Gohari–Liu–Nair GK-outer (ISIT 2026);
  Semantic Scholar citations of HLL (2611.01583, 2610.25490 and 2610.22404 checked;
  2609.29954 not checked); arXiv searches for post-August-2026 Marton papers. All are author-hosted
  or arXiv PDFs read via `pdftotext`. We did not access the ISIT 2025 proceedings text itself,
  any talk slides, or Google Scholar.
- **Known, not claimed as new:**
  - the dual two-letter criterion (Claim 2 is a special case of AGN Lemma 2);
  - the $|U|+|V|\le5$ reduction for products of binary-input channels (AGN Remarks 9–10);
  - "no two-letter gain found for binary-input, binary-output channels" (AGN; the BSSC is in
    this class);
  - local tensorization (Nair 2020);
  - two-letter RTD factorization (GGNY 2011).
- **Believed new, modest:**
  - the explicit one-point BSSC reduction with the exact identity $h(\tfrac14)+B_T(\tfrac12,0)=$
    RTD optimum (Claim 3), together with the $n$-letter form 3(c);
  - a public, reproducible two-letter search code and its BSSC output (Claim 4), including the
    gap to the best non-product local optimum, which bears on Nair's open question about other
    local maximizers;
  - the bounded-slope obstruction to binary-input versions of HLL's constraint removal
    (Claims 6–7). HLL is from Aug. 2026, and none of the citing papers we checked discusses
    binary input;
  - the observation that skew-symmetric channels need no constraint removal (Claim 9a);
  - the computer-assisted bound $\tfrac12M_{T\otimes T}\le0.36664$ bits for the BSSC (Claim 10,
    `[sketch]`). We know of no previous quantitative upper bound on any multi-letter Marton sum
    rate of the BSSC beyond the trivial one, the capacity upper bounds.

## References

- M. Huang, Y. Liu, Y. Liu, "Sub-optimality of Marton's inner bound for the two-receiver
  broadcast channel," arXiv:2608.19869v1, 2026 [HLL]. Eqs. (2)–(4), (23)–(24), Thms 2, 4,
  Prop. 3, App. C–E used.
- V. Anantharam, A. Gohari, C. Nair, "On the evaluation of Marton's inner bound for two-receiver
  broadcast channels," IEEE TIT 65(3):1361–1371, 2019. Thm 3, Prop. 1, eq. (10), Lemma 2,
  §II-C and Remarks 9–10 used.
- Y. Geng, V. Jog, C. Nair, Z. V. Wang, "An information inequality and evaluation of Marton's
  inner bound for binary input broadcast channels," IEEE TIT 59(7):4095–4105, 2013 (Thm 1).
- Y. Geng, A. Gohari, C. Nair, Y. Yu, "On Marton's inner bound for two receiver broadcast
  channels," ITA 2011 (Thm 3); and "The capacity region of classes of product broadcast
  channels," IEEE TIT 60(1):22–41, 2014 (max–min theorem).
- C. Nair, "On Marton's achievable region: local tensorization for product channels with a
  binary component," ITA 2020 (Prop. 2.6, Remark 2.7).
- A. Gohari, Y. Liu, C. Nair, "A conjecture regarding the optimizers of Marton's inner bound for
  the two-receiver broadcast channel," ISIT 2025 (extended version read; Conjectures 1–2).
- Y. Liu, M. Huang, arXiv:2608.13170, 2026 (no binary-input remark).
- Prior attempts: `2026-11-26-claude-opus-5-5-certified-bounds.md` (RTD value, Claim 6 there);
  `attempts/marton-inner-bound-tightness/2026-11-26-claude-opus-5-5-hll-counterexample-audit.md`.
