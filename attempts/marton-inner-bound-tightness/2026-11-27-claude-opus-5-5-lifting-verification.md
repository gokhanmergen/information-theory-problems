---
problem: marton-inner-bound-tightness
date: 2026-11-27
attempter: claude
model: claude-opus-5-5
type: partial-result
status: unverified
---

## Summary

This file checks the steps of Huang–Liu–Liu [HLL, arXiv:2608.19869v1] that the two earlier
attempts left unchecked:
- the analytic **lifting**: the dual bound (24), Theorem 2 (gradient shaping), eq. (9),
  Proposition 3, eq. (12), Theorem 4 (constraint removal) and Lemma 6;
- the **explicit lifted instance**, (30)–(43);
- the **final transfer** from $M_{\tilde T^{\otimes2}}>2M_{\tilde T}$ to "Marton's region
  (with $W$) is strictly inside the capacity region".

We wrote complete proofs of every analytic step in our own words, and found **no logical
gap**. There are presentation slips, listed in Claim 8. None affects validity:
- an $\alpha\leftrightarrow1-\alpha$ mislabel in (24);
- a superfluous hypothesis in Proposition 3;
- the both-shaping selector pairs in (51) are not spelled out (we supply the computation);
- printed (43) is computed from unrounded values, so it does not follow from printed (40)
  and (42) by $4.6\times10^{-17}$.

We re-certified every numerical inequality of (30)–(43) with exact rationals and
python-flint/Arb balls; no float enters any decision. The gap (43) holds:
$M_{\tilde T^{\otimes2}}-2M_{\tilde T}\ge1.8821256327185508\times10^{-6}$ nats, using HLL's
(25). With our sharper certified one-letter value ($B_T<G_T(19)+10^{-12}$) it is
$\ge2.88\times10^{-6}$ nats. With the exact $I(U;V|W)=0.00926\ldots$ in place of HLL's crude
$\ln4$ it is $\ge2.51\times10^{-6}$ (or $\ge3.51\times10^{-6}$ with the sharper value).

**Conclusion.** Combined with the independent certificate of the one-letter bound
(`2026-11-27-claude-opus-5-5-independent-certificate.md`), the whole HLL chain is now
independently checked. The explicit finite channel $\tilde T$ of HLL (30)–(35) satisfies
$M_{\tilde T^{\otimes2}}>2M_{\tilde T}$. Hence Marton's one-letter region, with the common
auxiliary and with or without a common message, is strictly inside the capacity region of
$\tilde T$. Both frozen Lean `Statement`s (`MartonInnerBoundTightness`, `BroadcastChannel`) are
therefore false.

This rests on three things, listed under Verification:
- Anantharam–Gohari–Nair 2019 Thm 3, cited;
- Marton's coding theorem, cited;
- Arb plus our own code.

There is no Lean proof.

## Approach

1. **Reading.** We read HLL in full (Secs. I–IV, App. A–E, from the arXiv PDF text), the two
   earlier attempts with their reviewer notes, and their code.
2. **Analytic steps.** Each step was re-proved from scratch (Claims 1–4, Details §1–§4). For
   every step we wrote down which hypotheses are used, and tried to break it:
   - *Small exact instances.* `code/lifting/test_lifting_identities.py` builds the
     receiver-revealed mixture channel symbol by symbol for small $N$, computes every Marton
     quantity from the full joint law, and tests (9), (10), (11), (12) and (51) on random
     instances. A negative control checks that the test has power.
   - *Independent referee.* A separate agent was given only the paper and asked to referee
     the same steps adversarially. Its report is summarized under Verification.
3. **Explicit instance.** `code/lifting/lifted_instance_arb.py` re-certifies (30)–(43) from
   scratch. It reuses the exact constants of `code/independent-cert/model.py`, the Appendix-A
   table loader of `code/independent-cert/fixed_input_gap_arb.py`, and the certified targets
   $T_5,T_{12}$ from `code/independent-cert/results_*.json`; it does not re-transcribe any of them. The lift
   weights (32) are cross-checked against `code/hll_check.py`. We evaluate the two-letter
   functional ourselves, with $W=(Q,W_c)$ as one variable, and the gradient of $\Phi$ directly
   rather than through HLL's surrogate $b$.
4. **Transfer.** The final transfer is written against the Lean definitions
   (`IsBCCommonAchievable`, `bcCommonCapacityRegion`, `martonCommonInnerBound`), including
   odd blocklengths and the message-set rounding.

HLL's repository (commit `cc33e85`, cloned earlier into a scratch directory) was consulted
only to see what their `verify_unconstrained_lift.cpp` computes. Nothing from it is used.

## Claims

Notation. All alphabets are finite and all logs natural. For a DMBC $T$ with marginals
$T_{Y|X},T_{Z|X}$ and a law $P=P_{WUVX}$ with $(W,U,V)\to X\to(Y,Z)$, we use HLL's functional (2):

$M_T(P)=\min\{I(W;Y),I(W;Z)\}+I(U;Y|W)+I(V;Z|W)-I(U;V|W)$.

We also write $L_t(P)=(1-t)I(W;Y)+tI(W;Z)+I(U;Y|W)+I(V;Z|W)-I(U;V|W)$, so that
$M_T(P)=\min_{t\in[0,1]}L_t(P)$; this uses only that $L_t$ is affine in $t$, not the
Geng–Gohari–Nair–Yu max-min theorem. Further:
- $M_T(p)=\sup\{M_T(P):P_X=p\}$, the supremum over all finite $\mathcal W,\mathcal U,\mathcal V$;
- $M_T=\sup_pM_T(p)$;
- $G_T$, $B_T=\sup G_T$ and $UB$ are as in HLL (4), (23).

1. **[proved]** *(Dual bound, HLL (24), with corrected labelling.)* Fix $\alpha\in[0,1]$, $a\in\mathbb R^{\mathcal X}$
   and any real $\tau\ge B_T(\alpha,a)$. Then for every $p\in\Delta(\mathcal X)$,
   $M_T(p)\le f_\tau(p):=\alpha H_p(Y)+\bar\alpha H_p(Z)+\tau-a\cdot p$, and $f_\tau$ is finite and concave on $\Delta(\mathcal X)$.
   HLL's intermediate step "$\le L_{\alpha,T}(P_X)$" should read $L_{1-\alpha,T}(P_X)$ under their
   definition (3). The conclusion is unaffected, because $M_T(p)\le L_\beta(p)$ for every $\beta$.
2. **[proved]** *(HLL Theorem 2, gradient shaping.)* The statement is correct as written,
   with "sufficiently large $L$" meaning $L>\max_{i\ne r}\ln\frac{p^*_i}{1-p^*_i}$.
   We also prove the quantitative form used for the explicit instance:
   - **Lemma B.** If $\Phi$ is concave on $\Delta_d$ and has a supergradient $s$ at $p^*$ (for
     instance its gradient, where it is differentiable), then
     $\max_{\Delta_d}\Phi\le\Phi(p^*)+(\max_is_i-\min_is_i)$.
3. **[proved]** *(HLL eq. (9), Proposition 3, eq. (12).)* For the receiver-revealed mixture
   $\tilde T_L$ and *every* law $P_{WUV\tilde X}$:
   - identity (10) holds, and so does its analogue for every $L_t$;
   - (11) holds;
   - hence $M_{\tilde T_L}(P)\le\lambda M_T(p)+\sum_i\delta_i[h_2(p_i)+p_iL]$, where $p=P_X$.

   Two comments:
   - Proposition 3's hypothesis "$X$ is a function of $(U,V,W)$" is not needed.
   - The identity uses two facts: the selector $Q$ is independent of $(W,U,V,\tilde X)$ and
     revealed to both receivers, and the shaping outputs are *common*, which is what lets the
     $\min$ split.
4. **[proved]** *(HLL Theorem 4, constraint removal, and Lemma 6.)* Theorem 4 is correct as
   stated. Our proof of the two-letter bound (51) includes the selector pairs where *both*
   coordinates use shaping components, which HLL do not spell out. There the label credit is
   exactly $q_{X_1}(i)L+q_{X_2}(j)L$. "With $W$" is preserved: the lift puts the labels
   $K_1,K_2$ into the common auxiliary $\tilde W=(W,K_1,K_2)$, and the one-letter bound
   allows an arbitrary $W$. Lemma 6, the concavity of $p\mapsto M_T(p)$, is correct; it is used only
   for the "in particular" clause of Theorem 4.
5. **[proved]** *(Computer-assisted: exact rationals plus Arb balls at 320 bits.)* For HLL's
   explicit instance (30)–(35), with $M=2\cdot10^6$, $N=2^M$, $L=M\ln2$ and weights (32), every
   numerical inequality HLL use holds in the direction needed. The certified values are listed
   in Details §5. In particular:
   - (32): $\lambda+\delta_0+\delta_1=1$ exactly;
   - (37): range of $\nabla UB(p^*)-b$ $\le4.692109048907094\times10^{-22}$, below the printed bound;
   - (39): $\varepsilon:=\mathrm{range}\,\nabla\Phi(p^*)\le1.846757655822741\times10^{-17}$, below the printed $1.846843880121467\times10^{-17}$;
   - (40): $M_{\tilde T}\le0.3008418660991544625389$, below the printed $0.30084186609915448$;
   - (42): $M_{\tilde T^{\otimes2}}\ge0.6016856143239416436287$, above the printed $0.60168561432394163$;
   - (43): $M_{\tilde T^{\otimes2}}-2M_{\tilde T}\ge1.8821256327185508826\times10^{-6}$, above the printed $1.8821256327185490\times10^{-6}$.

   This uses the global one-letter bound $B_T<T_5$, which is independent-cert Claim 2 (equivalent to HLL (25)).
   With $B_T<T_{12}=G_T(19)+10^{-12}$ (independent-cert Claim 3), the gap is
   $\ge2.8821234047\times10^{-6}$.
6. **[proved]** *(Sharper explicit gap.)* Replacing HLL's bound $I(U;V|W)\le\ln4$ in (41) by
   the exact value $C=I(U;V|W)=0.0092647350296779100\ldots$ of their witness, and $\gamma$ by
   the exact two-letter functional $M_{T^{\otimes2}}(P^*)\ge0.18330459432780758988$ (with $W=(Q,W_c)$
   as one variable), the same channel has a gap of
   - $\ge2.5100987784669\times10^{-6}$ with $T_5$;
   - $\ge3.5100965504527\times10^{-6}$ with $T_{12}$.
7. **[proved]** *(Final transfer; uses Marton's coding theorem, which we cite and do not
   re-prove.)* Let $\tilde T$ be any finite DMBC with $M_{\tilde T^{\otimes2}}>2M_{\tilde T}$; by
   Claims 4 and 5 such channels exist. Then:
   - the capacity region contains $(0,R_1,R_2)$ with $R_1+R_2=\frac12M_{\tilde T^{\otimes2}}(P)>M_{\tilde T}$ for a suitable $P$;
   - every point of Marton's region satisfies $R_0+R_1+R_2\le M_{\tilde T}$.

   Hence Marton's region is strictly inside the capacity region, for:
   - the five-inequality region with a common message;
   - HLL's (1a)–(1d);
   - the private-message region.

   Against the Lean definitions this gives `¬ MartonInnerBoundTightness.Statement` and
   `¬ BroadcastChannel.Statement`. That is a mathematical proof, not a formal one. The
   argument handles the Lean-specific details: achievability for all large $n$, odd blocklengths,
   message sets $\max(1,\lfloor2^{nR}\rfloor)$, average joint error, and closures.
8. **[proved]** *(Presentation slips in HLL; none affects validity.)*
   - (a) The $\alpha$ labelling in (24) (Claim 1).
   - (b) Proposition 3's hypothesis "$X$ a function of $(U,V,W)$" is unnecessary, and the
     "input distribution $\pi$" in (11) plays no role.
   - (c) In (51), the both-shaping selector pairs are not treated explicitly (Claim 4).
   - (d) The printed (43) does not follow from the printed (40) and (42):
     $0.60168561432394163-2\cdot0.30084186609915448=1.88212563267\times10^{-6}<1.8821256327185490\times10^{-6}$.
     It was evidently computed from unrounded values. The true certified gap does exceed the
     printed (43), even with HLL's printed $\varepsilon_\nabla$ (Claim 5).
   - (e) "Concave envelope $f=UB$" (Sec. III-C) is a misnomer. $UB$ is simply a concave upper bound on $M_T(\cdot)$.
   - (f) The letter $Q$ names both the time-sharing variable inside $W$ in $P^*$ (Sec. III-B)
     and the channel selector of $\tilde T$ (Sec. II-A). These are different variables.
   - (g) (27) prints $0.1833045943206552249020$, which rounds the certified
     $\gamma=0.18330459432065522490176\ldots$ *up* by $2\times10^{-22}$. Their certified
     computation uses the correct value. This was already noted by the 2026-11-26 reviewer.
   - (h) Further slips, flagged by the independent referee pass (Verification):
     - App. C ends "so $p$ is a global maximizer"; it should read $p^*$.
     - In (41) and App. E, "contributes exactly $p^*_jL$" should be "at least". The excess is
       $I(W;E)$ plus $I(\tilde W;\text{other output}\mid G)$, both $\ge0$.
     - In (51)–(52) the left side should be $L_t(\tilde P)$ for the fixed lifted law, with
       $\min_t$ taken for that fixed law, as in our §4. Read as "$L_t$ maximised over all
       laws", the step to (52) would need a max–min theorem; it is never needed.
     - The symbol $U$ in (40) is undefined; it means the bound (25).
     - (24) says "let $P_{WUV|X}$ attain", which assumes a maximiser exists. Take any feasible law, then the supremum.
     - The functionals in Prop. 3 are written with argument $P_{UVWX}$. They must take
       $P_{WUV\tilde X}$, since $H(G_i)$ depends on $K$.
     - Theorem 1 omits the constraint $2R_0+R_1+R_2\le\ldots$. That does not matter here,
       because only the sum-rate bound (1d) is used.

## Details

### 1. The dual bound (Claim 1)

Let $P=P_{WUVX}$ have $P_X=p$, and write $P_w$ for the law of $(U,V,X)$ given $W=w$. Since
$(W,U,V)\to X\to(Y,Z)$, under $P_w$ we again have $(U,V)\to X\to(Y,Z)$ through the same
channel. Expand
$I(W;Y)=H(Y)-\sum_wP(w)H(Y|W=w)$, and likewise for $Z$, together with
$I(U;Y|W)=\sum_wP(w)I(U;Y|W=w)$, the analogous identities for the other conditional terms,
and $a\cdot p=\sum_wP(w)\sum_xp(x|w)a_x$. This gives

$\alpha I(W;Y)+\bar\alpha I(W;Z)+I(U;Y|W)+I(V;Z|W)-I(U;V|W)=\alpha H_p(Y)+\bar\alpha H_p(Z)-a\cdot p+\sum_wP(w)\,G_T(P_w)$,

with $G_T(P_{UVX})=-\alpha H(Y)-\bar\alpha H(Z)+I(U;Y)+I(V;Z)-I(U;V)+\sum_xp(x)a_x$, exactly HLL (4).
Each $G_T(P_w)\le B_T\le\tau$. Moreover
$\min\{I(W;Y),I(W;Z)\}\le\alpha I(W;Y)+\bar\alpha I(W;Z)$. So $M_T(P)\le f_\tau(p)$, and taking
the supremum over $P$ gives $M_T(p)\le f_\tau(p)$.

$f_\tau$ is concave because $p\mapsto H(T^\top p)$ is concave: $-t\ln t$ is concave and
$p\mapsto T^\top p$ is linear. $B_T$ is finite because $G_T\le\ln|\mathcal Y|+\ln|\mathcal Z|+\max a$.

The left-hand side above is $L_{1-\alpha}(P)$ in HLL's notation (3), not $L_\alpha(P)$, which is
the labelling slip (a). ∎

*Use in the chain.* With $\tau=T_5$ or $\tau=T_{12}$, the certified upper bounds of the
independent certificate, $f_\tau$ is a **certified** concave majorant of $M_T(\cdot)$ on the whole
simplex. Moreover $\nabla f_\tau=\nabla UB$, since the gradient does not depend on $\tau$.

### 2. Gradient shaping (Claim 2)

**Theorem 2 (HLL).** Let $f$ be finite and concave on $\Delta_d$, and let $p^*\in\mathrm{ri}\,\Delta_d$. Let $g$
be a supergradient, i.e. $f(p)\le f(p^*)+\langle g,p-p^*\rangle$ for all $p\in\Delta_d$. Such a $g$
exists because $p^*$ is in the relative interior of the domain; see Rockafellar, *Convex Analysis*, Thm 23.4.
- *Choice of weights.* Fix $r\in\arg\max g_i$. For $i\ne r$ put $A_i=L+\ln\frac{1-p_i^*}{p_i^*}$.
  Then $0<p^*_i<1$ (this needs $d\ge2$; see §4 for why $d=1$ cannot occur), and
  $L>\max_{i\ne r}\ln\frac{p^*_i}{1-p^*_i}$ makes every $A_i>0$.
- Define $\lambda=(1+\sum_{i\ne r}(g_r-g_i)/A_i)^{-1}\in(0,1]$ and $\delta_i=\lambda(g_r-g_i)/A_i\ge0$.
  Then $\lambda+\sum_{i\ne r}\delta_i=\lambda(1+\sum_{i\ne r}(g_r-g_i)/A_i)=1$.
- Each $\varphi_i(p)=h_2(p_i)+p_iL$ is concave on $\Delta_d$ and differentiable at $p^*$, with
  $\nabla\varphi_i(p^*)=A_ie_i$. So by the tangent inequality,
  $\varphi_i(p)\le\varphi_i(p^*)+A_i(p_i-p^*_i)$ for all $p\in\Delta_d$, including $p_i\in\{0,1\}$, by
  continuity of $h_2$.
- Multiply by $\delta_i\ge0$, add $\lambda\times$ the supergradient inequality for $f$, and set
  $\Phi_L=\lambda f+\sum\delta_i\varphi_i$. This gives
  $\Phi_L(p)\le\Phi_L(p^*)+\langle s,p-p^*\rangle$ with $s=\lambda g+\sum_{i\ne r}\delta_iA_ie_i$.
- Coordinatewise, $s_r=\lambda g_r$ and $s_i=\lambda g_i+\lambda(g_r-g_i)=\lambda g_r$. So
  $s=\lambda g_r\mathbf 1$ and $\langle s,p-p^*\rangle=0$, hence $\Phi_L(p)\le\Phi_L(p^*)$. ∎
- *Limits.* $A_i=L+O(1)$ gives $\delta_i=O(1/L)$ and $\lambda=1-O(1/L)$. Also
  $\delta_iL=\lambda(g_r-g_i)-\delta_i\ln\frac{1-p_i^*}{p_i^*}\to g_r-g_i$ stays bounded.

**Lemma B.** Let $\Phi$ be concave on $\Delta_d$ with a supergradient $s$ at $p^*\in\Delta_d$, and let
$c=\min_is_i$. Then

$\Phi(p)\le\Phi(p^*)+\langle s-c\mathbf 1,p-p^*\rangle=\Phi(p^*)+\sum_i(s_i-c)p_i-\sum_i(s_i-c)p^*_i\le\Phi(p^*)+\max_i(s_i-c)$,

using $s_i-c\ge0$ and $\sum p_i=1$. ∎

This is HLL's "By concavity, $\Phi(p)\le\Phi(p^*)+\varepsilon_\nabla$". It is valid because $f_\tau$ and
$\varphi_i$ are differentiable at $p^*$: all channel entries are positive, so $T^\top p^*>0$.
Hence $\nabla\Phi(p^*)$ is a supergradient.

### 3. The receiver-revealed mixture (Claim 3)

**Channel.** Input $\tilde x=(x,k)\in\mathcal X\times[N]$. Each use draws a selector
$Q\in\{0\}\cup I$, independently of everything before, with $P(Q=0)=\lambda$ and $P(Q=i)=\delta_i$.
- If $Q=0$: $\tilde Y=(0,Y)$ and $\tilde Z=(0,Z)$, with $(Y,Z)\sim T(\cdot|x)$.
- If $Q=i$: $\tilde Y=\tilde Z=(i,G_i(x,k))$, where $G_i=k$ if $x=i$, else the erasure symbol $e_i$.

**Identity (10).** Fix any finite $W,U,V$ and any $P_{WUV\tilde X}$. Then $Q$ is independent of
$(W,U,V,\tilde X)$, and given $Q=q$ the output is produced by component $q$ from $\tilde X$. Since
$Q$ is a coordinate of $\tilde Y$:
- $I(W;\tilde Y)=I(W;Q)+I(W;Y_Q|Q)=\lambda I(W;Y)+\sum_i\delta_iI(W;G_i)$;
- $I(U;\tilde Y|W)=I(U;Q|W)+I(U;Y_Q|Q,W)=\lambda I(U;Y|W)+\sum_i\delta_iI(U;G_i|W)$, because $Q\perp(U,W)$;
- likewise for $\tilde Z$ and for $I(V;\tilde Z|W)$;
- $I(U;V|W)$ involves no output, and $\lambda+\sum\delta_i=1$.

The shaping terms $c:=\sum_i\delta_iI(W;G_i)$ are the same for both receivers, so
$\min\{\lambda a+c,\lambda b+c\}=\lambda\min\{a,b\}+c$. Collecting terms gives (10):
$M_{\tilde T}(P)=\lambda M_T(P_{WUVX})+\sum_i\delta_iM_{G_i}(P)$, and the same holds with $L_t$
for every $t$ (no $\min$ is involved there).

Here $M_T(P_{WUVX})$ is the base-channel functional of the $(W,U,V,X)$-marginal; $K$ is
ignored, and $(W,U,V,K)\to X\to(Y,Z)$ holds trivially. No determinism of $X$ is used, so
Proposition 3's hypothesis is superfluous (slip (b)).

**(11).** For a common deterministic output $G=g(\tilde X)$, use the identity
$I(U;G|W)+I(V;G|W)-I(U;V|W)=I(U,V;G|W)-I(U;V|W,G)$. It follows from
$I(V;G|W,U)-I(V;G|W)=I(U;V|W,G)-I(U;V|W)$. This gives

$M_G(P)=I(W,U,V;G)-I(U;V|W,G)\le H(G)$.

**(9).** $E_i=\mathbf 1\{X=i\}$ is a function of $G_i$. So
$H(G_i)=H(G_i,E_i)=h_2(p_i)+p_iH(K|X=i)\le h_2(p_i)+p_i\ln N$.

**(12).** By (10), (11), (9), $\lambda\ge0$, $M_T(P_{WUVX})\le M_T(p)\le f(p)$ and $\delta_i\ge0$:

$M_{\tilde T}(P)\le\lambda f(p)+\sum_i\delta_i[h_2(p_i)+p_iL]=\Phi_L(p)$.

Taking the supremum over $P$ gives $M_{\tilde T}\le\sup_{p\in\Delta}\Phi_L(p)$. ∎

Each identity and inequality of this section was also tested on 200 random small instances
(Verification).

### 4. Constraint removal (Claim 4)

**Theorem 4 (HLL).** Let $T$ be a finite DMBC and $f$ a finite concave majorant of $M_T(\cdot)$.
Suppose $P^*=P^*_{WUVX_1X_2}$, a law for $T^{\otimes2}$, has $\frac12(q^*_{X_1}+q^*_{X_2})=p^*$ and
$M^{(2)}_*:=M_{T^{\otimes2}}(P^*)>2f(p^*)$. Then some finite $T'$ has $M_{T'^{\otimes2}}>2M_{T'}$.

*Proof.*

*(0) Support.* $|\mathrm{supp}\,p^*|\ge2$. Otherwise $X_1,X_2$ are a.s. constant, so every
mutual information with an output vanishes and $M_*^{(2)}=-I(U;V|W)\le0\le M_T(p^*)\le f(p^*)$.
(Here $M_T(p^*)\ge0$, taking $W,U,V$ constant.) This contradicts the hypothesis.

*(0') Restriction.* Restrict the input alphabet to $S=\mathrm{supp}\,p^*$. This is again a finite
DMBC. Its $M(\cdot)$ is the restriction of $M_T(\cdot)$ to the face $\Delta(S)$, so $f|_{\Delta(S)}$
is a finite concave majorant. $p^*\in\mathrm{ri}\,\Delta(S)$. Since $q^*_{X_\ell}\le2p^*$, $P^*$ uses only
inputs in $S$ and stays feasible with the same value. Henceforth $\mathcal X=S$.

*(1) One-letter side.* Take $g$, $r$, $\lambda=\lambda_L$, $\delta_i=\delta_{i,L}$ from Theorem 2, and build $\tilde T_L$
with $I=\mathcal X\setminus\{r\}$ and $N$ labels, $L=\ln N$. By §3 and Theorem 2,
$M_{\tilde T_L}\le\Phi_L(p^*)=\lambda f(p^*)+\sum_i\delta_i[h_2(p^*_i)+p^*_iL]$, which is (50).

*(2) Two-letter law.* Draw $K_1,K_2$ i.i.d. uniform on $[N]$, independent of
$(W,U,V,X_1,X_2)$. Put $\tilde W=(W,K_1,K_2)$ and $\tilde X_\ell=(X_\ell,K_\ell)$, and keep $U,V$. This
is a feasible law for $\tilde T_L^{\otimes2}$ with finite alphabets. The two selectors
$Q_1,Q_2$ are i.i.d., independent of $(\tilde W,U,V,\tilde X_1,\tilde X_2)$, and revealed to both receivers.
As in §3, every output term is the $\pi_{q_1}\pi_{q_2}$-average over selector pairs
$\mathbf q=(q_1,q_2)$ of the corresponding term for the deterministic pair of components.
Also $I(U;V|\tilde W)=I(U;V|W)=:C$, because $(K_1,K_2)\perp(W,U,V)$. Hence, for each $t\in[0,1]$,

$L_t(\tilde P)=\sum_{\mathbf q}\pi_{\mathbf q}\,\big[(1-t)I(\tilde W;Y^{\mathbf q})+tI(\tilde W;Z^{\mathbf q})+I(U;Y^{\mathbf q}|\tilde W)+I(V;Z^{\mathbf q}|\tilde W)\big]-C$.

We bound the bracket case by case.
- *$\mathbf q=(0,0)$, probability $\lambda^2$.* The outputs are $T^{\otimes2}$ outputs of $(X_1,X_2)$. Because
  $(K_1,K_2)$ is independent of $(W,U,V,Y^2,Z^2)$, $I(\tilde W;Y^2)=I(W;Y^2)$ and
  $I(U;Y^2|\tilde W)=I(U;Y^2|W)$, and likewise for $Z$. So the bracket equals
  $L_t^{T^{\otimes2}}(P^*)+C$.
- *$\mathbf q=(i,0)$.* Drop the nonnegative conditional terms and $I(\tilde W;Y_2|G_i(\tilde X_1))\ge0$. Then
  the bracket is at least $I(\tilde W;G_i(\tilde X_1))\ge I(K_1;G_i(\tilde X_1))$. Given $K_1$, $G_i$ and
  $E_i=\mathbf 1\{X_1=i\}$ determine each other, and $E_i\perp K_1$. So
  $I(K_1;G_i)=H(G_i)-H(E_i)=q^*_{X_1}(i)L$, by (9) with $H(K_1|X_1=i)=L$. The case $(0,j)$ is symmetric.
- *$\mathbf q=(i,j)$, both shaping.* The bracket is at least $I(K_1,K_2;G_i(\tilde X_1),G_j(\tilde X_2))$.
  Given $(K_1,K_2)$, the pair of $G$'s and the pair $(E_i(X_1),E_j(X_2))$ determine each other, and
  $(E,E)\perp(K_1,K_2)$, so $H(G,G|K_1,K_2)=H(E,E)$. Also
  $H(G,G)=H(E,E)+H(G,G|E,E)=H(E,E)+q^*_{X_1}(i)L+q^*_{X_2}(j)L$, since given the $E$'s the
  $G$'s reveal exactly the independent uniform labels of the active coordinates. Hence the
  bracket is $\ge q^*_{X_1}(i)L+q^*_{X_2}(j)L$. This holds for $X_1,X_2$ arbitrarily correlated,
  and also for $i=j$.

Summing, coordinate 1 earns $q^*_{X_1}(i)L$ on all pairs with $q_1=i$, of total probability $\delta_i$,
and likewise for coordinate 2. So

$L_t(\tilde P)\ge\lambda^2\big(L_t^{T^{\otimes2}}(P^*)+C\big)+L\sum_i\delta_i(q^*_{X_1}(i)+q^*_{X_2}(i))-C=\lambda^2L_t^{T^{\otimes2}}(P^*)+2L\sum_i\delta_ip^*_i-(1-\lambda^2)C$.

This is (51). Take $\min_t$; only the first term depends on $t$, and $\lambda^2\ge0$. So
$M_{\tilde T_L^{\otimes2}}\ge M_{\tilde T_L^{\otimes2}}(\tilde P)\ge\lambda^2M_*^{(2)}+2L\sum\delta_ip^*_i-(1-\lambda^2)C$, which is (52).

*(3) Comparison.* Subtracting $2\times$(50), the $L$-terms cancel *exactly*:

$M_{\tilde T_L^{\otimes2}}-2M_{\tilde T_L}\ge\lambda^2M_*^{(2)}-2\lambda f(p^*)-2\sum_i\delta_ih_2(p^*_i)-(1-\lambda^2)C$.

As $L\to\infty$, $\lambda\to1$ and $\delta_i\to0$, while $C\le\ln\min(|\mathcal U|,|\mathcal V|)$ is fixed. So the right
side tends to $M_*^{(2)}-2f(p^*)>0$. Fix such a finite $N$ and set $T'=\tilde T_L$. ∎

*"With $W$" through the lifting.* The lower bound uses the common auxiliary essentially, since
the labels live in $\tilde W$. The upper bound (12) allows any $W$. So the theorem is about the
Marton functional *with* $W$, on both sides. The region without $W$ is a subset, so strict
inclusion for it follows a fortiori.

*Lemma 6 (concavity of $M_T(\cdot)$).* Mix two laws with an independent $Q\sim\mathrm{Bern}(\theta)$ and
take $W'=(Q,W_Q)$. Then
- $I(W';Y)=I(Q;Y)+I(W_Q;Y|Q)\ge\theta I(W_0;Y)+\bar\theta I(W_1;Y)$, and likewise for $Z$;
- the three conditional terms average exactly, because conditioning on $W'$ includes $Q$;
- $\min$ is superadditive over convex combinations.

Taking near-optimal laws gives concavity. ∎ It is only needed for the "in particular" clause.

### 5. The explicit instance (Claim 5–6): what is certified, and why it is the right inequality

**Channel.** $\tilde T$ is the mixture of §3 with base $T$ (HLL (14)–(15)), $I=\{0,1\}$, $r=2$, weights
(32) and $N=2^{2\cdot10^6}$, i.e. HLL (34)–(35). The weights (32) are *not* exactly the Theorem-2
weights. So the one-letter bound goes through Lemma B instead of Theorem 2:

$M_{\tilde T}\overset{(12)}{\le}\sup_p\Phi(p)\overset{\text{Lemma B}}{\le}\Phi(p^*)+\varepsilon$, where

$\Phi=\lambda f_{\tau}+\delta_0\varphi_0+\delta_1\varphi_1$, $\tau\in\{T_5,T_{12}\}$, and $\varepsilon\ge\mathrm{range}\,\nabla\Phi(p^*)$.

Then $\Phi(p^*)=\lambda f_\tau(p^*)+\sum_j\delta_j[h_2(p_j^*)+p_j^*L]$. HLL's version uses
$f_\tau(p^*)\le$ (25), which holds for $\tau=T_5$.

**Two-letter side.** $M_{\tilde T^{\otimes2}}\ge\lambda^2M_*+2L(\delta_0p_0^*+\delta_1p_1^*)-(1-\lambda^2)C$, by (52)
with $q^*_{X_1}=q^*_{X_2}=p^*$, which is (26) and was checked exactly. Then:
- $M_*\ge\gamma$, HLL's mixture bound, or $M_*\ge$ our exact value;
- $C\le\ln4$, since $|\mathcal U|=|\mathcal V|=4$; we also compute $C$ exactly.

Output of `code/lifting/lifted_instance_arb.py` (320-bit Arb; full log in
`lifted_instance_arb.out`, all 27 checks PASS):

| quantity | HLL | certified here | needed direction |
|---|---|---|---|
| $\lambda+\delta_0+\delta_1$ (32) | $=1$ | $=1$ exactly; all $>0$ | — |
| $p^*$ (16) | — | sums to 1 exactly, full support | $p^*\in\mathrm{ri}\,\Delta$ |
| $L=M\ln2$ (30) | $1386294.36\ldots$ | $[1386294.36111989061883446424292\pm4\times10^{-24}]$ | — |
| $A_0,A_1>0$ | implicit | yes | Thm 2 / $\delta\ge0$ |
| $\nabla UB(p^*)$ | (36) | $(0.07483781700631014724,\ 0.34017590594901844869,\ 0.36555458501504418885)$ | — |
| range$(\nabla UB-b)$ (37) | $<4.692109048907095\times10^{-22}$ | $\le4.692109048907094\times10^{-22}$ | upper ✓ |
| $r=\arg\max\nabla UB$ | $2$ | $\partial_2>\partial_1>\partial_0$ certified | — |
| $\varepsilon=$ range $\nabla\Phi(p^*)$ (39) | $<1.846843880121467\times10^{-17}$ | $\le1.846757655822741\times10^{-17}$ | upper ✓ |
| $f_{T_5}(p^*)$ vs (25) | $\le0.0916508833913554746710$ | $\le0.09165088339135547467100000$ | upper ✓ |
| (40) $M_{\tilde T}$, $U$=(25) or $f_{T_5}$ | $\le0.30084186609915448$ | $\le0.3008418660991544625389$ | upper ✓ |
| (40) with $f_{T_{12}}$ | — | $\le0.3008413661002684696681$ | upper |
| $\gamma$ (46)/(49) | $0.183304594320655224901767\ldots$ | $\ge0.1833045943206552249017673$ | lower ✓ |
| exact $M_{T^{\otimes2}}(P^*)$, $W=(Q,W_c)$ | — | $\ge0.1833045943278075898887$ | lower |
| $I(Q;Y^2)$, $I(Q;Z^2)$ (dropped in (49)) | $\ge0$ | $7.91\times10^{-11}$, $7.15\times10^{-12}$ | — |
| $C=I(U;V\mid W)$ | $\le\ln4$ | $0.0092647350296779100317$ | upper ✓ |
| (42) with $\gamma$, $\ln4$ | $\ge0.60168561432394163$ | $\ge0.6016856143239416436287$ | lower ✓ |
| (43) gap, HLL chain | $>1.8821256327185490\times10^{-6}$ | $\ge1.8821256327185508826\times10^{-6}$ | lower ✓ |
| (43) via $L$-free form (53) | — | same value; the direct and cancelled forms agree to $5\times10^{-96}$ | — |
| (43) with printed $\varepsilon$ (39) | — | $\ge1.8821256327185491581\times10^{-6}$ | lower ✓ |
| gap with $T_{12}$ | — | $\ge2.8821234047042925684\times10^{-6}$ | — |
| gap, exact $M_*$ and $C$, $T_5$ / $T_{12}$ | — | $\ge2.5100987784669641979\times10^{-6}$ / $\ge3.5100965504527058837\times10^{-6}$ | — |

**Theorem-2 weights, for comparison.** From the certified gradient, the ideal Theorem-2 weights
at this $L$ are:
- $\lambda_L=0.99999977198527428838942\underline{51}$, against $\ldots8942$ in (32);
- $\delta_{0,L}=2.0970790337007939079\times10^{-7}$;
- $\delta_{1,L}=1.8306822341531184116\times10^{-8}$.

So (32) are the ideal weights rounded at the $10^{-23}$ grid. That is why the residual $\varepsilon$ is of
order $10^{-17}\approx L\times10^{-23}$.

**Why the inequalities are the right ones.**
- Every quantity entering an *upper* bound on $M_{\tilde T}$ is taken at its upper endpoint:
  $f_\tau(p^*)$, $\varepsilon$, the $h_2$ and label terms.
- Every quantity entering a *lower* bound on $M_{\tilde T^{\otimes2}}$ is taken at its lower
  endpoint: $\gamma$ or $M_*$, the label terms, $-\ln4$ or $-C$.
- The gap is the lower endpoint of the difference ball.
- $\lambda,\delta_j,p^*$ are exact rationals, and $L$ is an Arb ball for $2\cdot10^6\ln2$.

**Two points HLL leave implicit**, both checked:
- the one-letter bound needs $B_T$ to be the *global* bound over all finite $\mathcal U,\mathcal V$;
  that is what independent-cert Claims 1–3 certify;
- Lemma B needs $\nabla\Phi(p^*)$ to be a genuine supergradient on the whole simplex, which
  holds by concavity of $\Phi$.

### 6. Final transfer (Claim 7)

All rates below are in nats; the Lean regions use bits, and multiplying every rate by
$1/\ln2$ changes nothing. Let $\tilde T$ be a finite DMBC, viewed as `BroadcastChannel (Fin kX) (Fin kY₁) (Fin kY₂)`
by enumerating its alphabets, with $M_{\tilde T^{\otimes2}}>2M_{\tilde T}$. Pick a law $P$ for $\tilde T^{\otimes2}$ with
$S:=M_{\tilde T^{\otimes2}}(P)>2M_{\tilde T}$. The explicit $\tilde P$ of §4–5 works, with $S\ge0.6016856\ldots$.

**(a) The rate point.** Put $\rho_1=\min\{I(U,W;Y^2),S\}$ and $\rho_2=S-\rho_1$. Then $\rho_i\ge0$, and
$\rho_2\le I(V,W;Z^2)$ because $S\le I(W;Y^2)+I(U;Y^2|W)+I(V;Z^2|W)\le I(UW;Y^2)+I(VW;Z^2)$.
So $(0,\rho_1,\rho_2)$ satisfies:
- HLL's (1a)–(1d) for $\tilde T^{\otimes2}$;
- the five-inequality form. Its two sum constraints at $R_0=0$ reduce to
  $R_1+R_2\le S$, and the fifth reads $R_1+R_2\le S+\max\{I(W;Y^2),I(W;Z^2)\}$.

**(b) Marton's theorem on the super-channel.** By Marton's coding theorem (Marton 1979;
El Gamal–Kim Thm 8.3, with the common auxiliary), applied to the finite DMBC $\tilde T^{\otimes2}$,
$(\rho_1,\rho_2)$ lies in the closure of the achievable set of $\tilde T^{\otimes2}$. Achievability here is in
the operational sense of `IsBCAchievable`: codes for all large blocklengths $m$ with
$\max(1,\lfloor e^{mR}\rfloor)$ messages and average joint error $\to0$.

**(c) Two operational facts.** These are proved here.
- *(c1) Sub-codes.* From a code with message sets $[M_0]\times[M_1]\times[M_2]$ and average error
  $\bar e$, choose $S_j\subseteq[M_j]$ uniformly at random with $|S_j|=K_j\le M_j$, independently.
  Each message triple lies in $S_0\times S_1\times S_2$ with probability $\prod_jK_j/M_j$, so the
  expected average error over the sub-code is $\bar e$. Hence some product sub-code has
  error $\le\bar e$.
- *(c2) Halving and padding.* Let $(R_1',R_2')$ be achievable for $\tilde T^{\otimes2}$. Let
  $R_j\ge0$ with $2R_j<R_j'$ or $R_j=0$. For $n=2m$ or $2m+1$, take the length-$m$
  $\tilde T^{\otimes2}$ code, read it as a length-$2m$ $\tilde T$ code, and append one fixed input
  symbol, which the decoders ignore. Since $mR_j'\ge(2m+1)R_j$ for large $m$, (c1) cuts the
  message sets down to $\max(1,\lfloor e^{nR_j}\rfloor)$ without increasing the error.
  Memorylessness makes the error of the padded code equal to that of the sub-code. Hence
  $(R_1,R_2)$ is achievable for $\tilde T$, and $(0,R_1,R_2)$ satisfies `IsBCCommonAchievable`
  with $M_0=1$.

**(d) Closure.** Given $\eta>0$, take $(R'_1,R'_2)$ achievable for $\tilde T^{\otimes2}$ within $\eta$ of
$(\rho_1,\rho_2)$, and put $R_j=\max(0,R'_j/2-\eta)$. Then $(R_1,R_2)$ is achievable for $\tilde T$ by (c2),
and it lies within $2\eta$ of $(\rho_1/2,\rho_2/2)$. So
$(0,\rho_1/2,\rho_2/2)\in$ `bcCommonCapacityRegion` $\tilde T$, and $(\rho_1/2,\rho_2/2)\in$ `bcCapacityRegion` $\tilde T$.
Its rate sum is $S/2>M_{\tilde T}$.

**(e) The Marton side.** Every point of the pre-closure set of `martonCommonInnerBound` $\tilde T$, with
auxiliaries $(U_0,U_1,U_2)$, satisfies

$r_0+r_1+r_2\le\min\{I(U_0U_1;Y_1)+I(U_2;Y_2|U_0),\,I(U_1;Y_1|U_0)+I(U_0U_2;Y_2)\}-I(U_1;U_2|U_0)=M_{\tilde T}(P_{U_0U_1U_2X})\le M_{\tilde T}$,

by the chain rule. Likewise $r_1+r_2\le M_{\tilde T}$ on `martonInnerBound`. These are closed
half-spaces, so the bounds survive the closure, and also any convexification, should a
variant of the region include one. Since $S/2>M_{\tilde T}$, the capacity region contains a point
outside Marton's region. Both regions differ, so both Lean `Statement`s
(`∀ … , capacity = Marton`) are false. ∎

The only external input is Marton's achievability theorem, together with the standard
chain rule for the Core `mutualInfo`/`condMutualInfo`, which the 2026-11-26 reviewer checked
against `Core/Entropy.lean`. A formal Lean disproof would need a formalized Marton
achievability theorem, which the repository does not have.

## Verification

**Environment.** Scratch venv with Python 3.14.3 and python-flint 0.9.0 (Arb) for the
certificate; numpy 2.5.5 for the float tests. Run from
`attempts/marton-inner-bound-tightness/code/lifting/`:

```
python -I lifted_instance_arb.py           # Claims 5-6; < 1 s; prints 27 PASS lines, exit 0
python -I test_lifting_identities.py 200   # sanity tests of Claims 3-4 (float64; not proof); ~1 s
```

**The float tests** (`test_lifting_identities.out`, seed 20261127) build $\tilde T$ explicitly, with
tags, erasures and labels, for $N=3$ in the one-letter case and $N=2$ in the two-letter case,
$|\mathcal X|=3$ and $|\mathcal W|=|\mathcal U|=|\mathcal V|=2$, using random channels and laws. All Marton quantities
are computed from the full joint law; nothing uses the identities under test.

| test | result |
|---|---|
| identity (10), for $M$ and $L_t$ | max error $2.1\times10^{-15}$ |
| (9), identity part | max error $6.7\times10^{-16}$ |
| (9), inequality part | $\le-1.4\times10^{-4}$ |
| (11), identity part | max error $1.1\times10^{-15}$ |
| (11), inequality part | $\le-0.27$ |
| (12) chain | $\le-0.022$ |
| (51)/(52), 50 instances × 11 values of $t$ | $\le-0.050$ |
| **negative control**: 1.5× the label credit in (51) | violated, $+0.097$, so the test has power |

**Independent referee pass.** A separate agent read only the paper and refereed the same
steps adversarially; it was not shown this file.

Its verdict is **no logical gap**. Per step:
- **(24):** correct, with the mislabel $\alpha\leftrightarrow1-\alpha$. The referee confirmed
  numerically that the third line of HLL's derivation is off by exactly
  $(1-2\alpha)(I(W;Y)-I(W;Z))$ under (3).
- **Theorem 2, (9), Proposition 3, (12) and Lemma 6:** correct.
- **Theorem 4:** correct. The both-shaping case is missing from the text but true:
  $I(\tilde W;G_i,G_j)=I(W;E)+(q_1(i)+q_2(j))L$.
- **(40)–(42):** correct. "By concavity" is valid via the gradient-range argument.
- **Transfer:** correct.

The referee independently re-checked (10), (51) and the both-shaping identity on random
instances, and recomputed (40) and (42). It also found the extra wording slips listed in
Claim 8(h). It found no issue with this file's argument, which it never saw. Its scratch
scripts are not committed.

**Trust base for the whole HLL chain**, combining this file with the independent certificate:
- AGN 2019 Thm 3 (cited, as in independent-cert Claim 1);
- Marton's coding theorem (cited textbook result);
- Arb/FLINT enclosures and Python big integers;
- our `bnb_rigorous.py` (about 350 lines, adversarially reviewed once) and
  `lifted_instance_arb.py` (about 360 lines, not yet reviewed by a second party).

**Not checked here:**
- HLL Sec. III-A, the Markovity counterexample (20)–(21). It is not used by the
  sub-optimality chain;
- AGN's internal lemmas;
- the existence of maximisers. It is never needed: every step works with suprema;
- a Lean formalization.

**Status: unverified.** A human expert review is wanted before `verified`.

## Dead ends

No approach was abandoned. Two places where we expected trouble and found none:
- *A selector-pair case missing from (51).* HLL's text handles "coordinate $\ell$ selects a
  shaping component" one coordinate at a time. When both coordinates use shaping, the
  outputs $(G_i(\tilde X_1),G_j(\tilde X_2))$ are jointly correlated through $(X_1,X_2)$, so additivity
  of the label credit is not automatic. It holds exactly (Details §4), because the labels are
  independent of the inputs and of each other.
- *The rounded weights (32).* Theorem 2 needs exact weights, and with rounded ones $p^*$ is
  not exactly a maximiser of $\Phi$. Lemma B makes the residual cost exactly
  $\mathrm{range}\,\nabla\Phi(p^*)$, about $1.85\times10^{-17}$, which is negligible.

## References

- M. Huang, Y. Liu, Y. Liu, "Sub-optimality of Marton's inner bound for the two-receiver
  broadcast channel," arXiv:2608.19869v1, 20 Aug 2026. Read in full: Secs. I–IV, App. A–E.
- HLL repository github.com/yanxiaoliu-mike/Suboptimality_Marton, commit `cc33e85`. Only
  `results/unconstrained_lift_mpfr.txt` and `src/cpp/verify_unconstrained_lift.cpp` were read,
  to see what their lift check computes. They use a stored rational one-letter bound and a
  surrogate gradient $b$ with a stored residual spread; we compute both directly instead.
- V. Anantharam, A. Gohari, C. Nair, IEEE TIT 65(3):1361–1371, 2019, Thm 3. Used only through
  the independent certificate.
- K. Marton, IEEE TIT 25(3):306–311, 1979; A. El Gamal and Y.-H. Kim, *Network Information
  Theory*, CUP 2011, Thm 8.3 (private messages) and Thm 8.4 (with a common message).
- R. T. Rockafellar, *Convex Analysis*, Princeton 1970, Thm 23.4: supergradients exist at
  relative-interior points.
- Prior attempts:
  - `2026-11-26-claude-opus-5-5-hll-counterexample-audit.md`. Its Claim 2 is made rigorous here
    as Claim 7, and its Dead end "Thms 2 and 4 read, not checked" is closed by Claims 2–4;
  - `2026-11-27-claude-opus-5-5-independent-certificate.md`. Its Claims 2–4 are the inputs
    $T_5$, $T_{12}$ and $\gamma$ here.
