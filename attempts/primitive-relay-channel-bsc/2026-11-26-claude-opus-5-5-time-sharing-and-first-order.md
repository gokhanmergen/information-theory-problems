---
problem: primitive-relay-channel-bsc
date: 2026-11-26
attempter: claude
model: claude-opus-5-5
type: partial-result
status: unverified
---

## Summary

Two results. **(A)** The question in the problem file before this commit, "does
$C_{\rm BSC}(p_1,p_2,R_0)=\max(R_{\rm PDF},R_{\rm CF})$ for all $p_1,p_2,R_0$?",
has a **negative** answer. $C(R_0)$ is concave in $R_0$ (time-sharing), and at
$(p_1,p_2,R_0)=(0.2,0.1,0.3)$, time-sharing decode-forward with
compress-forward gives $C\ge 0.539568$. A strong data-processing bound gives
$\max(R_{\rm PDF},R_{\rm CF})\le 0.531005$. The frozen Lean statement (symmetric
$p_1=p_2$, compared against *time-shared* CF) avoids this failure, and the problem
file is now synced to it. **(B)** For the symmetric channel I pin down the first-order
picture at $R_0\to0$. The uniform-input CF slope is exactly
$s_\rho=(1-2\rho)^2/(1+(1-2\rho)^2)$, with a three-line power-series proof. The
El Gamal–Gohari–Nair (EGN) Theorem 6 converse has slope **exactly 1** at $R_0=0$,
the same as cutset. A sketch shows the same for the Liu–Özgür bound. So
$s_\rho\le C'(0^+)\le 1$ (at $\rho=0.1$: $[0.3902,1]$), and none of the converses
I examined narrows this first-order gap.

## Approach

Lead 1: test whether the catalog's "max of the two classical schemes" is even
concave in $R_0$, as capacity must be. It is not. Then upper-bound both schemes
sharply enough, just past the DF corner, to separate them from the time-shared
rate. Lead 2: look at the symmetric channel at $R_0\to0$, the regime the published
converses handle least well. There the CF test-channel optimization collapses to a
one-dimensional ratio, and the EGN bound reduces to the question "is the point
$(\rho,h(\rho))$ on the concave envelope of $g_\lambda$?".

Notation: $h$ is binary entropy in bits, $a\star b=a(1-b)+(1-a)b$, $Y$ is the
destination output (BSC$(p_1)$), $Y_r$ is the relay output (BSC$(p_2)$), and $\Delta=h(p_1)-h(p_2)$.

## Claims

1. **[proved]** *(time-sharing.)* In the operational model of the problem file
   (identical to `IsPrimitiveBscAchievable` in the Lean file), suppose $R_a$ is achievable at
   pipe rate $R_{0a}$ and $R_b$ at $R_{0b}$, and let $\lambda\in(0,1)$. Then every
   $R<\lambda R_a+(1-\lambda)R_b$ is achievable at every pipe rate
   $R_0>\lambda R_{0a}+(1-\lambda)R_{0b}$. Hence $C(p_1,p_2,\cdot)$ is concave and
   nondecreasing on $[0,\infty)$.
2. **[proved]** For all $p_1,p_2\in(0,1/2)$ and $R_0\ge0$:
   $R_{\rm CF}(p_1,p_2,R_0)\le 1-h(p_1)+(1-2p_2)R_0$. If moreover $p_2\le p_1$:
   $R_{\rm PDF}(p_1,p_2,R_0)\le\min\{1-h(p_1)+R_0,\,1-h(p_2)\}$. Both right-hand
   sides are concave in $R_0$, so the same bounds hold for the time-shared
   (concavified) versions of each scheme separately.
3. **[proved]** *(negative answer to the former catalog question.)* At
   $(p_1,p_2,R_0)=(0.2,0.1,0.3)$:
   $$C\ \ge\ 0.539568\ >\ 0.531005\ \ge\ \max\{R_{\rm PDF},R_{\rm CF}\},$$
   a certified gap $\ge 0.00856$ bits. More generally, for every $0<p_2<p_1<1/2$
   there is $\varepsilon>0$ such that $C>\max\{R_{\rm PDF},R_{\rm CF}\}$ for all
   $R_0\in(\Delta,\Delta+\varepsilon)$. For $(0.2,0.1)$ the argument covers
   $R_0\in(0.25293,\,0.33487)$. Even the separately concavified schemes fail here:
   one has to time-share *across* schemes.
4. **[heuristic]** For $(p_1,p_2)=(0.2,0.1)$, the numerically optimized CF rate
   (uniform input is optimal on the search grid) shows that $\max(R_{\rm PDF},R_{\rm CF})$
   lies strictly below its upper concave envelope on all of $(0.2529,\approx0.82)$.
   The largest gap is $\approx0.045$ bits, near $R_0=0.5$.
5. **[proved]** *(exact CF slope, symmetric case.)* Let $p_1=p_2=\rho$ and
   $k=1-2\rho$. For uniform $X$ and *every* finite-alphabet $U$ with
   $U-Y_r-(X,Y)$,
   $$I(U;X\mid Y)\ \le\ s_\rho\,I(U;Y_r\mid Y),\qquad s_\rho=\frac{k^2}{1+k^2},$$
   and the constant is sharp. Consequently the uniform-input CF rate, with or
   without time-sharing, is at most $1-h(\rho)+s_\rho R_0$. Its right-derivative at
   $R_0=0$ equals $s_\rho$, so $C'(0^+)\ge s_\rho$. ($s_\rho$ is the squared
   correlation of $X$ and $Y_r$ given $Y$.)
6. **[proved]** *(EGN Theorem 6 is first-order equal to cutset.)* For every
   $\rho\in(0,1/2)$, let
   $B(R_0)=\inf_{\lambda\in[0,1]}\big[1-2h(\rho)+\lambda R_0+\mathfrak C[g_\lambda](\rho)\big]$
   be the EGN Theorem 6 bound. Then $B(0)=1-h(\rho)$, and its right-derivative at
   $0$ is $1$.
7. **[proved]** *(quantitative, $\rho=0.1$; statements about the EGN bound, not
   about capacity.)* $B(0.01)\ge0.540620$ against cutset $0.541004$, and
   $B(0.05)\ge0.574050$ against cutset $0.581004$. More values are in the table
   below. At $R_0=0.01$, EGN Theorem 6 can remove at most $3.9\times10^{-4}$ of a
   cutset-to-CF gap of $\approx6.1\times10^{-3}$ bits.
8. **[sketch]** The Liu–Özgür reverse-hypercontractivity bound for discrete
   symmetric primitive relay channels (their Lemma 8 with their Proposition 1)
   gives $C\le 1-h(\rho)+R_0-c_\alpha^{-1}(R_0)$, with
   $c_\alpha^{-1}(R_0)=O(R_0^2)$. It therefore also has slope 1 at $R_0=0$.
9. **[proved]** *(tensorization.)* If $X^n$ is i.i.d. uniform, then
   $I(U;X^n\mid Y^n)\le s_\rho\,I(U;Y_r^n\mid Y^n)$ for every
   $U-Y_r^n-(X^n,Y^n)$. Multi-letter CF with i.i.d. uniform inputs therefore has
   the same slope $s_\rho$. A scheme with slope $>s_\rho$ needs non-product
   (coded) input structure, and so does any converse that improves on slope 1.
10. **[heuristic]** Numerics for $\rho\in\{0.02,0.05,0.1,0.2,0.3,0.4,0.45\}$ give
    three findings. (i) Uniform input maximizes the CF rate at all 49 grid points
    tested. (ii) BSC test channels generate the uniform-input CF region: the curve
    $\theta\mapsto(b(\theta),a(\theta))$ is concave. (iii) At $\rho=0.1$ the sharp
    slope $s_\pi$ for input bias $\pi$ is maximized at $\pi=1/2$. If these hold,
    then $R_{\rm CF}(\rho,\rho,\cdot)$ is already concave, the concavification in
    the Lean statement is vacuous, and the Lean `Statement` implies
    $C'(0^+)=s_\rho$. Any scheme with slope $>s_\rho$ at $R_0=0$ would then
    disprove it.

## Details

### Claim 1 (time-sharing in the catalog's operational model)

Fix $\delta>0$ with $R+\delta<\lambda R_a+(1-\lambda)R_b$ and
$R_0-\delta>\lambda R_{0a}+(1-\lambda)R_{0b}$. Given $n$, put $n_a=\lfloor\lambda n\rfloor$
and $n_b=n-n_a$. Both tend to $\infty$, so for large $n$ there are codes
$(f_a,\phi_a,g_a)$ of length $n_a$ and $(f_b,\phi_b,g_b)$ of length $n_b$ with
average errors $\le\varepsilon/2$. They have
$M_a=\max(1,\lfloor2^{n_aR_a}\rfloor)$ and $M_b=\max(1,\lfloor2^{n_bR_b}\rfloor)$
messages, and relay index sets of sizes
$M_{0a}=\max(1,\lfloor2^{n_aR_{0a}}\rfloor)$ and $M_{0b}=\max(1,\lfloor2^{n_bR_{0b}}\rfloor)$.
The concatenated code runs code $a$ on the first $n_a$ uses and code $b$ on the rest:
- **Relay index.** The relay sends the pair $(\phi_a(Y_r^{n_a}),\phi_b(Y_{r,n_a+1}^n))$.
  We have $M_{0a}M_{0b}\le 2^{n_aR_{0a}+n_bR_{0b}}\le 2^{n(\lambda R_{0a}+(1-\lambda)R_{0b})+R_{0b}}\le 2^{nR_0}$
  for large $n$. Since $M_{0a}M_{0b}$ is an integer, it is at most
  $\lfloor 2^{nR_0}\rfloor$, so the pair embeds injectively into the allowed index set.
- **Messages.** $M_aM_b\ge 2^{n_aR_a+n_bR_b-2}\ge 2^{nR}\ge\max(1,\lfloor2^{nR}\rfloor)$
  for large $n$, because $n_aR_a+n_bR_b\ge n(\lambda R_a+(1-\lambda)R_b)-R_a$. The
  channel uses of the two sub-blocks are independent (memoryless product channel),
  so by the union bound the error probability of the pair $(m_a,m_b)$ is
  $\le e_a(m_a)+e_b(m_b)$, whose average over all $M_aM_b$ pairs is $\le\varepsilon$.
  Map the $M=\max(1,\lfloor2^{nR}\rfloor)$ messages injectively onto the $M$ pairs
  with the smallest error probabilities. Their average error is at most the overall
  average, hence $\le\varepsilon$.

Monotonicity holds because a code for pipe rate $R_0$ is also a code for any larger
rate. For concavity, the lemma gives
$C(\lambda a+(1-\lambda)b+\eta)\ge\lambda C(a)+(1-\lambda)C(b)$ for every
$\eta>0$. Applying it at $a+\eta',b+\eta'$ shows that the right limit
$D(x)=C(x^+)$ is concave on $[0,\infty)$, hence continuous on $(0,\infty)$. Since
$C$ is nondecreasing, $C(x)\ge D(x-\delta)$ for every $\delta>0$, so
$D(x)\le C(x)\le D(x)$, i.e. $C=D$ on $(0,\infty)$. At $0$, $C(0)\le D(0)$ suffices.
Only the strict form with a margin is used below.

### Claim 2 (upper bounds on the two schemes)

**CF.** Fix any $p(x)$ and test channel $p(u|y_r)$. Put $a=I(U;X|Y)$ and
$b=I(U;Y_r|Y)$. Because $U-Y_r-(X,Y)$, we have $I(U;X|Y,Y_r)=0$. Hence
$I(U;Y_r,X|Y)=b=a+I(U;Y_r|X,Y)$, i.e. $I(U;Y_r|X,Y)=b-a$, and the CF objective is
$$\min\{I(X;Y)+a,\ I(X;Y)+R_0-b+a\}=I(X;Y)+a-\max(0,b-R_0).$$
*SDPI step.* Condition on $Y=y$. Then $U-Y_r-X$, and $X\mid(Y_r,Y=y)$ is a channel
$K_y$ with two input letters $y_r\in\{0,1\}$. Its rows are posteriors with
log-odds $\ell_y\pm\log\frac{1-p_2}{p_2}$, where $\ell_y$ is the log-odds of $X$
given $Y=y$ alone. The total-variation distance between the rows is
$\sigma(\ell_y+c)-\sigma(\ell_y-c)$, with $\sigma$ the logistic function and
$c=\ln\frac{1-p_2}{p_2}$. Because $\sigma'$ is even and decreasing in $|t|$, this is
maximal at $\ell_y=0$, where it equals $2\sigma(c)-1=1-2p_2$. So the Dobrushin
coefficient satisfies $\tau_y\le1-2p_2$ for every input distribution and every $y$.
For a binary-input channel this gives the SDPI with a one-line proof. Write
$K_y(\cdot|y_r)=(1-\tau_y)Q(\cdot)+\tau_yK'(\cdot|y_r)$, where $Q$ is the
normalized common part of the two rows. This realizes $X$ as follows: draw
$E\sim{\rm Bern}(\tau_y)$ independent of $(U,Y_r)$; if $E=0$, draw $X\sim Q$; if
$E=1$, draw $X\sim K'(\cdot|Y_r)$. Then
$$I(U;X|Y=y)\le I(U;X,E|Y=y)=\tau_y I(U;X|E=1,Y=y)\le\tau_y I(U;Y_r|Y=y).$$
Averaging over $y$ gives $a\le\eta b$ with $\eta=1-2p_2$. If $b\le R_0$, the
objective is at most $I(X;Y)+\eta b\le I(X;Y)+\eta R_0$. If $b>R_0$, it is at most
$I(X;Y)+R_0-(1-\eta)b<I(X;Y)+\eta R_0$. Finally $I(X;Y)\le1-h(p_1)$.

**PDF.** $b_1=I(X;Y)+R_0\le1-h(p_1)+R_0$. For $b_2$, BSC$(p_1)$ equals BSC$(p_2)$
followed by BSC$(q)$, with $q=(p_1-p_2)/(1-2p_2)\in[0,1/2)$. Because $U-X-(Y,Y_r)$
holds in the PDF formula, data processing given $U=u$ gives
$I(X;Y|U=u)\le I(X;Y_r|U=u)$. Hence
$b_2\le I(U;Y_r)+I(X;Y_r|U)=I(U,X;Y_r)=I(X;Y_r)\le1-h(p_2)$.

### Claim 3 (the counterexample)

*Lower bound.* (i) Decode-forward at pipe rate $0.2530>\Delta=0.252932501\ldots$
achieves every $R<1-h(0.1)=0.531004406\ldots$. The relay decodes, which needs
$R<I(X;Y_r)$. It forwards a random bin index of the message, and the destination
decodes within the bin, which needs $R-0.2530<I(X;Y)=1-h(0.2)$ (Cover–El Gamal
1979; El Gamal–Kim 2011, Ch. 16). (ii) Compress-forward with $U=Y_r$ (Slepian–Wolf
binning of $Y_r^n$ against side information $Y^n$) at pipe rate
$0.8270>h(0.2\star0.1)=h(0.26)=0.826746\ldots$ achieves every
$R<I(X;Y,Y_r)=1+h(0.26)-h(0.2)-h(0.1)=0.635822684\ldots$. (iii) Apply Claim 1 with
$\lambda=(0.8270-0.2999)/(0.8270-0.2530)=0.9182926\ldots$. The pipe rate used is
$0.2999<0.3$, and every rate below
$\lambda\cdot0.5310044+(1-\lambda)\cdot0.6358227=0.5395688\ldots$ is achievable. So
$C(0.2,0.1,0.3)\ge0.539568$.

*Upper bound.* By Claim 2, $R_{\rm PDF}\le1-h(0.1)=0.5310044\ldots$ and
$R_{\rm CF}\le1-h(0.2)+0.8\cdot0.3=0.5180719\ldots$.

*General statement.* At $R_0=\Delta$ we have
$1-h(p_1)+(1-2p_2)\Delta<1-h(p_1)+\Delta=1-h(p_2)$. By continuity, the CF bound
stays below $1-h(p_2)$ for $R_0\in(\Delta,\Delta+\varepsilon)$, while the
time-shared rate exceeds $1-h(p_2)$ for every $R_0>\Delta$. That rate is the line
from $(\Delta,1-h(p_2))$ to $(h(p_1\star p_2),I(X;Y,Y_r))$, and
$I(X;Y,Y_r)-(1-h(p_2))=h(p_1\star p_2)-h(p_1)>0$. The right endpoint $0.33487$ for
$(0.2,0.1)$ is where the CF bound meets that line. Since the bounds in Claim 2 are
concave, they also hold for each scheme's own concave envelope.

### Claim 4 (heuristic picture for (0.2, 0.1))

`code/lead1_time_sharing_counterexample.py` Part C, using `code/cf_dual.py`
(Lagrange dual over the posterior $\theta=P(Y_r=1|U)$, floating point):

| $R_0$ | DF | CF (opt. $\pi$) | envelope | gap |
|---|---|---|---|---|
| 0.3 | 0.531004 | 0.431412 | 0.539616 | 0.0086 |
| 0.4 | 0.531004 | 0.478817 | 0.557912 | 0.0269 |
| 0.5 | 0.531004 | 0.523558 | 0.576209 | 0.0452 |
| 0.6 | 0.531004 | 0.564838 | 0.594505 | 0.0297 |
| 0.7 | 0.531004 | 0.601394 | 0.612801 | 0.0114 |
| 0.8 | 0.531004 | 0.630554 | 0.631098 | 0.0005 |

The tangent from the DF corner touches the CF curve near $R_0\approx0.8195$ (slope
0.182964). These time-shared rates are also the best known achievable rates for
this pair. The earlier `relay-channel/2026-07-18-claude-fable-5-bsc-baseline.md`
measured its gap against $\max(\mathrm{DF},\mathrm{CF})$, so its reported 0.1048-bit
gap at $R_0=0.4$ shrinks to $0.6358-0.5579\approx0.078$ bits once time-sharing is
counted.

### Claim 5 (exact CF slope at uniform input)

With uniform $X$ the reverse channel $Y_r\to X$ is again BSC$(\rho)$. So given
$U=u$ with $\theta_u=P(Y_r=1|U=u)$, the triple $(Y_r,X,Y)$ is a Markov chain with
$Y_r\sim{\rm Bern}(\theta_u)$ and BSC$(\rho)$ links. Hence
$H(X|Y,U=u)=h(\theta_u\star\rho)+h(\rho)-h(\theta_u\star\rho\star\rho)$ and
$H(Y_r|Y,U=u)=h(\theta_u)+h(\rho\star\rho)-h(\theta_u\star\rho\star\rho)$. Subtracting
these from their values at $\theta=1/2$ gives
$$I(U;X|Y)=\textstyle\sum_uP(u)\,a(\theta_u),\quad I(U;Y_r|Y)=\sum_uP(u)\,b(\theta_u),$$
$$a(\theta)=h(\theta\star\rho\star\rho)-h(\theta\star\rho),\qquad b(\theta)=h(\theta\star\rho\star\rho)-h(\theta).$$
So it suffices to show $(1+k^2)a(\theta)\le k^2b(\theta)$ pointwise. Put
$\theta=\tfrac12+x$; then $\theta\star\rho=\tfrac12+kx$ and $\theta\star\rho\star\rho=\tfrac12+k^2x$.
With $\psi(t)=1-h(\tfrac12+t)=\frac1{\ln2}\sum_{m\ge1}\frac{(2t)^{2m}}{2m(2m-1)}$,
the inequality becomes
$$\psi(k^2x)+k^2\psi(x)\ \ge\ (1+k^2)\psi(kx).$$
The coefficient of $(2x)^{2m}$ on the left minus the right is proportional to
$k^{4m}+k^2-(1+k^2)k^{2m}=(k^{2m}-k^2)(k^{2m}-1)\ge0$. It is zero for $m=1$ and
strictly positive for $m\ge2$, so the inequality is strict for $\theta\ne1/2$, with
ratio $a/b\to k^2/(1+k^2)$ as $\theta\to1/2$. The bound
$a\le s_\rho b$ turns the CF objective into $\le1-h(\rho)+s_\rho R_0$, by the same
case split as in Claim 2. Write $g(R)=\sup\{a:b\le R\}$. It is concave, because $U$
can absorb a time-sharing flag. A binary symmetric $U$ with
$\theta\to1/2$ gives $g(b(\theta))\ge a(\theta)$ with ratio $\to s_\rho$, so
$g'(0^+)=s_\rho$. Then $C'(0^+)$ exists (Claim 1), is $\le1$ (cutset), and is
$\ge s_\rho$. Finally, $s_\rho=\mathrm{corr}^2(X,Y_r\mid Y=y)$, since
$\mathrm{Cov}=\rho(1-\rho)k$, $\mathrm{Var}(X|Y)=\rho(1-\rho)$, and
$\mathrm{Var}(Y_r|Y)=2\rho(1-\rho)(1-2\rho(1-\rho))$.

Numbers: $s_{0.1}=0.390244$, $s_{0.2}=0.264706$, $s_{0.3}=0.137931$. For comparison,
the ratio for $U=Y_r$ is $(h(\rho\star\rho)-h(\rho))/h(\rho\star\rho)$, which is
$0.310379$ at $\rho=0.1$.

### Claim 6 (EGN Theorem 6 has slope 1 at $R_0=0$)

EGN Theorem 6 (arXiv:2101.11139v3) defines $g_\lambda(c)$ as the maximum of
$(1-\lambda)(H(Y_1)-H(Y_r))+H(Y_r|X)$ over all $p(x,y_r)$ with $P(X\ne Y_r)=c$, and
proves $C\le1-2h(\rho)+\lambda R_0+\mathfrak C[g_\lambda](\rho)$ for every
$\lambda\in[0,1]$. In the parameterization of
`relay-channel/2026-07-18-gpt-5-codex-symmetric-egn-certificate.md`, with
$a=P(X=1)$, $u=P(Y_r=1|X=0)$, $v=P(Y_r=0|X=1)$, $y=a\star\rho$,
$z=(1-a)u+a(1-v)$, $c=(1-a)u+av$:
$f_\lambda=(1-\lambda)(h(y)-h(z))+(1-a)h(u)+ah(v)$.

- The point $(a,u,v)=(\tfrac12,t,t)$ gives $f_\lambda=h(t)$ at $c=t$, so
  $g_\lambda\ge h$ and $\mathfrak C[g_\lambda](\rho)\ge h(\rho)$. Hence $B\ge1-h(\rho)$.
  At $\lambda=1$, concavity of $h$ gives $g_1=h$, so the bound equals
  $1-h(\rho)+R_0$, which is cutset. Thus $B(0)=1-h(\rho)$.
- Fix $\lambda<1$ and suppose $\mathfrak C[g_\lambda](\rho)=h(\rho)$. A supporting
  line $\ell$ at the interior point $\rho$ would satisfy $\ell\ge g_\lambda\ge h$ and
  $\ell(\rho)=h(\rho)$, so $\ell$ is the tangent of slope $h'(\rho)$. Subtracting this
  line from $f_\lambda$ gives exactly
  $$\Phi_\lambda=(1-\lambda)\big(h(y)-h(z)\big)-(1-a)\,d(u\|\rho)-a\,d(v\|\rho),$$
  where $d$ is binary KL divergence. Take $a\in(0,\tfrac12)$, $u=\rho-t$, $v=\rho+t$.
  Then $z=y-t$ with $y<\tfrac12$, so $h(y)-h(z)=h'(y)t+O(t^2)$ with $h'(y)>0$, while
  the divergence terms are $O(t^2)$. Hence $\Phi_\lambda>0$ for small $t>0$, a
  contradiction. So $e(\lambda):=\mathfrak C[g_\lambda](\rho)-h(\rho)>0$ for every
  $\lambda<1$.
- $\mathfrak C[g](\rho)=\sup\{\sum_iw_ig(c_i):\sum w_ic_i=\rho\}$ is convex in $g$,
  and $g_\lambda(c)$ is a pointwise maximum of affine functions of $\lambda$. So $e$
  is convex on $[0,1]$ with $e(1)=0\le e$, hence nonincreasing. For any
  $\lambda'<1$ let $m=e(\lambda')>0$. Then
  $B(R_0)-(1-h(\rho))\ge\min\{m,\lambda'R_0\}=\lambda'R_0$ for $R_0\le m$. So
  $B'(0^+)\ge\lambda'$ for every $\lambda'<1$, and $B'(0^+)\le1$ by cutset.

`code/symmetric_first_order.py egn-pos` exhibits explicit witnesses in 50-digit
arithmetic. For instance at $\lambda=0.99$, the point $a=0.25$, $t=0.000775$ gives
$\Phi=4.67\times10^{-6}>0$. These witnesses indicate $e(\lambda)\approx\kappa(1-\lambda)^2$,
so $B(R_0)=1-h(\rho)+R_0-\Theta(R_0^2)$.

### Claim 7 (how close EGN is to cutset at small $R_0$, $\rho=0.1$)

For any $P=(a,u,v)$, $t$, and $w\in[0,1]$ with $wc(P)+(1-w)t=\rho$, we have
$\mathfrak C[g_\lambda](\rho)\ge w f_\lambda(P)+(1-w)h(t)$. This is affine in
$\lambda$. `egn-low` collects 28 such configurations, found by a float search and
evaluated in 50-digit `mpmath`. It then computes exactly the minimum over
$\lambda\in[0,1]$ of the maximum of these affine functions, by checking all
breakpoints. Each resulting number is a valid lower bound on $B(R_0)$; the margins
are many orders above rounding.

| $R_0$ | EGN Thm 6 bound $B(R_0)\ge$ | cutset | cutset $-$ lower | uniform CF (numerical) |
|---|---|---|---|---|
| 0.005 | 0.5359129 | 0.5360044 | $9.2\times10^{-5}$ | 0.5329542 |
| 0.01 | 0.5406201 | 0.5410044 | $3.8\times10^{-4}$ | 0.5349013 |
| 0.02 | 0.5497515 | 0.5510044 | $1.25\times10^{-3}$ | 0.5387869 |
| 0.05 | 0.5740505 | 0.5810044 | $6.95\times10^{-3}$ | 0.5503733 |
| 0.1 | 0.6063741 | 0.6310044 | 0.0246 | 0.5694304 |
| 0.2 | 0.6489250 | 0.7310044 | 0.0821 | 0.6064328 |

Consistency check: at $R_0=0.2$ this lower estimate, 0.648925, sits just below the
certified EGN value $<0.649557$ from `relay-channel/2026-07-18-gpt-5-codex-fixed-bias-concavity.md`.

### Claim 8 (Liu–Özgür, sketch)

Liu–Özgür (arXiv:1811.11303, nats) prove
$R\le I(X_Q;Y_Q)+\frac1nH(I|Y^n)-\frac1nH(I|X^n)+\mu(\epsilon)$ (their Proposition 1),
and, for discrete channels, $\frac1nH(I|Y^n)\le c_\alpha(\frac1nH(I|X^n))$ with
$c_\alpha(h)=\min_{t>0}[(\alpha-1)t+h/(1-e^{-t})]$ (their Lemma 8;
$\alpha=2(1-\rho)$ for the BSC). Arguing exactly as in the proof of their
Gaussian Corollary 5, this gives $C\le1-h(\rho)+R_0-c_\alpha^{-1}(R_0)$. As
$h\to0$, $c_\alpha(h)=2\sqrt{(\alpha-1)h}\,(1+o(1))$, so
$c_\alpha^{-1}(R_0)=\Theta(R_0^2)$ and the slope at 0 is 1. I did not find a written
statement of this discrete corollary in the text I read, hence the label. EGN state
that their bound improves the binary-symmetric bounds of Wu–Özgür–Xie and
Barnes–Wu–Özgür. If that improvement is pointwise in $R_0$, those bounds also have
slope 1 by Claim 6. I could not access either paper's full text to check directly.

### Claim 9 (tensorization)

Write $O_i=(X^{i-1},Y^{i-1},Y_{i+1}^n)$ and $U_i=(U,O_i)$. Index $i$ is independent
of all other indices and $U$ is a randomized function of $Y_r^n$, so
$U_i-Y_{r,i}-(X_i,Y_i)$ and $O_i\perp(X_i,Y_i,Y_{r,i})$. By the chain rule and
Claim 5 applied to $U_i$:
$$I(U;X^n|Y^n)=\sum_iI(U_i;X_i|Y_i)\le s_\rho\sum_iI(U;Y_{r,i}|Y^n,X^{i-1}).$$
Next, $I(U;Y_{r,i}|Y^n,X^{i-1})\le I(U;Y_{r,i}|Y^n,X^{i-1},Y_r^{i-1})$, because
$I(Y_r^{i-1};Y_{r,i}|Y^n,X^{i-1})=0$. This equals $I(U;Y_{r,i}|Y^n,Y_r^{i-1})$, because
$X^{i-1}\perp(U,Y_{r,i}^n)$ given $(Y^n,Y_r^{i-1})$ (the joint law factorizes). Summing
gives $s_\rho I(U;Y_r^n|Y^n)$.

### Claim 10 (numerics)

- `symmetric_first_order.py unif` compares CF at $\pi=1/2$ against a grid of
  $\pi\in\{0.02,\dots,0.48\}$ and a bounded local optimizer, at 7 values of $R_0$ for
  each of 7 values of $\rho$. All 49 local optima are at $\pi^*=0.5000$. The largest
  value of $\mathrm{CF}(\pi)-\mathrm{CF}(1/2)$ is $9.5\times10^{-10}$ (optimizer
  noise).
- `bsc-curve`: chord slopes $da/db$ along $\theta\in(0,\tfrac12)$ increase
  monotonically from about 0.13 to $s_\rho$ (at $\rho=0.1$), so the curve is concave.
  Uniform-input CF is therefore achieved by a BSC test channel without time-sharing.
  The dual computation agrees: at $(0.1,0.2)$ it returns 0.6064328, versus 0.6064325
  for the BSC point in the existing certificate.
- The sharp slope $s_\pi$ at $\rho=0.1$, from the envelope computation, takes the
  values $0.39024$ (π=0.5), $0.39007$ (0.45), $0.38929$ (0.4), $0.38287$ (0.3),
  $0.36037$ (0.2), and $0.29177$ (0.1).
  If $s_\pi\le s_{1/2}$ holds for all $\pi$, then $R_{\rm CF}\le1-h(\rho)+s_\rho R_0$
  for all inputs. Hence the concavified CF of the Lean statement has
  right-derivative $s_\rho$ at 0.

## Verification

- `python3 code/lead1_time_sharing_counterexample.py` (about 20 s) reproduces
  every number in Claim 3 in 50-digit arithmetic. It also checks two things
  numerically: the Dobrushin coefficient is $\le0.8$ over a 20,001-point grid of
  input biases, with a maximum of $0.799999999999$; and 20,000 random test channels
  ($|U|\le4$, random $\pi$) satisfy $I(U;X|Y)/I(U;Y_r|Y)\le0.5322<0.8$.
- `python3 code/symmetric_first_order.py slope` evaluates $r(\theta)$ on a 2000-point
  grid in 50-digit arithmetic for seven values of $\rho$. The maximum is always just
  below $s_\rho$, at $\theta=0.49975$. In float, cancellation near $\theta=1/2$
  produced spurious $10^{-5}$ excursions, which is why the check uses `mpmath`.
- `egn-pos` and `egn-low` reproduce Claims 6 and 7 (about 2.5 min). `bsc-curve`,
  `unif` and `spi` reproduce Claim 10 (about 5 min with `nice`).
  `code/egn_prop1_perturbation.py` reproduces the Proposition 1 ratios quoted in
  Dead ends.
- The EGN Theorem 6 statement was read from the arXiv HTML (v3). Liu–Özgür's
  Proposition 1, Lemma 8, Corollaries 5 and 7, and Section VI were read from the arXiv
  PDF (v1).
- Python environment: numpy, scipy, mpmath from the repository `.venv`.

## Novelty check

Where I looked: the full text of Mondelli–Hassani–Urbanke, arXiv:1801.03153
(primitive relay with BEC components; they note that "the CF bound is in general not
convex" and can be improved by time-sharing, and their chaining scheme beats both DF
and CF); EGN arXiv:2101.11139 (Theorem 6, Remarks 6 and 14, Section 3.9, where CF
*with time-sharing* is optimal for a deterministic class, citing Kim 2007, Prop. 3);
Liu–Özgür arXiv:1811.11303 in full; and searches on "time-sharing decode-forward
compress-forward primitive relay concave", "slope at zero relay rate", and "tangent
to cutset". The El Gamal–Kim remark that CF can be improved by coded time-sharing
(Remark 16.4) was seen only through citing papers.

- **Claims 1–3.** Concavity of capacity in the link rate, and the fact that
  time-sharing can improve CF, are folklore. I found no source that states
  $C>\max(R_{\rm PDF},R_{\rm CF})$ for the BSC primitive relay, or that shows each
  scheme's own concavification is insufficient. No priority is claimed for the
  idea; the contribution is the explicit, certified instance and the uniform SDPI
  bound that makes it rigorous.
- **A September 2026 preprint**, Ponniah, arXiv:2609.15709v2, claims that the
  capacity of the *general* relay channel is $\max\{R_{\rm DF},R_{\rm U\text{-}CF},R_{\rm C\text{-}CF}\}$,
  with no time-sharing variable. I did not check whether its expressions specialize
  to $R_{\rm PDF}$ and $R_{\rm CF}$ when the orthogonal relay link is embedded as a
  relay input. If they do, Claim 3 would contradict that claim. This is flagged for
  a referee, not asserted.
- **Claims 5 and 9.** $s_\rho$ is a conditional maximal-correlation (χ²) constant.
  SDPI tensorization is classical (Ahlswede–Gács; Anantharam–Gohari–Kamath–Nair
  2013). I did not find the statement "CF slope at zero equals
  $(1-2\rho)^2/(1+(1-2\rho)^2)$, with the termwise power-series proof"; it may be
  implicit somewhere.
- **Claims 6–8.** I did not find any statement that the EGN or Liu–Özgür bounds are
  tangent to cutset at $R_0=0$. Liu–Özgür discuss the opposite, high-rate regime
  (their Section VI).

## Open question sharpened by this attempt

For $p_1=p_2=\rho$, the right-derivative $C'(0^+)$ exists and lies in
$[s_\rho,1]$, with $s_\rho=(1-2\rho)^2/(1+(1-2\rho)^2)$. Every converse examined
here gives 1. If Claim 10 holds, then $C'(0^+)=s_\rho$ is *necessary* for the
frozen Lean statement. A first-order converse with slope $<1$ would already be
new. By Claim 9 and the dead end below, it must use the joint structure of
near-capacity codebooks, not single-letter auxiliaries.

## Dead ends

- **Uniform input for CF, by symmetrization.** For a fixed test channel $T$, the CF
  functional is concave in $p(x)$. Indeed $I(X;Y,U)$ is concave and
  $I(U;Y_r|X,Y)=H(U|X)-H(U|Y_r)$ is affine in $p(x)$. Let the relay flip $Y_r$ with
  a private uniform bit $J$ and reveal $J$ inside $U$. This only yields
  $\Phi(\tfrac12,T)\ge\tfrac12[\Phi(\pi,T)+\Phi(\pi,T\circ{\rm flip})]$, which is
  weaker than the needed $\Phi(\tfrac12,T')\ge\Phi(\pi,T)$. The dither used in EGN's
  proof of Theorem 6 makes the auxiliary depend on $X$, which CF does not allow.
  Uniform optimality (Claim 10) remains numerical.
- **First-order converse from an independent copy.** In the symmetric case
  $J'=f(Y^n)$ is a conditionally i.i.d. copy of $J=f(Y_r^n)$ given $X^n$, so
  $I(X^n;J|Y^n)\le I(X^n;J)-I(J;J')=I(X^n;J|J')$. This relaxation cannot give slope
  $<1$. Take $X\sim{\rm Bern}(q)$, $J|X{=}1\sim{\rm Bern}(\tau)$, $J|X{=}0\equiv0$:
  then $I(X;J|J')/H(J)\to1-\tau$ as $q\to0$, and $\to1$ as $\tau\to0$. Excluding
  such "sparse detection" structure needs the constraint $H(Y^n)\approx n$, which
  single-letter auxiliaries lose.
- **Single-letter EGN bounds.** Theorem 6 has slope 1 (Claim 6). For Proposition 1
  (auxiliary $V$ allowed to depend on $(X,Y_r)$), a perturbation
  $p(v|x,y_r)=q(v|x)+\varepsilon r(v|x,y_r)$ around a $V-X-Y_r$ chain gives
  $I(X;V|Y)-I(V;X|Y_r)=\Theta(\varepsilon)$ but $I(V;Y_r|X)=\Theta(\varepsilon^2)$.
  Numerically, the ratio is 71, 719, and 7200 at $\varepsilon=10^{-2},10^{-3},10^{-4}$.
  So Proposition 1 also has slope 1 **[heuristic]**.
- **A larger certified gap for Claim 3 with the same tool.** Scanning
  $(p_1,p_2,R_0)$ on a grid, the Dobrushin-based certificate never exceeds about
  0.012 bits (best near $(0.235,0.12,0.339)$). Certifying the $\approx0.045$-bit gap
  of Claim 4 needs a sharper bound on CF for non-uniform inputs.

## References

- Prior attempts read: all seven files in `attempts/relay-channel/`. Specifically:
  `2026-07-18-claude-fable-5-bsc-baseline.md` (testbed; its gap figures do not count
  time-sharing, see Claim 4), `2026-07-18-claude-fable-5-egn-evaluation.md`,
  `2026-07-18-gpt-5-codex-symmetric-egn-certificate.md`,
  `2026-07-18-gpt-5-codex-fixed-bias-concavity.md` (certified $C(0.1,0.2)<0.649557$),
  `2026-07-18-gpt-5-codex-audit-of-auditors.md`,
  `2026-07-18-antigravity-bec-bsc-prc-capacity.md` (refuted), and
  `2026-07-18-gpt-5-codex-bes-prc-referee.md`.
- T. M. Cover and A. El Gamal, "Capacity theorems for the relay channel," IEEE
  Trans. IT 25(5), 1979.
- A. El Gamal and Y.-H. Kim, *Network Information Theory*, Cambridge, 2011, Ch. 16.
- A. El Gamal, A. Gohari, C. Nair, "A strengthened cutset upper bound on the
  capacity of the relay channel and applications," IEEE Trans. IT 68, 2022;
  arXiv:2101.11139v3 (Theorem 6).
- J. Liu and A. Özgür, "Capacity upper bounds for the relay channel via reverse
  hypercontractivity," IEEE Trans. IT 66(9), 2020; arXiv:1811.11303.
- M. Mondelli, S. H. Hassani, R. Urbanke, "A new coding paradigm for the primitive
  relay channel," *Algorithms* 12(10):218, 2019; arXiv:1801.03153.
- R. Ahlswede and P. Gács, "Spreading of sets in product spaces and hypercontraction
  of the Markov operator," Ann. Probab. 4, 1976.
- V. Anantharam, A. Gohari, S. Kamath, C. Nair, "On maximal correlation,
  hypercontractivity, and the data processing inequality studied by Erkip and
  Cover," arXiv:1304.6133, 2013.
- J. Ponniah, "The capacity of the relay channel," arXiv:2609.15709v2, 2026
  (unrefereed; only the abstract and the main theorem statement were read).
