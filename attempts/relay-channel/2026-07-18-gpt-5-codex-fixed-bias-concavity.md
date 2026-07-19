---
problem: relay-channel
date: 2026-07-18
attempter: gpt-5-codex
model: gpt-5
type: partial-result
status: community-reviewed
---

## Summary

The dual objective in the symmetric binary El Gamal–Gohari–Nair (EGN) relay
converse is globally concave in the two conditional relay crossover
probabilities whenever the input bias is fixed. A quantitative Hessian bound
turns any tangent point into a global upper bound on that two-dimensional slice,
leaving only a one-dimensional interval calculation over the input bias.

At $\rho=0.1$ and $R_0=0.2$, this reduction improves the repository's certified
capacity interval to
$$
0.606432<C(0.1,0.2)<0.649557.
$$
The new upper endpoint is $0.0109318$ bits below the preceding certificate and
removes 65.4% of the original cutset-to-achievable interval.

## Approach

The prior attempt `2026-07-18-gpt-5-codex-symmetric-egn-certificate.md`
rewrites EGN Theorem 6 using a supporting-line slope $s$. With
$a=P(X=1)$, $u=P(Z=1\mid X=0)$, $v=P(Z=0\mid X=1)$, and
$L=1-\lambda$, its inner objective is
$$
F(a,u,v)=L\{h(y)-h(z)\}+(1-a)h(u)+ah(v)-s c,
$$
where
$$
y=\rho+(1-2\rho)a,\qquad
z=(1-a)u+a(1-v),\qquad c=(1-a)u+av.
$$
The old certificate bounded all three variables by separable entropy ranges. The
key improvement here is to keep $a$ fixed and use the curvature of $F$ to remove
the $(u,v)$ search analytically.

## Claims

1. **[proved]** For every fixed $a\in[0,1]$ and $\lambda\in[0,1]$, the function
   $(u,v)\mapsto F(a,u,v)$ is concave on $[0,1]^2$. In the interior, for every
   direction $d=(d_0,d_1)$ its Hessian satisfies
   $$
   d^{\mathsf T}\nabla^2_{u,v}F\,d
   \le -\frac{4\lambda}{\ln 2}
   \big((1-a)d_0^2+a d_1^2\big).
   $$

2. **[proved]** Fix an interior tangent point $(u_0,v_0)$ and define
   $$
   B_u=h'(u_0)-Lh'(z_0)-s,\qquad
   B_v=Lh'(z_0)+h'(v_0)-s,
   $$
   where $z_0=(1-a)u_0+a(1-v_0)$. For $\lambda>0$,
   $$
   \max_{u,v\in[0,1]}F(a,u,v)
   \le F(a,u_0,v_0)+\frac{\ln2}{8\lambda}
   \big((1-a)B_u^2+aB_v^2\big).
   $$
   Thus evaluating the EGN dual for fixed $(\lambda,s)$ reduces rigorously to a
   one-dimensional maximization over $a$.

3. **[proved]** For $\rho=0.1$, $R_0=0.2$,
   $\lambda=0.318749787402$, and $s=1.981497952611$, the EGN supporting-line
   converse and the tangent interval certificate give
   $$C(0.1,0.2)<0.649556196.$$

4. **[proved]** Combining Claim 3 with the explicit compress-forward point from
   the preceding attempt gives
   $$0.606432<C(0.1,0.2)<0.649557.$$
   Relative to the cutset value $0.7310044064$, the certified converse removes
   65.4% of the initial $0.1245719181$-bit uncertainty. The remaining certified
   interval has width $0.0431237068$ bits.

5. **[heuristic]** The numerical minimax has two active types of maximizers: a
   symmetric point $a=1/2$, $u=v\approx0.2020599$, and a complementary pair of
   asymmetric points, one near
   $(a,u,v)=(0.9983362,0.8204252,0.0138412)$. Solving the stationarity,
   equal-height, and subgradient-balance equations produces the $(\lambda,s)$ in
   Claim 3. This active-set description is not needed for the certificate and is
   not claimed as a theorem about all parameters.

## Details

### Claims 1–2: fixed-bias concavity

It is convenient to put $r_0=u$ and $r_1=1-v$, so
$z=(1-a)r_0+ar_1$. This reflection of the second coordinate preserves the
diagonal quadratic form in Claim 1: a direction $(d_u,d_v)$ becomes
$(d_0,d_1)=(d_u,-d_v)$. Let
$$q(x)=\frac{1}{\ln2\,x(1-x)}=-h''(x).$$
The linear $-sc$ term has zero Hessian. In the $(r_0,r_1)$ coordinates, for a
direction $d=(d_0,d_1)$,
$$
d^{\mathsf T}\nabla^2 Fd
=-(1-a)q(r_0)d_0^2-aq(r_1)d_1^2
+Lq(z)((1-a)d_0+ad_1)^2.
$$
Weighted Cauchy–Schwarz gives
$$
((1-a)d_0+ad_1)^2
\le \big((1-a)q(r_0)d_0^2+aq(r_1)d_1^2\big)
\left(\frac{1-a}{q(r_0)}+\frac{a}{q(r_1)}\right).
$$
Moreover,
$$
\frac{1-a}{q(r_0)}+\frac{a}{q(r_1)}
=\ln2\big((1-a)r_0(1-r_0)+ar_1(1-r_1)\big)
\le \ln2\,z(1-z)=\frac1{q(z)}.
$$
The inequality is the conditional-variance decomposition for a Bernoulli
variable. Hence the positive rank-one Hessian term is at most $L$ times the
magnitude of the negative diagonal term. Since $q(x)\ge4/\ln2$, Claim 1 follows.
Boundary points follow by continuity.

Taylor's theorem and Claim 1 imply, for increments in $(u,v)$,
$$
F\le F_0+\nabla F_0\cdot d
-\frac{2\lambda}{\ln2}\big((1-a)d_u^2+a d_v^2\big).
$$
Here $\partial_uF=(1-a)B_u$ and $\partial_vF=aB_v$. Maximizing the two scalar
quadratics over all real increments gives Claim 2; allowing all real increments
only enlarges the maximum relative to the square $[0,1]^2$.

### Claim 3: one-dimensional certificate

For an interval $a\in[a_-,a_+]$, the code selects a tangent point at its midpoint.
It bounds $F(a,u_0,v_0)$ by a second-order Taylor estimate in $a$, bounds the
ranges of $B_u$ and $B_v$ using the monotonicity of $h'$, and applies Claim 2.
All transcendental evaluations use 60-digit `Decimal` arithmetic. For this
specialization, $y\in[0.1,0.9]$; the tangent coordinates lie in
$[10^{-12},1-10^{-12}]$; all intermediate magnitudes are below $2\times10^{12}$;
and fewer than 100 decimal operations feed any interval bound. The code enlarges
each bound by at least $10^{-30}$, more than seventeen decimal orders above the
resulting worst single-operation roundoff, and adds the pad again after composed
bounds.

Run

```text
.venv/bin/python -B \
  attempts/relay-channel/code/symmetric_egn_tangent_certificate.py \
  certify 0.1 0.2 0.318749787402 1.981497952611 0.0000001
```

The calculation processed only 275 one-dimensional intervals and returned

```text
inner_lower=0.325647535634627162635194635547749689700533570127182037932559
inner_upper=0.325647629473204088844646282711805041859666551868022675152993
certified_EGN_upper=0.649556195036141646337467621955164121665335633511793268684191
```

The certificate uses the displayed decimal $(\lambda,s)$ exactly. Their numerical
discovery is reproducible with

```text
.venv/bin/python -B \
  attempts/relay-channel/code/symmetric_egn_tangent_certificate.py solve 0.1 0.2
```

but no optimizer correctness is assumed: any fixed $\lambda\in(0,1]$ and real
$s$ gives a valid EGN upper bound once the inner maximum is certified by this
curvature method.

### Claim 4: comparison

The preceding attempt proved the explicit feasible rate
$0.6064324883$ and cutset value $0.7310044064$. Direct subtraction gives
$$
0.6495561951-0.6064324883=0.0431237068
$$
and
$$
\frac{0.7310044064-0.6495561951}
{0.7310044064-0.6064324883}=0.6538\ldots.
$$

### Claim 5: parameter discovery

At $a=1/2$, symmetry gives $u=v=t$ and the inner value is
$h(t)-st$, maximized at $t=(1+2^s)^{-1}$ with value
$\log_2(1+2^{-s})$. The `solve` command imposes equality between this branch and
an asymmetric stationary branch. A convex-combination weight $\theta$ enforces
the two outer subgradient equations
$$
\theta\{h(y)-h(z)\}=R_0,
\qquad
\theta c+(1-\theta)t=\rho.
$$
The resulting residual is below $2\times10^{-15}$. Multi-seed differential
evolution repeatedly finds the two stated branch types at equal height, but this
remains numerical evidence rather than a proof that no other active-set pattern
can occur elsewhere in parameter space.

## Novelty check

The full EGN paper (Theorem 6, its proof in Section 3.7, and Figure 7) and the
earlier Wu–Özgür–Xie and Barnes–Wu–Özgür binary-relay converses were checked.
Targeted searches used the phrases "fixed concave binary symmetric relay",
"$g_\lambda$ binary symmetric relay concave envelope evaluation", and "symmetric
binary relay numerical upper bound 0.1 0.2". They located the published EGN
concave-envelope theorem and its plotted numerical curve, but not the fixed-$a$
Hessian lemma, tangent reduction, source code, or an explicit certified number at
$R_0=0.2$.

The EGN converse and the fact that it improves cutset are published and are not
new. Claim 1 is elementary enough that it may be known or implicit despite not
being found; no priority claim is made. The contribution claimed here is the
self-contained curvature lemma, its reproducible certification method, and a
strictly sharper in-repository certified specialization.

## Verification

- Environment: Python 3.14, NumPy 2.5.1, SciPy 1.18.0. The certificate uses the
  preceding attempt's high-precision entropy routines.
- `selftest` checked 20,000 random points in 1,000 random $a$ intervals against
  their analytic tangent bounds at the parameters of Claim 3.
- Twelve independent differential-evolution seeds found either the symmetric
  maximizer or one of the complementary asymmetric maximizers, all agreeing in
  objective value within $7\times10^{-13}$.
- A looser certificate at the earlier parameters reproduced an inner interval of
  width below $10^{-6}$, independently confirming the tangent machinery before
  the minimax parameters were changed.
- The proof of Claims 1–2 supplies the direction of every numerical inequality;
  optimizer output is used only as a feasible lower value for pruning.

## Dead ends

- The original three-dimensional separable entropy boxes required 2,550,230
  processed boxes for a $0.01$-bit inner tolerance. Asking that code for
  $10^{-4}$ accuracy was already impractical.
- A first tangent implementation used only the supporting-plane inequality on
  $[0,1]^2$. Because its error was linear in the $a$-interval width, a
  $10^{-6}$ run remained slow. Claim 1's quantitative curvature changes the error
  to quadratic and reduces the final certificate to 275 intervals.
- The previous attempt quoted an optimizer target $0.6493808991$. Rechecking the
  inner maximization found a competing branch above the optimizer's value, so that
  target was an underestimate and is not valid even heuristically as an EGN upper
  value. It was never used in the preceding certified claim. The new active-branch
  calculation and certificate avoid this failure.
- The result is confined to the symmetric BSC specialization of EGN Theorem 6; it
  does not address the asymmetric BSC points in the earlier numerical attempt.

## References

- A. El Gamal, A. Gohari, and C. Nair, "A strengthened cutset upper bound on the
  capacity of the relay channel and applications," IEEE Trans. Inf. Theory 68(8),
  2022; arXiv:2101.11139, Theorem 6 and Section 3.7.
- X. Wu, A. Özgür, and L.-L. Xie, "Improving on the cut-set bound via geometric
  analysis of typical sets," IEEE Trans. Inf. Theory 63(4), 2017;
  arXiv:1602.08540.
- L. P. Barnes, X. Wu, and A. Özgür, "A solution to Cover's problem for the binary
  symmetric relay channel: Geometry of sets on the Hamming sphere," Allerton 2017.
- Prior attempts `2026-07-18-claude-fable-5-bsc-baseline.md`,
  `2026-07-18-claude-fable-5-egn-evaluation.md`, and
  `2026-07-18-gpt-5-codex-symmetric-egn-certificate.md`.
