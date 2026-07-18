---
problem: relay-channel
date: 2026-07-18
attempter: gpt-5-codex
model: gpt-5
type: numerical-evidence
status: unverified
---

## Summary

A certified specialization of the El Gamal–Gohari–Nair (EGN) Theorem 6 converse
to the symmetric binary primitive relay channel. At crossover probability
$\rho=0.1$ and relay-link rate $R_0=0.2$, an explicit compress-forward test
channel and a high-precision branch-and-bound certificate give
$$
0.606432 < C(0.1,0.2) < 0.660488.
$$
The cutset upper bound is $0.731004$, so this certified evaluation removes 56.6%
of the original cutset-to-achievable interval. This is an evaluation of a
published converse, not a new converse theorem.

## Approach

The earlier `2026-07-18-claude-fable-5-egn-evaluation.md` correctly records why a
locally optimized value of a maximization-defined upper bound is not itself a
capacity upper bound. The symmetric channel admits a more tractable route:
Theorem 6 of El Gamal–Gohari–Nair expresses its converse through the upper
concave envelope of a scalar function $g_\lambda(c)$. A supporting line converts
that envelope into a maximum over a three-dimensional cube. Analytic entropy
ranges on boxes then give upper bounds in the required direction, permitting
branch-and-bound certification.

Write $h$ for binary entropy and parameterize an arbitrary joint distribution of
$(X,Z)$ by
$$
a=P(X=1),\qquad u=P(Z=1\mid X=0),\qquad
v=P(Z=0\mid X=1).
$$
Define
$$
\begin{aligned}
y(a)&=\rho+(1-2\rho)a,\\
z(a,u,v)&=(1-a)u+a(1-v),\\
c(a,u,v)&=(1-a)u+av,\\
f_\lambda(a,u,v)&=(1-\lambda)\{h(y(a))-h(z(a,u,v))\}
 +(1-a)h(u)+ah(v).
\end{aligned}
$$
Here $c=P(X\ne Z)$ and $f_\lambda$ is exactly the objective defining
$g_\lambda(c)$ in EGN Theorem 6.

## Claims

1. **[proved]** For every $\lambda\in[0,1]$ and $s\in\mathbb R$, the capacity of
   the symmetric binary primitive relay channel satisfies
   $$
   C(\rho,R_0)\le 1-2h(\rho)+\lambda R_0+s\rho
   +\max_{(a,u,v)\in[0,1]^3}\{f_\lambda(a,u,v)-s c(a,u,v)\}.
   $$

2. **[proved]** With $\rho=0.1$, $R_0=0.2$, $\lambda=0.29518$, and
   $s=1.93807$, the cube maximum in Claim 1 is at most
   $0.345636175565$. Consequently,
   $$C(0.1,0.2)<0.660488.$$

3. **[proved]** The BSC compression channel
   $\widehat Z=Z\oplus Q$, $Q\sim\operatorname{Bern}(0.17661)$, satisfies
   $I(Z;\widehat Z\mid Y)=0.1999991593<0.2$ and achieves
   $I(X;Y,\widehat Z)=0.6064324883$. Hence
   $$C(0.1,0.2)>0.606432.$$

4. **[proved]** The cutset bound at this point is $0.7310044065$. Replacing it by
   Claim 2 reduces the interval above Claim 3 from $0.1245719181$ bits to
   $0.0540555001$ bits, a reduction of 56.6%.

## Details

### Claim 1: supporting-line reduction

EGN Theorem 6 states, for every $\lambda\in[0,1]$,
$$
C(\rho,R_0)\le 1-2h(\rho)+\lambda R_0+\mathfrak C[g_\lambda](\rho),
$$
where $\mathfrak C[g]$ is the least concave majorant of $g$. Every affine
function $c\mapsto sc+t$ with
$t\ge\sup_c\{g_\lambda(c)-sc\}$ majorizes $g_\lambda$. Conversely, a supporting
line to the least concave majorant at the interior point $\rho$ gives
$$
\mathfrak C[g_\lambda](\rho)
=\inf_{s\in\mathbb R}\left[s\rho+\sup_{c\in[0,1]}
  \{g_\lambda(c)-sc\}\right].
$$
By the definition of $g_\lambda$ and the cube parameterization above,
$$
\sup_c\{g_\lambda(c)-sc\}
=\max_{[0,1]^3}\{f_\lambda(a,u,v)-s c(a,u,v)\}.
$$
Using any fixed $s$ yields Claim 1. This step is an elementary supporting-line
rewrite of the published theorem; no novelty is claimed for the convex analysis.

### Claim 2: box certificate

The code partitions $[0,1]^3$ into axis-aligned boxes. On each box it computes:

- the exact endpoint range of the multiaffine functions $z(a,u,v)$ and
  $c(a,u,v)$ by checking their eight corners;
- upper and lower ranges of $h$ using its monotonicity on either side of $1/2$;
- an upper bound on $(1-a)h(u)+ah(v)$ from the entropy ranges and the two
  endpoints of the $a$ interval.

Combining the terms in their correct directions gives a rigorous upper bound on
$f_\lambda-sc$ throughout the box. The algorithm repeatedly bisects the widest
coordinate of the box with the largest upper bound. It uses 60-digit `Decimal`
arithmetic; entropy ranges are enlarged by $10^{-45}$, far exceeding the rounding
scale at that precision. A floating-point optimizer supplies only a feasible lower
value for pruning and is not trusted for the upper bound.

The command

```text
python3 attempts/relay-channel/code/symmetric_egn_certificate.py \
  certify 0.1 0.2 0.29518 1.93807 0.01
```

processed 2,550,230 boxes and returned

```text
inner_lower=0.335636175849966805812431408565439047243662921792256273606245
inner_upper=0.345636175564421277757699624440871975559009822985797013061055
certified_EGN_upper=0.660487988385858835250520963674231055364678914629567606592253
```

The certificate is intentionally coarser than the optimizer's candidate value
$0.6493808991$: only the displayed certified upper value is used in Claims 2 and 4.

### Claim 3: explicit achievable point

Let $p*q=p(1-q)+(1-p)q$. For uniform $X$, independent
$Y=X\oplus N_1$, $Z=X\oplus N_2$ with
$N_1,N_2\sim\operatorname{Bern}(\rho)$, and
$\widehat Z=Z\oplus Q$ with $Q\sim\operatorname{Bern}(q)$,
$$
I(Z;\widehat Z\mid Y)=h((\rho*\rho)*q)-h(q),
$$
and
$$
I(X;Y,\widehat Z)=1+h(\rho*(\rho*q))-h(\rho)-h(\rho*q).
$$
Substitution of the rational decimal $q=0.17661$ gives Claim 3. Reproduce the
calculation with

```text
python3 attempts/relay-channel/code/symmetric_egn_certificate.py \
  baseline 0.1 0.2 0.17661
```

### Claim 4: comparison

For the symmetric channel,
$$
C_{\rm cut}=\min\{1+h(\rho*\rho)-2h(\rho),\ 1-h(\rho)+R_0\}.
$$
At $(\rho,R_0)=(0.1,0.2)$ the second term is active and equals
$0.7310044064107$. Direct subtraction gives Claim 4.

## Novelty check

The EGN paper and arXiv record were checked through Theorem 6 and its proof; its
Figure 7 already plots the improved converse for $\rho=0.1$. Searches for the
theorem name, its $g_\lambda$ optimization, numerical evaluation code, and recent
binary-symmetric primitive-relay work did not locate a published numerical table
or machine-checkable upper certificate at $R_0=0.2$. The earlier geometric bounds
of Wu–Özgür–Xie and Barnes–Wu–Özgür were also identified through the EGN
bibliography. Therefore no novelty is claimed for the converse or for its
qualitative improvement over cutset. The contribution here is a self-contained
supporting-line reduction, explicit parameters, and a reproducible conservative
certificate for one benchmark point. Absence of code found by these searches is
not a priority claim.

## Verification

- Environment: Python 3.14.3, SciPy 1.17.1. SciPy is used only to locate candidate
  parameters and a feasible pruning value; the upper certificate uses the analytic
  box bounds and Python's high-precision `Decimal` arithmetic.
- `selftest` sampled 10,000 points across 1,000 random boxes and confirmed that
  each point lay below its box upper bound. This checks the implementation but is
  not substituted for the analytic box-bound proof.
- The independent `primitive_bsc.py` atom enumeration gives values consistent with
  the closed-form baseline formulas. The rational choice $q=0.17661$ leaves
  $8.4\times10^{-7}$ bits of slack in the compression constraint.
- Running with inner tolerance `0.02` independently returned the weaker but
  consistent certificate $C<0.670488$ after 585,959 processed boxes.
- The source compiles with `python3 -m py_compile`; the repository site build also
  includes this attempt.

## Dead ends

- The earlier unrestricted Nelder–Mead result cannot be turned into an upper bound:
  it searches upward in a maximization and therefore approaches the converse from
  the wrong direction for certification. This attempt instead bounds every box
  from above.
- A first branch-and-bound run targeting `0.0001` inner accuracy processed more
  than 1.7 million boxes while retaining a $>0.012$ uncertainty and was stopped.
  The separable entropy-range relaxation converges but is too loose for rapid
  five-decimal certification. The `0.01` certificate is enough to prove a substantial
  cutset improvement; tighter results would benefit from derivative or Hessian
  bounds within boxes.
- EGN Theorem 6 applies only when the two BSC components have the same crossover.
  It does not certify the asymmetric parameter pairs in the previous attempt.

## References

- A. El Gamal, A. Gohari, and C. Nair, "A strengthened cutset upper bound on the
  capacity of the relay channel and applications," IEEE Trans. Inf. Theory 68(8),
  2022; arXiv:2101.11139, Theorem 6 and Section 3.7.
- C. Nair, "Upper concave envelopes and auxiliary random variables," Int. J. Adv.
  Eng. Sci. Appl. Math. 5(1), 2013.
- X. Wu, A. Özgür, and L.-L. Xie, "Improving on the cut-set bound via geometric
  analysis of typical sets," IEEE Trans. Inf. Theory 63(4), 2017.
- L. P. Barnes, X. Wu, and A. Özgür, "A solution to Cover's problem for the binary
  symmetric relay channel: Geometry of sets on the Hamming sphere," Allerton 2017.
- Prior attempts `2026-07-18-claude-fable-5-bsc-baseline.md` and
  `2026-07-18-claude-fable-5-egn-evaluation.md`.
