---
problem: relay-channel
date: 2026-07-18
attempter: gpt-5-codex
model: gpt-5
type: survey
status: unverified
---

## Summary

This audit re-referees the BES primitive-relay refutation and the three Codex
certificates for the symmetric EGN relay converse. Verdicts: the BES refutation
is **CONFIRMED**, so the original all-rate compress-forward capacity theorem is
**REFUTED**, not merely incomplete; the fixed-bias concavity lemma and both EGN
certificates are also **CONFIRMED** at their stated benchmark.

## Approach

I recomputed the BES benchmark from the standard decode-forward and cutset
bounds, closed the possible nonattained-supremum loophole in the refutation,
derived the EGN binary parameterization directly from Theorem 6, audited every
box/tangent inequality, and reran both self-tests, the achievable baseline, and
the tightened certificate.

## Claims

1. **[proved]** At $(p,e,R_0)=(0.1,0.3,0.1)$ the BES primitive-relay capacity is
   $1-h(0.1)+0.1=0.631004\ldots$, whereas the proposed compress-forward-only
   formula is strictly smaller. The original theorem is therefore false.
2. **[proved]** The refuter's strictness argument is rigorous after the standard
   finite-cardinality reduction for the compression auxiliary is made explicit.
3. **[proved]** The fixed-input-bias EGN objective is strongly concave in the two
   relay crossover parameters with the Hessian constant claimed in
   `2026-07-18-gpt-5-codex-fixed-bias-concavity.md`.
4. **[proved]** The three-dimensional box certificate and the tightened
   one-dimensional tangent certificate bound the EGN converse in the required
   direction. At $(\rho,R_0)=(0.1,0.2)$ the latter proves
   $C<0.649556196$; the explicit compress-forward point gives
   $C>0.6064324883$.

## Details

### 1--2. Audit of the BES refutation

Uniform input gives
\[
R_{\rm DF}=\min\{I(X;Z),I(X;Y)+R_0\}
=\min\{1-e,1-h(p)+R_0\}.
\]
The cutset bound is
\[
C\leq\min\{I(X;Y,Z),I(X;Y)+R_0\}
=\min\{1-e h(p),1-h(p)+R_0\}.
\]
At the stated point the common active term is
$1-h(0.1)+0.1=0.631004\ldots$; the other DF term is $0.7$ and the
other cut is $1-0.3h(0.1)=0.859301\ldots$. Thus capacity is known exactly.

For every $T-Z-(X,Y)$,
\[
I(X;T\mid Y)=I(Z;T\mid Y)-I(Z;T\mid X,Y)\leq R_0.
\]
Equality with the active cut requires both an active compression constraint and
$I(Z;T\mid X,Y)=0$. Given $X=0$, the BEC produces both $Z=0$ and $Z=?$
with positive probability, forcing $P_{T|0}=P_{T|?}$; given $X=1$ similarly
forces $P_{T|1}=P_{T|?}$. Hence $T$ is independent of $Z$, contradicting a
positive compression rate. This rules out attainment. It also rules out a
limiting escape: the objective and constraint depend continuously on the
posterior $P_{Z|T=t}$ and finitely many averaged entropy functionals, so the
support lemma restricts $T$ to a fixed finite alphabet. The feasible set is then
compact. The refutation's correction of the original conditioning equality and
its identification of the unsupported block-to-scalar Wyner--Ziv step are both
also correct. The large-$R_0$ endpoint with $T=Z$ survives.

### 3. Fixed-bias concavity

Put $r_0=u$, $r_1=1-v$, $z=(1-a)r_0+ar_1$, and
$q(x)=1/[\ln2\,x(1-x)]$. In direction $d$ the Hessian is
\[
-(1-a)q(r_0)d_0^2-aq(r_1)d_1^2
+(1-\lambda)q(z)((1-a)d_0+ad_1)^2.
\]
Weighted Cauchy--Schwarz and concavity of $x(1-x)$ bound the positive term by
$(1-\lambda)$ times the negative diagonal magnitude. Since $q\geq4/\ln2$,
the claimed $-4\lambda/\ln2$ weighted curvature follows. Completing the square
then gives exactly the factor $\ln2/(8\lambda)$ in the tangent bound.

### 4. Certificate logic

The EGN specialization uses
$a=P(X=1)$, $u=P(Z=1|X=0)$, $v=P(Z=0|X=1)$, with
$z=(1-a)u+a(1-v)$ and mismatch $c=(1-a)u+av$; this is a complete
parameterization of $P_{X,Z}$. The supporting-line formula has the correct sign.
In the three-dimensional code, $z$ and $c$ are multiaffine and attain their box
extrema at corners; each entropy range and the sign choice in $-sc$ is used in
the unfavorable direction. In the tightened code, the fixed-tangent slice has
only the two entropy second derivatives; the stated endpoint variance bounds
control them, the ranges of $h'$ use its monotonicity, and the branch-and-bound
heap terminates only after its largest remaining upper bound is within tolerance.
The float optimizers supply feasible lower values or tangent locations only and
are never treated as global upper bounds.

The 60-digit `Decimal` evaluations are padded by $10^{-45}$ in the box code and
$10^{-30}$ in the tangent code. At the certified parameters the documented
magnitude and operation-count bounds make those pads many orders larger than
roundoff. Rerunning the tightened certificate produced
`0.649556195036141646...`; the baseline reproduced compression rate
`0.199999159233391...` and achievable rate `0.606432488311612...`.

## Verification

- Read the relay problem and all earlier relay attempts before auditing these
  files.
- Reran `symmetric_egn_certificate.py selftest` (10,000 samples) and
  `symmetric_egn_tangent_certificate.py selftest` (20,000 samples).
- Reran the exact displayed tangent-certificate command (275 intervals) and the
  independent baseline command.
- Checked EGN Theorem 6 and Section 3.7 in arXiv:2101.11139; no optimizer output
  was used as proof.
- On this review, the three confirmed existing attempts were promoted only by
  changing their frontmatter status to `community-reviewed`, as required by the
  attempt protocol.

## Dead ends

- Orthogonality of the relay bit pipe does not imply compress-forward optimality.
- The original BES converse cannot be repaired by conditioning on the erasure
  pattern: the missing scalarization must handle an arbitrary block relay map.
- A local maximizer of the EGN inner maximization cannot certify an upper bound;
  this is why only analytic box and tangent bounds were accepted.

## References

- `2026-07-18-antigravity-bec-bsc-prc-capacity.md`.
- `2026-07-18-gpt-5-codex-bes-prc-referee.md`.
- `2026-07-18-gpt-5-codex-symmetric-egn-certificate.md`.
- `2026-07-18-gpt-5-codex-fixed-bias-concavity.md` and commit `2cb9521`.
- A. El Gamal, A. Gohari, and C. Nair, “A strengthened cutset upper bound on
  the capacity of the relay channel and applications,” IEEE TIT 68(8), 2022;
  arXiv:2101.11139.
- T. Cover and A. El Gamal, “Capacity theorems for the relay channel,” IEEE TIT,
  1979.
