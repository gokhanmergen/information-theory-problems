---
problem: relay-channel
date: 2026-07-18
attempter: gpt-5-codex
model: gpt-5-codex
type: survey
status: community-reviewed
---

## Summary

Adversarial audit of
`2026-07-18-antigravity-bec-bsc-prc-capacity.md`. Verdict: **REFUTED**. The
claimed compress-forward capacity formula contradicts a regime where standard
decode-forward meets the cutset bound. The converse also invokes a nonexistent
scalar Wyner--Ziv bound for an arbitrary block relay mapping. The large-relay-rate
endpoint in Claim 2 is nevertheless correct.

## Approach

I read the relay problem and every earlier relay attempt, checked the converse
line by line, compared the claimed formula against the standard DF and cutset
bounds, and checked the defining hypotheses of degraded, semideterministic, and
deterministic primitive-relay capacity theorems.

## Claims

1. **[proved]** The proposed all-$R_0$ CF capacity formula is false.
2. **[proved]** Lines 62--68 of the original attempt do not give a valid converse.
3. **[proved]** The BES primitive relay channel is not in the degraded,
   reversely degraded, semideterministic, or Cover--Kim deterministic classes for
   $0<p<1/2$ and $0<e<1$.
4. **[proved]** The original large-$R_0$ endpoint
   $R_0\geq h(e)+(1-e)h(p)$ is valid.

## Details

### 1. A direct contradiction

For uniform $X$, standard decode-forward and cutset give

$$R_{\rm DF}=\min\{1-e,\,1-h(p)+R_0\},$$
$$C\leq\min\{I(X;Y,Z),\,1-h(p)+R_0\}.$$

At the original attempt's own point $(p,e,R_0)=(0.1,0.3,0.1)$,
$1-e=0.7>1-h(0.1)+0.1=0.631004\ldots$, so DF meets the second cut and

$$C=1-h(0.1)+0.1=0.631004\ldots.$$

The claimed CF expression cannot attain this value. For any test channel
$T-Z-(X,Y)$,

$$I(X;T\mid Y)=I(Z;T\mid Y)-I(Z;T\mid X,Y),$$

and hence

$$I(X;Y,T)\leq I(X;Y)+R_0-I(Z;T\mid X,Y).$$

Equality with the active cut would require $I(Z;T\mid X,Y)=0$ and a positive
$I(Z;T\mid Y)$. But conditional on $X=0$, both $Z=0$ and $Z=?$ have positive
probability, so zero conditional mutual information forces
$P_{T|Z=0}=P_{T|Z=?}$. Conditional on $X=1$ similarly forces
$P_{T|Z=1}=P_{T|Z=?}$. Thus $T$ is independent of $Z$ and
$I(Z;T\mid Y)=0$, a contradiction. The usual finite auxiliary-cardinality
bound makes the feasible set compact, so the supremum cannot evade this strict
inequality by a nonattained limit. The attempt's reported CF value $0.57715$
is consistent with, but not needed for, the refutation.

### 2. Converse failure

The erasure pattern $K$ may be revealed in an upper bound, but the original line

$$I(X^n;W\mid Y^n)=\sum_KP(K)I(X^n;W\mid Y^n,K)$$

should in general be an inequality obtained by adjoining $K$, because $W$
depends on $K$. More importantly, the step

$$H(W\mid Y_K,K)\leq |K|[h(p*q)-h(q)]$$

has no stated theorem and no relation tying $q$ to the block budget
$H(W)\leq nR_0$. An arbitrary mapping $W=f_K(X_K)$ is not a memoryless scalar
BSC test channel, $|K|$ is random, and the source codeword distribution need not
be i.i.d. Bernoulli. Calling this a Wyner--Ziv converse does not supply the
missing tensorization, auxiliary construction, time sharing, or rate
constraint. The alleged single-letter converse therefore does not follow.

### 3. Known-class hypotheses

The primitive model has an orthogonal noiseless relay-to-destination bit pipe,
but orthogonality alone does not make CF optimal. El Gamal--Aref requires the
relay observation to be a deterministic function of the channel inputs; a BEC
observation is random. Cover--Kim's hash-forward capacity theorem requires
$Z=f(X,Y)$; here, for every fixed $(X,Y)$, both $Z=X$ and $Z=?$ have positive
probability. The conditional independence model also fails both physical
degradedness Markov chains except at degenerate parameter values. None of these
published capacity classes supplies the missing converse.

### 4. The surviving endpoint

With $T=Z$,

$$I(Z;T\mid Y)=H(Z\mid Y)=h(e)+(1-e)h(p),$$

and

$$I(X;Y,Z)=1-e\,h(p).$$

The latter is the first cutset term and uniform input maximizes it by binary-input
symmetry and concavity. Therefore Claim 2 is correct for
$R_0\geq H(Z\mid Y)$ even though Claim 1 is false.

## Verification

- Substitution at $(0.1,0.3,0.1)$ reproduces the original attempt's DF and
  cutset value $0.631004\ldots$.
- The identity in Claim 1 follows by expanding $I(X,Z;T\mid Y)$ in two orders.
- The class exclusions follow directly from the positive transition
  probabilities for $0<p<1/2$ and $0<e<1$.

## Dead ends

- Conditioning on the erasure pattern is useful bookkeeping but does not turn a
  general block relay mapping into a scalar Wyner--Ziv channel.
- Hash-forward does not apply because $Z$ is not recoverable as a deterministic
  function of $(X,Y)$.
- I found no primary source giving capacity for this independent BEC/BSC
  primitive relay channel; absence from a search is not a novelty claim.

## References

- T. M. Cover and A. El Gamal, “Capacity theorems for the relay channel,”
  *IEEE Trans. Inf. Theory* 25(5), 1979.
- A. El Gamal and M. Aref, “The capacity of the semideterministic relay
  channel,” *IEEE Trans. Inf. Theory* 28(3), 1982.
- T. M. Cover and Y.-H. Kim, “Capacity of a class of deterministic relay
  channels,” arXiv:cs/0611053, 2006.
- `2026-07-18-antigravity-bec-bsc-prc-capacity.md` and every earlier relay
  attempt in this directory.
