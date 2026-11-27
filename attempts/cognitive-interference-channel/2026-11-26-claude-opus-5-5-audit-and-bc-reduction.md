---
problem: cognitive-interference-channel
date: 2026-11-26
attempter: claude
model: claude-opus-5-5
type: reduction
status: unverified
---

## Summary

I audited the frozen region `rtdInnerBound` against Rini–Tuninetti–Devroye (RTD) 2011,
checking every constraint. The **audit** found that it is *not* a literal transcription
of RTD's Theorem 7 (Theorem V.1 in arXiv v1). It is a different, self-consistent
superposition-plus-binning region of the same family, with a different codebook
structure (differences D1–D7). It still lies inside a proved outer bound (Claim 5), and
achievability is sketched (Claim 6).

**Key check.** When the primary input is degenerate ($|\mathcal X_1|=1$), the frozen
region equals the catalog's own `martonInnerBound`, i.e. Marton's private-message region
*with* the common auxiliary $W$ (Claim 2). It therefore contains superposition coding in
both directions for every degraded BC. Gohari–El Gamal–Anantharam (2014) show only that
Marton *without* $W$ is suboptimal, so their result does not falsify the Statement. **No
catalog error.**

**Reduction.** The cognitive Statement implies `broadcast-channel`'s Statement
(`bcCapacityRegion = martonInnerBound`). Restricted to $|\mathcal X_1|=1$ the two are
equivalent (Claim 3). `marton-inner-bound-tightness` implies the same `broadcast-channel`
Statement.

**Known capacity classes.** The frozen region contains the capacity region in the
"better cognitive decoding" regime. That regime contains the very-weak and very-strong
interference regimes. It also contains the capacity region of the semi-deterministic
cognitive IC, and hence of the deterministic one (Claim 7). The containments are
explicit and were checked numerically.

## Approach

1. Decode the Lean projections into standard notation. Then transcribe the Lean
   constraints literally into an LP so that every algebraic claim below can be
   cross-checked numerically.
2. Compare constraint by constraint with RTD's Theorem 7. Sources: the IEEE version (its
   inner bound is labelled "Theorem 7", inequalities (11a)–(11k)) and arXiv:1003.4328v1
   (Theorem V.1, (12a)–(12k)). The two lists are identical.
3. Specialize to $|\mathcal X_1|=1$ and compare with the Core definition `martonInnerBound`.
4. For each known capacity class, choose auxiliaries explicitly.

## Notation: the frozen region in standard form

The Lean tuple is
`z = (Q, (U0, U1p, U2c, U2p, X1, X2), (Y1, Y2))`, with
`z.2.1.1 = U0`, `z.2.1.2.1 = U1p`, `z.2.1.2.2.1 = U2c`, `z.2.1.2.2.2.1 = U2p`,
`z.2.1.2.2.2.2.1 = X1`, `z.2.1.2.2.2.2.2 = X2`. Also `condMutualInfo (A, B, C)` $= I(A;B\mid C)$.
Every term below is conditioned on $Q$ as well; I suppress $Q$. The joint pmf of
$(Q,U_0,U_{1p},U_{2c},U_{2p},X_1,X_2)$ is arbitrary, and so are the auxiliary alphabet
sizes. The region is the closure of the set of $(R_1,R_2)=(R_{1c}+R_{1p},R_{2c}+R_{2p})$
with all seven rates $\ge 0$ such that:

| # | Lean | constraint |
|---|---|---|
| (1) | `rp₂c ≥ bin2c` | $R'_{2c} \ge I(U_{2c};X_1\mid U_0)$ |
| (2) | `rp₂p ≥ bin2p` | $R'_{2p} \ge I(U_{2p};X_1\mid U_0,U_{2c})$ |
| (3) | `rp₁p + rp₂c ≥ pen1` | $R'_{1p}+R'_{2c} \ge I(X_1,U_{1p};U_{2c}\mid U_0)$ |
| (4) | | $R'_{1p}+R'_{2p} \ge I(U_{2p};X_1\mid U_0,U_{2c}) + I(U_{1p};U_{2p}\mid U_0,X_1,U_{2c})$ |
| (5) | | $R'_{1p}+R'_{2c}+R'_{2p} \ge I(U_{2c},U_{2p};X_1\mid U_0) + I(U_{1p};U_{2c},U_{2p}\mid U_0,X_1)$ |
| (6) | | $R_{1p}+R'_{1p} \le I(X_1,U_{1p};Y_1\mid U_0,U_{2c}) + \pi$ |
| (7) | | $R_{1p}+R_{2c}+R'_{1p}+R'_{2c} \le I(X_1,U_{1p},U_{2c};Y_1\mid U_0) + \pi$ |
| (8) | | $R_{1c}+R_{1p}+R_{2c}+R'_{1p}+R'_{2c} \le I(U_0,X_1,U_{1p},U_{2c};Y_1) + \pi$ |
| (9) | | $R_{2p}+R'_{2p} \le I(U_{2p};Y_2\mid U_0,U_{2c})$ |
| (10) | | $R_{2c}+R_{2p}+R'_{2c}+R'_{2p} \le I(U_{2c},U_{2p};Y_2\mid U_0)$ |
| (11) | | $R_{1c}+R_{2c}+R_{2p}+R'_{2c}+R'_{2p} \le I(U_0,U_{2c},U_{2p};Y_2)$ |

Here $\pi := I(X_1,U_{1p};U_{2c}\mid U_0)$ (Lean `pen1`). This table is what
`code/lean_region_checks.py` implements, term by term from the Lean source.

**Basic properties** [proved].
- The set is convex. Every information term is conditioned on $Q$, so mixing two
  feasible configurations through $Q$ (after padding alphabets) mixes rates and terms
  linearly.
- It is downward closed in $\mathbb R^2_{\ge0}$. Rates appear only with nonnegative
  coefficients on the small side of "$\le$" constraints, and never in "$\ge$" constraints.

## Claims

1. **[proved]** Operational identity. Let $W'$ be any BC on `Fin kX → Fin kY₁ × Fin kY₂`.
   Define $W := W'$ viewed as a cognitive IC with $\mathcal X_1 = $ `Fin 1`, i.e.
   $W((x_1,x_2)) := W'(x_2)$. Then `cognitiveICCapacityRegion W = bcCapacityRegion W'`.
2. **[proved]** Marton specialization. For the same $W, W'$:
   `rtdInnerBound W = martonInnerBound W'`. That is the Core private-message Marton region
   with common auxiliary $W$: $R_1\le I(W,U;Y_1)$, $R_2\le I(W,V;Y_2)$, and
   $R_1+R_2\le \min\{I(W,U;Y_1)+I(V;Y_2|W),\ I(U;Y_1|W)+I(W,V;Y_2)\}-I(U;V|W)$.
   **Corollary [proved]:** for every BC the frozen region at $|\mathcal X_1|=1$ contains
   the superposition-coding region in both directions. Hence it equals capacity for every
   degraded BC (Bergmans; Gallager / Ahlswede–Körner), and GEA 2014 does not apply.
3. **[proved]** Reduction. `CognitiveInterferenceChannel.Statement → BroadcastChannel.Statement`.
   Moreover, the cognitive Statement restricted to `kX₁ = 1` is *equivalent* to
   `BroadcastChannel.Statement`. Also
   `MartonInnerBoundTightness.Statement → BroadcastChannel.Statement` (take the
   $R_0=0$ slice). So a positive answer here gives Marton's private-message region as the
   capacity region of every finite 2-receiver DM-BC. A counterexample to Marton's
   private-message tightness disproves the cognitive Statement.
4. **[proved]** GEA check. Gohari–El Gamal–Anantharam (IEEE Trans. IT 60(7):3748–3762,
   2014; arXiv:1006.5166, Claim 1 of §II-A) prove the following. *There are degraded
   broadcast channels for which Marton's private-message inner bound without $W$ is
   strictly contained in the capacity region.* By Claim 2 the frozen region includes $W$
   (realized by $U_{2c}$ with $U_0$ constant), so their theorem does not bear on the
   Statement. The faithful RTD Theorem 7 region also contains Marton with $W$: set
   RTD's $U_{2c}$ (primary common) to a constant and let RTD's $U_{1c}$ play $W$.
5. **[proved]** Outer-bound sandwich. For every $W$, the frozen region lies inside the
   one-auxiliary outer bound of Wu–Vishwanath–Arapostathis (RTD arXiv v1 Theorem III.1),
   written in this file's indexing as
   $$R_2\le I(X_2;Y_2\mid X_1),\quad R_1\le I(X_1,U;Y_1),\quad R_1+R_2\le I(X_1,U;Y_1)+I(X_2;Y_2\mid X_1,U),$$
   with $U=(Q,U_0,U_{1p},U_{2c})$.
6. **[sketch]** Achievability. The frozen region is achievable, so
   `rtdInnerBound W ⊆ cognitiveICCapacityRegion W`. The scheme is (a) in Details: the
   primary sends $X_1^n(m_{1c},m_{1p})$ superposed on $U_0^n(m_{1c})$; the cognitive
   transmitter GP-bins $U_{2c}$ and $U_{2p}$ against $X_1^n$, superposes $U_{1p}$ on
   $(U_0,X_1)$, and mutually covers $U_{1p}$ against $(U_{2c},U_{2p})$. Hence the Statement
   asks a well-posed question: is this inner bound tight?
7. **[proved, given the cited capacity theorems]** Known classes. The frozen region
   contains the capacity region in each of these cases:
   - (a) the "better cognitive decoding" (BCD) regime $I(U,X_1;Y_1)\le I(U,X_1;Y_2)$ for
     all $p(u,x_1,x_2)$ (RTD arXiv v1 Theorem VII.1). By RTD Remark VII.2 this includes
     the very-weak and very-strong interference regimes, i.e. the WVA and
     Maric–Yates–Kramer capacity results.
   - (b) the semi-deterministic cognitive IC $Y_2=f(X_1,X_2)$ (RTD arXiv v1 Theorem VIII.1),
     and hence the deterministic one.

   With Claim 6, the Statement therefore holds on every class listed in the problem file.
8. **[proved]** Audit (textual comparison). The frozen region differs from RTD Theorem 7
   in the ways D1–D7 below. **[open]** Whether `rtdInnerBound` contains the faithful
   Theorem 7 region for every channel is not established. If some channel had a point
   achievable by Theorem 7 but outside the frozen region, the frozen Statement would be
   false there. I found no such channel: all known capacity classes are covered
   (Claim 7).

## Details

### Claim 1
With $\mathcal X_1=$ `Fin 1`, `enc₁` is unique. Since
$W^{\otimes n}((\cdot, x_2^n), y) = \prod_i W'(x_{2,i}, y_i) = W'^{\otimes n}(x_2^n, y)$, the
error expression in `cognitiveICCapacityRegion` with `enc₂` is literally the expression in
`IsBCAchievable` with `enc := enc₂`. The message-set sizes $M_i$ are the same, and both
regions are closures of the same set. ∎

### Claim 2
Write $\mathcal R$ for the inner set of `rtdInnerBound W` and $\mathcal M$ for that of
`martonInnerBound W'`. With $X_1$ constant, every term with $X_1$ in the first or second
slot vanishes, and $X_1$ disappears from conditionings. So $I(U_{2c};X_1|U_0)=I(U_{2p};X_1|U_0U_{2c})=0$,
$\pi=I(U_{1p};U_{2c}|U_0)$, the right side of (4) is $K:=I(U_{1p};U_{2p}|U_0U_{2c})$, and the
right side of (5) is $\pi+K$.

*$\mathcal R\subseteq\mathcal M$.* Take a feasible configuration and set Marton's
$W:=(Q,U_0,U_{2c})$, $U:=U_{1p}$, $V:=U_{2p}$, $X:=X_2$. The random encoder
$p(x_2|\cdot)$ is allowed: apply Marton to the induced BC from $(W,U,V)$, then
derandomize. Write $I_1=I(U;Y_1|W)$, $I_2=I(V;Y_2|W)$, $J_1=I(W,U;Y_1)$, $J_2=I(W,V;Y_2)$.
Note $I(U_0U_{1p}U_{2c};Y_1|Q)\le J_1$ and $I(U_0U_{2c}U_{2p};Y_2|Q)\le J_2$ by the chain rule.
- (8) and (3) give $R_1\le J_1$.
- (11) gives $R_2\le J_2$.
- (8)+(9), with (5), gives $R_1+R_2\le J_1+I_2-K$.
- (6)+(11), with (5), gives $R_1+R_2\le I_1+J_2-K$.

These are exactly the four `martonInnerBound` inequalities.

*$\mathcal M\subseteq\mathcal R$.* Take Marton's $p(w,u,v,x)$ and embed it as $Q=U_0=$ const,
$U_{2c}=W$, $U_{1p}=U$, $U_{2p}=V$, $X_2=X$. Choose $R'_{2c}=0$,
$R'_{1p}=I(U;W)+a$, $R'_{2p}=b$ with $a,b\ge0$ and $a+b\ge K$, which satisfies (1)–(5).
Constraint (7) is implied by (8), and (10) by (11). The rest reduce to Marton's
rate-splitting scheme with $R_0:=R_{1c}+R_{2c}$:
$$R_{1p}+a\le I_1,\quad R_0+R_{1p}+a\le J_1,\quad R_{2p}+b\le I_2,\quad R_0+R_{2p}+b\le J_2.$$
Fourier–Motzkin elimination (done explicitly below) shows the following.
- If $K\le I_1+I_2$, the projection onto $(R_1,R_2)$ is exactly Marton's 4-inequality
  polytope.
- If $K>I_1+I_2$, every point of that polytope has
  $R_1+R_2<\min\{I(W;Y_1),I(W;Y_2)\}$. It is then feasible for the embedding
  $U_{1p}=U_{2p}=$ const, $R_{1c}=R_1$, $R_{2c}=R_2$, whose constraints reduce to
  $R_{1c}+R_{2c}\le\min\{I(W;Y_1),I(W;Y_2)\}$.

Hence $\mathcal M\subseteq\mathcal R$ and the closures agree. ∎

*Fourier–Motzkin step.* Eliminating $a,b$ requires $\min(I_1-R_{11},J_1-R_0-R_{11})\ge 0$,
$\min(I_2-R_{22},J_2-R_0-R_{22})\ge0$ and that the two minima sum to at least $K$. With
$R_{10}=x\in[0,R_1]$, $R_{20}=y\in[0,R_2]$, $R_{11}=R_1-x$, $R_{22}=R_2-y$, this is
- $x\ge R_1-I_1$ and $x\le J_2-R_2$;
- $y\ge R_2-I_2$ and $y\le J_1-R_1$;
- $x+y\ge R_1+R_2-I_1-I_2+K$ and $x+y\le J_1+J_2-K-R_1-R_2$;
- $R_1+R_2\le I_1+J_2-K$ and $R_1+R_2\le J_1+I_2-K$.

A box meets a slab iff the box is nonempty, the slab is nonempty, the box's low corner
lies below the slab's top, and its high corner lies above the slab's bottom. Checking the
16 resulting inequalities, all are implied by $R_1\le J_1$, $R_2\le J_2$ and the two sum
constraints, except one: $K\le I_1+I_2$. (The same reasoning is in El Gamal–Kim, Thm 8.4;
`T2` checks it numerically.)

*Corollary (superposition).*
- If $Y_1$ is the weaker receiver, take $W=U$, $V=X$, $U$ (Marton's) constant, with all
  of $M_1$ carried by $W$. This gives $R_1\le I(W;Y_1)$, $R_2\le I(X;Y_2|W)$.
- If $Y_2$ is the weaker receiver, swap the roles.

### Claim 3
For any BC $W'$, Claims 1 and 2 give `cognitiveICCapacityRegion W = bcCapacityRegion W'`
and `rtdInnerBound W = martonInnerBound W'`. So the instance `kX₁ = 1` of the cognitive
Statement is exactly the instance $W'$ of `BroadcastChannel.Statement`. Every $W'$ arises
this way.

For the Marton problem, take the slice $r.1=0$ of both sides of
`bcCommonCapacityRegion = martonCommonInnerBound`.
- The slice of the capacity side is `bcCapacityRegion`. ($\supseteq$: take $M_0=1$.
  $\subseteq$: fix a common message with conditional error at most the average.)
- The slice of the inner-bound side is `martonInnerBound`. At $R_0=0$ the fifth
  inequality is implied by the third, since $I(U_2;Y_2|U_0)\le I(U_0U_2;Y_2)$.
- Slicing commutes with closure because the inner set is downward closed in $R_0$. ∎

### Claim 5
Let $U=(Q,U_0,U_{1p},U_{2c})$.
- (8) with (3) gives $R_1\le I(U_0X_1U_{1p}U_{2c};Y_1|Q)\le I(X_1,U;Y_1)$.
- (10) with (1)+(2) gives $R_2\le I(U_{2c}U_{2p};Y_2|U_0Q)-I(U_{2c}U_{2p};X_1|U_0Q)$.
  This is at most $I(U_{2c}U_{2p};Y_2|X_1U_0Q)\le I(X_2;Y_2|X_1U_0Q)\le I(X_2;Y_2|X_1)$,
  using the Markov chain $(Q,U_0,U_{2c},U_{2p})-(X_1,X_2)-Y_2$.
- (8)+(9) with (5): a short chain-rule computation gives
  $\pi-(\text{rhs of }(5))=-I(U_{2p};X_1U_{1p}\mid U_0U_{2c}Q)$. Hence
  $R_1+R_2\le I(X_1,U;Y_1)+I(U_{2p};Y_2|U_0U_{2c}Q)-I(U_{2p};X_1U_{1p}|U_0U_{2c}Q)$.
  The last two terms together are at most $I(U_{2p};Y_2|U,X_1)\le I(X_2;Y_2|U,X_1)$. ∎

`T6` checks this on 60 random full instances.

### Claim 6 (sketch)
Scheme (a):
1. $U_0^n(m_{1c})$ is i.i.d. $p(u_0)$, and the primary sends $X_1^n(m_{1c},m_{1p})\sim p(x_1|u_0)$.
2. The cognitive transmitter knows $X_1^n$. It holds:
   - $U_{2c}^n(m_{1c},m_{2c},l_{2c})\sim p(u_{2c}|u_0)$;
   - $U_{2p}^n(\dots,m_{2p},l_{2p})\sim p(u_{2p}|u_0,u_{2c})$;
   - $U_{1p}^n(m_{1c},m_{1p},l_{1p})\sim p(u_{1p}|u_0,x_1)$.

   It looks for $(l_{2c},l_{2p},l_{1p})$ making the whole tuple jointly typical, then
   sends $X_2$ through $p(x_2|\cdot)$ and derandomizes.
3. Second-moment covering. Index sets that share codewords must be closed under
   superposition. The conditions $R'_A>D_A$ for
   $A=\{l_{2c}\},\{l_{2c},l_{2p}\},\{l_{1p}\},\{l_{1p},l_{2c}\},\{\text{all}\}$ are implied
   by (1)–(5), with (2) and (4) stronger than needed.
4. Receiver 1 decodes $(m_{1c},m_{1p})$ uniquely and $(l_{1p},m_{2c},l_{2c})$ non-uniquely.
   Its error events (m1c wrong) / (m1p wrong, $U_{2c}$ right) / (m1p and $U_{2c}$ wrong)
   give (8)/(6)/(7). The bonus $\pi$ appears because the wrong pair $(X_1,U_{1p})'$ is
   independent of the correct $U_{2c}$.
5. Receiver 2 decodes $(m_{2c},m_{2p})$ uniquely and $m_{1c}$ non-uniquely, giving
   (9)–(11).

I did not write out the typicality bookkeeping, hence [sketch]. A soundness bug would
make the Statement trivially false; Claim 5 rules out the gross form of such a bug.

### Claim 7
Indexing: Tx1/Rx1 primary, as in the Lean file. RTD's theorems have Tx1 cognitive, so
swap the indices 1↔2 when reading them.

**(a) BCD.** Capacity is region (1),
$\{R_1\le I(X_1U;Y_1),\ R_2\le I(X_2;Y_2|X_1),\ R_1+R_2\le I(X_1U;Y_1)+I(X_2;Y_2|X_1U)\}$,
for fixed $p(u,x_1,x_2)$. Its corner points are $B=(I(X_1U;Y_1),\,I(X_2;Y_2|X_1U))$ and
$A=(I(X_1U;Y_1)-I(U;Y_2|X_1),\,I(X_2;Y_2|X_1))$.
- *Config B* ($U_0:=(X_1,U)$, $U_{2p}:=X_2$, others constant) gives $R_1\le I(X_1U;Y_1)$
  and $R_2\le I(X_2;Y_2|X_1U)$. The sum constraint (11),
  $R_1+R_2\le I(X_1X_2;Y_2)$, holds by BCD.
- *Config A* ($U_0:=X_1$, $U_{2c}:=U$, $U_{2p}:=X_2$, $U_{1p}$ constant, all bin rates 0)
  reaches $A$ whenever $I(U;Y_1|X_1)\ge I(U;Y_2|X_1)$. The only extra constraint is (7):
  $R_{2c}=I(U;Y_2|X_1)\le I(U;Y_1|X_1)$. Constraint (11) holds by BCD.
- Otherwise $A$'s first coordinate is $I(X_1;Y_1)+I(U;Y_1|X_1)-I(U;Y_2|X_1)<I(X_1;Y_1)$.
  Then $A$ is dominated by $A_0=(I(X_1;Y_1),I(X_2;Y_2|X_1))$, which is Config A with $U$
  constant. It satisfies (11) by BCD with $U$ constant.
- If $A$'s first coordinate is negative, the top-left corner is dominated by
  $(0,I(X_2;Y_2|X_1))$.

The region is convex and downward closed, so the pentagon is contained.

This case split matters. The frozen region imposes (7) even when $R_{1p}=0$; RTD's
Remark V.2 would drop it. The split shows that this omission costs nothing in the BCD
regime.

**(b) Semi-deterministic** ($Y_2=f(X_1,X_2)$). Capacity is
$\{R_2\le H(Y_2|X_1),\ R_1\le I(Y_1;U,X_1),\ R_1+R_2\le I(Y_1;U,X_1)+H(Y_2|U,X_1)\}$.

Take $U_0=U_{2c}=$ const, $U_{1p}=U$, $U_{2p}=Y_2$, $R_{1c}=R_{2c}=R'_{2c}=0$,
$R'_{2p}=I(Y_2;X_1)+t$ and $R'_{1p}=I(U;Y_2|X_1)-t$ with $t\in[0,I(U;Y_2|X_1)]$. Then
(1)–(5) hold. Constraints (6)–(11) reduce to $R_1\le I(X_1U;Y_1)-I(U;Y_2|X_1)+t$ and
$R_2\le H(Y_2|X_1)-t$. The union over $t$ is the capacity pentagon: choose
$t=\max(0,R_1-I(X_1U;Y_1)+I(U;Y_2|X_1))$. This is the frozen-region analogue of RTD's
"$U_{1pb}=Y_1$" choice.

The deterministic cognitive IC is a sub-case. `T3` checks the "asymmetric clipper" of RTD
§X-A (capacity $R_1\le3$, $R_2\le2$, $R_1+R_2\le4$ in Lean indexing): both corner points
$(3,1)$ and $(2,2)$ are feasible.

### Claim 8: audit table

RTD → Lean renaming (RTD's Tx1 is cognitive):

| RTD | $U_{2c}$ | $X_2$ | $U_{1c}$ | $U_{2pb}$ | $U_{1pb}$ | $X_1$ | $Y_2$ | $Y_1$ |
|---|---|---|---|---|---|---|---|---|
| Lean | $U_0$ | $X_1$ | $U_{2c}$ | $U_{1p}$ | $U_{2p}$ | $X_2$ | $Y_1$ | $Y_2$ |

The rates map as $R_{2c}\to R_{1c}$, $R_{1c}\to R_{2c}$, $R_{1pb}\to R_{2p}$, $R_{2pb}\to R_{1p}$,
and RTD's $R_{2pa}$ has no counterpart. The binning rates map as
$R'_{1c}\to R'_{2c}$, $R'_{1pb}\to R'_{2p}$, $R'_{2pb}\to R'_{1p}$.

- **D1 (message splitting).** RTD splits the primary message three ways: $W_{2c}$, $W_{2pa}$
  (only in the primary's codeword) and $W_{2pb}$ (only in the cognitive transmitter's
  $U_{2pb}$). Lean splits it two ways. The frozen region recovers RTD's cases with
  $R_{2pa}=0$ ($X_1$ a function of $U_0$) or $R_{2pb}=0$ ($U_{1p}$ constant), but not
  both rates positive at once.
- **D2 (codebook structure).** RTD superposes $U_{2pb}$ on $(U_{2c},X_2,U_{1c})$, i.e. Lean's
  $U_{1p}$ on $(U_0,X_1,U_{2c})$. The Lean constraints instead correspond to $U_{1p}$
  superposed on $(U_0,X_1)$ only and *binned* against $U_{2c}$. Hence Lean has:
  - covering constraint (3), which has no RTD counterpart;
  - the extra term $I(U_{1p};U_{2c}|U_0X_1)$ in (5), compared with RTD (11c);
  - the receiver-1 bonus $\pi=I(X_1U_{1p};U_{2c}|U_0)$ in place of RTD's
    $I(U_{1c};X_2|U_{2c})$, i.e. Lean's $I(U_{2c};X_1|U_0)$.
- **D3.** RTD (11a) is an equality, $R'_{1c}=I(U_{1c};X_2|U_{2c})$. Lean (1) is an
  inequality. This is harmless.
- **D4 (receiver 1).** RTD has five constraints at the primary receiver, (11d)–(11h). Lean
  has three, (6)–(8), because $X_1$ and $U_{1p}$ are always wrong together.
- **D5 (receiver 2).** Lean (9)–(11) equal RTD (11k), (11j), (11i) exactly.
- **D6.** RTD Remark V.2 drops the constraints for events in which no intended message is
  in error. The frozen region never drops a constraint; for example, (7) is imposed even
  when $R_{1p}=R'_{1p}=0$. In the BCD regime this is harmless (Claim 7a).
- **D7.** The problem file listed four covering constraints. The Lean file has five; the
  file omitted (3). This is fixed in the problem file.

**Proposed correction** (not a catalog error; a fidelity issue).
- (A, recommended, applied to the Markdown): describe `rtdInnerBound` as "an RTD-type
  inner bound modelled on RTD 2011 Thm 7". Keep the frozen Lean statement. It is a sound
  (Claim 6), well-posed open question that already implies `broadcast-channel`.
- (B, optional statement-fix PR): replace the region by a literal transcription of RTD
  (11a)–(11k), after the renaming above, with eight rates
  $(R_{1c},R_{1a},R_{1p},R_{2c},R_{2p})$ and three binning rates. The Remark V.2 droppings
  can be encoded by a disjunction over which rates vanish, or by non-unique-decoding
  minima. Option B would make the docstring literally true. Its Statement is a different
  open question, with the same implication to `broadcast-channel` (Claim 4).

## Verification

`code/lean_region_checks.py` uses a fixed seed (20261126) and needs numpy and scipy. It
runs in about 30 s and reports ALL PASS:
- **T1** checks Claim 2 ⊆: across 60 random $|\mathcal X_1|=1$ instances × 21 directions,
  the frozen-region support minus the Marton($W=(U_0,U_{2c},Q)$) support is at most
  $9\times10^{-16}$.
- **T2** checks Claim 2 ⊇: on 34 instances with $K\le I_1+I_2$, the embedded support
  equals Marton's to within $4\times10^{-16}$.
- **T3** checks Claim 7b on the clipper.
- **T4** checks $Y_1=Y_2$ (very strong interference with equality): the region equals the
  capacity polytope to within $4\times10^{-16}$.
- **T5** checks Claim 7a on 40 distributions, with $Y_1$ degraded from $Y_2$ or
  $Y_1=Y_2$. There were no failures, and the direct branch of Config A was exercised 20
  times.
- **T6** checks Claim 5 on 60 random full instances: maximum excess $2\times10^{-16}$.

The LP transcribes the Lean constraint list projection by projection. So these tests also
check the index decoding in the Notation section. They are evidence for the algebra, not
proofs. The proofs are in Details.

## Dead ends

- **Hoped-for catalog error via GEA 2014.** The coordinator's hypothesis was that at
  $|\mathcal X_1|=1$ the formal region might reduce to Marton *without* superposition. It
  does not. Through $U_0$ (primary common) and $U_{2c}$ (cognitive common, GP-binned) the
  region has a common layer that both receivers decode. With $U_0$ constant, $U_{2c}$
  carries both common sub-messages: because of the "virtual cloud" indexing in (8) and
  (11), $R_{1c}>0$ is allowed with constant $U_0$. That alone recovers Marton with $W$.
- **Hoped-for catalog error via D6.** Constraint (7) blocks the obvious BCD scheme when
  $I(U;Y_2|X_1)>I(U;Y_1|X_1)$. However, the blocked corner is then dominated by the
  treat-as-noise point $A_0$ (Claim 7a). So D6 yields no counterexample on any class with
  known capacity. A counterexample to "formal ⊇ RTD Thm 7" would need an outer bound on a
  union over unbounded auxiliaries. I did not find a tractable one.

## References

- S. Rini, D. Tuninetti, N. Devroye, "New inner and outer bounds for the memoryless
  cognitive interference channel and some new capacity results," IEEE Trans. IT 57(7):
  4087–4109, 2011. The inner bound is Thm 7, (11a)–(11k), checked in the IEEE PDF. I used
  arXiv:1003.4328v1 for the full text: Thm V.1 and Remark V.2; outer bound Thm III.1;
  very weak and very strong interference Thms III.5 and III.6; BCD Thm VII.1 and
  Remark VII.2; semi-deterministic Thm VIII.1; clipper §X-A.
- W. Wu, S. Vishwanath, A. Arapostathis, IEEE Trans. IT 53(11), 2007; arXiv cs/0605071
  (Theorem 3.4, "type C" channels). RTD restate the result with the two "very weak
  interference" conditions (7). I did not reconcile the two versions beyond noting that
  both conditions imply BCD.
- A. Gohari, A. El Gamal, V. Anantharam, "On Marton's inner bound for the general
  broadcast channel," IEEE Trans. IT 60(7):3748–3762, 2014; arXiv:1006.5166 (abstract and
  §II-A Claim 1).
- A. El Gamal, Y.-H. Kim, *Network Information Theory*, 2011, Thm 8.4 (Marton with common
  message) and Ch. 8 (mutual covering).
- Catalog: `problems/broadcast-channel.md`, `problems/marton-inner-bound-tightness.md`,
  Core definitions `bcCapacityRegion` and `martonInnerBound`
  (`lean/InfoTheory/Core/Channels.lean`).
- Prior attempts on this problem: none.

**Novelty check.** The statement "at $X_1$ degenerate the cognitive IC is a BC, so the
problem is at least as hard as the BC" is folklore, and the problem file states it
informally. What this file adds:
- the exact identity between the *frozen* region and the *Core* `martonInnerBound`, giving
  a formal reduction between catalog Statements;
- the D1–D7 audit;
- the class containments for the frozen region specifically.

I searched for audits of RTD Thm 7 transcriptions and found none. The claim that RTD's
own region contains all known regions is RTD's §VI, not mine.
