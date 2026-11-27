---
problem: relay-channel
date: 2026-11-26
attempter: claude
model: claude-opus-5-5
type: partial-result
status: verified
---

## Summary

**The frozen Lean `Statement` (`relayCapacity W = coverElGamalTheorem7Rate W` for every
finite DM relay channel) is false. This is a catalog error.** The cause is that
`coverElGamalTheorem7Rate` is not Cover–El Gamal Theorem 7. It keeps only two of
Theorem 7's three rate constraints, and it allows an arbitrary joint law
$P(u,x,x_r)$. As a result it credits compress-forward with *coherent* (correlated)
source and relay inputs. That is impossible when the relay's input carries compression
indices that the source does not know.

The counterexample is a channel $W_\star$ with $|\mathcal X|=4$, $|\mathcal X_r|=2$,
$|\mathcal Y|=6$, $|\mathcal Y_r|=2$. The relay observes only the destination's noise
$Z$. The destination sees $X_1\oplus Z$ and the binary adder $X_2+X_r$. On this channel:
- $C(W_\star)=3/2$ exactly, by a short Fano argument plus an explicit scheme;
- the Lean functional equals $\log_2 3\approx1.585$;
- the faithful Theorem 7 (Chong–Motani 2011, Lemma 2 form) also gives $3/2$.

The Lean functional is always at least Theorem 7 and at most the cutset bound, so it is
correct on every classical capacity class. That is why the defect is invisible there.
A corrected statement is proposed below.

Survey: I found no standard DM relay channel on which any scheme is *proved* to beat
Theorem 7. Two follow-ups from the coordinator are resolved:
- **Ponniah (arXiv:2609.15709, 2026, unrefereed).** It claims $C=\max\{R_{\rm DF},R_{\rm U\text{-}CF},R_{\rm C\text{-}CF}\}$. This is refuted. Embed the primitive-BSC time-sharing example as a DM relay channel with an orthogonal BSC link of capacity $0.3$. Then $C\ge0.5396$, while all three of Ponniah's rates are at most $0.5310$.
- **The same time-sharing example and the Lean functional.** It does *not* affect `coverElGamalTheorem7Rate`: there $U$ can carry a time-sharing coin, and the functional reaches $0.5396$.

## Approach

1. Transcribe the Lean functional term by term, and compare it with the three-constraint
   form of Theorem 7 that Chong–Motani (CM11, Lemma 2) and El Gamal–Gohari–Nair
   (orthogonal-receiver paper, Theorem 1) state. The comparison shows a missing
   constraint and a missing conditional-independence structure ($X\perp X_r\mid W$).
2. Find where these omissions matter. In a primitive (orthogonal-receiver) channel,
   correlating $X$ with $X_r$ is only coded time-sharing, so nothing breaks (see Dead
   ends). One needs a channel where the destination benefits from *coherent* $X,X_r$
   while the relay can only describe noise. Combining a binary adder (cooperation gain:
   $\log_2 3$ vs $1.5$) with a relay that sees the destination's noise gives that.
3. Prove an elementary converse for that channel. Evaluate the Lean functional exactly.
   As a sanity check, evaluate the faithful Theorem 7.
4. Survey the literature for schemes beating Theorem 7 and for converses beyond cutset.
5. Coordinator lead: check Ponniah's three-scheme formula against the primitive-BSC
   time-sharing example, and check the Lean functional against the same example.

## Claims

1. **[proved]** *(What the Lean functional is.)* Let $L(W)$ denote
   `coverElGamalTheorem7Rate W`. It is the supremum of
   $\min\{r_1,r_2\}$ with
   $r_1=I(U;Y_r|X_r)+I(X;Y,\hat Y|U,X_r)$ and
   $r_2=I(X,X_r;Y)-I(Y_r;\hat Y|U,X,X_r,Y)$. The supremum is over **arbitrary** joint
   $P(u,x,x_r)$ and test channels $Q(\hat y|u,x_r,y_r)$. For every DM relay channel,
   $$R_{\rm Thm7}(W)\ \le\ R_{\rm CM}(W)\ \le\ L(W)\ \le\ R_{\rm cutset}(W).$$
   Here $R_{\rm Thm7}$ is Cover–El Gamal Theorem 7 (CM11 Lemma 2) and $R_{\rm CM}$ is the
   Chong–Motani (CM11) Theorem 2 bound. $L$ contains DF ($U=X$, $\hat Y$ const), partial
   DF ($\hat Y$ const) and CF ($U$ const, $P=p(x)p(x_r)$). A time-sharing coin is absorbed
   by putting it into $U$.
2. **[proved]** *(Catalog error.)* For the channel $W_\star$ defined in Details §2,
   $\texttt{relayCapacity}\,W_\star\le 3/2<\log_2 3\le L(W_\star)$, and in fact
   $L(W_\star)=\log_2 3$ and $C(W_\star)=3/2$. Hence
   `InfoTheory.Problems.RelayChannel.Statement` is false, with $(k_X,k_{X_r},k_Y,k_{Y_r})=(4,2,6,2)$.
3. **[proved]** On $W_\star$, $R_{\rm Thm7}(W_\star)=3/2=C(W_\star)$. The excess of $L$ comes
   from the transcription, not from the channel.
4. **[proved]** On every classical capacity class, Theorem 7 (and hence $L$, by Claim 1)
   equals capacity. The classes are: degraded, reversely degraded, semideterministic,
   orthogonal-sender-components (El Gamal–Zahedi), and the Cover–Kim deterministic class
   $Y_r=f(X,Y_1)$ with orthogonal receiver components. The hash-forward rate equals CF
   with $\hat Y=Y_r$, so it is contained in Theorem 7.
5. **[heuristic]** *(Survey.)* No standard DM relay channel $p(y,y_r|x,x_r)$ is known on
   which some coding scheme is *proved* to beat Theorem 7. Details §5 lists the near
   misses. The status of the problem (open) is unchanged once the statement is repaired.
6. **[proved]** *(Ponniah's Theorem 4 is false.)* Take the DM relay channel with
   orthogonal receiver components: $Y_1=X\oplus{\rm Bern}(0.2)$,
   $Y_r=X\oplus{\rm Bern}(0.1)$, $Y_2=X_r\oplus{\rm Bern}(q)$ with $1-h(q)=0.3$
   ($q\approx0.189298$), and $Y=(Y_1,Y_2)$. Then $C\ge 0.539568$. But
   $R_{\rm DF}\le0.531004$, $R_{\rm U\text{-}CF}\le0.518072$ and
   $R_{\rm C\text{-}CF}\le0.518072$, with each rate read as defined in arXiv:2609.15709,
   eqs. (80)–(98). The bound on $R_{\rm C\text{-}CF}$ uses only the feasibility
   inequality (93) and the form of the joint law (85). It does not use the
   "circuit-consistency" condition (88), so typesetting ambiguities in (82)/(88) do not
   matter. *(Reviewer qualification, 2026-11-27: this argument covers the reading in
   which each rate is evaluated under the same joint law as its own feasibility
   constraint, as the subscripts in (92), (93), (96), (97) indicate. The sentence after
   (97) of arXiv:2609.15709v2 pairs (96)/(97) with (85)/(86) the other way round; the
   argument above does not cover that pairing. Under it, with the natural normalisation
   of (82), Theorem 4 still fails on this channel, now from above. See the reviewer
   note in Verification.)*
7. **[proved]** On the channel of Claim 6, $L\ge 0.5396$ and $R_{\rm Thm7}\ge0.5396$. Both
   formulas carry time-sharing ($U\ni$ coin in $L$; an explicit $Q$ in Theorem 7). So the
   primitive-BSC time-sharing counterexample does **not** refute "$C=L$" or "$C=R_{\rm Thm7}$".

## Details

### 1. Audit of `coverElGamalTheorem7Rate`

The Lean joint law is
$J(u,x,x_r,y,y_r,\hat y)=P(u,x,x_r)\,W(y,y_r|x,x_r)\,Q(\hat y|u,x_r,y_r)$. The index maps
in the file give exactly
$r_1=I(U;Y_r|X_r)+I(X;Y,\hat Y|U,X_r)$ and $r_2=I(X,X_r;Y)-I(Y_r;\hat Y|U,X,X_r,Y)$.
I checked every `J.map` tuple against Lean's `condMutualInfo (α×β×γ) = I(α;β|γ)`.

**The faithful Theorem 7.** CM11 Lemma 2, restated as Theorem 1 of El Gamal–Gohari–Nair
("Achievable rates for the relay channel with orthogonal receiver components"), achieves
every $R$ with
$$\begin{aligned}
R&\le I(X,X_r;Y|Q)-I(Y_r;V|U,X,X_r,Y,Q),\\
R&\le I(X;V,Y|U,X_r,Q)+I(U;Y_r|W,X_r,Q),\\
R&\le I(X;V,Y|U,X_r,Q)+I(U;Y_r|W,X_r,Q)+I(X_r;Y|W,Q)-I(Y_r;V|U,X_r,Y,Q),
\end{aligned}$$
for some joint law
$p(q)p(w|q)p(u|w,q)p(x|u,q)p(x_r|w,q)\,p(y,y_r|x,x_r)\,p(v|u,x_r,y_r,q)$.

The structural point is that $X$ and $X_r$ are conditionally independent given the
cooperative part $(W,Q)$. The relay's extra freedom, the compression index, is invisible
to the source. CM11 Theorem 2 differs only in the third line, where $I(X_r;Y|U,W,Q)$
replaces $I(X_r;Y|W,Q)$. EGN (Remark 1) rewrite it without $Q$ as
$$R\le I(X,X_r;Y)-I(Y_r;V|U,X,X_r,Y,W),\quad
R\le I(X;V,Y|U,X_r,W)+I(U;Y_r|W,X_r),$$
$$R\le I(X;Y|U,X_r,W)+I(U;Y_r|W,X_r)+I(X_r;Y|U,W)-I(Y_r;V|U,X_r,X,Y,W),$$
over $p(u,w)p(x|u,w)p(x_r|w)p(y,y_r|x,x_r)p(v|u,w,x_r,y_r)$.

*Proof of $R_{\rm CM}\le L$.* Given a CM distribution, put $U_L:=(U,W)$ and feed the
Lean functional the joint law of $(U_L,X,X_r)$ together with $V$ as $\hat Y$. The test
channel $p(v|u,w,x_r,y_r)$ is admissible. Lean's $r_2$ equals CM's first constraint, and
$r_1=I(W;Y_r|X_r)+I(U;Y_r|W,X_r)+I(X;V,Y|U,W,X_r)$ is at least CM's second constraint.
CM's third constraint is simply dropped. $R_{\rm Thm7}\le R_{\rm CM}$ is CM11 Remark 6:
$I(X_r;Y|U,W,Q)=I(X_r;Y,U|W,Q)\ge I(X_r;Y|W,Q)$. Both steps hold for each fixed law, so
they survive the suprema.

*Proof of $L\le R_{\rm cutset}$ (same $P(x,x_r)$).* First, $r_2\le I(X,X_r;Y)$. Second,
since $\hat Y$ is generated from $(U,X_r,Y_r)$,
$I(X;Y,\hat Y|U,X_r)\le I(X;Y,Y_r|U,X_r)$. Hence
$r_1\le I(U;Y,Y_r|X_r)+I(X;Y,Y_r|U,X_r)=I(X,U;Y,Y_r|X_r)=I(X;Y,Y_r|X_r)$, using
$U-(X,X_r)-(Y,Y_r)$.

Time-sharing in $L$: let $U'=(T,U)$ with $T$ a coin. Then $I(T,U;Y_r|X_r)\ge I(U;Y_r|X_r,T)$
and $I(X,X_r;Y)\ge I(X,X_r;Y|T)$, while the subtracted term is unchanged. So $L$ dominates
coded time-sharing of its own points, i.e. a min of averages.

### 2. The counterexample channel $W_\star$

$X=(X_1,X_2)\in\{0,1\}^2$, $X_r\in\{0,1\}$, $Z\sim{\rm Bern}(1/2)$ independent of all
inputs, $Y_r=Z$, $Y=(Y_1,Y_2)$ with $Y_1=X_1\oplus Z$ and $Y_2=X_2+X_r\in\{0,1,2\}$
(integer sum).

**Converse ($C\le 3/2$).** Take any code in the sense of `IsRelayAchievable`: a
deterministic encoder $m\mapsto x^n(m)$, strictly causal relay maps
$x_{r,i}=\phi_i(y_r^{i-1})$, and a decoder. Since $Y_r^n=Z^n$ regardless of the inputs,
$X_r^n=\phi(Z^n)$ is a function of $Z^n$. $Z^n$ is independent of $M$, hence of
$X^n=x^n(M)$. Given $M=m$, the map $Z^n\mapsto(Y_1^n,Y_2^n)$ is injective ($Z^n=Y_1^n\oplus x_1^n(m)$),
so $H(Y^n|M)=H(Z^n)=n$. Also
$$H(Y^n)\le H(Y_1^n)+\sum_i H(X_{2,i}+X_{r,i})\le n+n\cdot\tfrac32 .$$
Here $X_{2,i}$ (a function of $M$) and $X_{r,i}$ (a function of $Z^{i-1}$) are independent
binary variables. $\max H(B_1+B_2)$ over independent Bernoulli pairs is $3/2$: this is the
sum capacity of the binary erasure MAC (Cover–Thomas, Elements of Information Theory,
binary erasure multiple-access channel example), and a $2001^2$ grid check is in the code.
Therefore $I(M;Y^n)\le \tfrac32 n$. Fano with average error $\varepsilon$ and
$\log M\ge nR-1$ gives $(1-\varepsilon)(nR-1)-1\le\tfrac32 n$. So no $R>3/2$ satisfies
`IsRelayAchievable`. The achievable set contains $0$ and is bounded by $3/2$, so
`relayCapacity` $W_\star=\sup\le 3/2$.

**Achievability ($C\ge3/2$, not needed for the disproof).** Use block-Markov coding. In
block $b$ the source sends $n$ fresh uncoded bits on $X_1$ and a $0.5n$-bit message on
$X_2$. The relay sends $Z^n$ of block $b-1$ ($n$ bits) on $X_r$. The pair (relay rate 1,
source rate 0.5) is a corner of the binary-adder MAC region
$\{R_r\le1,R_2\le1,R_r+R_2\le1.5\}$. So the destination jointly decodes both messages from
$Y_2$ in block $b$, recovers $Z^n$ of block $b-1$, and reads $X_1^n=Y_1^n\oplus Z^n$. The
rate is $3/2-O(1/B)$.

**Lean functional ($L(W_\star)=\log_2 3$).** Take $U$ constant,
$X_1\sim{\rm Bern}(1/2)$ independent of $(X_2,X_r)$, and
$P(X_2,X_r)=\begin{pmatrix}1/3&1/6\\1/6&1/3\end{pmatrix}$, so that $X_2+X_r$ is uniform on
$\{0,1,2\}$. Take $\hat Y=Y_r$. Then:
- $r_1=I(X;Y_1,Y_2,Z|X_r)=H(X_1)+H(X_2|X_r)=1+h(1/3)=1.9183$;
- $r_2=I(X,X_r;Y)-H(Z|X,X_r,Y)=[1+\log_2 3]-1-0=\log_2 3$. ($Y_1$ is uniform and
  independent of $(X,X_r)$, and $Z=Y_1\oplus X_1$.)

Thus $L\ge\log_2 3$. Conversely, $L\le$ cutset $\le\max I(X,X_r;Y)=\max H(Y)-1\le\log_2 3$.
The set inside the `sSup` is bounded above (by $\log_2 6$), so `sSup` $\ge\log_2 3$ is
legitimate in Lean's $\mathbb R$.

**What goes wrong.** The pair $(X_2,X_r)$ is correlated while the relay's input is
supposed to describe $Z$ (compression index $\hat Y=Y_r$). No code can do this: Details §2
shows $X^n\perp X_r^n$ for every code on $W_\star$. Theorem 7 forbids it through
$X\perp X_r\mid(W,Q)$ together with the third constraint (see Claim 3).

### 3. Theorem 7 on $W_\star$

Upper bound: $R_{\rm Thm7}\le C=3/2$. Lower bound: take $Q,W,U$ constant, $V=Y_r$, and
$X_1,X_2,X_r$ i.i.d. uniform. The three constraints evaluate to $1.5$, $2$ and
$2+I(X_r;Y)-H(Z|X_r,Y)=2+0.5-1=1.5$. A random search over $|W|=2,|U|=3,|V|=2$
(3000 draws) never exceeds $1.5$, which checks the implementation.
(Reviewer: this point is feasible for the three-constraint CM11 Lemma 2 form only. In CEG79's
original form (83a–c) it violates (83c): $H(Z|Y,X_r)=1\le I(X_r;Y)=0.5$ fails. The original
form still reaches $3/2$ with $\hat Y=Y_r\oplus{\rm Bern}(\delta)$, $h(\delta)=1/2$; see
the reviewer note.)

### 4. Classical capacity classes

Each class's capacity equals the cutset bound and is attained inside Theorem 7:
- degraded: DF with $U=X$ (CEG79 Thm 1);
- reversely degraded: direct transmission, with $Q$ fixing $x_r$ (CEG79 Thm 2);
- semideterministic $Y_r=f(X,X_r)$: partial DF with $U=Y_r$ (El Gamal–Aref 1982);
- orthogonal sender components: partial DF (El Gamal–Zahedi 2005);
- Cover–Kim class, with orthogonal receiver components and $Y_r=f(X,Y_1)$
  (Kim, IEEE TIT 54(3), 2008): CF with $V=Y_r$.

For the Cover–Kim class, with $X_r$ uniform on a link of capacity $C_0$, the three
constraints become $I(X;Y_1)+C_0-H(Y_r|X,Y_1)$, $I(X;Y_1,Y_r)$, and again
$I(X;Y_1)+C_0-H(Y_r|X,Y_1)$. With $H(Y_r|X,Y_1)=0$ this is
$\min\{I(X;Y_1)+C_0,\,I(X;Y_1,Y_r)\}$, the cutset value. For general primitive channels
this computation shows that the hash-forward rate
$\max\min\{I(X;Y_1)+C_0-H(Y_r|X,Y_1),I(X;Y_1,Y_r)\}$ (Kim, Allerton 2007) is contained in
Theorem 7. By Claim 1, on all these classes
$R_{\rm Thm7}=L=R_{\rm cutset}=C$.

### 5. Survey: can anything beat Theorem 7? Converses beyond cutset

*Achievability side:*
- **Chong–Motani (CM07; CM11, Remark 6).** They give a bound $\ge$ Theorem 7 and
  conjectured, from Gaussian numerics, that it can be strictly larger. El Gamal–Gohari–Nair
  ("Achievable rates for the relay channel with orthogonal receiver components", manuscript
  at chandra.ie.cuhk.edu.hk/pub/papers/NIT/Prim-Rel-LB.pdf, Theorem 3) prove the two
  coincide for orthogonal receiver components and give a simplified expression. The same
  paper (Lemma 1) shows the Mondelli–Hassani–Urbanke scheme (Algorithms 12(10):218, 2019)
  is subsumed by Theorem 7, which refutes MHU's conjecture. It also disproves the
  Ahlswede–Han conjecture: time-sharing strictly improves pure CF for the i.i.d.-output
  subclass. That separates CF from CF with time-sharing, not Theorem 7 from capacity.
  Strictness of CM11 over Theorem 7 for general channels remains open as far as I found.
- **Noisy network coding** (Lim–Kim–El Gamal–Chung 2011) reduces to CF for one relay.
- **Wu (arXiv:1504.04515, 2015–16).** The schemes beat Theorem 7 only (i) with
  relay-to-source feedback, or (ii) on an "enhanced Gaussian relay channel" in which the
  source observes the relay's signal, with Gaussian-input evaluations (their Corollary 2,
  Table I). Neither is the standard DM relay channel.
- **Ponniah (arXiv:2609.15709, Sept 2026, unrefereed).** Claims
  $C=\max\{R_{\rm DF},R_{\rm U\text{-}CF},R_{\rm C\text{-}CF}\}$ with no time-sharing. The
  proof's step "WU-3" dismisses time-sharing because "all the mutual-information terms are
  concave functions of the input distributions". Refuted in §6.

*Converse side (all beyond cutset; none matches Theorem 7 in general):*
- Zhang (IEEE TIT 1988);
- Aleksic–Razaghi–Yu (IEEE TIT 55(3):921–930, 2009, modulo-sum class);
- Tandon–Ulukus (Allerton 2008);
- Wu–Özgür–Xie (IEEE TIT 63(4):2254–2277, 2017);
- Wu–Barnes–Özgür (IEEE TIT 65(1):255–275, 2019, Cover's problem, Gaussian case);
- Liu–Özgür (ISIT 2019; IEEE TIT 66(9):5448–5455, 2020, reverse hypercontractivity);
- Liu ("Minoration via mixed volumes and Cover's problem for general channels",
  arXiv:2012.14521; Probab. Theory Relat. Fields 2022);
- El Gamal–Gohari–Nair (strengthened cutset, arXiv:2101.11139, IEEE TIT 2022).

The repository's certified symmetric-BSC interval comes from the last of these (see the
problem file).

### 6. Ponniah's formula on the primitive-BSC example (Claims 6–7)

**The channel.** $X\to(Y_1,Y_r)$ through independent BSC(0.2) and BSC(0.1). $X_r\to Y_2$
through BSC($q$) with $1-h(q)=0.3$. Destination output $Y=(Y_1,Y_2)$. This is a finite DM
relay channel.

**Lower bound $C\ge0.539568$.** Theorem 7 with a binary $Q$, $W$ constant, $X,X_r$ uniform
and independent:
- phase $Q=0$ (DF): $U=X$, $V$ constant;
- phase $Q=1$ (CF): $U$ constant, $V=Y_r$.

With $\lambda_1=P(Q=1)$:
- line 2 $=(1-\lambda_1)(1-h(0.1))+\lambda_1 I(X;Y_1,Y_r)$;
- line 1 $=1-h(0.2)+0.3-\lambda_1 h(0.1)$;
- line 3 $=$ line 2 $+0.3-\lambda_1 h(0.26)$, which is slack.

Equating lines 1 and 2 gives $\lambda_1\approx0.082$ and rate $0.5396$. This equals the
primitive-BSC agent's time-sharing value; see
`attempts/primitive-relay-channel-bsc/2026-11-26-claude-opus-5-5-time-sharing-and-first-order.md`,
Claim 3. Operationally it is block-Markov coding in which the relay pools its link budget
across the two phases.

**Ponniah's three rates.** The facts used are:
- $Y_2$ is independent of $(X,Y_1,Y_r,\hat Y_r)$ given $X_r$;
- $Y_1$ is a degraded version of $Y_r$;
- the primitive-BSC agent's SDPI lemma (their Claim 2): for any input law and any
  $\hat Y-(Y_r,\cdot)-(X,Y_1)$, $I(\hat Y;X|Y_1)\le(1-2\cdot0.1)\,I(\hat Y;Y_r|Y_1)$. It
  holds conditionally on $X_r=x_r$, because the Dobrushin bound holds for every input law.

The three bounds:
- $R_{\rm DF}=\max_{p(x,x_r)}\min\{I(X;Y_r|X_r),I(X,X_r;Y)\}\le\max I(X;Y_r)=1-h(0.1)=0.531004$.
- U-CF (independent inputs; constraint (92)
  $I(\hat Y;Y_r|X_r)<I(X_r;Y)=I(X_r;Y_2)\le0.3$). The rate is
  $I(X;\hat Y,Y_1|X_r)=\sum_{x_r}p(x_r)[I(X;Y_1)+a(x_r)]$ with
  $a(x_r)\le0.8\,b(x_r)$ and $b(x_r)=I(\hat Y;Y_r|Y_1,x_r)\le I(\hat Y;Y_r|x_r)$. Hence the
  rate is at most $1-h(0.2)+0.8\cdot0.3=0.518072$.
- C-CF (correlated $p(x,x_r)$; joint law (85) of the form
  $p(x,x_r)W\,T(\hat y|y_r,x_r)$; constraint (93) $I(\hat Y;Y_r|X_r)<I(\hat Y,X_r;Y)$).
  Split $I(\hat Y;Y_r|X_r)=I(\hat Y;Y_1|X_r)+\sum p(x_r)b(x_r)$ and
  $I(\hat Y,X_r;Y)=I(X_r;Y_2)+I(X_r;Y_1|Y_2)+I(\hat Y;Y_1|X_r)$. Constraint (93) then
  becomes $\sum p\,b<I(X_r;Y_2)+I(X_r;Y_1|Y_2)\le0.3+I(X_r;Y_1)$. So
  $${\rm rate}=I(X;Y_1|X_r)+\textstyle\sum p\,a\le I(X;Y_1|X_r)+0.8\,(0.3+I(X_r;Y_1))\le I(X,X_r;Y_1)+0.24\le0.518072 ,$$
  using $I(X,X_r;Y_1)=I(X;Y_1)\le1-h(0.2)$.

So $\max\{\cdot\}\le0.531004<0.539568\le C$. Any reading of (88) only shrinks
$R_{\rm C\text{-}CF}$, and the restriction $|\hat{\mathcal Y}_r|=|\mathcal X_r|$ in (80)
shrinks both CF rates. Caveat: as typeset, the labels "Pcor-feasible"/"Pind-feasible" in
(94)–(95) look swapped relative to (87)–(88), and (82) is ambiguous. The argument above
needs neither. Twenty thousand random correlated draws on this channel stay below
$0.518072$ (code, part (D)), which checks the algebra.

**The Lean functional on the same channel (Claim 7).** Take $U=({\rm coin},X\text{ in the DF phase})$
with alphabet size 3, $X,X_r$ uniform and independent, and $\hat Y=Y_r$ in the CF phase,
constant otherwise. Then $L\ge0.539600$ at $P(\text{CF})=0.082$. As the coordinator
expected, the pooled $r_1$ and $r_2$ dominate time-sharing. On this channel
$L\le R_{\rm cutset}=\min\{I(X;Y_1,Y_r),I(X;Y_1)+0.3\}=0.578072$. Whether $C=L$ there is
exactly as open as before.

### 7. Proposed corrected statement (do not merge without a statement-fix PR)

Replace `coverElGamalTheorem7Rate` by the faithful three-constraint form. Sketch (not
typechecked; the `sum_one` proof is as in the current file, with two more kernels):

```lean
/-- Cover–El Gamal (1979) Theorem 7 in the form of Chong–Motani (2011, Lemma 2) =
    El Gamal–Gohari–Nair (orthogonal-receiver paper), Theorem 1.  Joint law
    p(q) p(w|q) p(u|w,q) p(x|u,q) p(xr|w,q) W(y,yr|x,xr) p(v|u,xr,yr,q). -/
noncomputable def coverElGamalTheorem7Rate (W : RelayChannel X Xr Y Yr) : ℝ :=
  sSup { r : ℝ | ∃ (kQ kW kU kV : ℕ) (pQ : ProbDist (Fin kQ))
      (pW : DMC (Fin kQ) (Fin kW)) (pU : DMC (Fin kW × Fin kQ) (Fin kU))
      (pX : DMC (Fin kU × Fin kQ) X) (pXr : DMC (Fin kW × Fin kQ) Xr)
      (pV : DMC (Fin kU × Xr × Yr × Fin kQ) (Fin kV)),
    -- t = (q, w, u, x, xr, y, yr, v)
    let J : ProbDist (Fin kQ × Fin kW × Fin kU × X × Xr × Y × Yr × Fin kV) :=
      { pmf := fun ⟨q, w, u, x, xr, y, yr, v⟩ =>
          pQ.pmf q * pW.trans q w * pU.trans (w, q) u * pX.trans (u, q) x *
          pXr.trans (w, q) xr * W.trans (x, xr) (y, yr) * pV.trans (u, xr, yr, q) v
        nonneg := _, sum_one := _ }
    let c1 := condMutualInfo (J.map fun t => ((x,xr), y, q))            -- I(X,Xr;Y|Q)
            - condMutualInfo (J.map fun t => (yr, v, (u,x,xr,y,q)))     -- I(Yr;V|U,X,Xr,Y,Q)
    let c2 := condMutualInfo (J.map fun t => (x, (v,y), (u,xr,q)))      -- I(X;V,Y|U,Xr,Q)
            + condMutualInfo (J.map fun t => (u, yr, (w,xr,q)))         -- I(U;Yr|W,Xr,Q)
    let c3 := c2 + condMutualInfo (J.map fun t => (xr, y, (w,q)))       -- I(Xr;Y|W,Q)
                 - condMutualInfo (J.map fun t => (yr, v, (u,xr,y,q)))  -- I(Yr;V|U,Xr,Y,Q)
    r = min c1 (min c2 c3) }
```

The docstring of `Statement` should then say "Does Cover–El Gamal Theorem 7 achieve the
capacity of every finite DM relay channel?". Three remarks:
- If CM11's conjecture (Theorem 2 strictly larger) were proved for some channel, this
  statement would become trivially false. An alternative is to freeze CM11 Theorem 2 in
  EGN's form (7) instead, i.e. the best known single-letter pDF+CF bound.
- Neither version is known to be false.
- A certificate module could prove $R_{\rm Thm7}\le R_{\rm cutset}$ and
  $R_{\rm Thm7}=R_{\rm cutset}$ on a degraded instance.

## Verification

- `attempts/relay-channel/code/lean_thm7_counterexample.py` (numpy, ~5 s):
  - (A) builds $W_\star$ and evaluates the Lean $r_1,r_2$ exactly as the `J.map` tuples
    prescribe: $r_1=1.918295834054=1+h(1/3)$, $r_2=1.584962500721=\log_2 3$;
  - (B) the maximum of $H({\rm Bern}(p)+{\rm Bern}(q))$ on a $2001^2$ grid is $1.5$;
  - (C) faithful Theorem 7 gives exactly $1.5$ at the explicit point, and at most $1.5$
    over 3000 random draws;
  - (D) the Claim 6/7 numbers: $L\ge0.539600$, and Ponniah-type feasible C-CF rates stay
    below $0.518072$ on 20000 random draws.
- The converse in Details §2 was checked line by line against the Lean definitions of
  `IsRelayAchievable` (deterministic encoder, strictly causal relay
  `relay i : (Fin i → Yr) → Xr`, average error over uniform messages, $M=\max(1,\lfloor2^{nR}\rfloor)$)
  and `relayCapacity` (`sSup` of a nonempty set bounded by $3/2$).
- Not done: no Lean proof of `disproof : ¬ Statement` (editing `lean/` was out of scope).
  A formal disproof needs Fano in the relay setting, which `InfoTheory.Bridge` provides
  for point-to-point codes, plus the explicit evaluation in (A).

### Reviewer note (claude-opus-5-5, independent review, 2026-11-27)

**Verdict: the headline holds. `InfoTheory.Problems.RelayChannel.Statement` is false as
written.** Status changed to `verified`: I independently checked every `[proved]` claim
(1–4, 6, 7); the scope of each check is below. My scripts are in `code/review/`
(`review_check.py`, `ccf_opt.py`, with the logs `review_check_out.txt` and `author_run.txt`).

- **Primary source.** I read CEG79 Theorem 7 from the scan
  (isl.stanford.edu/groups/elgamal/abbas_publications/J003.pdf, p. 582, (83a–c)). In Lean
  names ($X_1\to X$, $X_2\to X_r$, $Y_1\to Y_r$, $\hat Y_1\to\hat Y$) it reads
  $R^*=\sup\min\{I(X;Y,\hat Y|X_r,U)+I(U;Y_r|X_r,V),\ I(X,X_r;Y)-I(\hat Y;Y_r|X_r,X,U,Y)\}$
  over $p(v)p(u|v)p(x|u)p(x_r|v)\,p(y,y_r|x,x_r)\,p(\hat y|x_r,y_r,u)$, subject to
  (83c) $I(\hat Y;Y_r|Y,X_r,U)\le I(X_r;Y|V)$. I re-read every `J.map` tuple and confirm
  the Lean $r_1,r_2$ of Claim 1. Relative to the primary source, Lean (i) drops $V$, (ii)
  replaces (83b) by an arbitrary $P(u,x,x_r)$, and (iii) drops (83c). Omission (iii) alone is
  fatal. Keep (83b) with $V=U$ a uniform bit, $X_r=V$, $X_2|V\sim$ Bern(1/3)/Bern(2/3), $X_1$
  uniform and $\hat Y=Y_r$: the two terms of (83a) give $\log_2 3$ on $W_\star$, while (83c)
  reads $1\le0$. EGN's manuscript (eqs. (1)–(3), (7), Remark 1) matches the transcription in
  Details §1.
- **Direction.** The Statement is an equality for every finite channel, so one channel with
  capacity $\ne$ functional refutes it.
- **Lean value, by hand and exactly.** At the Details §2 point, $r_1=H(X|X_r)=1+h(1/3)$, since
  $(Y,Z,X_r)$ determines $X$. Also $r_2=(1+\log_2 3)-1-0$: $Y_1$ is uniform and independent of
  $(X,X_r)$, $X_2+X_r$ is uniform on $\{0,1,2\}$, and $Z=Y_1\oplus X_1$. A sympy evaluation in
  rationals gives $r_2-\log_2 3=0$. The `sSup` set is bounded above by $\log_2 6$
  ($r_2\le H(Y)$), so the functional is $\ge\log_2 3$; it is also $\le\log_2 3$, because
  $H(Y|X,X_r)=1$ for every input.
- **Converse.** I re-derived it against `IsRelayAchievable` and `relayCapacity`
  (Core/Channels.lean, l. 291–311):
  - $X_r^n=\phi(Z^n)$ is independent of $M$, and $H(Y^n|M)=n$ because the map from $Z^n$ is
    injective;
  - $H(Y^n)\le n+\sum_i H(X_{2,i}+X_{r,i})$, with independent binary summands;
  - Fano with $M=\max(1,\lfloor2^{nR}\rfloor)$ excludes every $R>3/2$, and $R=0$ makes the
    set nonempty.

  For the constant 3/2 I give my own reduction. Put $p=\tfrac12+\alpha$, $q=\tfrac12+\beta$,
  $t=2\alpha\beta$. Then $H(S)=h(\tfrac12-t)+(\tfrac12+t)\,h(\tfrac12+\tfrac{\alpha+\beta}{1+2t})$.
  The case $t\le0$ is immediate. For $t>0$ the bound reduces to a 1-D function whose maximum
  on a $2\cdot10^6$ grid is $1.4999999981$, approached as $t\to0$. A multistart optimisation
  gives 1.5. Exact $I(M;Y^3)$ over 1200 random codes with strictly causal relays is
  $\le3.89<4.5$. Typing: $W_\star$ is a `DMC (Fin 4 × Fin 2) (Fin 6 × Fin 2)` with entries in
  $\{0,\tfrac12\}$ and rows summing to 1. Edge cases with empty alphabets give $0=0$.
- **Claim 3 caveat.** The Details §3 point ($V=Y_r$ exactly) is feasible for the CM11 form, but
  it **violates** the original (83c) ($1\le0.5$). The original form still reaches 3/2 with
  $\hat Y=Y_r\oplus{\rm Bern}(\delta)$, $h(\delta)=\tfrac12$: both terms are 1.5 and (83c)
  holds with equality. So Claim 3 stands in either form. I also checked the
  block-Markov scheme.
- **Code.** It runs in float64 and is sound for what it claims. (A) matches the closed forms;
  (B), (C) and (D) are sanity checks, not proofs. (D)'s random C-CF search reaches only about
  0.41, so it barely tests the 0.518 bound. My SLSQP run (`code/review/ccf_opt.py`; 180 starts, $|\hat Y|\le4$,
  correlated inputs, constraint (93) in the same law) peaks at 0.431412, below 0.518072.
- **Ponniah.** arXiv:2609.15709 exists: v1 is dated 14 Sep 2026, v2 20 Sep 2026; I read v2
  through pdftotext. Theorem 4 says, verbatim, "The capacity of the relay channel is
  max{RDF, RU-CF, RC-CF}." It covers the general DM relay channel and has no further
  hypotheses. Equations (80), (85), (92), (93), (98) and the WU-3 sentence are as quoted.
  - I re-derived the three bounds by hand. The Dobrushin coefficient of the reverse BSC(0.1)
    channel is $s(a^2-b^2)/(ab+s(a-b)^2)\le0.8$, with $s=\pi(1-\pi)$. The split of (93) uses
    $Y_2\perp(X,Y_1,Y_r,\hat Y)\mid X_r$.
  - Theorem 7 time-sharing gives $\lambda=0.082026$ and rate 0.539602. The quoted 0.539568 is
    the primitive-BSC agent's slightly weaker pipe-rate scheme; both are valid.
  - Theorem 7 yields average-error codes, while Ponniah's (79) uses maximal error. Standard
    expurgation closes this gap.
  - Reading caveat (added in Claim 6). The sentence after (97) evaluates (96)/(97) under
    (85)/(86), the opposite of the subscripts. Read literally, (82) is not normalised. With
    the natural $p_{\rm for}(y_r|\hat y_r,x_r)=p(y_r|x_r)$, the $(85)$-law makes
    $\hat Y\perp Y_r\mid X_r$. Under that pairing, $R_{\rm C\text{-}CF}$ is then
    unconstrained and reaches $I(X;Y_1,Y_r)=0.6358$, above the cutset bound
    $0.5781\ge C$. I found no reading under which Theorem 4 holds on this channel.
- **Corrected statement.** Either the §7 sketch (the CM11 Lemma 2 / EGN Theorem 1 form; I
  checked the indices but did not typecheck it) or a direct transcription of (83a–c) works.
  The direct one adds one kernel $p(v)$, the factorisation (83b) and the constraint (83c);
  $\hat Y$ = const is always feasible. Neither is known to be false. The
  Aleksic–Razaghi–Yu modulo-sum capacity (arXiv:0704.3591 abstract) is achieved by
  quantize-forward, which lies inside Theorem 7. The stated risk is CM11's conjecture.
- **Problem file.** Two minimal hedges: "We know of no…", and the reading condition on the
  Ponniah refutation.
- **Not checked:**
  - the El Gamal–Kim book text, including the "Sec. 16.7" attribution in the Lean docstring;
  - CM11 itself (I relied on EGN's restatement of Lemma 2);
  - the capacity proofs behind Claim 4 (I checked only that each capacity-achieving scheme is
    a special case of Theorem 7);
  - no Lean `disproof` was written.

## Dead ends

- **Primitive channels cannot expose the defect.** With orthogonal receiver components and
  a noiseless link, $I(X,X_r;Y_1,X_r)=H(X_r)+I(X;Y_1|X_r)$. A correlated $P(x,x_r)$ is then
  CF with coded time-sharing (with $X_r$ as $Q$), which is achievable. All earlier attempts
  in this folder work on primitive BSC/BEC channels, which is why none of them could have
  met this issue. The fix was a destination output that depends *jointly* on $(X,X_r)$
  (the adder).
- **A relay that observes nothing ($Y_r$ constant) is harmless.** Then $L=\max I(X;Y|X_r)$,
  which equals capacity (the relay sends a fixed sequence). The relay must observe
  something useful (here, the destination's noise) so that the dropped third constraint
  binds.
- **I did not try to settle CM11's conjecture** (Theorem 2 strictly larger than Theorem 7
  on some non-orthogonal channel). A natural test bed is a small non-orthogonal binary
  channel with a random search over $(W,U,V)$. Margins are expected to be tiny, and a
  certified separation would need interval arithmetic.

## References

- Prior attempts consulted: all seven files in `attempts/relay-channel/` (primitive
  BSC/BES baselines, EGN evaluations, referee audits). None audits
  `coverElGamalTheorem7Rate`. Also
  `attempts/primitive-relay-channel-bsc/2026-11-26-claude-opus-5-5-time-sharing-and-first-order.md`
  (another agent, same date): its Claims 1–3 and SDPI lemma are used in §6.
- T. M. Cover, A. El Gamal, "Capacity theorems for the relay channel," IEEE TIT 25(5):572–584, 1979.
- H.-F. Chong, M. Motani, H. K. Garg, "Generalized backward decoding strategies for the relay channel," IEEE TIT 53(1):394–401, 2007.
- H.-F. Chong, M. Motani, "On achievable rates for the general relay channel," IEEE TIT 57(3):1249–1266, 2011.
- A. El Gamal, A. Gohari, C. Nair, "Achievable rates for the relay channel with orthogonal receiver components," manuscript, http://chandra.ie.cuhk.edu.hk/pub/papers/NIT/Prim-Rel-LB.pdf (read: Theorems 1–3, Remark 1, Lemma 1, §4). I could not find an arXiv or venue record.
- A. El Gamal, A. Gohari, C. Nair, "Strengthened cutset upper bounds on the capacity of the relay channel and applications," arXiv:2101.11139; IEEE TIT 2022.
- A. El Gamal, Y.-H. Kim, *Network Information Theory*, Cambridge 2011, Ch. 16 (book text not accessed). The arXiv lecture notes 1001.3404v4, Lecture 17, state only that CF "can be combined with partial decode–forward [CEG79, Thm 7]". They give no formula, and their CF bound uses $p(x)p(x_r)$. I could not verify the "Sec. 16.7" attribution in the Lean docstring.
- Y.-H. Kim, "Coding techniques for primitive relay channels," Allerton 2007; "Capacity of a class of deterministic relay channels," IEEE TIT 54(3):1328–1329, 2008.
- A. El Gamal, M. Aref, "The capacity of the semideterministic relay channel," IEEE TIT 1982; A. El Gamal, S. Zahedi, "Capacity of a class of relay channels with orthogonal components," IEEE TIT 2005.
- M. Mondelli, S. H. Hassani, R. Urbanke, "A new coding paradigm for the primitive relay channel," Algorithms 12(10):218, 2019 (arXiv:1801.03153).
- Y. Wu, "Coding schemes for discrete memoryless multicast networks with rate-limited feedback," arXiv:1504.04515 (v3, 2016).
- J. Ponniah, "The capacity of the relay channel," arXiv:2609.15709 (Sept 2026).
- Z. Zhang, "Partial converse for a relay channel," IEEE TIT 1988; M. Aleksic, P. Razaghi, W. Yu, IEEE TIT 55(3):921–930, 2009; R. Tandon, S. Ulukus, Allerton 2008; X. Wu, A. Özgür, L.-L. Xie, IEEE TIT 63(4):2254–2277, 2017; X. Wu, L. P. Barnes, A. Özgür, IEEE TIT 65(1):255–275, 2019; J. Liu, A. Özgür, IEEE TIT 66(9):5448–5455, 2020; J. Liu, arXiv:2012.14521.
- T. M. Cover, J. A. Thomas, *Elements of Information Theory*, 2nd ed., binary erasure multiple-access channel example (sum capacity 1.5).
- Code: `attempts/relay-channel/code/lean_thm7_counterexample.py`.
