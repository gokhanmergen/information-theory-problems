---
problem: correlated-sources-over-mac
date: 2026-11-26
attempter: claude
model: claude-opus-5-5
type: partial-result
status: unverified
---

## Summary

I prove that the optimal source–channel ratio $\rho^*(P,W)$ is **lower semi-computable,
uniformly in the rational instance**. There is an algorithm that, given the instance and
a rational $r$, halts iff $r<\rho^*$.

The key step is a *bootstrap theorem*. Any single finite code $(k,n)$ with error
$\varepsilon$ certifies that every ratio below
$k/(n+\varphi(\varepsilon)(1/C_1+1/C_2))$ is transmissible, where
$\varphi(\varepsilon)=h(\varepsilon)+\varepsilon k\log_2(|\mathcal U||\mathcal V|)$. The
proof uses an outer distributed (Slepian–Wolf-type) code that repairs the inner code's
residual errors, sent over extra channel uses.

Consequences:
- The frozen Statement is **equivalent to uniform upper semi-computability** of $\rho^*$.
  The open content is exactly whether $\rho^*$ has computable outer bounds converging to it.
- On instances where one encoder's input does not affect the output, $\rho^*$ has a closed
  form and is computable.
- Monotonicity of transmissibility in $\rho$, which the problem file only asserts, is
  proved.
- The edge-case audit of the Lean statement finds **no catalog error**.
- On the Cover–El Gamal–Salehi example, $\rho^*=1$ exactly. The canonical example sits on
  the one boundary value the $\rho^*$ proxy cannot resolve.

## Approach

Achievability in this problem is witnessed by finite objects: codes with an exactly
computable rational error. The difficulty is that "transmissible at $\rho$" is an
asymptotic statement about all large $n$ with error tending to 0. Finite codes give an
r.e. lower cut only if one good finite code implies asymptotic achievability at nearly
the same ratio. Separation fails for this problem, so the bootstrap must keep the inner
joint source–channel code and correct only its errors. A distributed source code with
decoder side information (the inner code's output) does this at a cost of
$\approx H(U^kV^k\mid\text{inner output})\le\varphi(\varepsilon)$ bits per inner block
for each encoder. Those bits travel over time-shared single-user channel uses.

## Claims

Notation: $a=|\mathcal U|$, $b=|\mathcal V|$, and the instance is $(P,W)$ with rational
entries. $S=\{\rho:\ $`IsTransmissibleAtRatio P W ρ`$\}$, so $\rho^*=\sup S$.
$C_1:=\max_{x_2}C(W(\cdot\mid\cdot,x_2))$ and $C_2:=\max_{x_1}C(W(\cdot\mid x_1,\cdot))$
are the single-user capacities with the other input frozen. $h$ is the binary entropy
function.

1. **[proved]** *Edge-case audit; no catalog error.* Under the Statement's hypotheses:
   - $a,b\ge1$ (forced by `hw`) and $e\ge1$ (forced by `hv` together with $c,d>0$).
   - The hypothesis `∀ u t, w u t < ∑ w` is exactly $H(U,V)>0$.
   - $0\in S$ and $S$ is bounded (certificate file), so $\rho^*$ is a genuine finite
     supremum. If nothing positive is achievable, $S=\{0\}$ and $\rho^*=0$; this happens,
     e.g., when both $C_1=C_2=0$ (Claim 6).
   - By Claim 2, $S$ is an interval $[0,\rho^*)$ or $[0,\rho^*]$.
   - By Claim 3, $\rho^*$ does not change if "for all $n\ge N$" in
     `IsTransmissibleAtRatio` is weakened to "for infinitely many $n$". So the
     $\lfloor\rho n\rfloor$ convention and the all-$n$ quantifier are harmless.
2. **[proved]** *Monotonicity.* If $\rho\in S$ and $0\le\rho'<\rho$, then $\rho'\in S$.
3. **[proved]** *Bootstrap theorem.* Suppose $C_1,C_2>0$, and some $(k,n)$ code
   ($k,n\ge1$) has `jsccError` $=\varepsilon$. Then every $0\le\rho<k/(n+\varphi(\varepsilon)(1/C_1+1/C_2))$
   lies in $S$.
4. **[proved]** *Lower semi-computability.* There is an algorithm, uniform over all
   instances satisfying the Statement's hypotheses, that on input (instance, rational $r$)
   halts iff $r<\rho^*(P,W)$.
5. **[proved]** *Reformulation.* The frozen Statement holds iff $\rho^*$ is *uniformly upper
   semi-computable*, i.e. some algorithm halts on (instance, rational $s$) iff
   $s>\rho^*$. This uses the standard fact that the Lean `TuringMachine` model simulates
   any algorithm.
6. **[proved]** *Degenerate MACs.*
   - If $C_1=0$ and $H(U|V)>0$, then $\rho^*=0$.
   - If $C_1=0$ and $H(U|V)=0$, then $\rho^*=C(W_2)/H(V)$, with
     $W_2(y|x_2):=W(y|x_1^*,x_2)$ for any $x_1^*$.
   - The same holds with the roles swapped.

   Which case applies is decidable from the instance, so the Statement holds on this
   subclass.
7. **[sketch]** *Independent sources.* If $P=P_U\times P_V$, then
   $\rho^*=\max\{\rho:\rho(H(U),H(V))\in\mathcal C_{\rm MAC}(W)\}$, which is computable.
   So the Statement also holds on this subclass.
8. **[proved]** *Examples.*
   - In the CES example ($(U,V)$ uniform on $\{00,01,11\}$, binary adder MAC),
     $\rho^*=1$ exactly.
   - In its noisy variant (adder output through a ternary symmetric channel with
     crossover $1/100$), $0.82489<\rho^*\le0.94272$.
9. **[heuristic]** *Upper semi-computability is the real obstruction.* No known converse
   gives a computable, monotonically convergent family of outer bounds. The CES converse
   is $n$-letter *at the code's own blocklength*, not a decreasing sequence of computable
   bounds. The situation parallels Shannon capacity $\Theta(G)$ (catalog
   `shannon-capacity-computability`): lower semi-computable, with upper semi-computability
   open. I have no argument for either answer.

## Details

### Claim 2 (monotonicity)
Fix $\delta>0$ and $n\ge N(\delta)$. Take a code for $K=\lfloor\rho n\rfloor$ symbols with
error at most $\delta$, and let $k'=\lfloor\rho' n\rfloor\le K$. Write the error as
$\sum_t P^{K-k'}(t)\,e(t)$ over tails $t\in(\mathcal U\times\mathcal V)^{K-k'}$, where
$e(t)$ is the error conditioned on the tail. Some $t^*$ with $P(t^*)>0$ has
$e(t^*)\le\delta$.

Pad with $t^*$: encoder 1 appends the $\mathcal U$-part of $t^*$, encoder 2 the
$\mathcal V$-part, and the decoder keeps the first $k'$ coordinates. A wrong truncated
decision implies a wrong full decision. So the new error is at most $e(t^*)\le\delta$. ∎

### Claim 3 (bootstrap)
Let $(f_1,f_2,g)$ be the $(k,n)$ code. Set $\tilde U=U^k$, $\tilde V=V^k$, and let
$Z=g(Y^n)$ be the inner decision when the code is used once.

**(i) Super-letters.** Use the inner code on $N$ consecutive source blocks. The triples
$(\tilde U_j,\tilde V_j,Z_j)_{j\le N}$ are i.i.d.: the source blocks are i.i.d., the
encoders act blockwise, and the channel is memoryless.

**(ii) Fano.** Since $Z$ estimates $(\tilde U,\tilde V)$ over an alphabet of size
$(ab)^k$ with error $\varepsilon$,
$$H(\tilde U,\tilde V\mid Z)\le h(\varepsilon)+\varepsilon\log_2((ab)^k-1)\le\varphi(\varepsilon).$$

**(iii) Lemma (crude Slepian–Wolf with side information) [proved].** Let $(A_j,B_j,Z_j)$
be i.i.d. on finite alphabets, $H:=H(A,B|Z)$, $\gamma>0$, and $R_1,R_2\ge H+2\gamma$.
Then there are maps $e_1:A^N\to[\lceil2^{NR_1}\rceil]$, $e_2:B^N\to[\lceil2^{NR_2}\rceil]$
and a decoder $d$ with $P(d(e_1(A^N),e_2(B^N),Z^N)\ne(A^N,B^N))\to0$.

*Proof.* Bin uniformly at random and independently. Let
$T(z)=\{(a,b):P(a,b|z)\ge2^{-N(H+\gamma)}\}$, so $|T(z)|\le2^{N(H+\gamma)}$. The decoder
outputs the unique element of $T(z)$ in the received bins. The error is at most:
- $P((A,B)\notin T(Z))$, which tends to 0 by the weak law of large numbers applied to
  $-\frac1N\sum_j\log P(A_jB_j|Z_j)$ (bounded i.i.d. summands with mean $H$); plus
- the expected number of other elements of $T(Z)$ in the same bin pair. For
  $(a',b')\ne(a,b)$ that collision has probability at most
  $\max(2^{-NR_1},2^{-NR_2})$: if $a'\ne a$ the $e_1$-bins must collide, and otherwise
  $b'\ne b$. So this term is at most $2^{N(H+\gamma)}2^{-N(H+2\gamma)}=2^{-N\gamma}$.

Then derandomize. ∎

**(iv) Channel coding.** By the definition of $C_1$, some $x_2^*$ has
$C(W(\cdot|\cdot,x_2^*))=C_1$; similarly $x_1^*$ for $C_2$. Fix rates $A_1'<C_1$ and
$A_2'<C_2$. By the channel coding theorem with *maximal* error, there are codes for
$\lceil2^{NR_i}\rceil$ messages of length $m_i=\lceil(NR_i+1)/A_i'\rceil$ with maximal
error $\lambda_i(N)\to0$. During encoder 1's slot, encoder 2 sends $x_2^*$, and vice
versa.

**(v) Assembly.** Each encoder:
1. sends its inner codewords for the $N$ blocks ($Nn$ uses);
2. then sends its bin index $e_i(\cdot)$ in its own slot ($m_1+m_2$ uses).

Both encoders depend only on their own source. The decoder computes $Z^N$, decodes the
two indices, and applies $d$. The error is at most
$P(\text{SW error})+\lambda_1+\lambda_2\to0$. The code sends $Nk$ symbols in
$L_N=Nn+m_1+m_2$ uses, and $Nk/L_N\to\rho_\infty:=k/(n+R_1/A_1'+R_2/A_2')$.

**(vi) All lengths.** Fix $\rho<\rho_\infty$. For large $n'$, let $N$ be maximal with
$L_N\le n'$. Since $L_{N+1}-L_N=O(1)$ and $\rho<\rho_\infty$, we get
$\lfloor\rho n'\rfloor\le Nk$ for large $n'$. Then:
- drop source symbols with the padding of Claim 2;
- fill the remaining $n'-L_N$ channel uses with fixed inputs that the decoder ignores
  (marginalizing them leaves the error unchanged).

The error is at most that of the length-$L_N$ code, which tends to 0. So $\rho\in S$.

Letting $\gamma\downarrow0$ with $R_i=\varphi(\varepsilon)+2\gamma$, and $A_i'\uparrow C_i$,
$\rho_\infty$ approaches $k/(n+\varphi(\varepsilon)(1/C_1+1/C_2))$. ∎

The "infinitely many $n$" remark in Claim 1 follows: a single code suffices as input.

### Claim 4 (algorithm)
On input (instance, $r$):
1. If $r<0$, halt.
2. Decide exactly, by comparing rational rows, whether $C_1>0$: this holds iff for some
   $x_2$ two rows $W(\cdot|x_1,x_2)\ne W(\cdot|x_1',x_2)$. Decide $C_2>0$ the same way.
   Decide whether $H(U|V)=0$ (each $v$ has at most one $u$ with $P(u,v)>0$) and whether
   $H(V|U)=0$.
3. **Case $C_1,C_2>0$.** Fix a distinguishing triple $(x_1,x_1',x_2^*)$ and let
   $A_1:=I(X_1;Y)$ for $X_1$ uniform on $\{x_1,x_1'\}$ through $W(\cdot|\cdot,x_2^*)$, so
   $0<A_1\le C_1$. Define $A_2$ symmetrically. Both are computable reals. Dovetail over
   all finite codes $(k,n,f_1,f_2,g)$ and precisions $j$:
   - compute $\varepsilon$ exactly as a rational, using the Lean `jsccError` formula;
   - evaluate $r\,(n+\varphi(\varepsilon)(1/A_1+1/A_2))<k$ in interval arithmetic at
     precision $2^{-j}$, and halt if it is confirmed.

   *Soundness.* Since $A_i\le C_i$, a confirmed inequality gives
   $r<r'<k/(n+\varphi(\varepsilon)(1/C_1+1/C_2))$ for some $r'$. By Claim 3,
   $r'\in S$, so $r<\rho^*$.

   *Completeness.* Suppose $0\le r<\rho^*$. Pick $\rho'\in S$ with $\rho'>r$, then
   $\delta\in(0,1/2]$ with $\rho'/(1+\delta\rho'\log_2(ab)(1/A_1+1/A_2))>r$. For
   $n\ge N(\delta)$ there is a code with $k=\lfloor\rho'n\rfloor$ and
   $\varepsilon\le\delta$. Since $h$ is increasing on $[0,1/2]$,
   $\varphi(\varepsilon)\le h(\delta)+\delta k\log_2(ab)$. The certificate value is then at
   least
   $$\frac{\rho'-1/n}{1+(h(\delta)/n+\delta\rho'\log_2(ab))(1/A_1+1/A_2)}\;\to\;\frac{\rho'}{1+\delta\rho'\log_2(ab)(1/A_1+1/A_2)}>r,$$
   so the search eventually halts.
4. **Other cases.** Use the closed form of Claim 6. It is a computable real: DMC capacity
   with rational entries is computable via Blahut–Arimoto upper and lower bounds. So
   "$r<\rho^*$" is semi-decidable. ∎

### Claim 5
(⇒) Let $M$ be the Statement's machine. Given $s$:
- If $s\le0$, never halt (correct, since $\rho^*\ge0$).
- Otherwise, for $m=1,2,\dots$ with $x:=s-2/m>0$, query $M$ on $(x,\text{prec}=m)$, and
  halt if it answers `true`.

Correctness:
- A `true` answer at $m$ excludes $\rho^*\ge x+1/m$, so $\rho^*<s$.
- Conversely, if $\rho^*<s$, then once $3/m<s-\rho^*$ we have $\rho^*\le x-1/m$, so $M$
  must answer `true`.
- $M$ halts on every query.

(⇐) Dovetail the lower enumeration (Claim 4) and the upper enumeration until some
certified $r<\rho^*<s$ has $s-r<1/\text{prec}$. Output `true` iff $s\le p/q$.
- If $\rho^*\le p/q-1/\text{prec}$, then $s<\rho^*+1/\text{prec}\le p/q$, so the output is
  `true`.
- If $\rho^*\ge p/q+1/\text{prec}$, then $s>p/q$, so the output is `false`.

Such a pair always exists, so the machine halts. ∎

### Claim 6
**Case $C_1=0$.** For every $x_2$, $W(\cdot|x_1,x_2)$ does not depend on $x_1$. So $Y^n$
depends on the inputs only through $X_2^n=f_2(V^k)$, and $U^k-V^k-Y^n$ is a Markov
chain.

- *Subcase $H(U|V)>0$.* If some $\rho>0$ were in $S$, Fano would give
  $kH(U|V)=H(U^k|V^k,Y^n)\le H(U^k|Y^n)\le1+P_e k\log_2a$ with $k=\lfloor\rho n\rfloor\to\infty$
  and $P_e\to0$, forcing $H(U|V)=0$. So $\rho^*=0$.
- *Subcase $H(U|V)=0$.* Here $U=g(V)$ a.s. and $H(V)=H(U,V)>0$.
  - Converse: $kH(V)\le I(U^kV^k;Y^n)+1+P_ek\log_2(ab)\le nC(W_2)+1+P_ek\log_2(ab)$.
  - Achievability: lossless coding of $V^k$ followed by a channel code for $W_2$; the
    decoder outputs $(g(\hat V^k),\hat V^k)$. This is point-to-point separation.

  Together, $\rho^*=C(W_2)/H(V)$.

The case $C_1=C_2=0$ is covered: there $C(W_2)=0$ or $H(U|V)>0$. ∎

### Claim 7 (sketch)
For independent sources, the necessary condition is
$(\rho H(U),\rho H(V))\in\mathcal C_{\rm MAC}$: standard MAC converse with independent
encoders plus Fano. Separate compression plus MAC coding achieves it, so
$\rho^*=\sup\{\rho\ge0:\rho(H(U),H(V))\in\mathcal C_{\rm MAC}\}$.

The support function $h(\lambda)$ of $\mathcal C_{\rm MAC}$ is a maximum of a continuous
function over a product of simplices, hence computable. Since $\mathcal C_{\rm MAC}$ is
convex, closed and downward closed,
$\rho^*=\inf_\lambda h(\lambda)/(\lambda H(U)+(1-\lambda)H(V))$ over $\lambda$ with a
positive denominator. This is computable; the endpoint cases with $H(U)=0$ or $H(V)=0$
are routine but not written out.

### Claim 8
**CES example.** `code/certificate_demo.py` computes the uncoded $k=n=1$ code's error
exactly: $\varepsilon=0$ (as a fraction). It also computes $A_1=A_2=1$. Claim 3 then
gives $\rho^*\ge1$.

Upper bound: the cooperative cut-set bound. Fano gives
$kH(U,V)\le n\max_{p(x_1,x_2)}I(X_1X_2;Y)+1+P_ek\log_24$, and
$\max I(X_1X_2;Y)\le\log_2|\mathcal Y|=\log_23=H(U,V)$. So $\rho^*\le1$, and hence
$\rho^*=1$.

**Noisy variant** (crossover $1/100$):
- The exact MAP error of the uncoded code is $\varepsilon=1/100$, and
  $A_1=A_2=0.9496216$. Claim 3 gives $\rho^*>0.8248915$.
- The cut-set bound gives
  $\rho^*\le(\log_23-H(0.99,0.005,0.005))/\log_23=0.9427159$.
- The log comparisons are evaluated at 50 digits and are far from tight.

**Remark for the problem file.** CES's motivating example has $\rho^*=1$ exactly. It *is*
transmissible at $\rho=1$ (uncoded, zero error), but the proxy $\rho^*$ alone does not
decide this.

### Claim 9 (heuristic discussion)
An upper semi-computation would need, for each instance, a computable decreasing sequence
of outer bounds converging to $\rho^*$. The available converses fall short:
- Kang–Ulukus (2011) give a single-letter outer bound. It is computable but not tight.
- The CES $n$-letter condition is necessary only at the code's own blocklength, with an
  uncontrolled slack. Restricting a long code to sub-blocks destroys the Markov
  structure $X_1^n-U^k-V^k-X_2^n$, so the $n$-letter conditions are not known to give
  outer bounds for each fixed $n$.

Lower semi-computable quantities with no known matching upper approximation are common in
information theory. The catalog's Shannon-capacity problem is the cleanest analogue. For
channels *with memory*, capacity is provably not computable: Elkouss–Pérez-García 2018;
Boche–Schaefer–Poor 2020. No such negative result is known for memoryless multi-terminal
problems, and the present problem has no "memory" from which to encode an undecidable
problem. I would not bet either way.

## Verification

- `code/certificate_demo.py` uses exact rational arithmetic (`fractions`) for all code
  error probabilities, and mpmath at 50 digits for the logarithmic quantities. It runs in
  under 1 s:
  ```
  CES example: exact error of uncoded code = 0 ; A1 = 1.0 A2 = 1.0
    certificate: every rho < 1.0 is transmissible  =>  rho* >= 1
    cut-set: rho* <= max I(X1X2;Y)/H(U,V) <= log2(3)/log2(3) = 1.0
  Noisy variant (TSC 1/100 after adder): exact MAP error of uncoded code = 1/100 = 0.01
    A1 = 0.94962156  A2 = 0.94962156
    certificate: rho* > 0.8248915
    cut-set:     rho* <= (log2 3 - H_T)/log2 3 = 0.94271591
  ```
- Claims 2–6 are pen-and-paper proofs. Each step uses only Fano's inequality, the weak law
  of large numbers, and the point-to-point channel coding theorem (maximal error) and
  source–channel separation theorem. Nobody has checked them independently yet.
- The certificate file `lean/InfoTheory/Known/Certificates/CorrelatedSourcesOverMac.lean`
  already proves $0\in S$ and boundedness, which Claims 1 and 4 use. Claim 2 (monotonicity)
  and the Lemma in Claim 3(iii) are elementary enough to formalize. They would be natural
  next certificates.

## Dead ends

- **Bootstrapping via the CES sufficient condition on super-letters.** Applying the CES
  single-letter sufficient condition to $(U^k,V^k)$ over $W^n$ with uncoded super-letters
  gives requirements like $H(\tilde U|\tilde V)<I(X_1^n;Y^n|X_2^n,\tilde V)$. For a
  deterministic good code the right side is $H(\tilde U|\tilde V)-H(\tilde U|\tilde V,Y^n)$,
  strictly smaller than the left side when $\varepsilon>0$. So the inequality fails, and
  extra channel uses (the outer code) are unavoidable. This is why the bootstrap pays the
  $\varphi(\varepsilon)/C_i$ overhead.
- **One-encoder correction.** Sending all correction bits through one encoder fails when
  the other source is not a function of that encoder's source. Hence the two time-shared
  slots, and hence the separate treatment of $C_1=0$ or $C_2=0$ (Claim 6). There, the
  silent encoder's source must be a function of the other's, or $\rho^*=0$.
- **Upper semi-computability via the $n$-letter CES converse.** I tried to obtain a
  per-$n$ outer bound by splitting a long code into length-$n$ sub-blocks. It fails because
  sub-block inputs depend on the whole source sequence, so the Markov structure that the
  $n$-letter condition needs does not survive. I see no fix.

## References

- T. M. Cover, A. El Gamal, M. Salehi, IEEE Trans. IT 26(6):648–657, 1980 (the example and
  the $n$-letter converse).
- W. Kang, S. Ulukus, IEEE Trans. IT 57(1):56–69, 2011.
- D. Slepian, J. K. Wolf, IEEE Trans. IT 19(4), 1973. Claim 3(iii) is a self-contained
  crude variant and does not rely on their theorem.
- H. Boche, R. F. Schaefer, H. V. Poor, "Shannon meets Turing: non-computability and
  non-approximability of the finite state channel capacity," Commun. Inf. Syst. 20(2),
  2020; arXiv:2008.13270 (abstract read).
- D. Elkouss, D. Pérez-García, "Memory effects can make the transmission capability of a
  communication channel uncomputable," Nat. Commun. 9:1149, 2018 (abstract read).
- C. T. Li, "First-order theory of probabilistic independence and single-letter
  characterizations of capacity regions," arXiv:2108.07324 (abstract read; it does not
  treat the MAC or joint source–channel coding).
- C. T. Li, "Undecidability of network coding, conditional information inequalities, and
  conditional independence implication," arXiv:2205.11461 (listing only; it concerns exact
  network-coding questions, not this problem).
- Catalog: `problems/shannon-capacity-computability.md` (the analogous r.e./co-r.e. split).
- Prior attempts on this problem: none.

**Novelty check.**
- Searches: "lower semi-computable capacity region"; "Turing computability multiple access
  channel correlated sources"; Boche–Schaefer–Poor's computability papers (FSC, 2019
  identification with correlated sources, "Turing meets Shannon" 2022, from search
  listings); Elkouss–Pérez-García; Agarwal arXiv:1804.05977; C. T. Li's two papers above.
- None states a computability or semi-computability result for $\rho^*$, or for joint
  source–channel coding over a MAC. The problem file's own search reached the same
  conclusion.
- The bootstrap combines textbook tools in the standard "outer code fixes inner residual
  errors" pattern. I expect experts would call the r.e. conclusion folklore for memoryless
  networks, but I did not find it written down for this problem. Treat Claim 4 as a
  careful write-up, not a discovery.
