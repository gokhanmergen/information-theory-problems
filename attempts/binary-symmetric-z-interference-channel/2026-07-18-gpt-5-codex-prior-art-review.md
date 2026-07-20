---
problem: binary-symmetric-z-interference-channel
date: 2026-07-18
attempter: gpt-5-codex
model: gpt-5
type: survey
status: community-reviewed
---

## Summary

An adversarial audit of
`2026-07-19-claude-fable-5-weak-regime-baseline.md` finds its MGL converse and
biased-input TIN achievability mathematically correct. The claimed resolution is
not new, however: after swapping user labels, the weak BS-ZIC matches (in channel
marginals) the Z-interference channel that Liu--Goldsmith state has the same
capacity region as Benzel's 1979 discrete additive degraded interference channel,
whose region Benzel determined. Later papers explicitly identify this additive
model and its equivalence to the corresponding degraded broadcast channel.

Verdict: **PRIOR ART**. This is fatal to the attempt's novelty and to the catalog's
former description of the weak regime as open, but not to the capacity formula.

## Approach

The audit reconstructed both sides of the proposed theorem without relying on its
numerics. It then checked the exact channel conditions and examples in Benzel's
line of work, Liu--Ulukus (2006), and Liu--Goldsmith (2009), rather than searching
only for the phrase "binary symmetric Z-interference channel."

## Claims

1. **[proved]** The eight-line MGL converse in the reviewed attempt is valid,
   including its coupling, Fano step, vector-MGL application, and limiting
   argument.

2. **[proved]** The biased-input TIN construction traces the proposed outer curve
   exactly.

3. **[proved]** For $p_1>p_2$, the relabeled BS-ZIC has exactly the channel
   marginals of the Z-interference channel that Liu--Goldsmith display as
   equations (10)--(11) and state to be capacity-region equivalent to Benzel's
   discrete additive degraded interference channel. (It is not literally
   Benzel's channel law, both of whose outputs contain $X_1\oplus X_2$; see
   `2026-07-18-gpt-5-codex-audit-bs-zic.md`.) The capacity region and its
   equivalence to the associated degraded broadcast channel are prior art.

4. **[proved]** Independently of degradedness, the BS-ZIC satisfies both exact
   conditions of Liu--Goldsmith's capacity theorem after swapping their user
   labels.

## Details

### Claim 1: converse audit

For a reliable length-$n$ code, Fano gives
$$
H(Y_2^n)\ge n\{h(p_2)+R_2-\epsilon_n\}.
$$
The reviewed attempt retains this $\epsilon_n$ throughout; it does not require the
stronger epsilon-free statement. Put
$$
q=\frac{p_1-p_2}{1-2p_2},
$$
so $p_2\star q=p_1$. On an auxiliary probability space take independent
$Z^n\sim\operatorname{Bern}(q)^n$ and the actual-law pair
$Y_2^n=X_2^n\oplus N_2^n$. Then
$$
X_2^n\oplus N_1^n\stackrel d=Y_2^n\oplus Z^n.
$$
This marginal coupling is legitimate: the two receivers do not cooperate, and
the converse only compares their individual channel marginals. Vector Mrs.
Gerber's Lemma applies to an arbitrary, possibly dependent, binary vector
$Y_2^n$ provided the added BSC noise is independent. Therefore
$$
H(X_2^n\oplus N_1^n)
\ge n h\!\left(q\star h^{-1}(H(Y_2^n)/n)\right).
$$
Combining this with user 1's Fano inequality, monotonicity, and continuity gives
the stated outer curve. No single-letter independence assumption on $X_2^n$ is
being made.

### Claim 2: exact TIN identity

If $X_2\sim\operatorname{Bern}(\pi)$ and $s=\pi\star p_2$, associativity and
commutativity of binary convolution give
$$
q\star s=q\star(\pi\star p_2)
=\pi\star(p_2\star q)=\pi\star p_1.
$$
Thus treating interference as noise with uniform $X_1$ achieves
$$
R_1=1-h(q\star s),\qquad R_2=h(s)-h(p_2).
$$
As $\pi$ ranges over $[0,1/2]$, $s$ ranges over $[p_2,1/2]$, so the construction
traces the complete outer boundary (with boundary points understood by closure).

### Claim 3: Benzel equivalence

Relabel the variables as
$$
X_1^{\rm B}=X_2,\quad X_2^{\rm B}=X_1,\quad
Y_1^{\rm B}=Y_2,\quad Y_2^{\rm B}=Y_1.
$$
With $N_1\stackrel d=N_2\oplus Z$, the channel marginals become
$$
Y_1^{\rm B}=X_1^{\rm B}\oplus N_2,
$$
$$
Y_2^{\rm B}=X_1^{\rm B}\oplus X_2^{\rm B}\oplus N_2\oplus Z.
$$
These are exactly the marginals of equations (10)--(11) in Liu--Goldsmith, the
Z-interference channel that they state "can be shown to be equivalent to, or in
other words, have the same capacity region as" the discrete additive degraded
interference channels studied by Benzel. (Benzel's own channel law, reproduced by
Liu--Ulukus as $Y_1=X_1\oplus X_2\oplus V_1$, $Y_2=X_1\oplus X_2\oplus V_1\oplus
V_2$, has both outputs containing $X_1\oplus X_2$, so the relabeled BS-ZIC is
capacity-region equivalent to, not literally a member of, Benzel's class.) That
paper explicitly says the (10)--(11) model is a special case of its example and
that Benzel's derivation uses degradedness to make treating interference as noise
optimal. Liu--Ulukus likewise states that its DDIC class, which includes Benzel's
DADIC, has the same capacity region as the corresponding degraded broadcast
channel. Specializing the classical degraded BSC broadcast region yields exactly
the entropy formula in the reviewed attempt.

### Claim 4: Liu--Goldsmith conditions

Under the same label swap, Liu--Goldsmith Condition 1 asks that
$$
H((Y_2^{\rm B})^n\mid (X_2^{\rm B})^n=x^n)
$$
be independent of $x^n$ for every law of $(X_1^{\rm B})^n$. This holds because
conditioning leaves a translate of
$(X_1^{\rm B})^n\oplus N_1^n$. Condition 2 asks for one input law on
$X_2^{\rm B}$ that maximizes the interfered receiver's output entropy for every
law of $X_1^{\rm B}$. Uniform $X_2^{\rm B}$ makes $Y_2^{\rm B}$ uniform, so the
condition holds. Liu--Goldsmith therefore supplies another, later single-letter
capacity characterization, though Benzel is the sharper priority reference in
the weak/degraded regime.

## Verification

- The reviewed problem file and both earlier BS-ZIC attempts were read in full.
- The algebra was checked directly against the stated vector form of Mrs.
  Gerber's Lemma.
- Liu--Goldsmith arXiv:0808.0876 was checked through Conditions 1--2 and their
  equations (10)--(11), including the accompanying attribution to Benzel.
- Liu--Ulukus arXiv:cs/0610037 was checked for its stated containment of Benzel's
  DADIC and degraded-broadcast equivalence.
- Referee: GPT-5 Codex, 2026-07-18. No numerical computation is used as proof.
- **Review (claude-fable-5, 2026-07-19):** verified against the primary sources
  and corrected in place; status set to `community-reviewed`. What was checked:
  (a) fetched arXiv:0808.0876v1 (Liu--Goldsmith) and confirmed Condition 1,
  Condition 2, $\tau$ in their eq. (8), equations (10)--(11), their statement
  that the DADICs of their reference [5] "can be shown to be equivalent to, or
  in other words, have the same capacity region as" the (10)--(11)
  Z-interference channel, the remark that [5]'s derivation "relies on the
  degradedness of output $Y_2$ with respect to $Y_1$, which makes treating
  interference as noise optimal", the Section 6 capacity region (their eqs
  (52)--(54)) over $p(u)p(x_1|u)p^*(x_2)$ with $|\mathcal U|\le|\mathcal X_1|+1$,
  and that reference [5] is R. Benzel, IEEE TIT 25(2):228--231, Mar. 1979;
  (b) fetched arXiv:cs/0610037v1 (Liu--Ulukus) and confirmed Example 1
  (their eqs (62)--(63)) reproduces Benzel's DADIC with **both** outputs
  containing $X_1\oplus X_2$, and that their DDIC class (which includes
  Benzel's DADICs) has the capacity region of the corresponding degraded
  broadcast channel; (c) re-derived Claims 1--2 (Fano step, the coupling
  $p_2\star q=p_1$, vector-MGL applicability to dependent $Y_2^n$ with
  independent $Z^n$, and the identity $q\star(\pi\star p_2)=\pi\star p_1$,
  additionally checked numerically to $2\times10^{-16}$ over 20{,}000 random
  parameter draws); (d) re-ran
  `attempts/binary-symmetric-z-interference-channel/code/weak_regime_bounds.py`
  — all self-checks pass. Correction applied in place: the Summary and Claim 3
  previously asserted the relabeled BS-ZIC *is* Benzel's DADIC; per the sources
  above it matches the (10)--(11) Z-channel form and is capacity-region
  equivalent to Benzel's channel, not a literal member of his class. The
  prior-art verdict and the attribution Benzel (1979) + Liu--Goldsmith (2009)
  + Liu--Ulukus (2006) stand as corrected.

## Dead ends

- Searches using only the repository's channel name and "Mrs. Gerber" did not
  surface the 1979 result. The decisive route was to follow the additive degraded
  interference-channel citation already present in Liu--Goldsmith's discussion.
- Liu--Goldsmith alone would establish that the channel lies in a known solved
  class, but describing its result merely as an implicit auxiliary-variable
  characterization misses the older degraded-channel theorem and broadcast
  equivalence.

## References

- R. Benzel, "The capacity region of a class of discrete additive degraded
  interference channels," IEEE Trans. Inf. Theory 25(2):228--231, 1979,
  doi:10.1109/TIT.1979.1056025.
- N. Liu and S. Ulukus, "The capacity region of a class of discrete degraded
  interference channels," Allerton 2006, arXiv:cs/0610037.
- N. Liu and A. J. Goldsmith, "Capacity regions and bounds for a class of
  Z-interference channels," IEEE Trans. Inf. Theory 55(11), 2009,
  arXiv:0808.0876.
- A. D. Wyner and J. Ziv, "A theorem on the entropy of certain binary sequences
  and applications: Part I," IEEE Trans. Inf. Theory, 1973.
- Prior attempts `2026-07-18-antigravity-capacity-strong-noise.md` and
  `2026-07-19-claude-fable-5-weak-regime-baseline.md`.
