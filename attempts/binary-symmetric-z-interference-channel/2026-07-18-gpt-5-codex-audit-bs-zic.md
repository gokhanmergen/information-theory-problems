---
problem: binary-symmetric-z-interference-channel
date: 2026-07-18
attempter: gpt-5-codex
model: gpt-5
type: survey
status: community-reviewed
---

## Summary

This audit checks the Benzel attribution, Liu--Goldsmith containment, and both
proofs in `paper/bs-zic-capacity/main.tex`. The capacity formulas and MGL/TIN
proofs are correct and are prior art. A precise attribution gap was found:
the relabeled BS-ZIC is not literally Benzel's two-output additive channel; it is
the Z-channel form that Liu--Goldsmith state has the same capacity region. The
paper also asserted uniqueness of the weak sum-capacity point without proving it.
Both statements have been repaired in non-attempt files.

## Approach

I derived both regimes from the code definition, checked the vector MGL and the
binary-convolution identity, compared the relabeled channel to the equations
reproducing Benzel's DADIC in Liu--Ulukus and to Liu--Goldsmith Conditions 1--2
and their Section VI theorem, and checked every bibliography entry.

## Claims

1. **[proved]** The weak-regime MGL converse and biased-input TIN achievability in
   the note are valid and trace the same curve exactly.
2. **[proved]** The relabeled BS-ZIC is not literally Benzel's DADIC channel law,
   but Liu--Goldsmith explicitly state capacity-region equivalence; specializing
   the associated degraded BSC broadcast region gives exactly the claimed formula.
3. **[proved]** After the label swap, the BS-ZIC satisfies Liu--Goldsmith's two
   conditions in their full theorem-level, $n$-letter form, and their capacity
   theorem applies for both noise orderings.
4. **[proved]** The strong-regime converse and achievability in the note are
   correct. The direct argument is self-contained; Sato's cited 1981 paper is a
   Gaussian historical antecedent, not by itself a literal theorem for this DMC.
5. **[proved]** The weak sum capacity is $1-h(p_2)$ uniquely at
   $(0,1-h(p_2))$; the missing proof has been added to the note.

## Details

### 1. Weak-regime proof

Fano at receiver 2 gives
\[
H(Y_2^n)\ge n\{h(p_2)+R_2-\epsilon_n\}.
\]
For $q=(p_1-p_2)/(1-2p_2)$, couple an independent BSC($q$) noise to the
marginal $V^n=Y_2^n$. Vector Mrs. Gerber's Lemma applies even though the
codeword coordinates are dependent and gives the displayed entropy lower bound.
Only receiver marginals are compared, so no joint receiver coupling is required.
The user-1 Fano bound and continuity then give the outer curve.

For achievability, $X_2\sim\operatorname{Bern}(\pi)$ yields
$s=\pi\star p_2$ and
\[
q\star s=q\star(\pi\star p_2)=\pi\star(p_2\star q)=\pi\star p_1.
\]
Therefore $R_2=h(s)-h(p_2)$ and $R_1=1-h(q\star s)$ trace the whole boundary.
Along it,
$R_1+R_2=1-h(p_2)+h(s)-h(q\star s)$; for $s<1/2$, one has
$s<q\star s<1/2$ and hence strict loss. This proves the unique sum corner.

### 2. What Benzel actually covers

Liu--Ulukus reproduce Benzel's DADIC as
\[
Y_1=X_1\oplus X_2\oplus V_1,\qquad
Y_2=X_1\oplus X_2\oplus V_1\oplus V_2.
\]
After swapping the BS-ZIC user labels, its marginals are instead
\[
Y_1^{B}=X_1^{B}\oplus N_2,\qquad
Y_2^{B}=X_1^{B}\oplus X_2^{B}\oplus N_2\oplus Z.
\]
The first output lacks $X_2^B$, so literal class membership is false. However,
Liu--Goldsmith display exactly this Z-channel and state it is equivalent, in the
sense of having the same capacity region, to the DADIC. Benzel's degraded
broadcast reduction therefore remains decisive prior art. The degraded BSC
broadcast parameterization
\[
R_{\rm bad}\le1-h(q\star s),\qquad
R_{\rm good}\le h(s)-h(p_2),\quad p_2\le s\le1/2
\]
eliminates $s$ to the claimed closed form.

### 3. Liu--Goldsmith

In their convention, Condition 1 requires the interfered receiver's output
entropy, conditioned on each fixed codeword of that receiver's own transmitter,
to be invariant for arbitrary $n$-letter laws of the interfering input. Mod-2
translation proves this exactly. Condition 2 requires a single input law for
the interfered pair's own transmitter that attains the maximum interfered-output
entropy for every interferer law; the uniform binary law makes that output
uniform. Their Section VI region over
$p(u)p(x_1|u)p^*(x_2)$, with $|\mathcal U|\le3$, therefore applies. Mapping labels
back gives the auxiliary expression recorded in the problem file. Degenerate
$U$ evaluates the weak boundary; $U=X_1$ in their labels evaluates the strong
polytope.

### 4. Strong-regime proof and references

When $p_1\le p_2$, coupling $p_2=p_1\star p_0$ gives
$I(X_2^n;Y_2^n)\le I(X_2^n;Y_1^n|X_1^n)$. Encoder independence and the chain rule
then give the sum bound; $H(Y_1^n)\le n$ closes it. Uniform independent inputs and
joint decoding at receiver 1 attain the mod-2 MAC region. This proof does not need
any literature theorem. The Costa--El Gamal DMC strong-interference paper and
El Gamal--Kim's one-sided discussion are appropriate context; Sato 1981 is
specifically Gaussian and should be read only as historical framing.

All seven bibliography entries in the note are real and their bibliographic data
are correct. Wyner--Ziv is the source of the entropy theorem used as vector MGL;
Liu--Goldsmith and Liu--Ulukus support the class/equivalence statements; Benzel is
the priority source for the additive degraded result.

## Verification

- Read the problem file and every BS-ZIC attempt before this audit.
- Checked Liu--Goldsmith arXiv:0808.0876 through Conditions 1--2, equations
  (10)--(11), and Section VI; checked Liu--Ulukus arXiv:cs/0610037, Example 1.
- Recomputed both Fano bounds, both noise couplings, and the boundary elimination
  without using the numerical grid.
- Corrected only the problem and paper; existing attempt prose was not edited.
- **Review (claude-fable-5, 2026-07-19):** verified and corrected in place;
  status set to `community-reviewed`. What was checked: (a) re-derived Claims
  1 and 5 — Fano at receiver 2, the coupling $p_2\star q=p_1$ with
  $q=(p_1-p_2)/(1-2p_2)$, the marginal legitimacy of comparing
  $X_2^n\oplus N_1^n\stackrel d=Y_2^n\oplus Z^n$, vector MGL applied to the
  dependent vector $Y_2^n$ with independent $Z^n$, the TIN identity
  $q\star s=q\star(\pi\star p_2)=\pi\star p_1$ (numerically confirmed to
  $2\times10^{-16}$ over 20{,}000 random $(p_1,p_2,\pi)$), and the strict sum
  loss $h(s)<h(q\star s)$ for $s\in[p_2,\tfrac12)$ giving the unique
  sum-capacity corner $(0,1-h(p_2))$ (numerically: boundary sum maximized only
  at $s=\tfrac12$); (b) fetched arXiv:0808.0876v1 and confirmed Claim 2's
  correction — Liu--Goldsmith introduce equations (10)--(11) as a
  Z-interference channel that the DADICs of Benzel [their ref. 5] "can be
  shown to be equivalent to, or in other words, have the same capacity region
  as", and fetched arXiv:cs/0610037v1, whose Example 1 (eqs (62)--(63)) shows
  Benzel's channel law has both outputs containing $X_1\oplus X_2$, so literal
  membership indeed fails; (c) confirmed both promised repairs are present in
  `paper/bs-zic-capacity/main.tex` (the "Unique sum-capacity rate pair"
  paragraph, and the Discussion sentence "This is a capacity-region
  equivalence, not a literal equality of channel laws") and the aligned
  phrasing in `problems/binary-symmetric-z-interference-channel.md`; the paper
  was substantially revised after this audit (its bibliography now has 19
  entries, not seven; the entries relevant here — Wyner--Ziv, Benzel,
  Liu--Ulukus, Liu--Goldsmith, Sato 1981, Costa--El Gamal 1987 — check out,
  with Sato 1981 cited only as strong-interference context, consistent with
  Claim 4); (d) re-ran `code/weak_regime_bounds.py` and `python3 build.py` —
  all self-checks pass. Correction applied in place: the Section 3 paraphrase
  of Liu--Goldsmith's Conditions 1--2 had the desired/interfering roles
  swapped (their Condition 1 fixes the interfered pair's own codeword,
  $H(Y_2^n\mid X_2^n=x_2^n)$, and quantifies over interferer laws $p(x_1^n)$;
  their Condition 2's universal law $p^*(x_2)$ is on the interfered pair's own
  input). Both instantiations for the BS-ZIC were and remain valid.

## Dead ends

- Matching Liu--Goldsmith equations (10)--(11) does not prove literal Benzel
  membership; those equations are the capacity-equivalent Z-channel form.
- Sato's Gaussian theorem cannot itself be cited as a discrete-memoryless class
  theorem, though the same decoding idea is classical.
- The sum-capacity uniqueness assertion does not follow merely from drawing the
  boundary; it needs the strict entropy comparison now included in the paper.

## References

- R. Benzel, “The capacity region of a class of discrete additive degraded
  interference channels,” IEEE TIT 25(2):228--231, 1979.
- N. Liu and S. Ulukus, “The capacity region of a class of discrete degraded
  interference channels,” Allerton 2006; arXiv:cs/0610037.
- N. Liu and A. Goldsmith, “Capacity regions and bounds for a class of
  Z-interference channels,” IEEE TIT 55(11):4986--4994, 2009;
  arXiv:0808.0876.
- A. Wyner and J. Ziv, “A theorem on the entropy of certain binary sequences and
  applications: Part I,” IEEE TIT 19(6):769--772, 1973.
