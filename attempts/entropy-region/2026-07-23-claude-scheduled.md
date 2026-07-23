---
problem: entropy-region
date: 2026-07-23
attempter: claude-scheduled
model: claude-fable-5
type: numerical-evidence
status: unverified
---

## Summary

Copy-lemma LP machinery on top of the certified baseline
(`2026-07-19-claude-fable-5-zy-baseline.md`): the Zhang–Yeung 1998 inequality
is re-derived from the Shannon cone plus **one** copy variable, and all six
Dougherty–Freiling–Zeger two-copy inequalities (arXiv:1104.3602, eqs
(37)–(42)) are certified valid on $\Gamma^*_4$ with **exact rational dual
certificates** (two copy variables each). Each of the six is also shown
non-Shannon by an exact rational point of $\Gamma_4$ violating it, and
one-copy-insufficient by exact rational witnesses against all 64 single-copy
specifications. The code (`code/copy_lemma.py`) was written by a scheduled
run on 2026-07-22 that stalled twice before completing verification; this
attempt credits that run, completed the verification in chunked short
computations, and closed its one open item — the widened copy-spec pass for
(39)/(41) — which turned out to yield *direct absolute* certificates,
making the planned lemma-relative pass unnecessary.

## Approach

The Copy Lemma (DFZ Lemma 2; essentially Zhang–Yeung 1998): for any
$(X_A,X_B,X_C,X_D)$ and disjoint $Y,Z \subseteq \{A,B,C,D,\dots\}$ there is a
new variable $R$ with $(X_Z,R) \sim (X_Z,X_Y)$ and $I(R; \text{rest} \mid
X_Z)=0$. Both conditions are *linear equalities* on the extended entropy
vector. So if

$$\max\{\,v\cdot h : h \in \Gamma_n,\ Ch=0,\ h_{ABCD}=1\,\} = 0$$

over the Shannon cone $\Gamma_n$ of the $n$ variables ($n = 4 + \#$copies)
with copy equalities $Ch=0$, then $v\cdot h \le 0$ on all of $\Gamma^*_4$.
The LP dual is the proof object: rationals $y \ge 0$ (one per elemental
Shannon inequality, 246 for $n=6$) and free $\mu$ (one per copy equality)
with the coordinate identity $v + \sum_i y_i E_i + \sum_j \mu_j C_j = 0$,
verified here in exact `fractions.Fraction` arithmetic. Floats appear only
inside the LP solver as a guess generator, exactly as in the baseline
attempt.

The six target inequalities are the DFZ family
$$2I(A;B) \le a\,I(A;B|C) + b\,I(A;C|B) + c\,I(B;C|A) + d\,I(A;B|D)
+ e\,I(A;D|B) + f\,I(B;D|A) + g\,I(C;D)$$
with $(a,\dots,g)$ = (5,3,1,2,0,0,2), (4,2,1,3,1,0,2), (4,4,1,2,1,1,2),
(3,3,3,2,0,0,2), (3,4,2,3,1,0,2), (3,2,2,2,1,1,2) for (37)–(42)
respectively (hand transcription from arXiv:1104.3602, Section V).

## Claims

1. **[proved]** (known: ZY98/DFZ) The canonical Zhang–Yeung inequality
   $2I(C;D) \le I(A;B) + I(A;CD) + 3I(C;D|A) + I(C;D|B)$ holds on
   $\Gamma^*_4$: with one copy variable $R = $ copy of $A$ over $(C,D)$,
   an exact rational dual certificate over $\Gamma_5$ + the 5 copy
   equalities was produced and verified coordinate-by-coordinate in
   `Fraction` arithmetic (11 nonzero Shannon multipliers, all equal to 1;
   details below).
2. **[proved]** (known: DFZ 2006/2011) Each of the six transcribed
   inequalities (37)–(42) holds on all of $\Gamma^*_4$: for each, an exact
   rational (in fact integer) dual certificate over $\Gamma_6$ + two copy
   equalitiy blocks was verified in `Fraction` arithmetic. Copy specs:
   (37): $R=$copy$(C|AB)$, $S=$copy$(R|AC)$; (38): $R=$copy$(C|AB)$,
   $S=$copy$(R|AD)$; (40): $R=$copy$(C|AB)$, $S=$copy$(A|BCR)$;
   (42): $R=$copy$(C|AB)$, $S=$copy$(A|BDR)$; **(39) and (41)**:
   $R=$copy$(A|BC)$, $S=$copy$(A|BDR)$. The certificate proves the stated
   inequality unconditionally; the *labels* "(37)–(42)" rest on the hand
   transcription in Approach.
3. **[proved]** Each of the six is **not** Shannon-implied: for each, an
   exact rational point $h \in \Gamma_4$ (all 28 elemental inequalities
   checked in `Fraction` arithmetic) violates it with exact slack $1/2$
   (at normalization $H(ABCD)=1$). Combined with Claim 2, each inequality
   strictly separates $\bar\Gamma^*_4$ from $\Gamma_4$. (The float LP
   reports $1/2$ as the *maximum* violation; the maximality is
   **[heuristic]** — only the witness is exact.)
4. **[proved]** No single-copy specification proves any of the six: for
   every one of the 64 specs $(Y,Z)$, $Y \ne \emptyset$, $Y,Z$ disjoint
   subsets of $\{A,B,C,D\}$, and each of the six inequalities, an exact
   rational $h \in \Gamma_5$ satisfying the copy equalities exactly and
   violating the inequality was verified (384/384 exact witnesses; float
   LP optimum $0.2$ in every case). This proves the *LP relaxation*
   "Shannon($n{=}5$) + that copy spec" cannot certify them — consistent
   with DFZ's statement that ZY98 is the only one-copy inequality — not
   that no other derivation style exists.
5. **[heuristic]** Negative control: the (false) Ingleton inequality
   $I(C;D) \le I(C;D|A)+I(C;D|B)+I(A;B)$ is *not* certified by any of the
   64 one-copy specs (min LP optimum $0.2 > 0$) nor by any two-copy spec
   used in Claim 2. A soundness bug that "proved" Ingleton would have been
   caught here. (Labelled heuristic because non-existence of a certificate
   is concluded from LP infeasibility in floats.)
6. **[heuristic]** Validity sanity sweep: for each of the six, the maximum
   violation over 300 pseudorandom pmfs (alphabets 2–3, Dirichlet
   $\alpha \in \{0.05,0.3,1\}$, 30% sparsified, seed 20260722) is
   $\le -2.7\cdot 10^{-2} < 0$, consistent with validity (Claim 2 already
   proves it).
7. **[heuristic]** Small search (220 uniform random coefficient tuples
   $(a..g) \in \{0..4\}^7$, seed 20260722): 126 violated by a random pmf
   (false inequalities), 4 certified via Shannon + one copy, 0 new
   two-copy certificates with the specs tried, 90 unresolved (no violation
   found, no certificate). No new inequality candidates are claimed.

## Details

All computations: `code/copy_lemma.py` (numpy, `scipy.optimize.linprog`
HiGHS, stdlib `fractions`; Python 3; run `nice -n 19 python3 copy_lemma.py`,
full run completes in well under 3 minutes and prints every certificate).
The script was written by the stalled 2026-07-22 scheduled run; this attempt
re-ran its verification path in chunked steps and added one line (the
first-copy spec $R=$copy$(A|BC)$ to part 4's spec list) so that the full run
certifies all six absolutely.

**Claim 1.** Copy equalities: $H(R)=H(A)$, $H(CR)=H(AC)$, $H(DR)=H(AD)$,
$H(CDR)=H(ACD)$, $I(R;AB|CD)=0$. Certificate: $y=1$ on
$I(A;B|R)$, $I(A;R|C)$, $I(A;R|D)$, $I(A;R|BCD)$, $I(B;R|C)$, $I(B;R|D)$,
$I(B;R|ACD)$, $I(C;D|AR)$, $I(C;D|BR)$, $I(C;R|ABD)$, $I(D;R|AB)$;
$\mu = (1,-2,-2,3,-3)$ on the five equalities in the order above. The
identity $v + \sum y_i E_i + \sum \mu_j C_j = 0$ holds coordinatewise in
$\mathbb{Q}^{31}$ (checked in `Fraction`s at runtime).

**Claim 2.** For each inequality the script prints the full multiplier list
(23–27 nonzero Shannon multipliers, 10–13 nonzero copy multipliers, all
integers in $\{1,\dots,7\}$ up to sign) and re-verifies the identity in
$\mathbb{Q}^{63}$ exactly on every run. Certification is *absolute*
(Shannon + copy equalities only — no previously proved inequality is cited
as a lemma), so the six proofs are independent of one another.

**Claim 3.** The violating points are obtained by rounding the float LP
optimizer over a denominator ladder and re-checking the 28 elemental
inequalities, and the violation, exactly; a bad rounding fails loudly.

**Claim 4.** Same exact-witness procedure in $\Gamma_5$ with the copy
equalities as exact linear constraints.

**Chunked verification protocol** (the previous run stalled on the
monolithic driver): part 1+2 (baseline + ZY one-copy) $\approx 0.1$ s;
the six absolute certificates via the DFZ-named second specs $\approx 0.1$ s
(four succeed); widened pass for (39)/(41) over all $64 \times 145$
first/second spec pairs: both certified at combo 593 in $< 1$ s each;
negative control + non-Shannon witnesses + one-copy insufficiency + random
sweep $\approx 2$ s; the full `main()` (including the part-6 search, the
slowest step) completes end-to-end within a 160 s alarm.

## Verification

- Re-run `nice -n 19 python3 code/copy_lemma.py`. Every certificate in
  Claims 1–2 and every witness in Claims 3–4 is reconstructed and
  re-verified in exact `Fraction` arithmetic at runtime; the script asserts
  and exits nonzero on any failure (including the Ingleton control).
- What is established: exact, machine-checkable proof objects for seven
  known non-Shannon inequalities (ZY98 + DFZ (37)–(42)) over $\Gamma^*_4$,
  and exact separations from $\Gamma_4$. What is *not* established:
  anything new about $\bar\Gamma^*_4$ — all seven inequalities are in DFZ
  arXiv:1104.3602; the transcription of (37)–(42) was done by hand and has
  not been independently re-checked against the paper's text (Claims 2–4
  are proofs about the transcribed functionals regardless).
- Novelty: none claimed. The (39)/(41) observation — that they admit
  *direct* two-copy certificates with first copy $A$ over $(B,C)$, whereas
  DFZ present them via iterated/cited-lemma derivations — is a minor
  presentational point, very likely known to DFZ (their computer search
  covered vastly more specs).

## Dead ends

- **Two watchdog stalls (2026-07-22 scheduled run).** The previous run was
  killed twice by the scheduler watchdog. Cause: running the monolithic
  `main()` — thousands of small LPs in the straggler scan for (39)/(41)
  plus the part-6 random search — as one long uninterrupted computation
  with sparse output. Nothing was mathematically wrong; the fix here was
  purely operational: chunk the verification into steps of seconds to ~2
  minutes each with frequent progress prints, and add the successful
  first-copy spec so `main()` no longer scans hundreds of straggler
  combinations.
- **The planned lemma-relative pass for (39)/(41) was unnecessary.** The
  stalled run's plan was to certify (39)/(41) *relative to* already-proved
  inequalities (mirroring DFZ's iteration; code in `part4b_relative`).
  Before that, with first copy fixed to $R=$copy$(C|AB)$ and the 17
  DFZ-named second specs, neither (39) nor (41) admits an absolute
  certificate (float screening). Widening to all $64 \times 145$
  first/second pairs found direct absolute certificates for both (first
  copy $A$ over $(B,C)$) at combo 593 of 9280 — so `part4b` is now dead
  code kept for reference and never triggers.
- **Random-pmf search is weak at refuting candidates** (Claim 7): 90 of
  220 random family members ended unresolved — no violating pmf among 250
  random distributions, but no certificate from the few copy specs tried.
  Obstruction: violating distributions for tight non-Shannon candidates
  are structured (DFZ's are supported on 3–4 atoms), and random Dirichlet
  pmfs rarely find them; a targeted (e.g. atom-support optimization)
  search would be the next tool.
- Not attempted (out of budget, natural next steps): three-copy
  certificates; certifying the *maximality* of the violations in Claim 3
  by exact dual bounds; re-deriving Matúš's infinite family (which needs a
  sequence of copy steps and shows no finite list suffices).

## References

- Prior attempts: `2026-07-19-claude-fable-5-zy-baseline.md` (conventions,
  exact-certification methodology, and the $\Gamma_4$-vs-ZY baseline
  re-checked here as part 1).
- R. Dougherty, C. Freiling, K. Zeger, "Non-Shannon information
  inequalities in four random variables," arXiv:1104.3602, 2011. (Lemma 2
  = Copy Lemma; Section V eqs (37)–(42) = the six inequalities; p. 5 and
  p. 8 list the copy specs their search used.)
- Z. Zhang, R. W. Yeung, "On characterization of entropy function via
  information inequalities," IEEE Trans. Inf. Theory 44(4), 1998.
- R. W. Yeung, *Information Theory and Network Coding*, Springer, 2008
  (Sec. 14.2, elemental inequalities).
- F. Matúš, "Infinitely many information inequalities," ISIT 2007 (context
  for why finite lists cannot close the problem).
