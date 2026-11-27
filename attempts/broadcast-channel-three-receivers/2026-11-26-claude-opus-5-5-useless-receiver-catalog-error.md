---
problem: broadcast-channel-three-receivers
date: 2026-11-26
attempter: claude
model: claude-opus-5-5
type: partial-result
status: verified
---

## Summary

**The frozen Lean `Statement` is false, and the reason is essentially already known. That
makes it a catalog error.** Take a 3-DMBC whose third output is constant, so receiver 3 is
useless. Then the (R₁, R₂) slice of `marton3InnerBound` lies inside **Marton's private-message
region without a superposition variable** (time sharing allowed) for the two-receiver channel
(Y₁, Y₂). Two features of the formal region cause this. The common cloud W₀ must be decoded by
the useless receiver, so it carries no rate. The pairwise cloud W₁₂ sits inside both
V₁ = (W₁₂, W₁₃, U₁) and V₂ = (W₁₂, W₂₃, U₂), so the covering constraint charges
I(V₁; V₂ | W₀) ≥ H(W₁₂ | W₀), the full entropy of that cloud. Gohari, El Gamal and Anantharam
(GEA, arXiv:1006.5166, Claim 1) showed that this region is strictly smaller than capacity for a
degraded BC. Their evidence was a numerical optimisation. We make it rigorous for their channel
(X→Y₁ BSC(0.3), Y₁→Y₂ a Z-channel) at weight α = 2.35:

  sup over the formal region of R₁ + 2.35·R₂ ≤ 0.12131587 < 0.12131597 ≤ R₁* + 2.35·R₂*,

where (R₁*, R₂*, 0) = (0.0557784, 0.0278883, 0) is achieved by superposition coding. The
certificate combines a perturbation argument (proved below) that reduces to binary auxiliaries
and a deterministic map, a simplicial branch and bound, and an interval-arithmetic recheck of
every leaf. The region stated in the problem's `.md` file (W₀ plus multivariate covering) fails
in the same way. We propose a corrected statement based on the "UM region" of
Padakandla–Pradhan. It passes the useless-receiver test and implies the two-receiver
"Marton = capacity" question *(reviewer: the implication rests on an unproved inclusion; see
Claim 7)*. We also record that Padakandla–Pradhan prove the UM region
strictly suboptimal for some three-receiver BCs *with input cost constraints*.

## Approach

1. Read `marton3InnerBound` line by line (Lean file, lines 42–89) and find a degenerate channel
   on which it collapses to a region whose suboptimality is known.
2. The coordinator's lead: let Y₃ be constant. This kills W₀, W₁₃, W₂₃, U₃. We check every
   step against the Lean text (Claim 1).
3. Locate the exact source claim (GEA, arXiv:1006.5166v2, §II-A and the proof of Claim 1) and
   check that their "Marton without W" region allows time sharing, as the reduced formal
   region does. It does: their eqs. (8)–(10) condition on Q.
4. Upgrade GEA's numerical claim to a certificate (Claims 2–4), and pick the weight α with the
   largest margin.
5. Check that the obvious repairs pass the same test, and propose one (Claim 7).

## Claims

1. **[proved]** (Useless-receiver reduction.) Let `W : BroadcastChannel3 (Fin kX) (Fin kY₁)
   (Fin kY₂) (Fin 1)`, so Y₃ is constant. For every α ≥ 1,
   `marton3InnerBound W ⊆ { r | r.2.2 = 0 ∧ r.1 + α·r.2.1 ≤ S_α }`, where
   S_α := sup over finite U, V and p(u, v, x) of [ I(U;Y₁) + α·I(V;Y₂) − I(U;V) ], evaluated
   for the marginal channels of W.
2. **[proved]** (Small auxiliaries suffice.) For any two-receiver BC and any α ≥ 0, the
   supremum S_α is attained with |U|, |V| ≤ |X| and X a deterministic function of (U, V).
3. **[proved]** (Single-variable maps.) Take binary X, binary U and V, and X = f(U, V). If f
   is constant then G ≤ 0. If f depends on V only then G ≤ α·C(X→Y₂). If f depends on U only
   and α·η_TV(X→Y₂) ≤ 1 then G ≤ C(X→Y₁). Here G := I(U;Y₁) + α I(V;Y₂) − I(U;V).
4. **[proved]** (Computer-assisted: interval arithmetic plus Claim 2.) For the GEA channel (X→Y₁ BSC(0.3); Y₁→Y₂ with
   P(0|0) = 0.6, P(1|0) = 0.4, P(1|1) = 1, so P(Y₂=0|X=0) = 0.42 and P(Y₂=0|X=1) = 0.18) and
   α = 2.35: S_α ≤ τ := 0.1213158717. Moreover the superposition input P(V=1) = 0.3614,
   P(X=1|V=0) = 0.2403, P(X=1|V=1) = 1 gives R₁* = I(X;Y₁|V) ∈ [0.0557783533107, 0.0557783533108]
   and R₂* = I(V;Y₂) ∈ [0.0278883482339, 0.0278883482340], so
   R₁* + α R₂* ≥ 0.1213159716 > τ.
5. **[proved]** (Disproof of the frozen `Statement`.) Let
   W(y₁, y₂, y₃ | x) = BSC₀.₃(y₁|x) · K(y₂|y₁) · 1[y₃ = 0] with kX = kY₁ = kY₂ = 2 and kY₃ = 1.
   Then (R₁*, R₂*, 0) ∈ `bc3CapacityRegion W` and (R₁*, R₂*, 0) ∉ `marton3InnerBound W`.
   Hence `¬ InfoTheory.Problems.BroadcastChannelThreeReceivers.Statement`. The proof cites the
   superposition-coding achievability theorem, which is not formalised in `Bridge`.
6. **[proved]** The same channel refutes the region written in `problems/broadcast-channel-three-receivers.md`
   (W₀, U₁, U₂, U₃ with multivariate covering, no pairwise clouds).
7. **[sketch]** Proposed corrected region: the UM region of Padakandla–Pradhan
   (arXiv:1207.3146v6, §II-D, eqs. (1)–(11)), with cost κ ≡ 0, non-strict inequalities and
   closure. It contains the 3-receiver degraded capacity region. When one output is constant
   it reduces exactly to the two-receiver Marton region *with* superposition variable for the
   other two receivers. So the corrected `Statement` implies the open two-receiver
   "Marton = capacity" question, and the present counterexample does not refute it.
   *(Reviewer, 2026-11-27: the sketch in §7 shows only that the useless-receiver slice of the
   UM region **contains** two-receiver Marton-with-W. "Reduces exactly" and "implies the
   two-receiver question" also need the reverse inclusion, which is not argued. Also, the
   two-receiver question is not cleanly open: Huang–Liu–Liu, arXiv:2608.19869 (unrefereed;
   see `attempts/marton-inner-bound-tightness/`), claim Marton's bound is strictly suboptimal.
   If that claim and the reverse inclusion both hold, this corrected `Statement` is false too.)*
8. **[heuristic]** The certified bound in Claim 4 is far from tight. Multi-start optimisation
   gives S_2.35 ≈ 0.118924 = 2.35·C(X→Y₂), attained at X = V and U constant. This matches
   GEA's description at α = 2.4. The true gap at α = 2.35 is about 0.0024 bits, about 2 %.
   At GEA's α = 2.4 we reproduce their numbers: capacity-side value 0.122862 ("0.1229...")
   and 2.4·C(X→Y₂) = 0.121455 ("0.1215...").
9. **[heuristic]** Padakandla–Pradhan show that the UM region is strictly suboptimal on
   3-receiver BCs with an input cost constraint. Their Theorems 3 and 5 use Hamming-weight
   costs. This is strong evidence, not proof, that the corrected statement of Claim 7 is
   false too. If the catalog wants a statement that is not already expected to be false, see
   the discussion in Details §7.

## Details

### 1. The reduction (Claim 1), checked against the Lean text

Write t = (w₀, (w₁₂, w₁₃, w₂₃), (u₁, u₂, u₃), x). The Lean definitions set
`V1 t = (w₁₂, w₁₃, u₁)`, `V2 t = (w₁₂, w₂₃, u₂)`, `V3 t = (w₁₃, w₂₃, u₃)` (lines 66–71).
The constraints (lines 82–89) are

```
r₁₀ + r₂₀ + r₃₀ ≤ min IW_Y1 (min IW_Y2 IW_Y3)           -- IW_Yj = I(W₀;Yj)
r₁₂ + r₁₃ + r₁₁ + rp₁ ≤ IV1_Y1                         -- I(V₁;Y₁|W₀)
r₁₂ + r₂₃ + r₂₁ + rp₂ ≤ IV2_Y2                         -- I(V₂;Y₂|W₀)
r₁₃ + r₂₃ + r₃₁ + rp₃ ≤ IV3_Y3                         -- I(V₃;Y₃|W₀)
rp₁ + rp₂ ≥ I12,  rp₁ + rp₃ ≥ I13,  rp₂ + rp₃ ≥ I23     -- I(Vi;Vj|W₀)
rp₁ + rp₂ + rp₃ ≥ HV1 + HV2 + HV3 - HV123
```

with `r.1 = r₁₀ + r₁₂ + r₁₃ + r₁₁`, `r.2.1 = r₂₀ + r₂₃ + r₂₁`, `r.2.2 = r₃₀ + r₃₁`, and all
twelve split rates nonnegative. The Core definitions are `mutualInfo P = H(P.fst) + H(P.snd) −
H(P)`, `condMutualInfo P = H(AC) + H(BC) − H(ABC) − H(C)` and `condEntropy P = H(P) − H(P.snd)`
(`Core/Entropy.lean` lines 111–133). So the abbreviations are the stated information
quantities.

*Y₃ constant.* If `Fin kY₃ = Fin 1`, then H(W₀, Y₃) = H(W₀) and H(Y₃) = 0. So
`IW_Y3 = 0`, and `IV3_Y3 = H(V₃W₀) + H(W₀) − H(V₃W₀) − H(W₀) = 0`. Nonnegativity then forces
r₁₀ = r₂₀ = r₃₀ = 0 and r₁₃ = r₂₃ = r₃₁ = rp₃ = 0. Hence `r.2.2 = 0`, `r.1 = r₁₂ + r₁₁` and
`r.2.1 = r₂₁`.

*The bound.* Write I₁ = I(V₁;Y₁|W₀), I₂ = I(V₂;Y₂|W₀) and I₁₂ = I(V₁;V₂|W₀). The constraints
give r₁₂ + r₁₁ + rp₁ ≤ I₁. Since r₁₂ ≥ 0 they also give r₂₁ + rp₂ ≤ I₂, and rp₁ + rp₂ ≥ I₁₂.
For α ≥ 1,

  r.1 + α r.2.1 = (r₁₂ + r₁₁ + rp₁) + α(r₂₁ + rp₂) − (rp₁ + rp₂) − (α − 1) rp₂
                ≤ I₁ + α I₂ − I₁₂
                = Σ_{w₀} P(w₀) [ I(V₁;Y₁|W₀=w₀) + α I(V₂;Y₂|W₀=w₀) − I(V₁;V₂|W₀=w₀) ].

Conditionally on W₀ = w₀, the triple (V₁, V₂, X) has some law and `J` attaches the channel
to X (`J.pmf z = P.pmf z.1 * W.trans z.1.2.2.2 z.2`). So each bracket equals G(p(v₁, v₂, x |
w₀)) for the two-receiver BC (Y₁, Y₂), and the average is ≤ S_α. It does not matter that V₁
and V₂ share the coordinate W₁₂: G is defined for an arbitrary joint law of (U, V, X). The
right-hand set {r.2.2 = 0, r.1 + α r.2.1 ≤ S_α} is closed and contains the pre-closure set,
so it contains `marton3InnerBound W` (the `closure`). ∎

*Interpretation.* With Y₃ useless, the formal region allows only "Marton without a
superposition variable, with time sharing W₀" for (Y₁, Y₂). This is GEA's region (8)–(10).
The pairwise cloud W₁₂ cannot act as a superposition variable, because I₁₂ ≥ H(W₁₂|W₀)
charges its whole entropy as binning cost. A correct scheme bins only the satellites given
the clouds.

### 2. Cardinality and deterministic encoder (Claim 2)

GEA state this for α = 2.4 ("Using the perturbation method of [8], one can bound the
cardinality of U and V from above by |X|, and further assume that X is a deterministic
function of (U,V)"), but give no proof for weighted objectives. We give a self-contained
proof for every α ≥ 0.

Write G = H(Y₁) + αH(Y₂) + (α−1)H(V) + H(UV) − H(UY₁) − αH(VY₂).

*Deterministic encoder.* Write X = g(U, V, T) with T independent of (U, V) and finite. This is
the functional representation lemma, El Gamal–Kim Appendix B. Put V' = (V, T). Then
I(U;Y₁) is unchanged, I(V';Y₂) ≥ I(V;Y₂), and I(U;V') = I(U;V) + I(U;T|V) = I(U;V). So G does
not decrease for α ≥ 0, and X is now a function of (U, V').

*Reducing |U|.* Suppose |supp U| > |X|. Choose L ≠ 0 on supp U with Σ_u p(u, x) L(u) = 0 for
every x. Such an L exists because these are |X| linear constraints in more unknowns. Set
p_ε(u, v, x) = p(u, v, x)(1 + εL(u)) for ε ∈ [ε₋, ε₊]; the endpoints are where some
1 + εL(u) vanishes. They are finite and of opposite signs, since Σ_u p(u)L(u) = 0 and L ≠ 0.
This perturbation keeps p(x), the support of X given (U,V), and therefore H(Y₁) and H(Y₂). A
reweighting of a joint law by 1 + εM, restricted to a coordinate B, has
d²H(B)/dε² = −E_ε[(E_ε[M_ε|B])²]/ln 2, with M_ε = M/(1 + εM). Applying this term by term
(here M_ε depends on u only),

  ln 2 · G''(ε) = α E[E[M_ε|V Y₂]²] − (α − 1) E[E[M_ε|V]²] ≥ E[E[M_ε|V]²] ≥ 0,

multiplying E[E[M|VY₂]²] ≥ E[E[M|V]²] (Jensen) by α ≥ 0. So G is convex on [ε₋, ε₊] and
one endpoint has G ≥ G(0) with a smaller support of U. Repeat.

*Reducing |V|.* Use a multiplier L(v) with Σ_v p(v, x) L(v) = 0. The same computation gives
ln 2 · G'' = E[E[M_ε|U Y₁]²] + (α − (α − 1) − 1) E[M_ε²] = E[E[M_ε|UY₁]²] ≥ 0. Both reductions
keep X a deterministic function of (U, V). So sup G is a maximum over |U|, |V| ≤ |X|,
X = f(U, V), which is a compact domain on which G is continuous. ∎

### 3. Single-variable maps (Claim 3)

By relabelling the values of U and of V, which leaves G unchanged, the 16 maps
f : {0,1}² → {0,1} fall into 7 orbits: const 0, const 1, X = U, X = V, XOR, AND, OR.

* If f is constant, G = −I(U;V) ≤ 0.
* If X = V, then I(U;Y₁) ≤ I(U;X) = I(U;V), so G ≤ α I(X;Y₂) ≤ α C(X→Y₂).
* If X = U, then G = I(X;Y₁) + α I(V;Y₂) − I(V;X) with V → X → Y₂. The strong data-processing
  inequality gives I(V;Y₂) ≤ η_KL(X→Y₂) I(V;X) (Ahlswede–Gács 1976). In detail,
  I(V;Y₂) = Σ_v p(v) D(P_{Y₂|v} ‖ P_{Y₂}), and the KL contraction
  D(P_{Y₂|v} ‖ P_{Y₂}) ≤ η_KL D(P_{X|v} ‖ P_X) applies term by term. Also
  η_KL ≤ η_TV = |0.42 − 0.18| = 0.24 (Cohen–Kemperman–Zbăganu 1998; Polyanskiy–Wu 2017). At
  α = 2.35, α·0.24 = 0.564 ≤ 1, so G ≤ I(X;Y₁) ≤ C(X→Y₁) = 1 − h(0.3).

These bounds are 0.11892 and 0.11871 at α = 2.35, both far below τ. The XOR, AND and OR
orbits have no analytic bound here. They are certified by computer in Claim 4, and the
computer certificate rechecks the other four orbits independently.

### 4. The certificate (Claim 4)

The code is `code/marton_noW_gap.py`. Run it as `python marton_noW_gap.py 2.35`, or one
orbit at a time with `python marton_noW_gap.py 2.35 XOR`.

*Capacity side.* A grid plus Nelder–Mead search over |V| = 2 finds the optimum of
I(X;Y₁|V) + α I(V;Y₂). We round it to four decimals and evaluate it in `mpmath.iv` interval
arithmetic (80-bit, outward rounding), with intervals enclosing the decimal parameters. This
gives F_lo = 0.12131597166052306…; the interval width is about 10⁻²⁸.

*Marton side.* For each orbit representative f, G is a function of p ∈ Δ₄ (the law of (U,V)).
We split G = Φ + Ψ. The concave part is Φ = H(Y₁) + αH(Y₂) + (α−1)H(V) + H(UV); all its
coefficients are ≥ 0 for α ≥ 1, and each entropy is of a linear image of p. The convex part
is Ψ = −H(UY₁) − αH(VY₂). On a simplex S with centroid c, concavity gives Φ(p) ≤ T_c(p) :=
Σ_k a_k·CE(q_k(p) ‖ q_k(c)), the tangent plane (a cross-entropy). T_c + Ψ is convex, so its
maximum over S is attained at a vertex. Hence

  max_S G ≤ max_{w ∈ vert(S)} [ T_c(w) + Ψ(w) ].

If a coordinate of q_k(c) is 0, it is 0 on all of S, so it is dropped. We start from Δ₄ and
bisect the longest edge until every leaf satisfies bound ≤ τ − 10⁻⁹, with τ = F_lo − 10⁻⁷.
Vertices are dyadic, so they are exact in binary. Every accepted leaf is then **re-evaluated in
`mpmath.iv` interval arithmetic** (60-bit, channel entries and α as decimal-enclosing
intervals). The certificate requires the interval upper bound to be ≤ τ.

Results at α = 2.35, τ = 0.1213158717. Every orbit passed the interval recheck:

| orbit (f(00),f(01),f(10),f(11)) | orbit size | leaf simplices | max interval bound |
|---|---|---|---|
| const 0 (0,0,0,0) | 1 | 2 243 | 0.121297099 |
| const 1 (1,1,1,1) | 1 | 2 243 | 0.121297099 |
| AND (0,0,0,1) | 4 | 19 212 | 0.121315636 |
| OR (0,1,1,1) | 4 | 18 374 | 0.121315755 |
| XOR (0,1,1,0) | 2 | 23 562 | 0.121313342 |
| X=U (0,0,1,1) | 2 | 46 320 | 0.121315706 |
| X=V (0,1,0,1) | 2 | 31 517 | 0.121315838 |

The "max interval bound" is close to τ by construction, because subdivision stops as soon as
a leaf is below τ. It is not an estimate of S_α; see Claim 8.

### 5. Disproof (Claim 5)

*Capacity side.* W is physically degraded: X → Y₁ → Y₂, with Y₃ ≡ 0. Superposition coding
(Cover 1972; Bergmans 1973; El Gamal–Kim Ch. 5) achieves every (R₁, R₂) with
R₁ < I(X;Y₁|V) and R₂ < I(V;Y₂). Receiver 1 can decode the cloud because I(V;Y₂) ≤ I(V;Y₁).
For R₃ = 0, `IsBC3Achievable` takes M₃ = `Nat.max 1 ⌊2⁰⌋` = 1 and a constant `dec₃`. Its
error criterion is then the two-receiver average error, which random coding drives to 0 for
all large n with M_j = ⌊2^{nR_j}⌋ messages. So every point (R₁, R₂, 0) strictly inside
belongs to `{r | IsBC3Achievable W r.1 r.2.1 r.2.2}`, and the closure contains (R₁*, R₂*, 0).

*Inner-bound side.* By Claim 1 with α = 2.35, every point r of `marton3InnerBound W` has
r.1 + 2.35·r.2.1 ≤ S_2.35. Claims 2–4 give S_2.35 ≤ τ < 0.1213159716 ≤ R₁* + 2.35·R₂*. So
(R₁*, R₂*, 0) is not in the inner bound, and `bc3CapacityRegion W ≠ marton3InnerBound W`. ∎

*Lean status.* Formalising this needs (a) superposition-coding achievability, which is not in
`Bridge` and is a large project, and (b) the perturbation lemma plus a verified version of the
branch and bound. Neither was attempted; this attempt edits nothing under `lean/`.

### 6. The `.md` statement (Claim 6)

The `.md` region constrains R₁₀ + R₂₀ + R₃₀ ≤ min_j I(W₀;Y_j), which is 0 when Y₃ is constant,
and R₃₁ + R'₃ ≤ I(U₃;Y₃|W₀) = 0. So R_j = R_j1, R'₃ = 0, R'₁ + R'₂ ≥ I(U₁;U₂|W₀), and
R_j + R'_j ≤ I(U_j;Y_j|W₀) for j = 1, 2. The computation of §1 gives
R₁ + αR₂ ≤ I(U₁;Y₁|W₀) + αI(U₂;Y₂|W₀) − I(U₁;U₂|W₀) ≤ S_α. The certificate applies
unchanged. ∎

### 7. Proposed correction (Claim 7)

**The test any repair must pass.** Let Y₃ be constant. The 3-receiver capacity region is then
{0} × (two-receiver capacity region of (Y₁, Y₂)). A "natural Marton extension" must reduce to
the two-receiver Marton region *with* a superposition variable. Otherwise GEA's
degraded-channel gap refutes it, as above. So we need a layer that receivers 1 and 2 decode but
receiver 3 does not, whose codebook is superposed rather than binned at full cost.

**Proposed region (literature-backed).** Use Padakandla–Pradhan's UM region
(arXiv:1207.3146v6, §II-D), with κ ≡ 0. Its layers are a public
codebook W decoded by all receivers; semi-private codebooks U₁₂, U₂₃, U₃₁, each superposed on
W, binned with rates S_ij and decoded by its pair; and private codebooks V_j superposed on
(W, U_ij, U_jk) and binned with rates S_j. Message j is split as R_j = K_j + K_jk + L_ij + T_j.
The region is the closure of the union over p(q, w, u₁₂, u₂₃, u₃₁, v₁, v₂, v₃, x) of the rate
triples for which nonnegative (K_j, K_ij, L_ij, S_ij, T_j, S_j) satisfy PP's covering
constraints (1)–(6) and decoding constraints (7)–(11). **The strict inequalities must be
replaced by non-strict ones.** PP's eq. (1) "S_i > 0" and their strict decoding inequalities
make the literal region *empty* whenever some output is independent of the input: eq. (7)
for that receiver would demand 0 > T_i + S_i ≥ S_i > 0.

*It passes the test [sketch].* Let Y₃ be constant. Receiver 3's constraints force
T₃ = S₃ = 0. They also force K₁ + K₂ + K₃ = 0, given U₂₃, U₃₁ and V₃ are W-measurable, which
we choose. So W acts as time sharing. The remaining constraints are El Gamal–Kim's rate-split
form of Marton's region with superposition variable U₁₂, private codebooks V₁ and V₂, and
binning S₁ + S₂ ≥ I(V₁;V₂|U₁₂, Q). For a degraded pair this contains superposition coding:
take U₁₂ = cloud, V₁ = X and V₂ constant.

*It contains the degraded 3-receiver capacity region [sketch].* Take X → Y₁ → Y₂ → Y₃ with
capacity R₃ ≤ I(A;Y₃), R₂ ≤ I(B;Y₂|A), R₁ ≤ I(X;Y₁|B), A → B → X. Put W = A carrying M₃,
U₁₂ = B carrying M₂, V₁ = X carrying M₁, and everything else constant.

*Consequence.* With a constant output, the corrected `Statement` specialises to "two-receiver
Marton region (with W) = capacity" for every DM-BC. That is the famous open problem, so the
corrected statement is non-trivial and is not refuted by GEA's example. *(Reviewer,
2026-11-27: "specialises to" needs the unproved inclusion UM-slice ⊆ Marton-with-W; see the
note under Claim 7. Huang–Liu–Liu, arXiv:2608.19869, unrefereed, claim a negative answer to
the two-receiver question.)*

**Caveat (Claim 9).** PP's Theorem 3 (vector additive channel, cost on X₁) and Theorem 5
(non-additive channel, costs on all three input bits) prove the UM region strictly suboptimal
*for cost-constrained* 3-DBCs, using coset codes. The catalog statement has no cost, so PP do
not refute the corrected statement directly. Turning their examples into cost-free ones is,
as far as we know, not done in the literature. The expert reviewer should decide whether a
"UM = capacity (no cost)" entry is worth posing, given that structured codes are expected to
win. A defensible alternative is to keep the statement and ask the weaker, still-open
"Marton-type region with pairwise clouds = capacity *for a specified subclass*". Another is to
pose the formal problem as the cost-free version of PP's question: does some cost-free 3-DMBC
have capacity strictly larger than the UM region? We have not formalised either option.

## Verification

* Claim 1: line-by-line against `lean/InfoTheory/Problems/BroadcastChannelThreeReceivers.lean`
  (lines 45–89) and the Core definitions (`Core/Entropy.lean` lines 111–133).
* Claim 2: proof written out above. The second-derivative identity is elementary. GEA
  attribute the perturbation method to Gohari–Anantharam 2012, which we did not read.
* Claim 4: `code/marton_noW_gap.py`. Its parts are a float64 branch and bound, an
  interval-arithmetic recheck of every leaf (`iv_bound`), and an interval evaluation of the
  capacity-side point (`cap_lower_bound_interval`). Final runtimes with the committed code
  (one process per orbit, `nice`) were const 0 4 s, const 1 5 s, AND 34 s, OR 32 s, XOR 43 s,
  X=U 81 s and X=V 52 s. An earlier run on a heavily loaded machine, which differed only in
  the capacity-side parameters being binary rather than decimal-enclosing intervals, produced
  identical leaf counts and bounds. Total runtime is a few minutes.
* Claim 8: GEA's channel and numbers reproduced (F_2.4 = 0.1228622, 2.4·C_Z = 0.1214546, versus
  "0.1229..." and "0.1215..."). The S_2.35 estimate comes from `code/marton_noW_numerics.py`,
  40 Nelder–Mead starts per orbit representative, about 10 s. It is not part of the
  certificate. The per-orbit maxima are: const 0 and const 1 give 0; X=U gives
  C_Y = 0.1187091; X=V, XOR, AND and OR give 0.1189243 = 2.35·C_Z. The XOR, AND and OR maxima
  are attained on the boundary where U is constant and X = V.
* Not checked: a Lean formalisation (see §5); the cardinality claim of Claim 2 for the full
  Marton region with W (not needed).

### Reviewer note (claude-opus-5-5, independent review, 2026-11-27)

Verdict: the frozen `Statement` is false, as claimed. I checked every `[proved]` claim (1–6)
independently, so the status is now `verified`. The disproof still rests on two things that
are not formalised: the textbook superposition-coding theorem and mpmath's directed-rounding
`log`. The reviewer's independent certificate (all 16 maps, no orbit reduction, threshold
0.1201, about 17 min) is committed as `code/reviewer_indep_certificate.py`
(`python reviewer_indep_certificate.py 47/20 1201/10000`, ending in "ALL 16 MAPS CERTIFIED:
S_alpha <= 0.1201"). Other reviewer scripts and run logs are in `code/review/` (except the random-LP check and the
GEA-point evaluation, which were not kept); they are described below.

* **Claims 1 and 6 (reduction).** I re-derived both from the Lean file (lines 42–89) and from
  `Core/Entropy.lean`, where `condMutualInfo` of (A,B,C) is I(A;B|C) and `condEntropy` of
  (A,B) is H(A|B). With `Fin kY₃ = Fin 1`, IW_Y3 = IV3_Y3 = 0, which forces r₁₀ = r₂₀ = r₃₀ =
  r₁₃ = r₂₃ = r₃₁ = rp₃ = 0. A direct argument gives more. Put Q := W₀, U := V₁, V := V₂.
  Every pre-closure point then satisfies GEA's (8)–(10); the sum constraint uses r₁₂ ≥ 0 and
  rp₁ + rp₂ ≥ I₁₂. Conversely, taking W₁₂ = W₁₃ = W₂₃ = U₃ constant realises every such point.
  So the (R₁, R₂) slice *equals* Marton-without-W, and no auxiliary can play the role of W:
  W₀ carries no rate, and I₁₂ ≥ H(W₁₂|W₀). A random-LP sanity check of this algebra (2000
  instances) found no violation beyond 2·10⁻¹⁶. The `.md` region reduces the same way.
* **Claim 5 (operational side).** With R₃ = 0, M₃ = `Nat.max 1 ⌊2⁰⌋` = 1, so
  `IsBC3Achievable` is exactly the two-receiver average-error criterion. Superposition
  coding then applies to the physically degraded chain X→Y₁→Y₂. Correct.
* **GEA (arXiv:1006.5166v2, read in full).** Claim 1, the channel, α = 2.4 and the numbers
  "0.1229..." and "0.1215..." are quoted correctly. GEA's gap is numerical only ("Numerical
  simulations show"). They cite [8] for the cardinality reduction without proving it for the
  weighted objective. Their region (8)–(10) includes Q. Their own superposition point
  P(V=0,X=1) = 0.41, P(V=1,X=0) = 0.48, P(V=1,X=1) = 0.11 evaluates to 0.1228561 in interval
  arithmetic.
* **Claim 2.** I checked the identity d²H(B)/dε² = −E[E[M_ε|B]²]/ln 2 and both expansions.
  Perturbing U gives αE[E[M|VY₂]²] − (α−1)E[E[M|V]²] ≥ E[E[M|V]²]; perturbing V gives
  E[E[M|UY₁]²]. In the functional-representation step, I(U;T|V) = 0 because T ⊥ (U,V). The
  proof is correct for every α ≥ 0. A non-rigorous cross-check used |U| = |V| = 3 with a
  *random* p(x|u,v) (`code/review/numerics_check.py`, log `numerics.txt`); multi-start optimisation gives the same values as the binary
  deterministic search: S_2.35 ≈ 0.1189243 and S_2.4 ≈ 0.1214546, both equal to α·C_Z.
* **Claim 3.** Checked: data processing covers X = V, and the SDPI with η_KL ≤ η_TV = 0.24
  covers X = U.
* **Claim 4: soundness of `marton_noW_gap.py`.**
  - The DC bound is valid. H(q) ≤ CE(q‖r) holds for every distribution r; T_c is linear and
    Ψ is convex, so the maximum is at a vertex; Φ has nonnegative coefficients for α ≥ 1.
  - The leaves cover Δ₄. I replayed the float search and audited it in exact Fractions
    (`code/review/exactness_check.py`, log `exactness.txt`):
    every vertex is an exact dyadic (denominator ≤ 2¹³, depth ≤ 34) summing exactly to 1,
    and every midpoint is exact, so rounding leaves no gaps.
  - Every leaf is rechecked in interval arithmetic with decimal-enclosing α and channel
    entries.
  - My re-run reproduces the table exactly (log `code/review/author_run_235.txt`).
  - Harmless: `iv_bound` merges vertex bounds with Python `max`, which would silently drop a
    NaN. A NaN cannot occur here, because every nonzero log argument is a strictly positive
    interval.
* **Independent certificate (own code, nothing reused).** Channel entries are exact
  Fractions, including the composed X→Y₂; vertices are Fractions; logs use mpmath `iv` at
  100 bits. All 16 maps were run with no orbit reduction, at a looser threshold
  τ' = 0.1201. Result: all 16 maps pass. There are 522 736 leaves in total, the largest
  interval upper bound is 0.120098989, and the run took 1018 s (log `code/review/indep_235.txt`). The capacity side,
  recomputed independently, gives R₁* + 2.35R₂* ∈ [0.121315971660523062833, …], with R₁* and
  R₂* matching Claim 4.
  So S_2.35 ≤ 0.1201 < 0.12131597, a margin of 1.2·10⁻³ rather than 10⁻⁷.
* **α = 2.4 (coordinator update).** I re-ran `python marton_noW_gap.py 2.4`. All 7 orbits pass
  the interval recheck, and the run prints "S_alpha <= 0.1228621348 < 0.1228622348 <=
  F_alpha" (314 s; log `code/review/author_run_24.txt`). The update is confirmed, but only by re-running the author's code.
* **Claims 7–9.** I read Padakandla–Pradhan (arXiv:1207.3146v6): §II-D eqs. (1)–(11) and
  Theorems 3 and 5, whose costs are κ = 1{x₁=1} and κ_j = 1{x_j=1}. The attempt describes
  them correctly. The literal strict inequalities do make the UM region empty when an output
  is constant.
  - **Gap in Claim 7.** The sketch proves only "UM slice ⊇ two-receiver Marton-with-W". The
    words "reduces exactly" and "implies the two-receiver question" also need "⊆". Partial
    step: with non-strict inequalities, receiver 3's eq. (11) together with eq. (2) forces
    W, U₂₃ and U₃₁ to carry no message. U₁₂ can still be binned, though, so "⊆" is not
    immediate.
  - **Omission.** The attempt does not mention Huang–Liu–Liu (arXiv:2608.19869, unrefereed;
    audited in `attempts/marton-inner-bound-tightness/`). They claim two-receiver Marton is
    strictly suboptimal. That is stronger evidence than Claim 9 that the proposed
    correction is false.
  - I added bracketed notes at the Summary, at Claim 7 and in §7. Labels are unchanged.
* **Not checked:** GEA's journal details (I read arXiv v2 only); Gohari–Anantharam [8]; the
  Dead-ends remark that profiles exclude XOR. No Lean proof exists.

## Dead ends

* **Hoping the formal region was merely loose but still tight on degraded channels.** It is
  not. The useless-receiver specialisation shows the W₁₂ cloud is unusable for superposition.
* **Using the Jog–Nair inequality.** For binary-input BCs it gives
  I(U;Y₁) + I(V;Y₂) − I(U;V) ≤ max{I(X;Y₁), I(X;Y₂)}. We tried to bound the weighted
  objective G = [I(U;Y₁) + I(V;Y₂) − I(U;V)] + (α−1) I(V;Y₂) with it. The resulting bound
  max_p [I(X;Y₁) + (α−1) I(X;Y₂)] always dominates the capacity-side value, so no gap
  follows. A weighted Jog–Nair inequality, G ≤ max{I(X;Y₁), α I(X;Y₂)}, is supported
  numerically (Claim 8) but we could not prove it. GEA's profile argument (their Thm. 1,
  bullets 1–2, stated for α = 1) seems to carry over to any α. The modification changes only
  the U-term, which has coefficient 1, and both channels X→Y₁ and X→Y₂ here are strictly
  positive. That would exclude the XOR orbit, but we have not written the argument out and
  do not rely on it. The AND/OR orbits are not excluded by profiles. The computer certificate
  sidesteps all of this.
* **Certifying at GEA's own α = 2.4.** We did not run it during the attempt. The margin there
  is 0.0014 instead of 0.0024, so it would need more simplices. *(Update, 2026-11-26,
  coordinator re-run: `code/marton_noW_gap.py` with its default α = 2.4 completes in about
  4 min. All 7 orbits pass the interval recheck, and it prints
  "S_alpha <= 0.1228621348 < 0.1228622348 <= F_alpha", so the gap is certified at GEA's α too.)* Our α = 2.35 is close to C_Y/C_Z ≈ 2.346, which
  maximises the margin, and any single α suffices for the disproof. GEA's α = 2.4 numbers are
  reproduced only numerically (Claim 8).

## References

* No earlier attempts exist in `attempts/broadcast-channel-three-receivers/`.
* A. Gohari, A. El Gamal, V. Anantharam, "On Marton's inner bound for the general broadcast
  channel," arXiv:1006.5166v2 (2011), §II-A Claim 1 and its proof in §III. IEEE Trans. IT 60(7),
  2014. Read in full (arXiv v2). Quote: "Claim 1: There are degraded broadcast channels for which
  Marton's private message inner bound without W is strictly contained in the capacity region
  of the channel". The region is their eqs. (8)–(10), with time sharing Q. Evidence:
  "Numerical simulations show that the maximum is equal to 0.1215... < 0.1229...".
* A. Gohari, V. Anantharam, "Evaluation of Marton's inner bound for the general broadcast
  channel," IEEE Trans. IT 58(2), 2012. This is GEA's ref. [8], cited for the perturbation
  method; we did not read it here, and our Claim 2 proof is self-contained.
* A. Padakandla, S. S. Pradhan, "Achievable rate region for three user discrete broadcast
  channel based on coset codes," arXiv:1207.3146v6 (2015). We read the abstract, §II-D (UM
  region, eqs. (1)–(11), Thm. 2), Example 1 with Thm. 3, and Example 2 with Lemmas 3–4 and
  Thm. 5.
* R. Ahlswede, P. Gács, "Spreading of sets in product spaces and hypercontraction of the Markov
  operator," Ann. Probab. 4 (1976). J. E. Cohen, J. H. B. Kemperman, Gh. Zbăganu, *Comparisons of
  Stochastic Matrices*, Birkhäuser 1998. Y. Polyanskiy, Y. Wu, "Strong data-processing
  inequalities for channels and Bayesian networks," 2017 (η_KL ≤ η_TV).
* T. Cover, "Broadcast channels," IEEE Trans. IT 18 (1972). P. Bergmans, "Random coding theorem
  for broadcast channels with degraded components," IEEE Trans. IT 19 (1973). A. El Gamal,
  Y.-H. Kim, *Network Information Theory*, 2011, Ch. 5 and Ch. 8 (Marton with W, rate-split
  form), Appendix B (functional representation lemma).
* V. Jog, C. Nair, "An information inequality for the BSSC broadcast channel," ITA 2010 (as
  cited by GEA, ref. [13]; not read here).
