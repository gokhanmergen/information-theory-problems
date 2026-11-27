---
problem: degraded-message-sets-bc-three-receivers
date: 2026-11-26
attempter: claude
model: claude-opus-5-5
type: partial-result
status: unverified
---

## Summary

**Audit:** no catalog error. `nairElGamalInnerBound` matches Nair–El Gamal (NE) 2009 Prop. 5
line by line. We re-derived Prop. 5 from NE's code constraints (15)–(22) by Fourier–Motzkin
elimination, both by hand and by an LP cross-check. It contains the multilevel capacity region
(NE Thm. 1) and the Borade–Zheng–Trott / Körner–Marton region. A literal Python transcription
of the Lean formula reproduces NE's Fig. 2 point (½, ½), which lies outside the BZT region.

**New result:** a class of channels on which the NE inner bound is the capacity region and
none of the known sufficient conditions hold. In a *crossed degraded product*, X = (A, B):
receiver 2 sees only A, receiver 3 sees only B, and receiver 1 sees both through degraded
versions of what receivers 2 and 3 see. Capacity there is

  ∪ { R₀ ≤ min(I(A;Y₂|Q), I(B;Y₃|Q)),  R₀+R₁ ≤ I(A;Y₁ᴬ|Q) + I(B;Y₁ᴮ|Q),
      2R₀+R₁ ≤ I(A;Y₂|Q) + I(B;Y₃|Q) },

and it equals the NE region. When the degradations are non-trivial, Y₁ is less noisy than
neither Y₂ nor Y₃, the channel is not multilevel, and Y₂ and Y₃ are incomparable. The NE constraint
2R₀ + R₁ ≤ … is a genuine capacity face here. We also record the easy, probably folklore,
observation that NE is tight whenever Y₂ is less noisy than Y₃ or vice versa.

## Approach

1. Compare the Lean definition with Prop. 5 in arXiv:0712.3327v2 (read in full) and check the
   substitution V₂ = (U₁, U₂), V₃ = (U₁, U₃).
2. Redo the Fourier–Motzkin step that NE relegate to their Appendix II. A wrong elimination
   would make the catalog region not achievable, or not NE's region.
3. Check the sanity inclusions the coordinator asked for (multilevel and Körner–Marton), then
   run a numerical transcription test.
4. Look for channel classes that the known results (Thm. 1, Prop. 7) miss but where a converse
   is easy. Products whose components are degraded in *opposite* directions for different
   receivers are a natural place to look. Indirect decoding is designed for the situation
   where the common-message receivers see different parts of the input.

## Claims

1. **[proved]** (Transcription.) The pre-closure set of `nairElGamalInnerBound W` equals the
   union in NE Prop. 5, eq. (14). The ten Lean conjuncts are, in order, the ten scalar
   inequalities of (14), with I(U₂;Y₂) ↦ I(V₂;Y₂), I(X;Y₁|U₂,U₃) ↦ I(X;Y₁|U₁,U₂,U₃), and so on.
2. **[proved]** (Fourier–Motzkin.) NE's code constraints are (15)–(22) together with
   0 ≤ S_i, S₂ ≤ T₂, S₃ ≤ T₃ and R₁ = S₁ + S₂ + S₃. Eliminating S₁, S₂, S₃, T₂, T₃ gives
   exactly (14). The only redundancies used are L₂₃ ≤ L₂ and L₂₃ ≤ L₃, where L₂ = I(X;Y₁|U₂),
   L₃ = I(X;Y₁|U₃), L₂₃ = I(X;Y₁|U₂,U₃). Both hold for every distribution. So there is no
   transcription or elimination error in Prop. 5 or in the Lean statement.
3. **[proved]** (Sanity inclusions.) Setting U₃ constant in Lean, which gives V₃ ≅ U₁, yields
   NE eq. (23), which contains the multilevel capacity region of Thm. 1. Setting U₂ and U₃
   constant yields a region containing BZT, i.e. the straightforward Körner–Marton extension.
   With NE's achievability and the Thm. 1 converse, `dms3CapacityRegion W =
   nairElGamalInnerBound W` holds for every multilevel W. So the `Statement` is not vacuous.
4. **[proved]** (Numerical transcription test.) On NE's Fig. 2 channel, take U₁ = X₂, U₂ = X₁,
   U₃ constant and X uniform. The Lean quantities are I(V₂;Y₂) = 1, I(V₃;Y₃) = ½,
   I(V₂;V₃|U₁) = 0, I(X;Y₁|V₂) = 0, I(X;Y₁|V₃) = I(X;Y₁|U₁) = ½, I(X;Y₁|V₂,V₃) = 0 and
   I(X;Y₁) = 3/2. So (½, ½) satisfies all ten constraints, six with equality. NE Prop. 3
   shows BZT allows at most R₁ = 5/12 at R₀ = ½.
5. **[proved]** (New tight class: crossed degraded products.) Let X = (A, B) and
   Y₁ = (Y₁ᴬ, Y₁ᴮ), with p(y₁, y₂, y₃ | a, b) = p(y₁ᴬ, y₂ | a) · p(y₁ᴮ, y₃ | b). Assume Y₁ᴬ is
   a stochastically degraded version of Y₂ given A, and Y₁ᴮ of Y₃ given B. Then
   `dms3CapacityRegion W = nairElGamalInnerBound W = closure ∪_{p(q)p(a|q)p(b|q)} O(p)`, with
   O(p) = { (R₀, R₁) ≥ 0 : R₀ ≤ I(A;Y₂|Q), R₀ ≤ I(B;Y₃|Q),
   R₀ + R₁ ≤ I(A;Y₁ᴬ|Q) + I(B;Y₁ᴮ|Q), 2R₀ + R₁ ≤ I(A;Y₂|Q) + I(B;Y₃|Q) }.
   This uses NE's achievability theorem (Prop. 5) and a self-contained weak converse.
6. **[proved]** (Ordered common receivers.) Suppose Y₂ is less noisy than Y₃, i.e.
   I(U;Y₂) ≥ I(U;Y₃) for all p(u, x), or the reverse. Then the NE region equals the
   two-receiver Körner–Marton region of (Y₁, Y₃), resp. (Y₁, Y₂), and this is the capacity
   region. Almost certainly folklore: it is the two-receiver problem in disguise.
7. **[proved]** In the crossed product, Y₁ is less noisy than neither Y₂ nor Y₃ unless the
   degradations are trivial. The channel is not multilevel, and Y₂, Y₃ are not ordered, so
   Thm. 1, Prop. 7 and Claim 6 do not apply. In the symmetric BSC instance (a = 0.05,
   b = 0.11) the capacity region has three faces. One of them, 2R₀ + R₁ = 2(1 − h(a)), comes
   from the "2R₀ + R₁" inequality of (14), so that inequality is essential.
8. **[heuristic]** In the same instance, the straightforward Körner–Marton (BZT) region is
   strictly smaller than capacity. Multi-start optimisation of 1.5·R₀ + R₁ over BZT with
   |U| = 5 finds at most 1.070405, versus 1.213687 at the capacity corner. The best value
   found is attained at U = X, i.e. 1.5·min_j I(X;Y_j) = 1.5 c_s. This is not certified.

## Details

### 1–2. Transcription and Fourier–Motzkin

*Substitution.* Suppose (U₁, U₂, U₃, X) satisfies both of NE's Markov chains. Then
I(U₁U₂;Y₂) = I(U₂;Y₂), I(U₁U₂;U₁U₃|U₁) = I(U₂;U₃|U₁), I(X;Y₁|U₁U₂) = I(X;Y₁|U₂) and
I(X;Y₁|U₁U₂U₃) = I(X;Y₁|U₂U₃). The last uses U₁ → (U₂,U₃) → Y₁, which follows from
U₁ → U₂ → (U₃, X). Conversely, for an arbitrary Lean law, (U₁, V₂, V₃, X) satisfies both chains
trivially, because U₁ is a function of V₂ and of V₃. So the two unions coincide. This is NE's
Remark 1 after Prop. 5, and the problem file's formalisation note is correct.
(Typo in the source: Prop. 5 says "A rate pair (R₁, R₂) is achievable"; it should read
(R₀, R₁). This is immaterial.)

*Elimination.* Write I₂ = I(U₂;Y₂), I₃ = I(U₃;Y₃), I₂₃ = I(U₂;U₃|U₁), K = I(X;Y₁) and
L₁ = I(X;Y₁|U₁). Eliminating T₂ uses (15), (21) and S₂ ≤ T₂. Then eliminating T₃ leaves:
S₂ ≤ I₂ − R₀, S₃ ≤ I₃ − R₀ and S₂ + S₃ ≤ I₂ + I₃ − 2R₀ − I₂₃. Substitute S₁ = R₁ − S₂ − S₃
into (16)–(20). This gives R₀ + R₁ ≤ K, R₁ ≤ L₁, S₂ ≥ R₁ − L₂, S₃ ≥ R₁ − L₃,
S₂ + S₃ ≥ R₁ − L₂₃ and S₂ + S₃ ≤ R₁. Eliminating S₂ and then S₃ produces the ten inequalities
of (14) plus the following, each redundant:
2R₀ + R₁ ≤ I₂ + I₃ − I₂₃ + L₂ (by L₂₃ ≤ L₂);
2R₀ + R₁ ≤ I₂ + I₃ − I₂₃ + L₃ (by L₂₃ ≤ L₃);
2R₀ + R₁ ≤ I₂ + I₃ + L₂₃;
3R₀ + R₁ ≤ 2I₂ + I₃ − I₂₃ + L₂₃;
3R₀ + 2R₁ ≤ 2I₂ + I₃ − I₂₃ + L₂ + L₂₃;
R₀ + R₁ ≤ I₂ + L₂ + L₂₃;
R₀ ≤ I₂ + L₂₃.
Each is a nonnegative combination of members of (14), or follows from L₂₃ ≤ L₂, L₃.
`code/ne_region_check.py` (`fm_check`) confirms this by LP. For random channels and random
laws, it compares feasibility of (15)–(22) in (S, T) with membership in the ten Lean
constraints. It ran 12 000 samples (5 387 inside the region, 6 613 outside) with 0 mismatches.

### 3. Inclusions

*Multilevel.* Take Lean `k₃ = 1`. Then I(V₂;V₃|U₁) = 0, I(V₃;Y₃) = I(U₁;Y₃),
I(X;Y₁|V₃) = L₁ and I(X;Y₁|V₂V₃) = I(X;Y₁|V₂). Inequality (14) reduces to NE (23):
R₀ ≤ min{I(V₂;Y₂), I(U₁;Y₃)}, R₁ ≤ L₁ and
R₀ + R₁ ≤ min{K, I(V₂;Y₂) + I(X;Y₁|V₂), I(U₁;Y₃) + L₁}. The other three inequalities are sums
of these.

Now fix p with U₁ → U₂ → X, let m = min{I(U₁;Y₃), I(U₂;Y₂)} and
s = min{I(U₁;Y₃) + L₁, I(U₂;Y₂) + L₂}. The Thm. 1 region is the polygon
conv{(0,0), (m,0), (m, s−m), (0,s)}. The point (m, s−m) satisfies (23) with the same p:

* If m = I(U₁;Y₃), then s − m ≤ L₁.
* If m = I(U₂;Y₂), then s − m ≤ L₂ ≤ L₁, by the Markov chain.
* m + (s − m) ≤ I(U₁;Y₃) + L₁ ≤ I(U₁;Y₁) + L₁ = K, by degradedness of Y₃ w.r.t. Y₁.

The point (0, s) satisfies s ≤ K, so it lies in the region with all auxiliaries constant.
The Lean region is convex: the problem file's time-sharing note checks out, since Q can be
absorbed into U₁ and therefore into V₂ and V₃. So it contains the polygon.

*BZT.* Take U₁ = U and `k₂ = k₃ = 1`. Then (14) becomes R₀ ≤ min(I(U;Y₂), I(U;Y₃)),
R₁ ≤ I(X;Y₁|U) and R₀ + R₁ ≤ I(X;Y₁), with the remaining inequalities implied. This contains
{R₀ ≤ min_j I(U;Y_j), R₁ ≤ I(X;Y₁|U)}.

### 5. Crossed degraded products

*Achievability.* In Lean terms take U₁ = Q, U₂ = A and U₃ = B, with
P(q, a, b, x) = p(q)p(a|q)p(b|q)·1[x = (a,b)]. Write s₂ = I(A;Y₂|Q), s₃ = I(B;Y₃|Q),
w_A = I(A;Y₁ᴬ|Q) and w_B = I(B;Y₁ᴮ|Q). Degradedness gives w_A ≤ s₂ and w_B ≤ s₃. The
product structure and conditional independence give:

* I(V₂;Y₂) = I(QA;Y₂) ≥ s₂ and I(V₃;Y₃) ≥ s₃;
* I(V₂;V₃|U₁) = I(A;B|Q) = 0;
* I(X;Y₁|V₂) = w_B and I(X;Y₁|V₃) = w_A;
* I(X;Y₁|U₁) = w_A + w_B, I(X;Y₁|V₂,V₃) = 0, and I(X;Y₁) ≥ w_A + w_B.

The constraints of (14) are monotone in these terms, so they contain the system
R₀ ≤ min(s₂, s₃), 2R₀ ≤ s₂ + s₃, R₁ ≤ w_A + w_B, R₀ + R₁ ≤ min(w_A + w_B, s₂ + w_B, s₃ + w_A),
2R₀ + R₁ ≤ s₂ + s₃ and 2R₀ + 2R₁ ≤ s₂ + s₃ + w_A + w_B. Using w ≤ s, this is exactly O(p).

*Converse.* Fix a sequence of codes with error → 0. The error criterion depends on the joint
law of (Y₁, Y₂, Y₃), but vanishing joint error is equivalent to vanishing error at each
receiver. So only the marginals p(y_j|x) matter, and we may assume physical degradedness
A → Y₂ → Y₁ᴬ and B → Y₃ → Y₁ᴮ. The encoder is deterministic, so Xⁿ = (Aⁿ, Bⁿ) is a function of
(M₀, M₁). By Fano, with ε_n → 0:

1. nR₀ ≤ I(M₀;Y₂ⁿ) + nε_n ≤ Σ_i I(A_i;Y₂ᵢ) + nε_n, and likewise nR₀ ≤ Σ_i I(B_i;Y₃ᵢ) + nε_n.
2. n(R₀ + R₁) ≤ I(Xⁿ;Y₁ⁿ) + nε_n ≤ Σ_i [I(A_i;Y₁ᴬᵢ) + I(B_i;Y₁ᴮᵢ)] + nε_n. For a product
   channel, I(AB;Y₁ᴬY₁ᴮ) ≤ H(Y₁ᴬ) + H(Y₁ᴮ) − H(Y₁ᴬ|A) − H(Y₁ᴮ|B) even if A and B are dependent.
3. nR₁ ≤ I(M₁;Y₁ⁿ|M₀) + nε_n ≤ I(Xⁿ;Y₁ⁿ|M₀) + nε_n
   ≤ I(Aⁿ;Y₁ᴬⁿ|M₀) + I(Bⁿ;Y₁ᴮⁿ|M₀) + nε_n, by the same entropy split.
   Degradedness conditioned on M₀ gives I(Aⁿ;Y₁ᴬⁿ|M₀) ≤ I(Aⁿ;Y₂ⁿ|M₀) = I(Aⁿ;Y₂ⁿ) − I(M₀;Y₂ⁿ)
   ≤ Σ_i I(A_i;Y₂ᵢ) − nR₀ + nε'_n, and the same for B. Hence
   n(2R₀ + R₁) ≤ Σ_i [I(A_i;Y₂ᵢ) + I(B_i;Y₃ᵢ)] + nε''_n.

All four bounds depend only on the per-letter marginals p(a_i) and p(b_i). Let Q be uniform
on [n] and let A, B be conditionally independent given Q with those marginals. The rate pair
then lies in O(p) up to o(1). Passing to the closure finishes the proof. ∎

*Symmetric instance.* Take A, B ∈ {0,1}, Y₂ = BSC_a(A), Y₃ = BSC_a(B) and
Y₁ = (BSC_b(A), BSC_b(B)) with b > a. Uniform inputs maximise every term, so
C = {R₀ ≤ c_s, R₀ + R₁ ≤ 2c_w, 2R₀ + R₁ ≤ 2c_s}, with c_s = 1 − h(a) and c_w = 1 − h(b). For
a = 0.05 and b = 0.11, c_s = 0.713603 and c_w = 0.500084. The three corners are (0, 2c_w),
P* = (2(c_s − c_w), 2(2c_w − c_s)) = (0.427038, 0.573130), and (c_s, 0). The scheme behind
P* is simple: two independent codebooks Aⁿ(m₀, s₂) and Bⁿ(m₀, s₃), each decoded by its
common-message receiver (indirect decoding is not even needed here), and receiver 1 decodes
jointly across both components. `code/crossed_product.py` evaluates the literal Lean formula
at this law and confirms P* satisfies all ten constraints. The active ones are R₀ + R₁ ≤ I(X;Y₁)
and 2R₀ + R₁ ≤ I(V₂;Y₂) + I(V₃;Y₃) + I(X;Y₁|V₂V₃) − I(V₂;V₃|U₁) = 2c_s.

*Why the known results do not cover it (Claim 7).* Work in the symmetric BSC instance. Take
U = B with A constant and p(b) uniform. Then I(U;Y₃) = 1 − h(a) > 1 − h(b) = I(B;Y₁ᴮ) =
I(U;Y₁). The last equality holds because A is constant, so Y₁ᴬ is independent of B. So Y₁ is
not less noisy than Y₃, and symmetrically not than Y₂. In the general class the same holds
whenever some p(b) gives I(B;Y₃) > I(B;Y₁ᴮ), i.e. whenever the degradation Y₃ → Y₁ᴮ is
non-trivial. Y₃ is then not a degraded version of Y₁ either, so the channel is not multilevel.
Y₂ and Y₃ see independent components: a U correlated only with A gives I(U;Y₃) = 0, and a U
correlated only with B gives I(U;Y₂) = 0. So neither is less noisy than the other unless one
of the component channels is useless.

### 6. Ordered common receivers

Suppose Y₂ is less noisy than Y₃. Take U₁ = U and `k₂ = k₃ = 1`, as in §3. The NE region then
contains {R₀ ≤ I(U;Y₃), R₁ ≤ I(X;Y₁|U), R₀ + R₁ ≤ I(X;Y₁)}, because
min(I(U;Y₂), I(U;Y₃)) = I(U;Y₃).

The two-receiver Körner–Marton capacity region of (Y₁, Y₃) (Körner–Marton 1977; El Gamal–Kim
§8.1) is the union over p(u, x) of the polygons
P(U) = {R₀ ≤ I(U;Y₃), R₀ + R₁ ≤ I(U;Y₃) + I(X;Y₁|U), R₀ + R₁ ≤ I(X;Y₁)}. Write a = I(U;Y₃),
L = I(X;Y₁|U), K = I(X;Y₁), s = min(a + L, K) and m = min(a, s). The corners of P(U) are
(0,0), (m, 0), (m, s − m) and (0, s). The first three lie in the set displayed above for the
same U: R₀ ≤ a, R₁ = s − m ≤ L, and R₀ + R₁ ≤ s ≤ K. The last lies in it for U constant, since
s ≤ K = I(X;Y₁). The NE region is convex (§3), so it contains every P(U).

Dropping receiver 2's decoding requirement can only enlarge the capacity region, so
C ⊆ KM(Y₁, Y₃) ⊆ NE ⊆ C. ∎

## Verification

* Claims 1–3: line-by-line comparison of `lean/InfoTheory/Problems/DegradedMessageSetsBcThreeReceivers.lean`
  (lines 57–84) with arXiv:0712.3327v2, Prop. 5 (p. 11), the proof (pp. 11–12), Remarks 1–2
  (p. 12), Thm. 1 (p. 3) and Props. 6–7 (pp. 13–14). Hand FM elimination, plus the LP check
  in `code/ne_region_check.py`.
* Claim 4: `code/ne_region_check.py` (`check_fig2`), with exact values.
* Claims 5 and 7: proofs above. `code/crossed_product.py` part 1 checks the Lean-formula
  evaluation at the optimal law.
* Claim 8: `code/crossed_product.py` part 2 (300 Nelder–Mead starts, seed 0). Heuristic only.
* Runtimes: ne_region_check.py ≈ 6.5 s; crossed_product.py ≈ 95 s (single core, `nice`).

## Dead ends

* **Numerical gap search between Prop. 5 and Prop. 6 (outer bound).** We did not attempt a
  serious one. NE's cardinality bounds for Prop. 6 are |U₂|, |U₃| ≤ (|X|+1)(|X|+6), which is 24
  for binary X. Local optimisation over such laws gives only lower bounds on the outer-bound
  value. A "gap" found that way would show only that our inner-bound optimisation got stuck,
  unless the inner bound is also optimised globally, which is equally hard. A useful gap
  example would need an analytic or certified evaluation of both bounds. We found that out of
  reach in this session.
* **"Y₁ more capable than Y₃" in place of less noisy.** NE's converse needs
  I(U₃;Y₃|U₁) ≤ I(U₃;Y₁|U₁) to turn R₀ ≤ I(U₃;Y₃) − I(U₃;Y₁|U₁) into R₀ ≤ I(U₁;Y₃). This
  conditional comparison is exactly less-noisiness. More-capability compares only
  I(X;Y₃) ≤ I(X;Y₁) and does not give it. We see no way around this, and did not pursue it.
* **Expecting the 2R₀ + R₁ inequality of (14) to be redundant on "nice" channels.** It is not.
  In the crossed product it is a capacity face (Claim 7).

## References

* No earlier attempts exist in `attempts/degraded-message-sets-bc-three-receivers/`.
* C. Nair, A. El Gamal, "The capacity region of a class of three-receiver broadcast channels
  with degraded message sets," IEEE Trans. IT 55(10), 2009; arXiv:0712.3327v2, read in full.
* J. Körner, K. Marton, "General broadcast channels with degraded message sets," IEEE Trans. IT
  23(1), 1977. A. El Gamal, Y.-H. Kim, *Network Information Theory*, 2011, §8.1–8.2.
* C. Nair, Z. V. Wang, arXiv:0806.4415. Abstract only: it treats the other configuration (M₁ to
  two receivers).
* M. Salman, M. K. Varanasi, arXiv:1812.10520. Abstract only: its classes are defined by
  pairwise less-noisy / more-capable orderings. We did not read the full paper and cannot
  exclude that it, or Romero–Varanasi arXiv:2011.04745, covers Claim 5.
* Novelty check for Claim 5: NE 2009 in full (its product examples, Section IV, are multilevel);
  the problem file's "What is known"; the abstracts above. The crossed product is a natural
  example and may appear elsewhere, e.g. in the combination-network literature
  (Bidokhti–Prabhakaran–Diggavi, IEEE Trans. IT 2016, on nested message sets over combination
  networks, which we did not read). We claim only that we did not find it.
