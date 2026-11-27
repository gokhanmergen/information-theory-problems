import InfoTheory.Core

/-!
# Capacity region of the three-receiver broadcast channel

`Statement`: for every finite 3-DMBC with three private messages, the operational capacity
region `bc3CapacityRegion W` equals the **UM region** `umRegion W` of Padakandla–Pradhan
(public layer `W`, semi-private layers `U₁₂, U₂₃, U₃₁` decoded by pairs, private layers
`V₁, V₂, V₃`; superposition plus binning; time sharing `Q`).

**Statement-fix (2026-11-27).** The original statement used a region `marton3InnerBound`
(common cloud `W₀`, pairwise clouds folded into the binned auxiliaries
`V₁ = (W₁₂, W₁₃, U₁)`, …). Its covering constraint charged the full entropy of a pairwise
cloud, so with a constant third output it collapses to Marton's region *without* a
superposition variable for the other two receivers. That region is certifiably below
capacity for the degraded Gohari–El Gamal–Anantharam channel (arXiv:1006.5166, Claim 1):
`sup (R₁ + 2.35 R₂) ≤ 0.12131588 < 0.12131597 ≤` a superposition-coding point, so the old
statement was false
(`attempts/broadcast-channel-three-receivers/2026-11-26-claude-opus-5-5-useless-receiver-catalog-error.md`).
The UM region replaces it. With a constant third output, taking `U₂₃, U₃₁, V₃` constant
turns its constraints into El Gamal–Kim's rate-split form of Marton's region *with* the
common auxiliary `U₁₂`, so it contains the two-receiver region `martonInnerBound` (in
particular superposition coding), and the counterexample no longer applies.

Known facts. Capacity is known for degraded 3-DMBCs (Bergmans 1973; Gallager 1974), and the
UM region contains it (`W`, `U₁₂`, `V₁` carry `M₃`, `M₂`, `M₁`). It is achievable
(PP, Theorem 2). Both sides lie in the box `[0, C₁] × [0, C₂] × [0, C₃]`, `Cⱼ` the capacity
of `p(yⱼ | x)`. **Caveats:** Padakandla–Pradhan prove that the UM region is strictly
suboptimal for some 3-DMBCs *with input cost constraints* (coset codes do better); the
cost-free question posed here is open. Huang–Liu–Liu (arXiv:2608.19869, 2026, not peer
reviewed) claim that two-receiver Marton is suboptimal (see `broadcast-channel`); if so, and
if the UM region with a useless third receiver is no larger than Marton's region (expected,
not proved here), this statement is false as well.
-/

open scoped BigOperators

namespace InfoTheory.Problems.BroadcastChannelThreeReceivers

/-- Three-receiver Discrete Memoryless Broadcast Channel `p(y₁, y₂, y₃ | x)`. -/
abbrev BroadcastChannel3 (X Y₁ Y₂ Y₃ : Type*)
    [Fintype X] [Fintype Y₁] [Fintype Y₂] [Fintype Y₃] :=
  DMC X (Y₁ × Y₂ × Y₃)

/-- Operational achievability of private-message rate triple `(R₁, R₂, R₃)` over a 3-DMBC `W`. -/
def IsBC3Achievable {X Y₁ Y₂ Y₃ : Type*}
    [Fintype X] [Fintype Y₁] [Fintype Y₂] [Fintype Y₃]
    (W : BroadcastChannel3 X Y₁ Y₂ Y₃) (R₁ R₂ R₃ : ℝ) : Prop :=
  0 ≤ R₁ ∧ 0 ≤ R₂ ∧ 0 ≤ R₃ ∧
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    let M₁ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁)))
    let M₂ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₂)))
    let M₃ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₃)))
    ∃ (enc : Fin M₁ → Fin M₂ → Fin M₃ → Fin n → X)
      (dec₁ : (Fin n → Y₁) → Fin M₁)
      (dec₂ : (Fin n → Y₂) → Fin M₂)
      (dec₃ : (Fin n → Y₃) → Fin M₃),
      let err := ((1 : ℝ) / ((M₁ * M₂ * M₃ : ℕ) : ℝ)) *
        ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ m₃ : Fin M₃, ∑ y : Fin n → Y₁ × Y₂ × Y₃,
          if dec₁ (fun i => (y i).1) ≠ m₁ ∨
             dec₂ (fun i => (y i).2.1) ≠ m₂ ∨
             dec₃ (fun i => (y i).2.2) ≠ m₃
          then (W.power n).trans (enc m₁ m₂ m₃) y else 0
      err ≤ ε

/-- Capacity region (closed) `C₃(W)` of a three-receiver DMBC. -/
def bc3CapacityRegion {X Y₁ Y₂ Y₃ : Type*}
    [Fintype X] [Fintype Y₁] [Fintype Y₂] [Fintype Y₃]
    (W : BroadcastChannel3 X Y₁ Y₂ Y₃) : Set (ℝ × ℝ × ℝ) :=
  closure { r | IsBC3Achievable W r.1 r.2.1 r.2.2 }

/-! ### The UM region of Padakandla–Pradhan -/

/-- Auxiliary tuple `(Q, W, U, V, X)` of the three-layer *unstructured Marton* (UM) scheme of
    Padakandla–Pradhan: time sharing `Q`, public cloud `W`, semi-private clouds `U i`
    (`U 0 = U₁₂`, `U 1 = U₂₃`, `U 2 = U₃₁`: index `i` is the receiver pair `(i, i+1)`), private
    satellites `V i` (`V i` is decoded by receiver `i` only), and the channel input `X`.
    All auxiliary alphabets are `Fin k` for one common `k` (no loss: unused labels get
    probability zero). -/
abbrev UMAux (k : ℕ) (X : Type*) := Fin k × Fin k × (Fin 3 → Fin k) × (Fin 3 → Fin k) × X

/-- Covering (encoding) constraints (1)–(6) of Padakandla–Pradhan (arXiv:1207.3146v6, §II-D)
    for bin rates `S i = S_{i,i+1}` (semi-private) and `Sv i = S_i` (private), with
    non-strict inequalities. For `i` read the cyclic triple `(i, j, k) = (i, i+1, i+2)`;
    `I(A; B; C | ·) := I(A; B | ·) + I(A, B; C | ·)` is the multi-information
    (PP, footnote 4). Constraint (1), `S_i ≥ 0`, is imposed in `umRegion`. -/
def umCoveringConstraints {k : ℕ} {X : Type*} [Fintype X] (P : ProbDist (UMAux k X))
    (S Sv : Fin 3 → ℝ) : Prop :=
  let qw : UMAux k X → Fin k × Fin k := fun t => (t.1, t.2.1)
  let u : UMAux k X → Fin 3 → Fin k := fun t => t.2.2.1
  let v : UMAux k X → Fin 3 → Fin k := fun t => t.2.2.2.1
  -- `I(U₁₂; U₂₃; U₃₁ | W Q)`
  let TCU := condMutualInfo (P.map fun t => (u t 0, u t 1, qw t)) +
    condMutualInfo (P.map fun t => ((u t 0, u t 1), u t 2, qw t))
  -- `I(V₁; V₂; V₃ | Q W U)`
  let TCV := condMutualInfo (P.map fun t => (v t 0, v t 1, (qw t, u t))) +
    condMutualInfo (P.map fun t => ((v t 0, v t 1), v t 2, (qw t, u t)))
  -- `I(V_i; U_jk | U_ij, U_ki, W Q)`
  let IVU : Fin 3 → ℝ := fun i =>
    condMutualInfo (P.map fun t => (v t i, u t (i + 1), (qw t, u t i, u t (i + 2))))
  let SU := S 0 + S 1 + S 2
  (∀ i : Fin 3,
    -- (2)  `S_ij + S_jk ≥ I(U_ij; U_jk | W Q)`
    condMutualInfo (P.map fun t => (u t i, u t (i + 1), qw t)) ≤ S i + S (i + 1) ∧
    -- (4)  `S_i + S_ij + S_jk + S_ki ≥ I(U_ij; U_jk; U_ki | W Q) + I(V_i; U_jk | U_ij, U_ki, W Q)`
    TCU + IVU i ≤ Sv i + SU ∧
    -- (5)  `S_i + S_j + S_ij + S_jk + S_ki ≥ I(V_i; U_jk | ·) + I(V_j; U_ki | ·)
    --        + I(U_ij; U_jk; U_ki | W Q) + I(V_i; V_j | U_ij, U_jk, U_ki, W Q)`
    IVU i + IVU (i + 1) + TCU +
        condMutualInfo (P.map fun t => (v t i, v t (i + 1), (qw t, u t))) ≤
      Sv i + Sv (i + 1) + SU) ∧
  -- (3)  `S₁₂ + S₂₃ + S₃₁ ≥ I(U₁₂; U₂₃; U₃₁ | W Q)`
  TCU ≤ SU ∧
  -- (6)
  IVU 0 + IVU 1 + IVU 2 + TCV + TCU ≤ Sv 0 + Sv 1 + Sv 2 + SU

/-- Packing (decoding) constraints (7)–(11) of Padakandla–Pradhan for receiver `i`, with
    non-strict inequalities. `G` is the joint law of the auxiliary tuple and receiver `i`'s
    output. With `(i, j, k) = (i, i+1, i+2)`, receiver `i` decodes `W`, `U_ij = U i`,
    `U_ki = U (i+2)` and `V_i`. Rates: `K j` public part of message `j`; `Ks i = K_{i,i+1}`
    and `L i = L_{i,i+1}` the parts of messages `i` and `i+1` carried by `U i`; `T j` private
    part of message `j`; `S`, `Sv` bin rates. -/
def umDecodingConstraints {k : ℕ} {X Y : Type*} [Fintype X] [Fintype Y]
    (G : ProbDist (UMAux k X × Y)) (i : Fin 3) (K Ks L S T Sv : Fin 3 → ℝ) : Prop :=
  let q : UMAux k X → Fin k := fun t => t.1
  let w : UMAux k X → Fin k := fun t => t.2.1
  let qw : UMAux k X → Fin k × Fin k := fun t => (t.1, t.2.1)
  let a : UMAux k X → Fin k := fun t => t.2.2.1 i          -- `U_ij`
  let b : UMAux k X → Fin k := fun t => t.2.2.1 (i + 2)    -- `U_ki`
  let c : UMAux k X → Fin k := fun t => t.2.2.2.1 i        -- `V_i`
  -- `I(U_ij; U_ki | Q W)`
  let Iab := condMutualInfo (G.map fun z => (a z.1, b z.1, qw z.1))
  -- (7)  `I(V_i; Y_i | Q W U_ij U_ki) ≥ T_i + S_i`
  T i + Sv i ≤ condMutualInfo (G.map fun z => (c z.1, z.2, (qw z.1, a z.1, b z.1))) ∧
  -- (8)
  Ks i + L i + S i + T i + Sv i ≤
    condMutualInfo (G.map fun z => ((a z.1, c z.1), z.2, (qw z.1, b z.1))) + Iab ∧
  -- (9)
  Ks (i + 2) + L (i + 2) + S (i + 2) + T i + Sv i ≤
    condMutualInfo (G.map fun z => ((b z.1, c z.1), z.2, (qw z.1, a z.1))) + Iab ∧
  -- (10)
  Ks i + L i + S i + Ks (i + 2) + L (i + 2) + S (i + 2) + T i + Sv i ≤
    condMutualInfo (G.map fun z => ((a z.1, b z.1, c z.1), z.2, qw z.1)) + Iab ∧
  -- (11)
  K 0 + K 1 + K 2 + Ks i + L i + S i + Ks (i + 2) + L (i + 2) + S (i + 2) + T i + Sv i ≤
    condMutualInfo (G.map fun z => ((w z.1, a z.1, b z.1, c z.1), z.2, q z.1)) + Iab

/-- The **UM region** `α_U(W)` of Padakandla–Pradhan (arXiv:1207.3146v6, §II-D, Theorem 2;
    no cost constraint): message `j` is split as `R_j = T_j + K_{jk} + L_{ij} + K_j`
    (private, two semi-private, public parts), and the region is the closed convex hull of
    all rate triples admitting nonnegative split and bin rates that satisfy the covering
    constraints (1)–(6) and the packing constraints (7)–(11) of all three receivers, for some
    `p(q, w, u₁₂, u₂₃, u₃₁, v₁, v₂, v₃, x)` with `(Q, W, U, V) → X → (Y₁, Y₂, Y₃)`.
    Strict inequalities of the source are replaced by non-strict ones (before the closure);
    PP's literal `S_i > 0` would make the region empty whenever an output is useless. -/
def umRegion {X Y₁ Y₂ Y₃ : Type*}
    [Fintype X] [Fintype Y₁] [Fintype Y₂] [Fintype Y₃]
    (W : BroadcastChannel3 X Y₁ Y₂ Y₃) : Set (ℝ × ℝ × ℝ) :=
  closure (convexHull ℝ { r | ∃ (k : ℕ) (P : ProbDist (UMAux k X))
      (K Ks L S T Sv : Fin 3 → ℝ),
    (∀ i, 0 ≤ K i ∧ 0 ≤ Ks i ∧ 0 ≤ L i ∧ 0 ≤ S i ∧ 0 ≤ T i ∧ 0 ≤ Sv i) ∧
    r = (T 0 + Ks 0 + L 2 + K 0, T 1 + Ks 1 + L 0 + K 1, T 2 + Ks 2 + L 1 + K 2) ∧
    umCoveringConstraints P S Sv ∧
    let J : ProbDist (UMAux k X × (Y₁ × Y₂ × Y₃)) :=
      { pmf := fun z => P.pmf z.1 * W.trans z.1.2.2.2.2 z.2
        nonneg := fun z => mul_nonneg (P.nonneg z.1) (W.nonneg z.1.2.2.2.2 z.2)
        sum_one := by
          rw [Fintype.sum_prod_type]
          simp_rw [← Finset.mul_sum, W.sum_one, mul_one, P.sum_one] }
    umDecodingConstraints (J.map fun z => (z.1, z.2.1)) 0 K Ks L S T Sv ∧
    umDecodingConstraints (J.map fun z => (z.1, z.2.2.1)) 1 K Ks L S T Sv ∧
    umDecodingConstraints (J.map fun z => (z.1, z.2.2.2)) 2 K Ks L S T Sv })

/-- Capacity Region of the Three-Receiver Broadcast Channel (Cover 1972; Padakandla–Pradhan
    2012/2015): Does the UM region (Marton coding with a public layer, three pairwise
    semi-private layers and three private layers, with superposition and binning) equal the
    private-message capacity region for every finite-alphabet 3-DMBC? -/
def Statement : Prop :=
  ∀ (kX kY₁ kY₂ kY₃ : ℕ) (W : BroadcastChannel3 (Fin kX) (Fin kY₁) (Fin kY₂) (Fin kY₃)),
    bc3CapacityRegion W = umRegion W

def problem : OpenProblem where
  id := "broadcast-channel-three-receivers"
  title := "Capacity Region of the Three-Receiver Broadcast Channel"
  category := .networkInfoTheory
  status := .open
  posedBy := "Thomas Cover"
  posedYear := 1972
  statement := Statement

end InfoTheory.Problems.BroadcastChannelThreeReceivers
