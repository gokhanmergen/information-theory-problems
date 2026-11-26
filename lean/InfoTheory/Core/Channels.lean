import InfoTheory.Core.Entropy

/-!
# Point-to-Point and Multiuser Channels

Core definitions for:
- Discrete Memoryless Channels (DMCs), BSC, BEC, q-ary SC, block codes, reliability functions
- Noisy hypercube & Boolean function mutual information (`mutualInfoBSC`, `mutualInfoQSC`)
- Synchronization channels (binary deletion, insertion-deletion, duplication)
- Multiuser channels: Broadcast Channel (capacity region, Marton inner bound, UV outer bound,
  binary skew-symmetric BC), Relay Channel (capacity, cutset bound, primitive BSC relay,
  Gaussian relay), Interference Channel (DM-IC, Han-Kobayashi, Gaussian IC, BS-ZIC),
  Two-Way Channel (Blackwell BMC), MAC with feedback (Cover-Leung), Wiretap Channel.
-/

open scoped BigOperators

namespace InfoTheory

/-- A Discrete Memoryless Channel `W(y | x)` over finite alphabets `α, β`. -/
structure DMC (α β : Type*) [Fintype α] [Fintype β] where
  trans : α → β → ℝ
  nonneg : ∀ x y, 0 ≤ trans x y
  sum_one : ∀ x, ∑ y : β, trans x y = 1

/-- Joint distribution `(X, Y)` induced by input `P` and channel `W`. -/
def DMC.joint {α β : Type*} [Fintype α] [Fintype β]
    (W : DMC α β) (P : ProbDist α) : ProbDist (α × β) where
  pmf := fun xy => P.pmf xy.1 * W.trans xy.1 xy.2
  nonneg := fun xy => mul_nonneg (P.nonneg xy.1) (W.nonneg xy.1 xy.2)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, W.sum_one, mul_one, P.sum_one]

/-- Mutual information `I(X; Y)` across channel `W` with input `P`. -/
noncomputable def DMC.mutualInfo {α β : Type*} [Fintype α] [Fintype β]
    (W : DMC α β) (P : ProbDist α) : ℝ :=
  InfoTheory.mutualInfo (W.joint P)

/-- Shannon capacity `C(W) = sup_P I(X; Y)`. -/
noncomputable def DMC.capacity {α β : Type*} [Fintype α] [Fintype β] (W : DMC α β) : ℝ :=
  sSup { r : ℝ | ∃ P : ProbDist α, r = W.mutualInfo P }

/-- `n`-fold memoryless product channel `W^{⊗ n}` on `Fin n → α` to `Fin n → β`. -/
def DMC.power {α β : Type*} [Fintype α] [Fintype β]
    (W : DMC α β) (n : ℕ) : DMC (Fin n → α) (Fin n → β) where
  trans := fun x y => ∏ i : Fin n, W.trans (x i) (y i)
  nonneg := fun x y => Finset.prod_nonneg (fun i _ => W.nonneg (x i) (y i))
  sum_one := fun x => by
    rw [← Fintype.prod_sum]
    exact Finset.prod_eq_one (fun i _ => W.sum_one (x i))

/-- Binary Symmetric Channel `BSC(α)` for `0 ≤ α ≤ 1`. -/
def bsc (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) : DMC Bool Bool where
  trans := fun x y => if x = y then 1 - α else α
  nonneg := fun x y => by split_ifs <;> linarith
  sum_one := fun x => by cases x <;> simp <;> ring

/-- Binary Erasure Channel `BEC(ε)` with output `Option Bool` (`none` = erasure). -/
def bec (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) : DMC Bool (Option Bool) where
  trans := fun x y => match y with
    | none => ε
    | some b => if x = b then 1 - ε else 0
  nonneg := fun x y => by
    cases y with
    | none => exact h0
    | some b => dsimp; split_ifs <;> linarith
  sum_one := fun x => by cases x <;> simp <;> ring

/-- `q`-ary Symmetric Channel `QSC(q, α)` on `Fin q`. -/
noncomputable def qarySC (q : ℕ) (hq : 2 ≤ q) (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    DMC (Fin q) (Fin q) where
  trans := fun x y => if y = x then 1 - α else α / ((q : ℝ) - 1)
  nonneg := fun x y => by
    split_ifs
    · linarith
    · apply div_nonneg h0
      have : (2 : ℝ) ≤ (q : ℝ) := Nat.ofNat_le_cast.mpr hq
      linarith
  sum_one := fun x => by
    have hq1 : (q : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ (q : ℝ) := Nat.ofNat_le_cast.mpr hq
      linarith
    have hsplit : ∑ y : Fin q, (if y = x then 1 - α else α / ((q : ℝ) - 1)) =
        (1 - α) + ∑ y ∈ Finset.univ.erase x, (α / ((q : ℝ) - 1)) := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ x)]
      congr 1
      · simp
      · refine Finset.sum_congr rfl (fun y hy => ?_)
        simp [Finset.ne_of_mem_erase hy]
    rw [hsplit, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ x),
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hcast : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]
    rw [hcast, mul_div_cancel₀ _ hq1]; ring

/-- Joint distribution `(X, Y)` for `X ~ Uniform({0,1}^n)` passed through `BSC(α)^n`. -/
noncomputable def bscNoisyPair (n : ℕ) (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    ProbDist ((Fin n → Bool) × (Fin n → Bool)) :=
  ((bsc α h0 h1).power n).joint ProbDist.uniform

/-- Mutual information `I(f(X); Y)` for `f : {0,1}^n → Bool` and `X ~ Unif`, `Y = BSC(α)^n(X)`. -/
noncomputable def mutualInfoBSC (n : ℕ) (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1)
    (f : (Fin n → Bool) → Bool) : ℝ :=
  mutualInfo ((bscNoisyPair n α h0 h1).map (fun xy => (f xy.1, xy.2)))

/-- Mutual information `I(f(X); Y)` for `f : (Fin q)^n → Fin q` over `QSC(q, α)^n`. -/
noncomputable def mutualInfoQSC (q n : ℕ) (hq : 2 ≤ q) (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1)
    (f : (Fin n → Fin q) → Fin q) : ℝ :=
  haveI : Nonempty (Fin q) := ⟨⟨0, by omega⟩⟩
  mutualInfo ((((qarySC q hq α h0 h1).power n).joint ProbDist.uniform).map (fun xy => (f xy.1, xy.2)))

/-! ### Block Codes and Reliability Function -/

/-- Average error probability of an `(n, M)` block code `(enc, dec)` over a DMC `W`. -/
noncomputable def dmcAvgError {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (W : DMC α β) (n M : ℕ) (enc : Fin M → Fin n → α) (dec : (Fin n → β) → Fin M) : ℝ :=
  if M = 0 then 0 else
    ((1 : ℝ) / (M : ℝ)) *
      ∑ m : Fin M, ∑ y : Fin n → β,
        if dec y ≠ m then (W.power n).trans (enc m) y else 0

/-- Optimal minimum average error probability `P_e*(W, n, M)` over all `(n, M)` codes. -/
noncomputable def dmcMinError {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (W : DMC α β) (n M : ℕ) : ℝ :=
  sInf { e : ℝ | ∃ (enc : Fin M → Fin n → α) (dec : (Fin n → β) → Fin M),
    e = dmcAvgError W n M enc dec }

/-- Reliability function (error exponent) `E(R)` of a DMC `W` at rate `R` (in bits). -/
noncomputable def reliabilityFunction {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (W : DMC α β) (R : ℝ) : ℝ :=
  sSup { E : ℝ | ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    dmcMinError W n (Nat.ceil ((2 : ℝ) ^ ((n : ℝ) * R))) ≤ (2 : ℝ) ^ (-(n : ℝ) * (E - ε)) }

/-- Random coding exponent `E_r(R)` of a DMC `W`. -/
noncomputable def randomCodingExponent {α β : Type*} [Fintype α] [Fintype β]
    (W : DMC α β) (R : ℝ) : ℝ :=
  sSup { v : ℝ | ∃ (ρ : ℝ) (P : ProbDist α),
    0 ≤ ρ ∧ ρ ≤ 1 ∧
    let E0 := -log2 (∑ y : β, (∑ x : α, P.pmf x * (W.trans x y) ^ (1 / (1 + ρ))) ^ (1 + ρ))
    v = E0 - ρ * R }

/-- Expurgated exponent `E_ex(R)` of a DMC `W`. -/
noncomputable def expurgatedExponent {α β : Type*} [Fintype α] [Fintype β]
    (W : DMC α β) (R : ℝ) : ℝ :=
  sSup { v : ℝ | ∃ (ρ : ℝ) (P : ProbDist α),
    1 ≤ ρ ∧
    let Ex := -ρ * log2 (∑ x₁ : α, ∑ x₂ : α, P.pmf x₁ * P.pmf x₂ *
      (∑ y : β, Real.sqrt (W.trans x₁ y * W.trans x₂ y)) ^ (1 / ρ))
    v = Ex - ρ * R }

/-! ### Synchronization Channels (Deletion, Insertion-Deletion, Duplication) -/

/-- Exact number of ways `y` appears as a subsequence of `x`. -/
def subseqCount {α : Type*} [DecidableEq α] : List α → List α → ℕ
  | _, [] => 1
  | [], _ :: _ => 0
  | a :: xs, b :: ys =>
      subseqCount xs (b :: ys) + (if a = b then subseqCount xs ys else 0)

/-- Transition probability `Pr[Del_d(x) = y]` for the i.i.d. binary deletion channel with
    deletion probability `d ∈ [0, 1]`. -/
noncomputable def deletionProb (d : ℝ) (x y : List Bool) : ℝ :=
  if y.length ≤ x.length then
    (subseqCount x y : ℝ) * (1 - d) ^ y.length * d ^ (x.length - y.length)
  else 0

/-- Output distribution induced by an input distribution `P` on `{0,1}^n` over `Del_d`,
    represented on `Σ k : Fin (n+1), Fin k.1 → Bool`. -/
noncomputable def deletionChannelMI (d : ℝ) (n : ℕ) (P : ProbDist (Fin n → Bool)) : ℝ :=
  let toList : (Fin n → Bool) → List Bool := fun x => List.ofFn x
  let outType := Σ k : Fin (n + 1), Fin k.1 → Bool
  let py : outType → ℝ := fun y =>
    ∑ x : Fin n → Bool, P.pmf x * deletionProb d (toList x) (List.ofFn y.2)
  let hY : ℝ := ∑ y : outType, negPLogP (py y)
  let hYgivenX : ℝ := ∑ x : Fin n → Bool, P.pmf x *
    ∑ y : outType, negPLogP (deletionProb d (toList x) (List.ofFn y.2))
  hY - hYgivenX

/-- Strictly positive DMC (`W(y|x) > 0` for all `x, y`), guaranteeing finite reliability
    and expurgated error exponents (excluding zero-error / noiseless channels). -/
def DMC.IsPositive {α β : Type*} [Fintype α] [Fintype β] (W : DMC α β) : Prop :=
  ∀ x y, 0 < W.trans x y

/-- Maximum mutual information `C_n(d) = sup_{P(x^n)} I(X^n; Y)` at blocklength `n`
    for the binary deletion channel `Del_d`. -/
noncomputable def binaryDeletionMaxMI (d : ℝ) (n : ℕ) : ℝ :=
  sSup { m : ℝ | ∃ P : ProbDist (Fin n → Bool), m = deletionChannelMI d n P }

/-- Capacity `C(d) = lim_{n → ∞} C_n(d)/n = inf_{n ≥ 1} (1/n) max_{P(x^n)} I(X^n; Y)`
    of the binary deletion channel (Dobrushin 1967; Fekete's subadditivity lemma).
    Note: `C_n(d)` is subadditive in `n`, so the limit equals the infimum over `n ≥ 1`
    of the per-letter maximized mutual information (NOT the supremum, which equals `1 - d` at `n = 1`). -/
noncomputable def binaryDeletionCapacity (d : ℝ) : ℝ :=
  sInf { r : ℝ | ∃ n : ℕ, 0 < n ∧ r = binaryDeletionMaxMI d n / (n : ℝ) }

/-! ### Multiuser Channels: Broadcast, Relay, Interference, Two-Way, MAC, Wiretap -/

/-- Two-receiver Discrete Memoryless Broadcast Channel `p(y₁, y₂ | x)`. -/
abbrev BroadcastChannel (X Y₁ Y₂ : Type*) [Fintype X] [Fintype Y₁] [Fintype Y₂] :=
  DMC X (Y₁ × Y₂)

/-- Operational achievability of rate pair `(R₁, R₂)` over a 2-receiver DMBC `W`. -/
def IsBCAchievable {X Y₁ Y₂ : Type*} [Fintype X] [Fintype Y₁] [Fintype Y₂]
    (W : BroadcastChannel X Y₁ Y₂) (R₁ R₂ : ℝ) : Prop :=
  0 ≤ R₁ ∧ 0 ≤ R₂ ∧
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    let M₁ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁)))
    let M₂ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₂)))
    ∃ (enc : Fin M₁ → Fin M₂ → Fin n → X)
      (dec₁ : (Fin n → Y₁) → Fin M₁)
      (dec₂ : (Fin n → Y₂) → Fin M₂),
      let err := ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) *
        ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ y : Fin n → Y₁ × Y₂,
          if dec₁ (fun i => (y i).1) ≠ m₁ ∨ dec₂ (fun i => (y i).2) ≠ m₂
          then (W.power n).trans (enc m₁ m₂) y else 0
      err ≤ ε

/-- Capacity region `C(W)` of a two-receiver DMBC: the topological closure of the set
    of operationally achievable rate pairs `(R₁, R₂)`. -/
def bcCapacityRegion {X Y₁ Y₂ : Type*} [Fintype X] [Fintype Y₁] [Fintype Y₂]
    (W : BroadcastChannel X Y₁ Y₂) : Set (ℝ × ℝ) :=
  closure { p | IsBCAchievable W p.1 p.2 }

/-- Marton's full single-letter inner bound (1979; El Gamal–Kim Prop. 8.1) for a two-receiver
    DMBC with private messages, including the common auxiliary random variable `W`
    (which subsumes time-sharing) and closed under topological closure. -/
def martonInnerBound {X Y₁ Y₂ : Type*} [Fintype X] [Fintype Y₁] [Fintype Y₂]
    (W : BroadcastChannel X Y₁ Y₂) : Set (ℝ × ℝ) :=
  closure { p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧
    ∃ (kW kU kV : ℕ) (Pwuvx : ProbDist (Fin kW × Fin kU × Fin kV × X)),
      let joint : ProbDist ((Fin kW × Fin kU × Fin kV × X) × (Y₁ × Y₂)) :=
        { pmf := fun z => Pwuvx.pmf z.1 * W.trans z.1.2.2.2 z.2
          nonneg := fun z => mul_nonneg (Pwuvx.nonneg z.1) (W.nonneg z.1.2.2.2 z.2)
          sum_one := by
            rw [Fintype.sum_prod_type]
            simp_rw [← Finset.mul_sum, W.sum_one, mul_one, Pwuvx.sum_one] }
      let IWU_Y1 := mutualInfo (joint.map (fun z => ((z.1.1, z.1.2.1), z.2.1)))
      let IWV_Y2 := mutualInfo (joint.map (fun z => ((z.1.1, z.1.2.2.1), z.2.2)))
      let IU_Y1_W := condMutualInfo (joint.map (fun z => (z.1.2.1, z.2.1, z.1.1)))
      let IV_Y2_W := condMutualInfo (joint.map (fun z => (z.1.2.2.1, z.2.2, z.1.1)))
      let IUV_W := condMutualInfo (Pwuvx.map (fun t => (t.2.1, t.2.2.1, t.1)))
      p.1 ≤ IWU_Y1 ∧ p.2 ≤ IWV_Y2 ∧
      p.1 + p.2 ≤ IWU_Y1 + IV_Y2_W - IUV_W ∧
      p.1 + p.2 ≤ IU_Y1_W + IWV_Y2 - IUV_W }

/-- Nair-El Gamal UV outer bound (2007) for a two-receiver DMBC (closed). -/
def uvOuterBound {X Y₁ Y₂ : Type*} [Fintype X] [Fintype Y₁] [Fintype Y₂]
    (W : BroadcastChannel X Y₁ Y₂) : Set (ℝ × ℝ) :=
  closure { p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧
    ∃ (kU kV : ℕ) (Puvx : ProbDist (Fin kU × Fin kV × X)),
      let joint : ProbDist ((Fin kU × Fin kV × X) × (Y₁ × Y₂)) :=
        { pmf := fun z => Puvx.pmf z.1 * W.trans z.1.2.2 z.2
          nonneg := fun z => mul_nonneg (Puvx.nonneg z.1) (W.nonneg z.1.2.2 z.2)
          sum_one := by
            rw [Fintype.sum_prod_type]
            simp_rw [← Finset.mul_sum, W.sum_one, mul_one, Puvx.sum_one] }
      let IUY₁ := mutualInfo (joint.map (fun z => (z.1.1, z.2.1)))
      let IVY₂ := mutualInfo (joint.map (fun z => (z.1.2.1, z.2.2)))
      let IXY₁_V := condMutualInfo (joint.map (fun z => (z.1.2.2, z.2.1, z.1.2.1)))
      let IXY₂_U := condMutualInfo (joint.map (fun z => (z.1.2.2, z.2.2, z.1.1)))
      p.1 ≤ IUY₁ ∧ p.2 ≤ IVY₂ ∧
      p.1 + p.2 ≤ IUY₁ + IXY₂_U ∧ p.1 + p.2 ≤ IVY₂ + IXY₁_V }

/-- Binary Skew-Symmetric Broadcast Channel (Hajek-Pursley 1979):
    `Y₁` is a Z-channel (`0 → 0`, `1 → Unif{0,1}`), `Y₂` is a reversed Z-channel (`1 → 1`, `0 → Unif{0,1}`),
    with independent marginals. -/
noncomputable def binarySkewSymmetricBC : BroadcastChannel Bool Bool Bool where
  trans := fun x y =>
    let p1 : ℝ := if x = false then (if y.1 = false then 1 else 0) else (1 / 2 : ℝ)
    let p2 : ℝ := if x = true then (if y.2 = true then 1 else 0) else (1 / 2 : ℝ)
    p1 * p2
  nonneg := fun x y => by cases x <;> cases y.1 <;> cases y.2 <;> norm_num
  sum_one := fun x => by cases x <;> simp [Fintype.sum_prod_type] <;> norm_num

/-- Discrete Memoryless Relay Channel `p(y, y_r | x, x_r)`. -/
abbrev RelayChannel (X Xr Y Yr : Type*) [Fintype X] [Fintype Xr] [Fintype Y] [Fintype Yr] :=
  DMC (X × Xr) (Y × Yr)

/-- Cutset upper bound for a discrete memoryless relay channel (Cover-El Gamal 1979). -/
noncomputable def relayCutsetBound {X Xr Y Yr : Type*}
    [Fintype X] [Fintype Xr] [Fintype Y] [Fintype Yr]
    (W : RelayChannel X Xr Y Yr) : ℝ :=
  sSup { r : ℝ | ∃ P : ProbDist (X × Xr),
    let J := W.joint P
    let I_X_YYr_given_Xr := condMutualInfo (J.map (fun z => (z.1.1, z.2, z.1.2)))
    let I_XXr_Y := mutualInfo (J.map (fun z => (z.1, z.2.1)))
    r = min I_X_YYr_given_Xr I_XXr_Y }

/-- Causal relay encoder and capacity of a DM relay channel `W`. -/
def IsRelayAchievable {X Xr Y Yr : Type*}
    [Fintype X] [Fintype Xr] [Fintype Y] [Fintype Yr]
    (W : RelayChannel X Xr Y Yr) (R : ℝ) : Prop :=
  0 ≤ R ∧
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    let M := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
    ∃ (enc : Fin M → Fin n → X)
      (relay : ∀ i : Fin n, (Fin i.1 → Yr) → Xr)
      (dec : (Fin n → Y) → Fin M),
      let transSeq (m : Fin M) (yr : Fin n → Yr) (y : Fin n → Y) : ℝ :=
        ∏ i : Fin n, W.trans (enc m i, relay i (fun j => yr ⟨j.1, Nat.lt_trans j.2 i.2⟩)) (y i, yr i)
      let err := ((1 : ℝ) / (M : ℝ)) *
        ∑ m : Fin M, ∑ yr : Fin n → Yr, ∑ y : Fin n → Y,
          if dec y ≠ m then transSeq m yr y else 0
      err ≤ ε

/-- Capacity `C(W)` of a discrete memoryless relay channel. -/
noncomputable def relayCapacity {X Xr Y Yr : Type*}
    [Fintype X] [Fintype Xr] [Fintype Y] [Fintype Yr]
    (W : RelayChannel X Xr Y Yr) : ℝ :=
  sSup { R : ℝ | IsRelayAchievable W R }

/-- Two-user Discrete Memoryless Interference Channel `p(y₁, y₂ | x₁, x₂)`. -/
abbrev InterferenceChannel (X₁ X₂ Y₁ Y₂ : Type*)
    [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂] :=
  DMC (X₁ × X₂) (Y₁ × Y₂)

/-- Operational capacity region (closed) of a two-user DM interference channel. -/
def icCapacityRegion {X₁ X₂ Y₁ Y₂ : Type*}
    [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂]
    (W : InterferenceChannel X₁ X₂ Y₁ Y₂) : Set (ℝ × ℝ) :=
  closure { p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      let M₁ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * p.1)))
      let M₂ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * p.2)))
      ∃ (enc₁ : Fin M₁ → Fin n → X₁) (enc₂ : Fin M₂ → Fin n → X₂)
        (dec₁ : (Fin n → Y₁) → Fin M₁) (dec₂ : (Fin n → Y₂) → Fin M₂),
        let err := ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) *
          ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ y : Fin n → Y₁ × Y₂,
            if dec₁ (fun i => (y i).1) ≠ m₁ ∨ dec₂ (fun i => (y i).2) ≠ m₂
            then (W.power n).trans (fun i => (enc₁ m₁ i, enc₂ m₂ i)) y else 0
        err ≤ ε }

/-- Binary Symmetric Z-Interference Channel `Y₁ = X₁ ⊕ X₂ ⊕ N₁`, `Y₂ = X₂ ⊕ N₂`. -/
def bsZicChannel (p₁ p₂ : ℝ) (h10 : 0 ≤ p₁) (h11 : p₁ ≤ 1) (h20 : 0 ≤ p₂) (h21 : p₂ ≤ 1) :
    InterferenceChannel Bool Bool Bool Bool where
  trans := fun x y =>
    let q1 := if y.1 = (xor x.1 x.2) then 1 - p₁ else p₁
    let q2 := if y.2 = x.2 then 1 - p₂ else p₂
    q1 * q2
  nonneg := fun x y => by cases x.1 <;> cases x.2 <;> cases y.1 <;> cases y.2 <;> simp <;> nlinarith
  sum_one := fun x => by
    cases x.1 <;> cases x.2 <;> simp [Fintype.sum_prod_type] <;> ring

/-- Two-way discrete memoryless channel `p(y₁, y₂ | x₁, x₂)` (Shannon 1961). -/
abbrev TwoWayChannel (X₁ X₂ Y₁ Y₂ : Type*)
    [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂] :=
  DMC (X₁ × X₂) (Y₁ × Y₂)

/-- Blackwell's Binary Multiplying Channel `Y₁ = Y₂ = X₁ · X₂`. -/
def binaryMultiplyingChannel : TwoWayChannel Bool Bool Bool Bool where
  trans := fun x y =>
    if y = (x.1 && x.2, x.1 && x.2) then 1 else 0
  nonneg := fun _ _ => by split_ifs <;> norm_num
  sum_one := fun x => by simp

/-- Achievable rate pair `(R₁, R₂)` over a Two-Way Channel with adaptive causal encoding. -/
def IsTWCAchievable {X₁ X₂ Y₁ Y₂ : Type*}
    [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂]
    (W : TwoWayChannel X₁ X₂ Y₁ Y₂) (R₁ R₂ : ℝ) : Prop :=
  0 ≤ R₁ ∧ 0 ≤ R₂ ∧
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    let M₁ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁)))
    let M₂ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₂)))
    ∃ (enc₁ : ∀ i : Fin n, Fin M₁ → (Fin i.1 → Y₁) → X₁)
      (enc₂ : ∀ i : Fin n, Fin M₂ → (Fin i.1 → Y₂) → X₂)
      (dec₁ : Fin M₁ → (Fin n → Y₁) → Fin M₂)
      (dec₂ : Fin M₂ → (Fin n → Y₂) → Fin M₁),
      let transSeq (m₁ : Fin M₁) (m₂ : Fin M₂) (y : Fin n → Y₁ × Y₂) : ℝ :=
        ∏ i : Fin n,
          W.trans
            (enc₁ i m₁ (fun j => (y ⟨j.1, Nat.lt_trans j.2 i.2⟩).1),
             enc₂ i m₂ (fun j => (y ⟨j.1, Nat.lt_trans j.2 i.2⟩).2))
            (y i)
      let err := ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) *
        ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ y : Fin n → Y₁ × Y₂,
          if dec₁ m₁ (fun i => (y i).1) ≠ m₂ ∨ dec₂ m₂ (fun i => (y i).2) ≠ m₁
          then transSeq m₁ m₂ y else 0
      err ≤ ε

/-- Capacity region (closed) of a Two-Way Channel. -/
def twcCapacityRegion {X₁ X₂ Y₁ Y₂ : Type*}
    [Fintype X₁] [Fintype X₂] [Fintype Y₁] [Fintype Y₂]
    (W : TwoWayChannel X₁ X₂ Y₁ Y₂) : Set (ℝ × ℝ) :=
  closure { p | IsTWCAchievable W p.1 p.2 }

/-- Two-user Discrete Memoryless Multiple-Access Channel `p(y | x₁, x₂)`. -/
abbrev MACChannel (X₁ X₂ Y : Type*) [Fintype X₁] [Fintype X₂] [Fintype Y] :=
  DMC (X₁ × X₂) Y

/-- Achievable rate pair `(R₁, R₂)` over a MAC with noiseless output feedback. -/
def IsMACFeedbackAchievable {X₁ X₂ Y : Type*} [Fintype X₁] [Fintype X₂] [Fintype Y]
    (W : MACChannel X₁ X₂ Y) (R₁ R₂ : ℝ) : Prop :=
  0 ≤ R₁ ∧ 0 ≤ R₂ ∧
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    let M₁ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁)))
    let M₂ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₂)))
    ∃ (enc₁ : ∀ i : Fin n, Fin M₁ → (Fin i.1 → Y) → X₁)
      (enc₂ : ∀ i : Fin n, Fin M₂ → (Fin i.1 → Y) → X₂)
      (dec : (Fin n → Y) → Fin M₁ × Fin M₂),
      let transSeq (m₁ : Fin M₁) (m₂ : Fin M₂) (y : Fin n → Y) : ℝ :=
        ∏ i : Fin n,
          W.trans
            (enc₁ i m₁ (fun j => y ⟨j.1, Nat.lt_trans j.2 i.2⟩),
             enc₂ i m₂ (fun j => y ⟨j.1, Nat.lt_trans j.2 i.2⟩))
            (y i)
      let err := ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) *
        ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, ∑ y : Fin n → Y,
          if dec y ≠ (m₁, m₂) then transSeq m₁ m₂ y else 0
      err ≤ ε

/-- Capacity region (closed) of a DM-MAC with noiseless feedback. -/
def macFeedbackCapacityRegion {X₁ X₂ Y : Type*} [Fintype X₁] [Fintype X₂] [Fintype Y]
    (W : MACChannel X₁ X₂ Y) : Set (ℝ × ℝ) :=
  closure { p | IsMACFeedbackAchievable W p.1 p.2 }

/-- Cover-Leung (1981) achievable region (closed) for a DM-MAC with feedback. -/
def coverLeungRegion {X₁ X₂ Y : Type*} [Fintype X₁] [Fintype X₂] [Fintype Y]
    (W : MACChannel X₁ X₂ Y) : Set (ℝ × ℝ) :=
  closure { p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧
    ∃ (kU : ℕ) (Pu : ProbDist (Fin kU))
      (Px₁ : Fin kU → ProbDist X₁) (Px₂ : Fin kU → ProbDist X₂),
      let joint : ProbDist (Fin kU × X₁ × X₂ × Y) :=
        { pmf := fun t => Pu.pmf t.1 * (Px₁ t.1).pmf t.2.1 * (Px₂ t.1).pmf t.2.2.1 *
            W.trans (t.2.1, t.2.2.1) t.2.2.2
          nonneg := fun t => mul_nonneg (mul_nonneg (mul_nonneg (Pu.nonneg _) ((Px₁ _).nonneg _))
            ((Px₂ _).nonneg _)) (W.nonneg _ _)
          sum_one := by
            simp_rw [Fintype.sum_prod_type]
            simp_rw [← Finset.mul_sum, W.sum_one, mul_one]
            simp_rw [← Finset.mul_sum, (Px₂ _).sum_one, mul_one]
            simp_rw [← Finset.mul_sum, (Px₁ _).sum_one, mul_one, Pu.sum_one] }
      p.1 ≤ condMutualInfo (joint.map (fun t => (t.2.1, t.2.2.2, (t.2.2.1, t.1)))) ∧
      p.2 ≤ condMutualInfo (joint.map (fun t => (t.2.2.1, t.2.2.2, (t.2.1, t.1)))) ∧
      p.1 + p.2 ≤ mutualInfo (joint.map (fun t => ((t.2.1, t.2.2.1), t.2.2.2))) }

/-- Wiretap channel `p(y, z | x)` (legitimate receiver `Y`, eavesdropper `Z`). -/
abbrev WiretapChannel (X Y Z : Type*) [Fintype X] [Fintype Y] [Fintype Z] :=
  DMC X (Y × Z)

/-- Csiszár-Körner secrecy capacity `C_s(W) = max_{V-X-YZ} [I(V;Y) - I(V;Z)]` of a DM wiretap channel. -/
noncomputable def wiretapSecrecyCapacity {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (W : WiretapChannel X Y Z) : ℝ :=
  sSup { r : ℝ | ∃ (kV : ℕ) (Pvx : ProbDist (Fin kV × X)),
    let joint : ProbDist (Fin kV × X × Y × Z) :=
      { pmf := fun t => Pvx.pmf (t.1, t.2.1) * W.trans t.2.1 (t.2.2.1, t.2.2.2)
        nonneg := fun t => mul_nonneg (Pvx.nonneg _) (W.nonneg _ _)
        sum_one := by
          simp_rw [Fintype.sum_prod_type]
          have hW : ∀ x, ∑ y : Y, ∑ z : Z, W.trans x (y, z) = 1 := fun x => by
            rw [← Fintype.sum_prod_type]; exact W.sum_one x
          simp_rw [← Finset.mul_sum, hW, mul_one]
          rw [← Fintype.sum_prod_type]; exact Pvx.sum_one }
    r = mutualInfo (joint.map (fun t => (t.1, t.2.2.1))) -
        mutualInfo (joint.map (fun t => (t.1, t.2.2.2))) }

end InfoTheory
