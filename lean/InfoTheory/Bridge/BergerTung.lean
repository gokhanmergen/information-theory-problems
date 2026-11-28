import InfoTheory.Core
import InfoTheory.Bridge.CoverThomas
import InfoTheory.Bridge.ChannelCoding
import InfoTheory.Bridge.RateDistortion
import InfoTheory.Bridge.NetworkIT
import InfoTheory.Bridge.WynerZiv
import InfoTheory.Bridge.GelfandPinsker

/-!
# Berger–Tung Inner and Outer Bounds for Multiterminal Lossy Source Coding
(Berger 1978; Tung 1978; El Gamal & Kim Theorem 12.1 & §12.1.3)

Purely additive, kernel-verified formalization of the Berger–Tung inner and outer bounds for
two-terminal distributed lossy source coding of a discrete memoryless correlated source
`(X₁, X₂) ~ P` under separate distortion measures `(d₁, d₂)`, directly matching
`InfoTheory.Core.SourceCoding` (`IsBergerTungAchievable`, `bergerTungInnerBound`):

1. **Single-Letter Berger–Tung Outer Bound, Inclusion & Special-Case Reductions**:
   - `bergerTungOuterBound`, `hammingDistortion`
   - `bergerTungInnerBound_subset_outerBound`
   - `bergerTungInnerBound_mono`, `bergerTungOuterBound_mono`
   - Lossless collapse to Slepian–Wolf (`D₁ = D₂ = 0`, Hamming distortion):
     `bergerTungInnerBound_lossless_eq_slepianWolf`,
     `bergerTungOuterBound_lossless_eq_slepianWolf`
   - One-sided collapse to Wyner–Ziv:
     `wynerZivRateDistortion_le_of_mem_bergerTungInnerBound`,
     `mem_bergerTungInnerBound_of_wynerZiv`,
     `sInf_bergerTungInnerBound_eq_wynerZiv`,
     `wynerZiv_converse_of_isBergerTungAchievable`

2. **Operational Berger–Tung Outer Bound Converse (El Gamal & Kim §12.1.3)**:
   - `bergerTung_outer_converse_block` (finite-blocklength single-letterization via prefix
     auxiliaries `U_{1,i} = (i, M₁, X₁^{<i}, X₂^{<i})`, `U_{2,i} = (i, M₂, X₁^{<i}, X₂^{<i})`)
   - `bergerTung_outer_converse` (operational converse for `IsBergerTungAchievable`)

3. **Two-Encoder (Permutation-Orbit) Markov Lemma**:
   - `markov_lemma_conditional_type_perm` (hypergeometric negative-correlation bound on
     fiber-preserving permutations `G(x₂)` for a Markov chain `U₂ — X₂ — (X₁, U₁)`)
   - `markov_lemma_first_covering_codeword` (second-stage Markov lemma for the first
     covering codeword in an independent i.i.d. random codebook `C₂`)

4. **Operational Berger–Tung Inner Bound Achievability (El Gamal & Kim Theorem 12.1)**:
   - `bergerTung_inner_achievability_of_dist` (dual covering + two-stage Markov lemma +
     3-event joint-typicality random binning)
   - `bergerTung_inner_achievability` (`(R₁, R₂) ∈ bergerTungInnerBound → IsBergerTungAchievable`)
   - `isBergerTungAchievable_timeSharing` and `bergerTung_inner_closure_achievability`
     (time-sharing convexity & closure achievability)
-/

open scoped BigOperators
open InfoTheory InfoTheory.Bridge

namespace InfoTheory.Bridge

/-! ### 0. Shared Private Helper Lemmas -/

section SharedHelpers

variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

private lemma bt_nonempty_of_probDist (P : ProbDist α) : Nonempty α := by
  by_contra h
  have h0 : ∑ a : α, P.pmf a = 0 := Finset.sum_eq_zero fun a _ => (h ⟨a⟩).elim
  linarith [P.sum_one]

private lemma bt_probDist_ext {P Q : ProbDist α} (h : ∀ a, P.pmf a = Q.pmf a) : P = Q := by
  cases P; cases Q; congr; funext a; exact h a

private lemma bt_probDist_map_id (P : ProbDist α) : P.map id = P := by
  classical
  cases P with | mk pmf h0 h1 =>
  unfold ProbDist.map
  congr
  funext a
  simp

private lemma bt_probDist_map_equiv_pmf (e : α ≃ β) (P : ProbDist α) (b : β) :
    (P.map e).pmf b = P.pmf (e.symm b) := by
  classical
  unfold ProbDist.map
  dsimp only
  rw [Finset.sum_eq_single (e.symm b)]
  · simp
  · intro a _ hne
    have : e a ≠ b := fun h => hne (e.symm_apply_eq.mpr h.symm).symm
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma bt_probDist_map_fst (P : ProbDist (α × β)) : P.map Prod.fst = P.fst := by
  classical
  unfold ProbDist.map ProbDist.fst
  congr; funext a
  rw [Fintype.sum_prod_type]
  refine Finset.sum_eq_single a (fun a' _ hne => by simp [hne])
    (fun h => absurd (Finset.mem_univ _) h) |>.trans ?_
  simp

private lemma bt_probDist_map_snd (P : ProbDist (α × β)) : P.map Prod.snd = P.snd := by
  classical
  unfold ProbDist.map ProbDist.snd
  congr; funext b
  rw [Fintype.sum_prod_type_right]
  refine Finset.sum_eq_single b (fun b' _ hne => by simp [hne])
    (fun h => absurd (Finset.mem_univ _) h) |>.trans ?_
  simp

private lemma bt_shannonEntropy_map_injective (P : ProbDist α) {f : α → β}
    (hf : Function.Injective f) :
    shannonEntropy (P.map f) = shannonEntropy P := by
  have : Nonempty α := bt_nonempty_of_probDist P
  let g : β → α := Function.invFun f
  have hgf : g ∘ f = id := funext (Function.leftInverse_invFun hf)
  have h1 : shannonEntropy (P.map f) ≤ shannonEntropy P := shannonEntropy_map_le f P
  have h2 : shannonEntropy P ≤ shannonEntropy (P.map f) := by
    have heq : (P.map f).map g = P := by
      rw [map_comp_eq, hgf, bt_probDist_map_id]
    calc shannonEntropy P = shannonEntropy ((P.map f).map g) := by rw [heq]
      _ ≤ shannonEntropy (P.map f) := shannonEntropy_map_le g (P.map f)
  exact le_antisymm h1 h2

private lemma bt_probDist_map_congr_support (P : ProbDist α) {f g : α → β}
    (h : ∀ a, 0 < P.pmf a → f a = g a) :
    P.map f = P.map g := by
  classical
  refine bt_probDist_ext fun b => ?_
  unfold ProbDist.map; dsimp only
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases hp : 0 < P.pmf a
  · rw [h a hp]
  · have hp0 : P.pmf a = 0 := le_antisymm (not_lt.mp hp) (P.nonneg a)
    simp [hp0]

private lemma bt_shannonEntropy_map_pair_det (P : ProbDist α) (f : α → β) (g : α → γ)
    (hdet : ∃ φ : γ → β, ∀ a, 0 < P.pmf a → f a = φ (g a)) :
    shannonEntropy (P.map (fun a => (f a, g a))) = shannonEntropy (P.map g) := by
  rcases hdet with ⟨φ, hφ⟩
  have heq : P.map (fun a => (f a, g a)) = (P.map g).map (fun c => (φ c, c)) := by
    rw [map_comp_eq]
    exact bt_probDist_map_congr_support P (fun a ha => by simp [hφ a ha])
  rw [heq]
  exact bt_shannonEntropy_map_injective (P.map g) (fun c₁ c₂ h => congrArg Prod.snd h)

private lemma bt_shannonEntropy_map_eq_of_bij (P : ProbDist α) (f : α → β) (g : α → γ)
    (h1 : ∃ φ : β → γ, ∀ a, φ (f a) = g a)
    (h2 : ∃ ψ : γ → β, ∀ a, ψ (g a) = f a) :
    shannonEntropy (P.map f) = shannonEntropy (P.map g) := by
  rcases h1 with ⟨φ, hφ⟩
  rcases h2 with ⟨ψ, hψ⟩
  have hle1 : shannonEntropy (P.map g) ≤ shannonEntropy (P.map f) := by
    have heq : (P.map f).map φ = P.map g := by
      rw [map_comp_eq]; congr; funext a; exact hφ a
    rw [← heq]
    exact shannonEntropy_map_le φ (P.map f)
  have hle2 : shannonEntropy (P.map f) ≤ shannonEntropy (P.map g) := by
    have heq : (P.map g).map ψ = P.map f := by
      rw [map_comp_eq]; congr; funext a; exact hψ a
    rw [← heq]
    exact shannonEntropy_map_le ψ (P.map g)
  exact le_antisymm hle2 hle1

private lemma bt_condMutualInfo_symm (Q : ProbDist (α × β × γ)) :
    condMutualInfo (Q.map (fun t => (t.2.1, t.1, t.2.2))) = condMutualInfo Q := by
  let e : (α × β × γ) ≃ (β × α × γ) :=
    { toFun := fun t => (t.2.1, t.1, t.2.2)
      invFun := fun t => (t.2.1, t.1, t.2.2)
      left_inv := fun ⟨_, _, _⟩ => rfl
      right_inv := fun ⟨_, _, _⟩ => rfl }
  unfold condMutualInfo
  have hAll : shannonEntropy (Q.map (fun t => (t.2.1, t.1, t.2.2))) = shannonEntropy Q :=
    shannonEntropy_map_equiv e Q
  have h1 : (Q.map (fun t => (t.2.1, t.1, t.2.2))).map (fun t => (t.1, t.2.2)) =
      Q.map (fun t => (t.2.1, t.2.2)) := by rw [map_comp_eq]; rfl
  have h2 : (Q.map (fun t => (t.2.1, t.1, t.2.2))).map (fun t => (t.2.1, t.2.2)) =
      Q.map (fun t => (t.1, t.2.2)) := by rw [map_comp_eq]; rfl
  have h3 : (Q.map (fun t => (t.2.1, t.1, t.2.2))).map (fun t => t.2.2) =
      Q.map (fun t => t.2.2) := by rw [map_comp_eq]; rfl
  dsimp only
  rw [hAll, h1, h2, h3]; ring

private lemma bt_condMutualInfo_map_fst_equiv (Q : ProbDist (α × β × γ)) (e : α ≃ δ) :
    condMutualInfo (Q.map (fun t => (e t.1, t.2.1, t.2.2))) = condMutualInfo Q := by
  let eAll : (α × β × γ) ≃ (δ × β × γ) :=
    { toFun := fun t => (e t.1, t.2.1, t.2.2)
      invFun := fun t => (e.symm t.1, t.2.1, t.2.2)
      left_inv := fun ⟨a, b, c⟩ => by simp
      right_inv := fun ⟨d, b, c⟩ => by simp }
  let eXZ : (α × γ) ≃ (δ × γ) :=
    { toFun := fun p => (e p.1, p.2)
      invFun := fun p => (e.symm p.1, p.2)
      left_inv := fun ⟨a, c⟩ => by simp
      right_inv := fun ⟨d, c⟩ => by simp }
  unfold condMutualInfo
  have hAll : shannonEntropy (Q.map (fun t => (e t.1, t.2.1, t.2.2))) = shannonEntropy Q :=
    shannonEntropy_map_equiv eAll Q
  have hXZ : shannonEntropy ((Q.map (fun t => (e t.1, t.2.1, t.2.2))).map (fun t => (t.1, t.2.2))) =
      shannonEntropy (Q.map (fun t => (t.1, t.2.2))) := by
    rw [map_comp_eq]
    have hcomp : ((fun t : δ × β × γ => (t.1, t.2.2)) ∘ fun t : α × β × γ => (e t.1, t.2.1, t.2.2)) =
        eXZ ∘ (fun t : α × β × γ => (t.1, t.2.2)) := rfl
    rw [hcomp, ← map_comp_eq, shannonEntropy_map_equiv eXZ]
  have hYZ : (Q.map (fun t => (e t.1, t.2.1, t.2.2))).map (fun t => (t.2.1, t.2.2)) =
      Q.map (fun t => (t.2.1, t.2.2)) := by rw [map_comp_eq]; rfl
  have hZ : (Q.map (fun t => (e t.1, t.2.1, t.2.2))).map (fun t => t.2.2) =
      Q.map (fun t => t.2.2) := by rw [map_comp_eq]; rfl
  dsimp only
  rw [hAll, hXZ, hYZ, hZ]

private lemma bt_condMutualInfo_map_snd_equiv (Q : ProbDist (α × β × γ)) (e : β ≃ δ) :
    condMutualInfo (Q.map (fun t => (t.1, e t.2.1, t.2.2))) = condMutualInfo Q := by
  have h1 : condMutualInfo (Q.map (fun t => (t.1, e t.2.1, t.2.2))) =
      condMutualInfo ((Q.map (fun t => (t.1, e t.2.1, t.2.2))).map (fun t => (t.2.1, t.1, t.2.2))) :=
    (bt_condMutualInfo_symm _).symm
  rw [h1, map_comp_eq]
  have hcomp : ((fun t : α × δ × γ => (t.2.1, t.1, t.2.2)) ∘
      fun t : α × β × γ => (t.1, e t.2.1, t.2.2)) =
      (fun t : β × α × γ => (e t.1, t.2.1, t.2.2)) ∘
        fun t : α × β × γ => (t.2.1, t.1, t.2.2) := rfl
  rw [hcomp, ← map_comp_eq, bt_condMutualInfo_map_fst_equiv, bt_condMutualInfo_symm]

private lemma bt_condMutualInfo_map_thd_equiv (Q : ProbDist (α × β × γ)) (e : γ ≃ δ) :
    condMutualInfo (Q.map (fun t => (t.1, t.2.1, e t.2.2))) = condMutualInfo Q := by
  let eAll : (α × β × γ) ≃ (α × β × δ) :=
    { toFun := fun t => (t.1, t.2.1, e t.2.2)
      invFun := fun t => (t.1, t.2.1, e.symm t.2.2)
      left_inv := fun ⟨a, b, c⟩ => by simp
      right_inv := fun ⟨a, b, d⟩ => by simp }
  let eXZ : (α × γ) ≃ (α × δ) :=
    { toFun := fun p => (p.1, e p.2)
      invFun := fun p => (p.1, e.symm p.2)
      left_inv := fun ⟨a, c⟩ => by simp
      right_inv := fun ⟨a, d⟩ => by simp }
  let eYZ : (β × γ) ≃ (β × δ) :=
    { toFun := fun p => (p.1, e p.2)
      invFun := fun p => (p.1, e.symm p.2)
      left_inv := fun ⟨b, c⟩ => by simp
      right_inv := fun ⟨b, d⟩ => by simp }
  unfold condMutualInfo
  have hAll : shannonEntropy (Q.map (fun t => (t.1, t.2.1, e t.2.2))) = shannonEntropy Q :=
    shannonEntropy_map_equiv eAll Q
  have hXZ : shannonEntropy ((Q.map (fun t => (t.1, t.2.1, e t.2.2))).map (fun t => (t.1, t.2.2))) =
      shannonEntropy (Q.map (fun t => (t.1, t.2.2))) := by
    rw [map_comp_eq]
    have hcomp : ((fun t : α × β × δ => (t.1, t.2.2)) ∘ fun t : α × β × γ => (t.1, t.2.1, e t.2.2)) =
        eXZ ∘ (fun t : α × β × γ => (t.1, t.2.2)) := rfl
    rw [hcomp, ← map_comp_eq, shannonEntropy_map_equiv eXZ]
  have hYZ : shannonEntropy ((Q.map (fun t => (t.1, t.2.1, e t.2.2))).map (fun t => (t.2.1, t.2.2))) =
      shannonEntropy (Q.map (fun t => (t.2.1, t.2.2))) := by
    rw [map_comp_eq]
    have hcomp : ((fun t : α × β × δ => (t.2.1, t.2.2)) ∘ fun t : α × β × γ => (t.1, t.2.1, e t.2.2)) =
        eYZ ∘ (fun t : α × β × γ => (t.2.1, t.2.2)) := rfl
    rw [hcomp, ← map_comp_eq, shannonEntropy_map_equiv eYZ]
  have hZ : shannonEntropy ((Q.map (fun t => (t.1, t.2.1, e t.2.2))).map (fun t => t.2.2)) =
      shannonEntropy (Q.map (fun t => t.2.2)) := by
    rw [map_comp_eq]
    have hcomp : ((fun t : α × β × δ => t.2.2) ∘ fun t : α × β × γ => (t.1, t.2.1, e t.2.2)) =
        e ∘ (fun t : α × β × γ => t.2.2) := rfl
    rw [hcomp, ← map_comp_eq, shannonEntropy_map_equiv e]
  dsimp only
  rw [hAll, hXZ, hYZ, hZ]

/-- Chain rule for conditional mutual information:
    `I(X; (Y, W) | Z) = I(X; Y | Z) + I(X; W | Y, Z)`. -/
private lemma bt_condMutualInfo_chain_rule (Q : ProbDist (α × β × γ × δ)) :
    condMutualInfo (Q.map (fun t => (t.1, (t.2.1, t.2.2.1), t.2.2.2))) =
      condMutualInfo (Q.map (fun t => (t.1, t.2.1, t.2.2.2))) +
      condMutualInfo (Q.map (fun t => (t.1, t.2.2.1, (t.2.1, t.2.2.2)))) := by
  unfold condMutualInfo
  dsimp only
  simp_rw [map_comp_eq]
  have hAll : shannonEntropy (Q.map (fun t => (t.1, (t.2.1, t.2.2.1), t.2.2.2))) =
      shannonEntropy (Q.map (fun t => (t.1, t.2.2.1, (t.2.1, t.2.2.2)))) :=
    bt_shannonEntropy_map_eq_of_bij Q _ _
      ⟨fun t => (t.1, t.2.1.2, (t.2.1.1, t.2.2)), fun _ => rfl⟩
      ⟨fun t => (t.1, (t.2.2.1, t.2.1), t.2.2.2), fun _ => rfl⟩
  have hYWZ : shannonEntropy (Q.map ((fun t : α × (β × γ) × δ => (t.2.1, t.2.2)) ∘
        fun t : α × β × γ × δ => (t.1, (t.2.1, t.2.2.1), t.2.2.2))) =
      shannonEntropy (Q.map ((fun t : α × γ × (β × δ) => (t.2.1, t.2.2)) ∘
        fun t : α × β × γ × δ => (t.1, t.2.2.1, (t.2.1, t.2.2.2)))) :=
    bt_shannonEntropy_map_eq_of_bij Q _ _
      ⟨fun p => (p.1.2, (p.1.1, p.2)), fun _ => rfl⟩
      ⟨fun p => ((p.2.1, p.1), p.2.2), fun _ => rfl⟩
  have hXYZ : shannonEntropy (Q.map (fun t : α × β × γ × δ => (t.1, t.2.1, t.2.2.2))) =
      shannonEntropy (Q.map ((fun t : α × γ × (β × δ) => (t.1, t.2.2)) ∘
        fun t : α × β × γ × δ => (t.1, t.2.2.1, (t.2.1, t.2.2.2)))) :=
    bt_shannonEntropy_map_eq_of_bij Q _ _
      ⟨fun p => (p.1, (p.2.1, p.2.2)), fun _ => rfl⟩
      ⟨fun p => (p.1, p.2.1, p.2.2), fun _ => rfl⟩
  have hXZ : (Q.map ((fun t : α × (β × γ) × δ => (t.1, t.2.2)) ∘
        fun t : α × β × γ × δ => (t.1, (t.2.1, t.2.2.1), t.2.2.2))) =
      Q.map ((fun t : α × β × δ => (t.1, t.2.2)) ∘
        fun t : α × β × γ × δ => (t.1, t.2.1, t.2.2.2)) := rfl
  have hYZ : (Q.map ((fun t : α × β × δ => (t.2.1, t.2.2)) ∘
        fun t : α × β × γ × δ => (t.1, t.2.1, t.2.2.2))) =
      Q.map ((fun t : α × γ × (β × δ) => t.2.2) ∘
        fun t : α × β × γ × δ => (t.1, t.2.2.1, (t.2.1, t.2.2.2))) := rfl
  have hZ : (Q.map ((fun t : α × (β × γ) × δ => t.2.2) ∘
        fun t : α × β × γ × δ => (t.1, (t.2.1, t.2.2.1), t.2.2.2))) =
      Q.map ((fun t : α × β × δ => t.2.2) ∘
        fun t : α × β × γ × δ => (t.1, t.2.1, t.2.2.2)) := rfl
  rw [hAll, hYWZ, hXYZ, hXZ, hYZ, hZ]
  ring

/-- If `I(X; (Y, W) | Z) = 0`, then `I(X; Y | Z) = 0` and `I(X; W | Y, Z) = 0`. -/
private lemma bt_condMutualInfo_zero_split (Q : ProbDist (α × β × γ × δ))
    (h0 : condMutualInfo (Q.map (fun t => (t.1, (t.2.1, t.2.2.1), t.2.2.2))) = 0) :
    condMutualInfo (Q.map (fun t => (t.1, t.2.1, t.2.2.2))) = 0 ∧
    condMutualInfo (Q.map (fun t => (t.1, t.2.2.1, (t.2.1, t.2.2.2)))) = 0 := by
  have hcr := bt_condMutualInfo_chain_rule Q
  have h1 : 0 ≤ condMutualInfo (Q.map (fun t => (t.1, t.2.1, t.2.2.2))) := condMutualInfo_nonneg _
  have h2 : 0 ≤ condMutualInfo (Q.map (fun t => (t.1, t.2.2.1, (t.2.1, t.2.2.2)))) :=
    condMutualInfo_nonneg _
  constructor <;> linarith

/-- If `I(X; (Y, W) | Z) = 0`, then also `I(X; W | Z) = 0` and `I(X; Y | W, Z) = 0`. -/
private lemma bt_condMutualInfo_zero_split_swap (Q : ProbDist (α × β × γ × δ))
    (h0 : condMutualInfo (Q.map (fun t => (t.1, (t.2.1, t.2.2.1), t.2.2.2))) = 0) :
    condMutualInfo (Q.map (fun t => (t.1, t.2.2.1, t.2.2.2))) = 0 ∧
    condMutualInfo (Q.map (fun t => (t.1, t.2.1, (t.2.2.1, t.2.2.2)))) = 0 := by
  let Q' : ProbDist (α × γ × β × δ) := Q.map (fun t => (t.1, t.2.2.1, t.2.1, t.2.2.2))
  have h0' : condMutualInfo (Q'.map (fun t => (t.1, (t.2.1, t.2.2.1), t.2.2.2))) = 0 := by
    unfold Q'; rw [map_comp_eq]
    have hcomp : ((fun t : α × γ × β × δ => (t.1, (t.2.1, t.2.2.1), t.2.2.2)) ∘
        fun t : α × β × γ × δ => (t.1, t.2.2.1, t.2.1, t.2.2.2)) =
        (fun t : α × (β × γ) × δ => (t.1, (Equiv.prodComm β γ) t.2.1, t.2.2)) ∘
          fun t : α × β × γ × δ => (t.1, (t.2.1, t.2.2.1), t.2.2.2) := rfl
    rw [hcomp, ← map_comp_eq, bt_condMutualInfo_map_snd_equiv, h0]
  have hs := bt_condMutualInfo_zero_split Q' h0'
  unfold Q' at hs
  rw [map_comp_eq, map_comp_eq] at hs
  exact hs

/-- If `X` is a deterministic function of `Z`, then `I(X; Y | Z) = 0`. -/
private lemma bt_condMutualInfo_eq_zero_of_det_left (P : ProbDist (β × γ)) (f : γ → α) :
    condMutualInfo (P.map (fun bc => (f bc.2, bc.1, bc.2))) = 0 := by
  unfold condMutualInfo; dsimp only
  simp_rw [map_comp_eq]
  have hAll : shannonEntropy (P.map (fun bc : β × γ => (f bc.2, bc.1, bc.2))) =
      shannonEntropy P :=
    bt_shannonEntropy_map_injective P (fun ⟨b₁, c₁⟩ ⟨b₂, c₂⟩ h =>
      Prod.ext (congrArg (fun t => t.2.1) h) (congrArg (fun t => t.2.2) h))
  have hXZ : shannonEntropy (P.map ((fun t : α × β × γ => (t.1, t.2.2)) ∘
        fun bc : β × γ => (f bc.2, bc.1, bc.2))) =
      shannonEntropy (P.map Prod.snd) :=
    bt_shannonEntropy_map_eq_of_bij P _ _
      ⟨Prod.snd, fun _ => rfl⟩
      ⟨fun c => (f c, c), fun _ => rfl⟩
  have hYZ : P.map ((fun t : α × β × γ => (t.2.1, t.2.2)) ∘
        fun bc : β × γ => (f bc.2, bc.1, bc.2)) = P := by
    have : ((fun t : α × β × γ => (t.2.1, t.2.2)) ∘ fun bc : β × γ => (f bc.2, bc.1, bc.2)) = id :=
      rfl
    rw [this, bt_probDist_map_id]
  have hZ : P.map ((fun t : α × β × γ => t.2.2) ∘
        fun bc : β × γ => (f bc.2, bc.1, bc.2)) = P.map Prod.snd := rfl
  rw [hAll, hXZ, hYZ, hZ]; ring

/-- Key Berger–Tung inner-bound identity 1:
    under `U₁ — X₁ — (X₂, U₂)`, `I(X₁, X₂; U₁ | U₂) = I(X₁; U₁ | U₂)`. -/
private lemma bt_cmi_X1X2_U1_given_U2_eq
    (Q : ProbDist (α × β × γ × δ))
    (hmk1 : condMutualInfo (Q.map (fun t => (t.2.2.1, (t.2.1, t.2.2.2), t.1))) = 0) :
    condMutualInfo (Q.map (fun t => ((t.1, t.2.1), t.2.2.1, t.2.2.2))) =
      condMutualInfo (Q.map (fun t => (t.1, t.2.2.1, t.2.2.2))) := by
  -- Apply chain rule to `(U₁, X₁, X₂, U₂)`:
  -- `I(U₁; (X₁, X₂) | U₂) = I(U₁; X₁ | U₂) + I(U₁; X₂ | X₁, U₂)`.
  let R : ProbDist (γ × α × β × δ) := Q.map (fun t => (t.2.2.1, t.1, t.2.1, t.2.2.2))
  have hcr := bt_condMutualInfo_chain_rule R
  -- Show `I(U₁; X₂ | X₁, U₂) = 0` from `hmk1`.
  let R1 : ProbDist (γ × β × δ × α) := Q.map (fun t => (t.2.2.1, t.2.1, t.2.2.2, t.1))
  have hR1 : condMutualInfo (R1.map (fun t => (t.1, (t.2.1, t.2.2.1), t.2.2.2))) = 0 := by
    unfold R1; rw [map_comp_eq]; exact hmk1
  have hzero := (bt_condMutualInfo_zero_split_swap R1 hR1).2
  unfold R1 at hzero; rw [map_comp_eq] at hzero
  -- Compare `I(U₁; X₂ | (U₂, X₁))` with `I(U₁; X₂ | (X₁, U₂))` via `Equiv.prodComm`.
  have hzero' : condMutualInfo (R.map (fun t => (t.1, t.2.2.1, (t.2.1, t.2.2.2)))) = 0 := by
    unfold R; rw [map_comp_eq]
    have hcomp : ((fun t : γ × α × β × δ => (t.1, t.2.2.1, (t.2.1, t.2.2.2))) ∘
        fun t : α × β × γ × δ => (t.2.2.1, t.1, t.2.1, t.2.2.2)) =
        (fun t : γ × β × (δ × α) => (t.1, t.2.1, (Equiv.prodComm δ α) t.2.2)) ∘
          fun t : α × β × γ × δ => (t.2.2.1, t.2.1, (t.2.2.2, t.1)) := rfl
    rw [hcomp, ← map_comp_eq, bt_condMutualInfo_map_thd_equiv]
    exact hzero
  have hsym1 : condMutualInfo (Q.map (fun t => ((t.1, t.2.1), t.2.2.1, t.2.2.2))) =
      condMutualInfo (R.map (fun t => (t.1, (t.2.1, t.2.2.1), t.2.2.2))) := by
    rw [← bt_condMutualInfo_symm (Q.map (fun t => ((t.1, t.2.1), t.2.2.1, t.2.2.2))), map_comp_eq]
    unfold R; rw [map_comp_eq]; rfl
  have hsym2 : condMutualInfo (Q.map (fun t => (t.1, t.2.2.1, t.2.2.2))) =
      condMutualInfo (R.map (fun t => (t.1, t.2.1, t.2.2.2))) := by
    rw [← bt_condMutualInfo_symm (Q.map (fun t => (t.1, t.2.2.1, t.2.2.2))), map_comp_eq]
    unfold R; rw [map_comp_eq]; rfl
  rw [hsym1, hsym2, hcr, hzero', add_zero]

/-- Key Berger–Tung inner-bound identity 2:
    under `U₂ — X₂ — (X₁, U₁)`, `I(X₁, X₂; U₂ | U₁) = I(X₂; U₂ | U₁)`. -/
private lemma bt_cmi_X1X2_U2_given_U1_eq
    (Q : ProbDist (α × β × γ × δ))
    (hmk2 : condMutualInfo (Q.map (fun t => (t.2.2.2, (t.1, t.2.2.1), t.2.1))) = 0) :
    condMutualInfo (Q.map (fun t => ((t.1, t.2.1), t.2.2.2, t.2.2.1))) =
      condMutualInfo (Q.map (fun t => (t.2.1, t.2.2.2, t.2.2.1))) := by
  let Qswap : ProbDist (β × α × δ × γ) := Q.map (fun t => (t.2.1, t.1, t.2.2.2, t.2.2.1))
  have hmk1' : condMutualInfo (Qswap.map (fun t => (t.2.2.1, (t.2.1, t.2.2.2), t.1))) = 0 := by
    unfold Qswap; rw [map_comp_eq]; exact hmk2
  have h := bt_cmi_X1X2_U1_given_U2_eq Qswap hmk1'
  unfold Qswap at h
  rw [map_comp_eq, map_comp_eq] at h
  have hL : condMutualInfo (Q.map (fun t => ((t.1, t.2.1), t.2.2.2, t.2.2.1))) =
      condMutualInfo (Q.map ((fun t : β × α × δ × γ => ((t.1, t.2.1), t.2.2.1, t.2.2.2)) ∘
        fun t : α × β × γ × δ => (t.2.1, t.1, t.2.2.2, t.2.2.1))) := by
    have hcomp : ((fun t : β × α × δ × γ => ((t.1, t.2.1), t.2.2.1, t.2.2.2)) ∘
        fun t : α × β × γ × δ => (t.2.1, t.1, t.2.2.2, t.2.2.1)) =
        (fun t : (α × β) × δ × γ => ((Equiv.prodComm α β) t.1, t.2.1, t.2.2)) ∘
          fun t : α × β × γ × δ => ((t.1, t.2.1), t.2.2.2, t.2.2.1) := rfl
    rw [hcomp, ← map_comp_eq, bt_condMutualInfo_map_fst_equiv]
  rw [hL, h]; rfl

/-- Symmetry of mutual information: `I(Y; X) = I(X; Y)`. -/
private lemma bt_mutualInfo_symm (P : ProbDist (α × β)) :
    mutualInfo (P.map Prod.swap) = mutualInfo P := by
  unfold mutualInfo
  have h1 : (P.map Prod.swap).fst = P.snd := by
    rw [← bt_probDist_map_fst, ← bt_probDist_map_snd, map_comp_eq]; rfl
  have h2 : (P.map Prod.swap).snd = P.fst := by
    rw [← bt_probDist_map_snd, ← bt_probDist_map_fst, map_comp_eq]; rfl
  have h3 : shannonEntropy (P.map Prod.swap) = shannonEntropy P :=
    shannonEntropy_map_equiv (Equiv.prodComm α β) P
  rw [h1, h2, h3]; ring

/-- Key identity: under `U₁ — X₁ — U₂` (i.e. `I(U₁; U₂ | X₁) = 0`),
    `I(X₁; U₁ | U₂) = I(X₁; U₁) - I(U₁; U₂)`. -/
private lemma bt_cmi_eq_sub_of_markov (Q : ProbDist (α × β × γ))
    (hmk : condMutualInfo (Q.map (fun t => (t.2.1, t.2.2, t.1))) = 0) :
    condMutualInfo Q =
      mutualInfo (Q.map (fun t => (t.1, t.2.1))) -
      mutualInfo (Q.map (fun t => (t.2.1, t.2.2))) := by
  unfold condMutualInfo at hmk ⊢
  unfold mutualInfo
  dsimp only at hmk ⊢
  simp_rw [map_comp_eq] at hmk
  have hQ_all : shannonEntropy (Q.map (fun t => (t.2.1, t.2.2, t.1))) = shannonEntropy Q :=
    bt_shannonEntropy_map_injective Q (fun ⟨a₁, b₁, c₁⟩ ⟨a₂, b₂, c₂⟩ h => by
      dsimp only at h
      rcases Prod.mk.inj h with ⟨hb, hca⟩
      rcases Prod.mk.inj hca with ⟨hc, ha⟩
      subst ha hb hc; rfl)
  have hQ_u1x1 : shannonEntropy (Q.map ((fun t : β × γ × α => (t.1, t.2.2)) ∘
        fun t : α × β × γ => (t.2.1, t.2.2, t.1))) =
      shannonEntropy (Q.map (fun t => (t.1, t.2.1))) :=
    bt_shannonEntropy_map_eq_of_bij Q _ _
      ⟨Prod.swap, fun _ => rfl⟩ ⟨Prod.swap, fun _ => rfl⟩
  have hQ_u2x1 : shannonEntropy (Q.map ((fun t : β × γ × α => (t.2.1, t.2.2)) ∘
        fun t : α × β × γ => (t.2.1, t.2.2, t.1))) =
      shannonEntropy (Q.map (fun t => (t.1, t.2.2))) :=
    bt_shannonEntropy_map_eq_of_bij Q _ _
      ⟨Prod.swap, fun _ => rfl⟩ ⟨Prod.swap, fun _ => rfl⟩
  have hX1 : (Q.map (fun t => (t.1, t.2.1))).fst =
      Q.map ((fun t : β × γ × α => t.2.2) ∘ fun t : α × β × γ => (t.2.1, t.2.2, t.1)) := by
    rw [← bt_probDist_map_fst, map_comp_eq]; rfl
  have hU1_1 : (Q.map (fun t => (t.1, t.2.1))).snd =
      (Q.map (fun t => (t.2.1, t.2.2))).fst := by
    rw [← bt_probDist_map_snd, ← bt_probDist_map_fst, map_comp_eq, map_comp_eq]; rfl
  have hU2_1 : (Q.map (fun t => (t.2.1, t.2.2))).snd = Q.map (fun t => t.2.2) := by
    rw [← bt_probDist_map_snd, map_comp_eq]; rfl
  rw [hQ_all, hQ_u1x1, hQ_u2x1] at hmk
  rw [hX1, hU1_1, hU2_1]
  linarith

/-- Key Berger–Tung inner-bound sum-rate identity:
    under `U₁ — X₁ — (X₂, U₂)` and `U₂ — X₂ — (X₁, U₁)`,
    `I(X₁, X₂; U₁, U₂) = I(X₁; U₁) + I(X₂; U₂) - I(U₁; U₂)`. -/
private lemma bt_mi_X1X2_U1U2_eq_sum_sub
    (Q : ProbDist (α × β × γ × δ))
    (hmk1 : condMutualInfo (Q.map (fun t => (t.2.2.1, (t.2.1, t.2.2.2), t.1))) = 0)
    (hmk2 : condMutualInfo (Q.map (fun t => (t.2.2.2, (t.1, t.2.2.1), t.2.1))) = 0) :
    mutualInfo (Q.map (fun t => ((t.1, t.2.1), (t.2.2.1, t.2.2.2)))) =
      mutualInfo (Q.map (fun t => (t.1, t.2.2.1))) +
      mutualInfo (Q.map (fun t => (t.2.1, t.2.2.2))) -
      mutualInfo (Q.map (fun t => (t.2.2.1, t.2.2.2))) := by
  -- From `hmk1`, `I(U₁; X₂ | X₁) = 0`.
  let R1 : ProbDist (γ × β × δ × α) := Q.map (fun t => (t.2.2.1, t.2.1, t.2.2.2, t.1))
  have hR1 : condMutualInfo (R1.map (fun t => (t.1, (t.2.1, t.2.2.1), t.2.2.2))) = 0 := by
    unfold R1; rw [map_comp_eq]; exact hmk1
  have hU1_X2_X1 : condMutualInfo (Q.map (fun t => (t.2.2.1, t.2.1, t.1))) = 0 := by
    have h := (bt_condMutualInfo_zero_split R1 hR1).1
    unfold R1 at h; rw [map_comp_eq] at h; exact h
  -- From `hmk2`, `I(U₂; U₁ | X₂) = 0`.
  let R2 : ProbDist (δ × α × γ × β) := Q.map (fun t => (t.2.2.2, t.1, t.2.2.1, t.2.1))
  have hR2 : condMutualInfo (R2.map (fun t => (t.1, (t.2.1, t.2.2.1), t.2.2.2))) = 0 := by
    unfold R2; rw [map_comp_eq]; exact hmk2
  have hU2_U1_X2 : condMutualInfo (Q.map (fun t => (t.2.2.2, t.2.2.1, t.2.1))) = 0 := by
    have h := (bt_condMutualInfo_zero_split_swap R2 hR2).1
    unfold R2 at h; rw [map_comp_eq] at h; exact h
  -- `I(X₁, X₂; U₁, U₂) = I(X₁, X₂; U₁) + I(X₁, X₂; U₂ | U₁)`.
  have hchain : mutualInfo (Q.map (fun t => ((t.1, t.2.1), (t.2.2.1, t.2.2.2)))) =
      mutualInfo (Q.map (fun t => ((t.1, t.2.1), t.2.2.1))) +
      condMutualInfo (Q.map (fun t => ((t.1, t.2.1), t.2.2.2, t.2.2.1))) := by
    unfold mutualInfo condMutualInfo; dsimp only
    simp_rw [map_comp_eq]
    have h1 : (Q.map (fun t => ((t.1, t.2.1), (t.2.2.1, t.2.2.2)))).fst =
        (Q.map (fun t => ((t.1, t.2.1), t.2.2.1))).fst := by
      rw [← bt_probDist_map_fst, ← bt_probDist_map_fst, map_comp_eq, map_comp_eq]; rfl
    have h2 : shannonEntropy (Q.map (fun t => ((t.1, t.2.1), (t.2.2.1, t.2.2.2)))).snd =
        shannonEntropy (Q.map ((fun t : (α × β) × δ × γ => (t.2.1, t.2.2)) ∘
          fun t : α × β × γ × δ => ((t.1, t.2.1), t.2.2.2, t.2.2.1))) := by
      rw [← bt_probDist_map_snd, map_comp_eq]
      exact bt_shannonEntropy_map_eq_of_bij Q _ _
        ⟨Prod.swap, fun _ => rfl⟩ ⟨Prod.swap, fun _ => rfl⟩
    have h3 : shannonEntropy (Q.map (fun t => ((t.1, t.2.1), (t.2.2.1, t.2.2.2)))) =
        shannonEntropy (Q.map (fun t => ((t.1, t.2.1), t.2.2.2, t.2.2.1))) :=
      bt_shannonEntropy_map_eq_of_bij Q _ _
        ⟨fun t => (t.1, t.2.2, t.2.1), fun _ => rfl⟩
        ⟨fun t => (t.1, (t.2.2, t.2.1)), fun _ => rfl⟩
    have h4 : (Q.map (fun t => ((t.1, t.2.1), t.2.2.1))).snd =
        Q.map ((fun t : (α × β) × δ × γ => t.2.2) ∘
          fun t : α × β × γ × δ => ((t.1, t.2.1), t.2.2.2, t.2.2.1)) := by
      rw [← bt_probDist_map_snd, map_comp_eq]; rfl
    have h5 : Q.map ((fun t : (α × β) × δ × γ => (t.1, t.2.2)) ∘
          fun t : α × β × γ × δ => ((t.1, t.2.1), t.2.2.2, t.2.2.1)) =
        Q.map (fun t => ((t.1, t.2.1), t.2.2.1)) := rfl
    rw [h1, h2, h3, h4, h5]; ring
  -- `I(X₁, X₂; U₁) = I(X₁; U₁)` since `I(U₁; X₂ | X₁) = 0`.
  have hfirst : mutualInfo (Q.map (fun t => ((t.1, t.2.1), t.2.2.1))) =
      mutualInfo (Q.map (fun t => (t.1, t.2.2.1))) := by
    unfold mutualInfo at ⊢
    unfold condMutualInfo at hU1_X2_X1
    dsimp only at hU1_X2_X1
    simp_rw [map_comp_eq] at hU1_X2_X1
    have hAll : shannonEntropy (Q.map (fun t => (t.2.2.1, t.2.1, t.1))) =
        shannonEntropy (Q.map (fun t => ((t.1, t.2.1), t.2.2.1))) :=
      bt_shannonEntropy_map_eq_of_bij Q _ _
        ⟨fun t => ((t.2.2, t.2.1), t.1), fun _ => rfl⟩
        ⟨fun t => (t.2, t.1.2, t.1.1), fun _ => rfl⟩
    have hU1X1 : shannonEntropy (Q.map ((fun t : γ × β × α => (t.1, t.2.2)) ∘
          fun t : α × β × γ × δ => (t.2.2.1, t.2.1, t.1))) =
        shannonEntropy (Q.map (fun t => (t.1, t.2.2.1))) :=
      bt_shannonEntropy_map_eq_of_bij Q _ _
        ⟨Prod.swap, fun _ => rfl⟩ ⟨Prod.swap, fun _ => rfl⟩
    have hX2X1 : shannonEntropy (Q.map ((fun t : γ × β × α => (t.2.1, t.2.2)) ∘
          fun t : α × β × γ × δ => (t.2.2.1, t.2.1, t.1))) =
        shannonEntropy (Q.map (fun t => ((t.1, t.2.1), t.2.2.1))).fst := by
      rw [← bt_probDist_map_fst, map_comp_eq]
      exact bt_shannonEntropy_map_eq_of_bij Q _ _
        ⟨Prod.swap, fun _ => rfl⟩ ⟨Prod.swap, fun _ => rfl⟩
    have hX1 : (Q.map (fun t => (t.1, t.2.2.1))).fst =
        Q.map ((fun t : γ × β × α => t.2.2) ∘ fun t : α × β × γ × δ => (t.2.2.1, t.2.1, t.1)) := by
      rw [← bt_probDist_map_fst, map_comp_eq]; rfl
    have hU1 : (Q.map (fun t => ((t.1, t.2.1), t.2.2.1))).snd =
        (Q.map (fun t => (t.1, t.2.2.1))).snd := by
      rw [← bt_probDist_map_snd, ← bt_probDist_map_snd, map_comp_eq, map_comp_eq]; rfl
    rw [hAll, hU1X1, hX2X1] at hU1_X2_X1
    rw [hX1, hU1]
    linarith
  -- `I(X₁, X₂; U₂ | U₁) = I(X₂; U₂ | U₁) = I(X₂; U₂) - I(U₁; U₂)`.
  have hsecond : condMutualInfo (Q.map (fun t => ((t.1, t.2.1), t.2.2.2, t.2.2.1))) =
      mutualInfo (Q.map (fun t => (t.2.1, t.2.2.2))) -
      mutualInfo (Q.map (fun t => (t.2.2.1, t.2.2.2))) := by
    rw [bt_cmi_X1X2_U2_given_U1_eq Q hmk2]
    have hsub := bt_cmi_eq_sub_of_markov (Q.map (fun t => (t.2.1, t.2.2.2, t.2.2.1))) (by
      rw [map_comp_eq]; exact hU2_U1_X2)
    rw [hsub, map_comp_eq, map_comp_eq]
    have hcomm : mutualInfo (Q.map ((fun t : β × δ × γ => (t.2.1, t.2.2)) ∘
          fun t : α × β × γ × δ => (t.2.1, t.2.2.2, t.2.2.1))) =
        mutualInfo (Q.map (fun t => (t.2.2.1, t.2.2.2))) := by
      have heq : Q.map ((fun t : β × δ × γ => (t.2.1, t.2.2)) ∘
          fun t : α × β × γ × δ => (t.2.1, t.2.2.2, t.2.2.1)) =
          (Q.map (fun t => (t.2.2.1, t.2.2.2))).map Prod.swap := by
        rw [map_comp_eq]; rfl
      rw [heq, bt_mutualInfo_symm]
    rw [hcomm]; rfl
  rw [hchain, hfirst, hsecond]; ring

private lemma bt_iidDist_map_coord (P : ProbDist α) {n : ℕ} (i : Fin n) :
    (iidDist P n).map (fun x => x i) = P := by
  classical
  unfold ProbDist.map
  congr; funext a; dsimp only
  have h1 : (∑ x : Fin n → α, if x i = a then (iidDist P n).pmf x else 0) =
      ∑ x : Fin n → α, (iidDist P n).pmf x * (if x i = a then 1 else 0) :=
    Finset.sum_congr rfl fun x _ => by split_ifs <;> ring
  rw [h1, iidDist_sum_coord P (fun b => if b = a then 1 else 0) i]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hne; simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma bt_max_one_floor_two_rpow_le (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ((Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R))) : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R) := by
  have hge1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R) := by
    calc (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) := (Real.rpow_zero 2).symm
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * R) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by positivity)
  have hfl : 1 ≤ Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)) := Nat.le_floor (by exact_mod_cast hge1)
  change ((max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R))) : ℕ) : ℝ) ≤ _
  rw [max_eq_right hfl]
  exact Nat.floor_le (by positivity)

private lemma bt_half_two_rpow_le_max_one_floor (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    (2 : ℝ) ^ ((n : ℝ) * R) / 2 ≤
      ((Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R))) : ℕ) : ℝ) := by
  let M := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.le_max_left 1 _
  have hfl : (2 : ℝ) ^ ((n : ℝ) * R) < (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hle : (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)) : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast Nat.le_max_right 1 _
  have _ := hR
  linarith

private lemma bt_log2_two_rpow_eq (x : ℝ) : log2 ((2 : ℝ) ^ x) = x := by
  unfold log2
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  exact mul_div_cancel_right₀ x (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))

private lemma bt_log2_mono_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : log2 x ≤ log2 y := by
  unfold log2
  exact div_le_div_of_nonneg_right (Real.log_le_log hx hxy)
    (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))

private lemma bt_two_rpow_neg_le_of_ge {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)
    {n : ℕ} (hn : log2 (1 / c) / ε ≤ (n : ℝ)) :
    (2 : ℝ) ^ (-((n : ℝ) * ε)) ≤ c := by
  have h1 : log2 (1 / c) ≤ (n : ℝ) * ε := (div_le_iff₀ hε).mp hn
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog : Real.log (1 / c) ≤ (n : ℝ) * ε * Real.log 2 := by
    unfold log2 at h1
    exact (div_le_iff₀ hlog2).mp h1
  have hexp : 1 / c ≤ (2 : ℝ) ^ ((n : ℝ) * ε) := by
    calc 1 / c
      _ = Real.exp (Real.log (1 / c)) := (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp ((n : ℝ) * ε * Real.log 2) := Real.exp_le_exp.mpr hlog
      _ = Real.exp (Real.log 2 * ((n : ℝ) * ε)) := by ring_nf
      _ = (2 : ℝ) ^ ((n : ℝ) * ε) := (Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) _).symm
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-((n : ℝ) * ε)) := Real.rpow_pos_of_pos (by norm_num) _
  have hmul1 : (2 : ℝ) ^ (-((n : ℝ) * ε)) * (2 : ℝ) ^ ((n : ℝ) * ε) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), neg_add_cancel, Real.rpow_zero]
  have hmul2 : (1 / c) * (2 : ℝ) ^ (-((n : ℝ) * ε)) ≤ 1 := by
    calc (1 / c) * (2 : ℝ) ^ (-((n : ℝ) * ε))
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * ε) * (2 : ℝ) ^ (-((n : ℝ) * ε)) :=
          mul_le_mul_of_nonneg_right hexp (le_of_lt hpos)
      _ = 1 := by rw [mul_comm, hmul1]
  have hmul3 := mul_le_mul_of_nonneg_left hmul2 (le_of_lt hc)
  have hsimp : c * ((1 / c) * (2 : ℝ) ^ (-((n : ℝ) * ε))) = (2 : ℝ) ^ (-((n : ℝ) * ε)) := by
    field_simp [ne_of_gt hc]
  linarith

private lemma bt_exists_le_of_expectation_le {Ω : Type*} [Fintype Ω] (W : ProbDist Ω)
    (f : Ω → ℝ) {B : ℝ} (h : ∑ ω : Ω, W.pmf ω * f ω ≤ B) :
    ∃ ω : Ω, f ω ≤ B := by
  by_contra hall
  push Not at hall
  have hex_pos : ∃ ω₀ : Ω, 0 < W.pmf ω₀ := by
    by_contra hno
    push Not at hno
    have hzero : ∑ ω : Ω, W.pmf ω = 0 :=
      Finset.sum_eq_zero fun ω _ => le_antisymm (hno ω) (W.nonneg ω)
    linarith [W.sum_one]
  obtain ⟨ω₀, hω₀⟩ := hex_pos
  have hlt : ∑ ω : Ω, W.pmf ω * B < ∑ ω : Ω, W.pmf ω * f ω :=
    Finset.sum_lt_sum
      (fun ω _ => mul_le_mul_of_nonneg_left (le_of_lt (hall ω)) (W.nonneg ω))
      ⟨ω₀, Finset.mem_univ ω₀, mul_lt_mul_of_pos_left (hall ω₀) hω₀⟩
  have hB : ∑ ω : Ω, W.pmf ω * B = B := by rw [← Finset.sum_mul, W.sum_one, one_mul]
  linarith

private lemma bt_uniform_binning_collision_prob {M_c M_b : ℕ} (hMb : 0 < M_b)
    (u v : Fin M_c) (hne : v ≠ u) :
    letI : Nonempty (Fin M_b) := ⟨⟨0, hMb⟩⟩
    let U := ProbDist.uniform (α := Fin M_b)
    ∑ b : Fin M_c → Fin M_b, (iidDist U M_c).pmf b * (if b v = b u then (1 : ℝ) else 0) =
      (1 : ℝ) / (M_b : ℝ) := by
  have : Nonempty (Fin M_b) := ⟨⟨0, hMb⟩⟩
  dsimp only
  let U := ProbDist.uniform (α := Fin M_b)
  have hind : ∀ b : Fin M_c → Fin M_b,
      (if b v = b u then (1 : ℝ) else 0) =
        ∑ m : Fin M_b, (if b u = m then (1 : ℝ) else 0) * (if b v = m then (1 : ℝ) else 0) := by
    intro b
    rw [Finset.sum_eq_single (b u)]
    · by_cases h : b v = b u <;> simp [h]
    · intro m _ hne_m; simp [hne_m.symm]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp_rw [hind, Finset.mul_sum]
  rw [Finset.sum_comm]
  have heach : ∀ m : Fin M_b,
      ∑ b : Fin M_c → Fin M_b, (iidDist U M_c).pmf b *
        ((if b u = m then (1 : ℝ) else 0) * (if b v = m then (1 : ℝ) else 0)) =
      ((1 : ℝ) / (M_b : ℝ)) * ((1 : ℝ) / (M_b : ℝ)) := by
    intro m
    rw [iidDist_sum_two_coords U (fun a => if a = m then (1 : ℝ) else 0)
        (fun a => if a = m then (1 : ℝ) else 0) hne.symm]
    have hsingle : ∑ a : Fin M_b, U.pmf a * (if a = m then (1 : ℝ) else 0) = (1 : ℝ) / (M_b : ℝ) := by
      rw [Finset.sum_eq_single m]
      · simp [U, ProbDist.uniform]
      · intro a _ hne_a; simp [hne_a]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hsingle]
  rw [Finset.sum_congr rfl fun m _ => heach m, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hMpos : (M_b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hMb)
  field_simp [hMpos]

private lemma bt_covering_exp_le {I ε R δ : ℝ} (hI : 0 ≤ I) (hε : 0 ≤ ε)
    (hR : I + 3 * ε < R) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N,
      let M := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
      Real.exp (-((M : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I + 3 * ε))))) ≤ δ := by
  have hgap : 0 < R - (I + 3 * ε) := by linarith
  have hR0 : 0 ≤ R := by linarith
  let K : ℝ := max 1 (Real.log (1 / δ))
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨N, hN⟩ := exists_nat_gt (log2 (2 * K) / (R - (I + 3 * ε)))
  refine ⟨N, fun n hn => ?_⟩
  dsimp only
  have hn_gt : log2 (2 * K) / (R - (I + 3 * ε)) < (n : ℝ) :=
    lt_of_lt_of_le hN (Nat.cast_le.mpr hn)
  have h2K : (2 : ℝ) ^ (-((n : ℝ) * (R - (I + 3 * ε)))) ≤ 1 / (2 * K) := by
    have hrew : log2 (1 / (1 / (2 * K))) / (R - (I + 3 * ε)) ≤ (n : ℝ) := by
      rw [one_div_one_div]; exact le_of_lt hn_gt
    exact bt_two_rpow_neg_le_of_ge hgap (by positivity) hrew
  have hpow_ge : 2 * K ≤ (2 : ℝ) ^ ((n : ℝ) * (R - (I + 3 * ε))) := by
    have hpos : (0 : ℝ) < (2 : ℝ) ^ ((n : ℝ) * (R - (I + 3 * ε))) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hmul : (2 : ℝ) ^ (-((n : ℝ) * (R - (I + 3 * ε)))) *
        (2 : ℝ) ^ ((n : ℝ) * (R - (I + 3 * ε))) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), neg_add_cancel, Real.rpow_zero]
    have h1 := mul_le_mul_of_nonneg_right h2K (le_of_lt hpos)
    rw [hmul] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * K)
    have hsimp : (2 * K) * (1 / (2 * K) * (2 : ℝ) ^ ((n : ℝ) * (R - (I + 3 * ε)))) =
        (2 : ℝ) ^ ((n : ℝ) * (R - (I + 3 * ε))) := by
      field_simp [ne_of_gt hK]
    linarith
  have hM_ge : (2 : ℝ) ^ ((n : ℝ) * R) / 2 ≤
      ((Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R))) : ℕ) : ℝ) :=
    bt_half_two_rpow_le_max_one_floor n hR0
  have hprod_ge : K ≤
      ((Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R))) : ℕ) : ℝ) *
        (2 : ℝ) ^ (-((n : ℝ) * (I + 3 * ε))) := by
    have hpow_eq : ((2 : ℝ) ^ ((n : ℝ) * R) / 2) * (2 : ℝ) ^ (-((n : ℝ) * (I + 3 * ε))) =
        (2 : ℝ) ^ ((n : ℝ) * (R - (I + 3 * ε))) / 2 := by
      rw [div_mul_eq_mul_div, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 2; ring
    calc K = (2 * K) / 2 := by ring
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * (R - (I + 3 * ε))) / 2 := by linarith
      _ = ((2 : ℝ) ^ ((n : ℝ) * R) / 2) * (2 : ℝ) ^ (-((n : ℝ) * (I + 3 * ε))) := hpow_eq.symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hM_ge (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
  have hlog_le : Real.log (1 / δ) ≤ K := le_max_right _ _
  calc Real.exp (-(((Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R))) : ℕ) : ℝ) *
        (2 : ℝ) ^ (-((n : ℝ) * (I + 3 * ε)))))
    _ ≤ Real.exp (-K) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ Real.exp (-Real.log (1 / δ)) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (Real.log δ) := by rw [Real.log_div one_ne_zero (ne_of_gt hδ), Real.log_one, zero_sub, neg_neg]
    _ = δ := Real.exp_log hδ

/-- Helper: telescoping sum `∑ i : Fin n, (f (i.1 + 1) - f i.1) = f n - f 0`. -/
private lemma bt_fin_sum_telescope (f : ℕ → ℝ) : ∀ n : ℕ,
    ∑ i : Fin n, (f (i.1 + 1) - f i.1) = f n - f 0
  | 0 => by simp
  | n + 1 => by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [bt_fin_sum_telescope f n]
    ring

end SharedHelpers

/-! ### 1. Single-Letter Berger–Tung Outer Bound, Inclusion & Special-Case Reductions -/

section SingleLetterBounds

variable {X₁ X₂ Xh₁ Xh₂ : Type*}
  [Fintype X₁] [Fintype X₂] [Fintype Xh₁] [Fintype Xh₂]

/-- **Berger–Tung (1977/1978) Outer Bound** for two-terminal distributed lossy source coding
    (Berger 1978; Tung 1978; El Gamal & Kim §12.1.3):
    relaxes the inner-bound long Markov chain `U₁ — X₁ — X₂ — U₂` to the two separate
    short Markov chains `U₁ — X₁ — X₂` (`I(U₁; X₂ | X₁) = 0`) and `U₂ — X₂ — X₁`
    (`I(U₂; X₁ | X₂) = 0`), with rate inequalities
    `R₁ ≥ I(X₁, X₂; U₁ | U₂)`, `R₂ ≥ I(X₁, X₂; U₂ | U₁)`, `R₁ + R₂ ≥ I(X₁, X₂; U₁, U₂)`. -/
def bergerTungOuterBound
    (P : ProbDist (X₁ × X₂)) (d₁ : Distortion X₁ Xh₁) (d₂ : Distortion X₂ Xh₂)
    (D₁ D₂ : ℝ) : Set (ℝ × ℝ) :=
  { r | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧
    ∃ (kU₁ kU₂ : ℕ) (Q : ProbDist (X₁ × X₂ × Fin kU₁ × Fin kU₂))
      (g₁ : Fin kU₁ × Fin kU₂ → Xh₁) (g₂ : Fin kU₁ × Fin kU₂ → Xh₂),
      Q.map (fun t => (t.1, t.2.1)) = P ∧
      -- Outer-bound Markov chains U₁ - X₁ - X₂ and U₂ - X₂ - X₁
      condMutualInfo (Q.map (fun t => (t.2.2.1, t.2.1, t.1))) = 0 ∧
      condMutualInfo (Q.map (fun t => (t.2.2.2, t.1, t.2.1))) = 0 ∧
      (∑ t, Q.pmf t * d₁.dist t.1 (g₁ (t.2.2.1, t.2.2.2))) ≤ D₁ ∧
      (∑ t, Q.pmf t * d₂.dist t.2.1 (g₂ (t.2.2.1, t.2.2.2))) ≤ D₂ ∧
      r.1 ≥ condMutualInfo (Q.map (fun t => ((t.1, t.2.1), t.2.2.1, t.2.2.2))) ∧
      r.2 ≥ condMutualInfo (Q.map (fun t => ((t.1, t.2.1), t.2.2.2, t.2.2.1))) ∧
      r.1 + r.2 ≥ mutualInfo (Q.map (fun t => ((t.1, t.2.1), (t.2.2.1, t.2.2.2)))) }

/-- Single-letter Hamming distortion measure `d(x, y) = 1_{x ≠ y}` on a discrete alphabet `α`. -/
def hammingDistortion (α : Type*) [DecidableEq α] : Distortion α α where
  dist := fun x y => if x = y then 0 else 1
  nonneg := fun x y => by split_ifs <;> norm_num

/-- **Berger–Tung Inner Bound ⊆ Outer Bound**:
    every rate pair in `bergerTungInnerBound` satisfies the outer-bound Markov chains
    `U₁ — X₁ — X₂` and `U₂ — X₂ — X₁` and identical rate/distortion inequalities. -/
theorem bergerTungInnerBound_subset_outerBound
    (P : ProbDist (X₁ × X₂)) (d₁ : Distortion X₁ Xh₁) (d₂ : Distortion X₂ Xh₂)
    (D₁ D₂ : ℝ) :
    bergerTungInnerBound P d₁ d₂ D₁ D₂ ⊆ bergerTungOuterBound P d₁ d₂ D₁ D₂ := by
  rintro ⟨r₁, r₂⟩ ⟨hr₁, hr₂, kU₁, kU₂, Q, g₁, g₂, hmarg, hmk1, hmk2, hd₁, hd₂, hR₁, hR₂, hR₁₂⟩
  refine ⟨hr₁, hr₂, kU₁, kU₂, Q, g₁, g₂, hmarg, ?_, ?_, hd₁, hd₂, ?_, ?_, hR₁₂⟩
  · -- `U₁ — X₁ — (X₂, U₂)` implies `U₁ — X₁ — X₂`.
    let R1 : ProbDist (Fin kU₁ × X₂ × Fin kU₂ × X₁) :=
      Q.map (fun t => (t.2.2.1, t.2.1, t.2.2.2, t.1))
    have hR1 : condMutualInfo (R1.map (fun t => (t.1, (t.2.1, t.2.2.1), t.2.2.2))) = 0 := by
      unfold R1; rw [map_comp_eq]; exact hmk1
    have h := (bt_condMutualInfo_zero_split R1 hR1).1
    unfold R1 at h; rw [map_comp_eq] at h; exact h
  · -- `U₂ — X₂ — (X₁, U₁)` implies `U₂ — X₂ — X₁`.
    let R2 : ProbDist (Fin kU₂ × X₁ × Fin kU₁ × X₂) :=
      Q.map (fun t => (t.2.2.2, t.1, t.2.2.1, t.2.1))
    have hR2 : condMutualInfo (R2.map (fun t => (t.1, (t.2.1, t.2.2.1), t.2.2.2))) = 0 := by
      unfold R2; rw [map_comp_eq]; exact hmk2
    have h := (bt_condMutualInfo_zero_split R2 hR2).1
    unfold R2 at h; rw [map_comp_eq] at h; exact h
  · -- `I(X₁, X₂; U₁ | U₂) = I(X₁; U₁ | U₂)`.
    rw [bt_cmi_X1X2_U1_given_U2_eq Q hmk1]; exact hR₁
  · -- `I(X₁, X₂; U₂ | U₁) = I(X₂; U₂ | U₁)`.
    rw [bt_cmi_X1X2_U2_given_U1_eq Q hmk2]; exact hR₂

/-- Upward monotonicity of `bergerTungInnerBound` in rates and distortions. -/
theorem bergerTungInnerBound_mono
    {P : ProbDist (X₁ × X₂)} {d₁ : Distortion X₁ Xh₁} {d₂ : Distortion X₂ Xh₂}
    {r r' : ℝ × ℝ} {D₁ D₂ D₁' D₂' : ℝ}
    (hr : r ∈ bergerTungInnerBound P d₁ d₂ D₁ D₂)
    (hr1 : r.1 ≤ r'.1) (hr2 : r.2 ≤ r'.2) (hD1 : D₁ ≤ D₁') (hD2 : D₂ ≤ D₂') :
    r' ∈ bergerTungInnerBound P d₁ d₂ D₁' D₂' := by
  rcases hr with ⟨h1, h2, kU₁, kU₂, Q, g₁, g₂, hmarg, hmk1, hmk2, hd1, hd2, hR1, hR2, hR12⟩
  exact ⟨le_trans h1 hr1, le_trans h2 hr2, kU₁, kU₂, Q, g₁, g₂, hmarg, hmk1, hmk2,
    le_trans hd1 hD1, le_trans hd2 hD2, le_trans hR1 hr1, le_trans hR2 hr2,
    le_trans hR12 (add_le_add hr1 hr2)⟩

omit [Fintype Xh₁] [Fintype Xh₂] in
/-- Upward monotonicity of `bergerTungOuterBound` in rates and distortions. -/
theorem bergerTungOuterBound_mono
    {P : ProbDist (X₁ × X₂)} {d₁ : Distortion X₁ Xh₁} {d₂ : Distortion X₂ Xh₂}
    {r r' : ℝ × ℝ} {D₁ D₂ D₁' D₂' : ℝ}
    (hr : r ∈ bergerTungOuterBound P d₁ d₂ D₁ D₂)
    (hr1 : r.1 ≤ r'.1) (hr2 : r.2 ≤ r'.2) (hD1 : D₁ ≤ D₁') (hD2 : D₂ ≤ D₂') :
    r' ∈ bergerTungOuterBound P d₁ d₂ D₁' D₂' := by
  rcases hr with ⟨h1, h2, kU₁, kU₂, Q, g₁, g₂, hmarg, hmk1, hmk2, hd1, hd2, hR1, hR2, hR12⟩
  exact ⟨le_trans h1 hr1, le_trans h2 hr2, kU₁, kU₂, Q, g₁, g₂, hmarg, hmk1, hmk2,
    le_trans hd1 hD1, le_trans hd2 hD2, le_trans hR1 hr1, le_trans hR2 hr2,
    le_trans hR12 (add_le_add hr1 hr2)⟩

/-- **Special Case 1a (Lossless / Slepian–Wolf Inclusion)**:
    every Slepian–Wolf rate pair lies in `bergerTungInnerBound` at `D₁ = D₂ = 0` under
    Hamming distortion (taking `U₁ = X₁`, `U₂ = X₂`). -/
theorem slepianWolfSingleLetter_subset_bergerTungInnerBound [DecidableEq X₁] [DecidableEq X₂]
    (P : ProbDist (X₁ × X₂)) :
    slepianWolfSingleLetter P ⊆
      bergerTungInnerBound P (hammingDistortion X₁) (hammingDistortion X₂) 0 0 := by
  rintro ⟨r₁, r₂⟩ ⟨hr₁, hr₂, hR₁, hR₂, hR₁₂⟩
  let kU₁ := Fintype.card X₁
  let kU₂ := Fintype.card X₂
  let e₁ : X₁ ≃ Fin kU₁ := Fintype.equivFin X₁
  let e₂ : X₂ ≃ Fin kU₂ := Fintype.equivFin X₂
  let Q : ProbDist (X₁ × X₂ × Fin kU₁ × Fin kU₂) :=
    P.map (fun xy => (xy.1, xy.2, e₁ xy.1, e₂ xy.2))
  let g₁ : Fin kU₁ × Fin kU₂ → X₁ := fun u => e₁.symm u.1
  let g₂ : Fin kU₁ × Fin kU₂ → X₂ := fun u => e₂.symm u.2
  refine ⟨hr₁, hr₂, kU₁, kU₂, Q, g₁, g₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Marginal `(X₁, X₂) ~ P`.
    unfold Q; rw [map_comp_eq]
    have hcomp : ((fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => (t.1, t.2.1)) ∘
        fun xy : X₁ × X₂ => (xy.1, xy.2, e₁ xy.1, e₂ xy.2)) = id := rfl
    rw [hcomp, bt_probDist_map_id]
  · -- `U₁ = e₁(X₁)` is deterministic in `X₁`, so `I(U₁; (X₂, U₂) | X₁) = 0`.
    unfold Q; rw [map_comp_eq]
    let P' : ProbDist ((X₂ × Fin kU₂) × X₁) := P.map (fun xy => ((xy.2, e₂ xy.2), xy.1))
    have hrew : P.map ((fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => (t.2.2.1, (t.2.1, t.2.2.2), t.1)) ∘
        fun xy : X₁ × X₂ => (xy.1, xy.2, e₁ xy.1, e₂ xy.2)) =
        P'.map (fun bc => (e₁ bc.2, bc.1, bc.2)) := by
      unfold P'; rw [map_comp_eq]; rfl
    rw [hrew]
    exact bt_condMutualInfo_eq_zero_of_det_left P' e₁
  · -- `U₂ = e₂(X₂)` is deterministic in `X₂`, so `I(U₂; (X₁, U₁) | X₂) = 0`.
    unfold Q; rw [map_comp_eq]
    let P' : ProbDist ((X₁ × Fin kU₁) × X₂) := P.map (fun xy => ((xy.1, e₁ xy.1), xy.2))
    have hrew : P.map ((fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => (t.2.2.2, (t.1, t.2.2.1), t.2.1)) ∘
        fun xy : X₁ × X₂ => (xy.1, xy.2, e₁ xy.1, e₂ xy.2)) =
        P'.map (fun bc => (e₂ bc.2, bc.1, bc.2)) := by
      unfold P'; rw [map_comp_eq]; rfl
    rw [hrew]
    exact bt_condMutualInfo_eq_zero_of_det_left P' e₂
  · -- `E[d₁(X₁, e₁⁻¹(e₁ X₁))] = 0`.
    unfold Q; rw [← sum_pmf_mul_comp P]
    have h0 : ∑ xy : X₁ × X₂, P.pmf xy * (hammingDistortion X₁).dist xy.1 (g₁ (e₁ xy.1, e₂ xy.2)) = 0 :=
      Finset.sum_eq_zero fun xy _ => by simp [hammingDistortion, g₁]
    linarith
  · -- `E[d₂(X₂, e₂⁻¹(e₂ X₂))] = 0`.
    unfold Q; rw [← sum_pmf_mul_comp P]
    have h0 : ∑ xy : X₁ × X₂, P.pmf xy * (hammingDistortion X₂).dist xy.2 (g₂ (e₁ xy.1, e₂ xy.2)) = 0 :=
      Finset.sum_eq_zero fun xy _ => by simp [hammingDistortion, g₂]
    linarith
  · -- `I(X₁; U₁ | U₂) = H(X₁ | X₂) = condEntropy P`.
    have hval : condMutualInfo (Q.map (fun t => (t.1, t.2.2.1, t.2.2.2))) = condEntropy P := by
      unfold Q; rw [map_comp_eq]
      unfold condMutualInfo condEntropy; dsimp only
      simp_rw [map_comp_eq]
      have h1 : shannonEntropy (P.map ((fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => (t.1, t.2.2.1, t.2.2.2)) ∘
          fun xy : X₁ × X₂ => (xy.1, xy.2, e₁ xy.1, e₂ xy.2))) = shannonEntropy P :=
        bt_shannonEntropy_map_injective P (fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h => by
          dsimp only [Function.comp_apply] at h
          rcases Prod.mk.inj h with ⟨ha, h2⟩
          exact Prod.ext ha (e₂.injective (Prod.mk.inj h2).2))
      have h2 : shannonEntropy (P.map ((fun t : X₁ × Fin kU₁ × Fin kU₂ => (t.1, t.2.2)) ∘
          (fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => (t.1, t.2.2.1, t.2.2.2)) ∘
          fun xy : X₁ × X₂ => (xy.1, xy.2, e₁ xy.1, e₂ xy.2))) = shannonEntropy P :=
        bt_shannonEntropy_map_injective P (fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h => by
          dsimp only [Function.comp_apply] at h
          rcases Prod.mk.inj h with ⟨ha, hb⟩
          exact Prod.ext ha (e₂.injective hb))
      have h3 : shannonEntropy (P.map ((fun t : X₁ × Fin kU₁ × Fin kU₂ => (t.2.1, t.2.2)) ∘
          (fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => (t.1, t.2.2.1, t.2.2.2)) ∘
          fun xy : X₁ × X₂ => (xy.1, xy.2, e₁ xy.1, e₂ xy.2))) = shannonEntropy P :=
        bt_shannonEntropy_map_injective P (fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h =>
          Prod.ext (e₁.injective (congrArg Prod.fst h)) (e₂.injective (congrArg Prod.snd h)))
      have h4 : shannonEntropy (P.map ((fun t : X₁ × Fin kU₁ × Fin kU₂ => t.2.2) ∘
          (fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => (t.1, t.2.2.1, t.2.2.2)) ∘
          fun xy : X₁ × X₂ => (xy.1, xy.2, e₁ xy.1, e₂ xy.2))) = shannonEntropy P.snd := by
        rw [← bt_probDist_map_snd]
        exact bt_shannonEntropy_map_eq_of_bij P _ _
          ⟨e₂.symm, fun ⟨_, b⟩ => by simp⟩ ⟨e₂, fun _ => rfl⟩
      rw [h1, h2, h3, h4]; ring
    linarith
  · -- `I(X₂; U₂ | U₁) = H(X₂ | X₁) = condEntropy (P.map Prod.swap)`.
    have hval : condMutualInfo (Q.map (fun t => (t.2.1, t.2.2.2, t.2.2.1))) =
        condEntropy (P.map Prod.swap) := by
      unfold Q; rw [map_comp_eq]
      unfold condMutualInfo condEntropy; dsimp only
      simp_rw [map_comp_eq]
      have hPswap : shannonEntropy (P.map Prod.swap) = shannonEntropy P :=
        shannonEntropy_map_equiv (Equiv.prodComm X₁ X₂) P
      have hPswap_snd : (P.map Prod.swap).snd = P.fst := by
        rw [← bt_probDist_map_snd, ← bt_probDist_map_fst, map_comp_eq]; rfl
      have h1 : shannonEntropy (P.map ((fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => (t.2.1, t.2.2.2, t.2.2.1)) ∘
          fun xy : X₁ × X₂ => (xy.1, xy.2, e₁ xy.1, e₂ xy.2))) = shannonEntropy P :=
        bt_shannonEntropy_map_injective P (fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h =>
          Prod.ext (e₁.injective (congrArg (fun t => t.2.2) h)) (congrArg Prod.fst h))
      have h2 : shannonEntropy (P.map ((fun t : X₂ × Fin kU₂ × Fin kU₁ => (t.1, t.2.2)) ∘
          (fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => (t.2.1, t.2.2.2, t.2.2.1)) ∘
          fun xy : X₁ × X₂ => (xy.1, xy.2, e₁ xy.1, e₂ xy.2))) = shannonEntropy P :=
        bt_shannonEntropy_map_injective P (fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h =>
          Prod.ext (e₁.injective (congrArg Prod.snd h)) (congrArg Prod.fst h))
      have h3 : shannonEntropy (P.map ((fun t : X₂ × Fin kU₂ × Fin kU₁ => (t.2.1, t.2.2)) ∘
          (fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => (t.2.1, t.2.2.2, t.2.2.1)) ∘
          fun xy : X₁ × X₂ => (xy.1, xy.2, e₁ xy.1, e₂ xy.2))) = shannonEntropy P :=
        bt_shannonEntropy_map_injective P (fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h =>
          Prod.ext (e₁.injective (congrArg Prod.snd h)) (e₂.injective (congrArg Prod.fst h)))
      have h4 : shannonEntropy (P.map ((fun t : X₂ × Fin kU₂ × Fin kU₁ => t.2.2) ∘
          (fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => (t.2.1, t.2.2.2, t.2.2.1)) ∘
          fun xy : X₁ × X₂ => (xy.1, xy.2, e₁ xy.1, e₂ xy.2))) = shannonEntropy P.fst := by
        rw [← bt_probDist_map_fst]
        exact bt_shannonEntropy_map_eq_of_bij P _ _
          ⟨e₁.symm, fun ⟨a, _⟩ => by simp⟩ ⟨e₁, fun _ => rfl⟩
      rw [h1, h2, h3, h4, hPswap, hPswap_snd]; ring
    linarith
  · -- `I(X₁, X₂; U₁, U₂) = H(X₁, X₂) = shannonEntropy P`.
    have hval : mutualInfo (Q.map (fun t => ((t.1, t.2.1), (t.2.2.1, t.2.2.2)))) =
        shannonEntropy P := by
      unfold Q; rw [map_comp_eq]
      unfold mutualInfo
      have hfst : shannonEntropy (P.map ((fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => ((t.1, t.2.1), (t.2.2.1, t.2.2.2))) ∘
          fun xy : X₁ × X₂ => (xy.1, xy.2, e₁ xy.1, e₂ xy.2))).fst = shannonEntropy P := by
        rw [← bt_probDist_map_fst, map_comp_eq]
        have : (Prod.fst ∘ (fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => ((t.1, t.2.1), (t.2.2.1, t.2.2.2))) ∘
            fun xy : X₁ × X₂ => (xy.1, xy.2, e₁ xy.1, e₂ xy.2)) = id := rfl
        rw [this, bt_probDist_map_id]
      have hsnd : shannonEntropy (P.map ((fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => ((t.1, t.2.1), (t.2.2.1, t.2.2.2))) ∘
          fun xy : X₁ × X₂ => (xy.1, xy.2, e₁ xy.1, e₂ xy.2))).snd = shannonEntropy P := by
        rw [← bt_probDist_map_snd, map_comp_eq]
        exact bt_shannonEntropy_map_injective P (fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h =>
          Prod.ext (e₁.injective (congrArg Prod.fst h)) (e₂.injective (congrArg Prod.snd h)))
      have hall : shannonEntropy (P.map ((fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => ((t.1, t.2.1), (t.2.2.1, t.2.2.2))) ∘
          fun xy : X₁ × X₂ => (xy.1, xy.2, e₁ xy.1, e₂ xy.2))) = shannonEntropy P :=
        bt_shannonEntropy_map_injective P (fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h => congrArg Prod.fst h)
      rw [hfst, hsnd, hall]; ring
    linarith

/-- **Special Case 1b (Lossless Outer Bound ⊆ Slepian–Wolf)**:
    under Hamming distortion at `D₁ = D₂ = 0`, every rate pair in `bergerTungOuterBound`
    lies in `slepianWolfSingleLetter P`. -/
theorem bergerTungOuterBound_zero_subset_slepianWolfSingleLetter
    [DecidableEq X₁] [DecidableEq X₂] (P : ProbDist (X₁ × X₂)) :
    bergerTungOuterBound P (hammingDistortion X₁) (hammingDistortion X₂) 0 0 ⊆
      slepianWolfSingleLetter P := by
  rintro ⟨r₁, r₂⟩ ⟨hr₁, hr₂, kU₁, kU₂, Q, g₁, g₂, hmarg, hmk1, hmk2, hd₁, hd₂, hR₁, hR₂, hR₁₂⟩
  -- Zero Hamming distortion forces `(X₁, X₂) = (g₁(U₁, U₂), g₂(U₁, U₂))` on the support of `Q`.
  have hdet₁ : ∀ t, 0 < Q.pmf t → t.1 = g₁ (t.2.2.1, t.2.2.2) := by
    intro t ht
    by_contra hne
    have hpos : 0 < Q.pmf t * (hammingDistortion X₁).dist t.1 (g₁ (t.2.2.1, t.2.2.2)) := by
      simp [hammingDistortion, hne, ht]
    have hle : Q.pmf t * (hammingDistortion X₁).dist t.1 (g₁ (t.2.2.1, t.2.2.2)) ≤
        ∑ t', Q.pmf t' * (hammingDistortion X₁).dist t'.1 (g₁ (t'.2.2.1, t'.2.2.2)) :=
      Finset.single_le_sum (fun t' _ => mul_nonneg (Q.nonneg t') ((hammingDistortion X₁).nonneg _ _))
        (Finset.mem_univ t)
    linarith
  have hdet₂ : ∀ t, 0 < Q.pmf t → t.2.1 = g₂ (t.2.2.1, t.2.2.2) := by
    intro t ht
    by_contra hne
    have hpos : 0 < Q.pmf t * (hammingDistortion X₂).dist t.2.1 (g₂ (t.2.2.1, t.2.2.2)) := by
      simp [hammingDistortion, hne, ht]
    have hle : Q.pmf t * (hammingDistortion X₂).dist t.2.1 (g₂ (t.2.2.1, t.2.2.2)) ≤
        ∑ t', Q.pmf t' * (hammingDistortion X₂).dist t'.2.1 (g₂ (t'.2.2.1, t'.2.2.2)) :=
      Finset.single_le_sum (fun t' _ => mul_nonneg (Q.nonneg t') ((hammingDistortion X₂).nonneg _ _))
        (Finset.mem_univ t)
    linarith
  -- Hence `H((X₁, X₂), (U₁, U₂)) = H(U₁, U₂)`.
  have hH_det : shannonEntropy (Q.map (fun t => ((t.1, t.2.1), (t.2.2.1, t.2.2.2)))) =
      shannonEntropy (Q.map (fun t => (t.2.2.1, t.2.2.2))) :=
    bt_shannonEntropy_map_pair_det Q (fun t => (t.1, t.2.1)) (fun t => (t.2.2.1, t.2.2.2))
      ⟨fun u => (g₁ u, g₂ u), fun t ht => Prod.ext (hdet₁ t ht) (hdet₂ t ht)⟩
  refine ⟨hr₁, hr₂, ?_, ?_, ?_⟩
  · -- `condEntropy P ≤ r₁`:
    -- `I(X₁, X₂; U₁ | U₂) = H(X₁, X₂, U₂) - H(U₂) ≥ H(X₁, X₂, U₂) - H(X₂, U₂) = H(X₁ | X₂, U₂) = H(X₁ | X₂)`.
    have h1 : condMutualInfo (Q.map (fun t => ((t.1, t.2.1), t.2.2.1, t.2.2.2))) =
        shannonEntropy (Q.map (fun t => ((t.1, t.2.1), t.2.2.2))) -
        shannonEntropy (Q.map (fun t => t.2.2.2)) := by
      unfold condMutualInfo; dsimp only; simp_rw [map_comp_eq]
      have hAll : shannonEntropy (Q.map (fun t => ((t.1, t.2.1), t.2.2.1, t.2.2.2))) =
          shannonEntropy (Q.map (fun t => (t.2.2.1, t.2.2.2))) := hH_det
      rw [hAll]
      change shannonEntropy (Q.map (fun t => ((t.1, t.2.1), t.2.2.2))) +
        shannonEntropy (Q.map (fun t => (t.2.2.1, t.2.2.2))) -
        shannonEntropy (Q.map (fun t => (t.2.2.1, t.2.2.2))) -
        shannonEntropy (Q.map (fun t => t.2.2.2)) = _
      ring
    have hU2_le : shannonEntropy (Q.map (fun t => t.2.2.2)) ≤
        shannonEntropy (Q.map (fun t => (t.2.1, t.2.2.2))) := by
      have heq : (Q.map (fun t => (t.2.1, t.2.2.2))).map Prod.snd = Q.map (fun t => t.2.2.2) := by
        rw [map_comp_eq]; rfl
      rw [← heq]
      exact shannonEntropy_map_le Prod.snd _
    -- From `hmk2`: `H(X₁, X₂, U₂) - H(X₂, U₂) = H(X₁, X₂) - H(X₂) = condEntropy P`.
    have hmk2_eq : shannonEntropy (Q.map (fun t => ((t.1, t.2.1), t.2.2.2))) -
        shannonEntropy (Q.map (fun t => (t.2.1, t.2.2.2))) = condEntropy P := by
      unfold condMutualInfo at hmk2; dsimp only at hmk2; simp_rw [map_comp_eq] at hmk2
      unfold condEntropy
      have hA : shannonEntropy (Q.map (fun t => (t.2.2.2, t.1, t.2.1))) =
          shannonEntropy (Q.map (fun t => ((t.1, t.2.1), t.2.2.2))) :=
        bt_shannonEntropy_map_eq_of_bij Q _ _
          ⟨fun t => ((t.2.1, t.2.2), t.1), fun _ => rfl⟩
          ⟨fun t => (t.2, t.1.1, t.1.2), fun _ => rfl⟩
      have hB : shannonEntropy (Q.map ((fun t : Fin kU₂ × X₁ × X₂ => (t.1, t.2.2)) ∘
          fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => (t.2.2.2, t.1, t.2.1))) =
          shannonEntropy (Q.map (fun t => (t.2.1, t.2.2.2))) :=
        bt_shannonEntropy_map_eq_of_bij Q _ _
          ⟨Prod.swap, fun _ => rfl⟩ ⟨Prod.swap, fun _ => rfl⟩
      have hC : Q.map ((fun t : Fin kU₂ × X₁ × X₂ => (t.2.1, t.2.2)) ∘
          fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => (t.2.2.2, t.1, t.2.1)) = P := hmarg
      have hD : Q.map ((fun t : Fin kU₂ × X₁ × X₂ => t.2.2) ∘
          fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => (t.2.2.2, t.1, t.2.1)) = P.snd := by
        rw [← bt_probDist_map_snd, ← hmarg, map_comp_eq]; rfl
      rw [hA, hB, hC, hD] at hmk2
      linarith
    linarith
  · -- `condEntropy (P.map Prod.swap) ≤ r₂`: symmetric using `hmk1`.
    have h1 : condMutualInfo (Q.map (fun t => ((t.1, t.2.1), t.2.2.2, t.2.2.1))) =
        shannonEntropy (Q.map (fun t => ((t.1, t.2.1), t.2.2.1))) -
        shannonEntropy (Q.map (fun t => t.2.2.1)) := by
      unfold condMutualInfo; dsimp only; simp_rw [map_comp_eq]
      have hAll : shannonEntropy (Q.map (fun t => ((t.1, t.2.1), t.2.2.2, t.2.2.1))) =
          shannonEntropy (Q.map (fun t => (t.2.2.1, t.2.2.2))) := by
        rw [← hH_det]
        exact bt_shannonEntropy_map_eq_of_bij Q _ _
          ⟨fun t => (t.1, (t.2.2, t.2.1)), fun _ => rfl⟩
          ⟨fun t => (t.1, t.2.2, t.2.1), fun _ => rfl⟩
      have hU2U1 : shannonEntropy (Q.map ((fun t : (X₁ × X₂) × Fin kU₂ × Fin kU₁ => (t.2.1, t.2.2)) ∘
          fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => ((t.1, t.2.1), t.2.2.2, t.2.2.1))) =
          shannonEntropy (Q.map (fun t => (t.2.2.1, t.2.2.2))) :=
        bt_shannonEntropy_map_eq_of_bij Q _ _
          ⟨Prod.swap, fun _ => rfl⟩ ⟨Prod.swap, fun _ => rfl⟩
      rw [hAll, hU2U1]
      change shannonEntropy (Q.map (fun t => ((t.1, t.2.1), t.2.2.1))) +
        shannonEntropy (Q.map (fun t => (t.2.2.1, t.2.2.2))) -
        shannonEntropy (Q.map (fun t => (t.2.2.1, t.2.2.2))) -
        shannonEntropy (Q.map (fun t => t.2.2.1)) = _
      ring
    have hU1_le : shannonEntropy (Q.map (fun t => t.2.2.1)) ≤
        shannonEntropy (Q.map (fun t => (t.1, t.2.2.1))) := by
      have heq : (Q.map (fun t => (t.1, t.2.2.1))).map Prod.snd = Q.map (fun t => t.2.2.1) := by
        rw [map_comp_eq]; rfl
      rw [← heq]
      exact shannonEntropy_map_le Prod.snd _
    have hmk1_eq : shannonEntropy (Q.map (fun t => ((t.1, t.2.1), t.2.2.1))) -
        shannonEntropy (Q.map (fun t => (t.1, t.2.2.1))) = condEntropy (P.map Prod.swap) := by
      unfold condMutualInfo at hmk1; dsimp only at hmk1; simp_rw [map_comp_eq] at hmk1
      unfold condEntropy
      have hA : shannonEntropy (Q.map (fun t => (t.2.2.1, t.2.1, t.1))) =
          shannonEntropy (Q.map (fun t => ((t.1, t.2.1), t.2.2.1))) :=
        bt_shannonEntropy_map_eq_of_bij Q _ _
          ⟨fun t => ((t.2.2, t.2.1), t.1), fun _ => rfl⟩
          ⟨fun t => (t.2, t.1.2, t.1.1), fun _ => rfl⟩
      have hB : shannonEntropy (Q.map ((fun t : Fin kU₁ × X₂ × X₁ => (t.1, t.2.2)) ∘
          fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => (t.2.2.1, t.2.1, t.1))) =
          shannonEntropy (Q.map (fun t => (t.1, t.2.2.1))) :=
        bt_shannonEntropy_map_eq_of_bij Q _ _
          ⟨Prod.swap, fun _ => rfl⟩ ⟨Prod.swap, fun _ => rfl⟩
      have hC : Q.map ((fun t : Fin kU₁ × X₂ × X₁ => (t.2.1, t.2.2)) ∘
          fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => (t.2.2.1, t.2.1, t.1)) = P.map Prod.swap := by
        rw [← hmarg, map_comp_eq]; rfl
      have hD : Q.map ((fun t : Fin kU₁ × X₂ × X₁ => t.2.2) ∘
          fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => (t.2.2.1, t.2.1, t.1)) = (P.map Prod.swap).snd := by
        rw [← bt_probDist_map_snd, ← hmarg, map_comp_eq, map_comp_eq]; rfl
      rw [hA, hB, hC, hD] at hmk1
      linarith
    linarith
  · -- `shannonEntropy P ≤ r₁ + r₂`: `I(X₁, X₂; U₁, U₂) = H(X₁, X₂)`.
    have hsum_eq : mutualInfo (Q.map (fun t => ((t.1, t.2.1), (t.2.2.1, t.2.2.2)))) =
        shannonEntropy P := by
      unfold mutualInfo
      have hfst : (Q.map (fun t => ((t.1, t.2.1), (t.2.2.1, t.2.2.2)))).fst = P := by
        rw [← bt_probDist_map_fst, map_comp_eq]; exact hmarg
      have hsnd : (Q.map (fun t => ((t.1, t.2.1), (t.2.2.1, t.2.2.2)))).snd =
          Q.map (fun t => (t.2.2.1, t.2.2.2)) := by
        rw [← bt_probDist_map_snd, map_comp_eq]; rfl
      rw [hfst, hsnd, hH_det]; ring
    linarith

/-- **Lossless Collapse of Berger–Tung Inner Bound to Slepian–Wolf**:
    at `D₁ = D₂ = 0` under Hamming distortion, `bergerTungInnerBound` equals `slepianWolfSingleLetter P`. -/
theorem bergerTungInnerBound_lossless_eq_slepianWolf [DecidableEq X₁] [DecidableEq X₂]
    (P : ProbDist (X₁ × X₂)) :
    bergerTungInnerBound P (hammingDistortion X₁) (hammingDistortion X₂) 0 0 =
      slepianWolfSingleLetter P :=
  Set.Subset.antisymm
    ((bergerTungInnerBound_subset_outerBound P _ _ 0 0).trans
      (bergerTungOuterBound_zero_subset_slepianWolfSingleLetter P))
    (slepianWolfSingleLetter_subset_bergerTungInnerBound P)

/-- **Lossless Collapse of Berger–Tung Outer Bound to Slepian–Wolf**:
    at `D₁ = D₂ = 0` under Hamming distortion, `bergerTungOuterBound` equals `slepianWolfSingleLetter P`. -/
theorem bergerTungOuterBound_lossless_eq_slepianWolf [DecidableEq X₁] [DecidableEq X₂]
    (P : ProbDist (X₁ × X₂)) :
    bergerTungOuterBound P (hammingDistortion X₁) (hammingDistortion X₂) 0 0 =
      slepianWolfSingleLetter P :=
  Set.Subset.antisymm
    (bergerTungOuterBound_zero_subset_slepianWolfSingleLetter P)
    ((slepianWolfSingleLetter_subset_bergerTungInnerBound P).trans
      (bergerTungInnerBound_subset_outerBound P _ _ 0 0))

/-- **Special Case 2a (Wyner–Ziv Lower Bound on Berger–Tung Inner Bound)**:
    for ANY `(R₁, R₂) ∈ bergerTungInnerBound P d₁ d₂ D₁ D₂`,
    `wynerZivRateDistortion P d₁ D₁ ≤ R₁`. -/
theorem wynerZivRateDistortion_le_of_mem_bergerTungInnerBound
    {P : ProbDist (X₁ × X₂)} {d₁ : Distortion X₁ Xh₁} {d₂ : Distortion X₂ Xh₂}
    {R₁ R₂ D₁ D₂ : ℝ}
    (hr : (R₁, R₂) ∈ bergerTungInnerBound P d₁ d₂ D₁ D₂) :
    wynerZivRateDistortion P d₁ D₁ ≤ R₁ := by
  classical
  rcases hr with ⟨_, _, kU₁, kU₂, Q, g₁, _, hmarg, hmk1, hmk2, hd₁, _, hR₁, _, _⟩
  have hQne : Nonempty (X₁ × X₂ × Fin kU₁ × Fin kU₂) := bt_nonempty_of_probDist Q
  have hkU₁ : 0 < kU₁ := by
    obtain ⟨⟨_, _, u₁, _⟩⟩ := hQne; exact Fin.pos u₁
  have hkU₂ : 0 < kU₂ := by
    obtain ⟨⟨_, _, _, u₂⟩⟩ := hQne; exact Fin.pos u₂
  let u2_def : Fin kU₂ := ⟨0, hkU₂⟩
  -- Marginal `Q₁₂U₁` on `X₁ × X₂ × Fin kU₁`.
  let Qwz : ProbDist (X₁ × X₂ × Fin kU₁) := Q.map (fun t => (t.1, t.2.1, t.2.2.1))
  have hQwz_marg : Qwz.map (fun t => (t.1, t.2.1)) = P := by
    unfold Qwz; rw [map_comp_eq]; exact hmarg
  -- `U₁ — X₁ — X₂` from `hmk1`.
  have hQwz_mk : condMutualInfo (Qwz.map (fun t => (t.2.2, t.2.1, t.1))) = 0 := by
    unfold Qwz; rw [map_comp_eq]
    let R1 : ProbDist (Fin kU₁ × X₂ × Fin kU₂ × X₁) :=
      Q.map (fun t => (t.2.2.1, t.2.1, t.2.2.2, t.1))
    have hR1 : condMutualInfo (R1.map (fun t => (t.1, (t.2.1, t.2.2.1), t.2.2.2))) = 0 := by
      unfold R1; rw [map_comp_eq]; exact hmk1
    have h := (bt_condMutualInfo_zero_split R1 hR1).1
    unfold R1 at h; rw [map_comp_eq] at h; exact h
  -- Factorization from `U₂ — X₂ — (X₁, U₁)`:
  -- `Q(x₁, x₂, u₁, u₂) * P₂(x₂) = Qwz(x₁, x₂, u₁) * Q_{X₂ U₂}(x₂, u₂)`.
  let R2 : ProbDist (Fin kU₂ × (X₁ × Fin kU₁) × X₂) :=
    Q.map (fun t => (t.2.2.2, (t.1, t.2.2.1), t.2.1))
  have hR2_ci : R2 = condIndepDist R2 := (condMutualInfo_eq_zero_iff R2).mp hmk2
  have hR2_pmf : ∀ x₁ x₂ u₁ u₂, R2.pmf (u₂, (x₁, u₁), x₂) = Q.pmf (x₁, x₂, u₁, u₂) := by
    intro x₁ x₂ u₁ u₂
    let e : (X₁ × X₂ × Fin kU₁ × Fin kU₂) ≃ (Fin kU₂ × (X₁ × Fin kU₁) × X₂) :=
      { toFun := fun t => (t.2.2.2, (t.1, t.2.2.1), t.2.1)
        invFun := fun s => (s.2.1.1, s.2.2, s.2.1.2, s.1)
        left_inv := fun ⟨_, _, _, _⟩ => rfl
        right_inv := fun ⟨_, ⟨_, _⟩, _⟩ => rfl }
    exact bt_probDist_map_equiv_pmf e Q (u₂, (x₁, u₁), x₂)
  have hR2_xz_pmf : ∀ u₂ x₂, (R2.map (fun s => (s.1, s.2.2))).pmf (u₂, x₂) =
      (Q.map (fun t => (t.2.2.2, t.2.1))).pmf (u₂, x₂) := by
    intro u₂ x₂; unfold R2; rw [map_comp_eq]; rfl
  have hR2_yz_pmf : ∀ x₁ u₁ x₂, (R2.map (fun s => (s.2.1, s.2.2))).pmf ((x₁, u₁), x₂) =
      Qwz.pmf (x₁, x₂, u₁) := by
    intro x₁ u₁ x₂
    let e : (X₁ × X₂ × Fin kU₁) ≃ ((X₁ × Fin kU₁) × X₂) :=
      { toFun := fun t => ((t.1, t.2.2), t.2.1)
        invFun := fun s => (s.1.1, s.2, s.1.2)
        left_inv := fun ⟨_, _, _⟩ => rfl
        right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
    have hmap : R2.map (fun s => (s.2.1, s.2.2)) = Qwz.map e := by
      unfold R2 Qwz; rw [map_comp_eq, map_comp_eq]; rfl
    rw [hmap]
    exact bt_probDist_map_equiv_pmf e Qwz ((x₁, u₁), x₂)
  have hR2_z : R2.map (fun s => s.2.2) = P.snd := by
    unfold R2; rw [map_comp_eq, ← bt_probDist_map_snd, ← hmarg, map_comp_eq]; rfl
  have hQ_fac : ∀ x₁ x₂ u₁ u₂,
      Q.pmf (x₁, x₂, u₁, u₂) =
        if P.snd.pmf x₂ = 0 then 0
        else (Q.map (fun t => (t.2.2.2, t.2.1))).pmf (u₂, x₂) *
          Qwz.pmf (x₁, x₂, u₁) / P.snd.pmf x₂ := by
    intro x₁ x₂ u₁ u₂
    rw [← hR2_pmf]
    have h := congrFun (congrArg ProbDist.pmf hR2_ci) (u₂, (x₁, u₁), x₂)
    dsimp only [condIndepDist] at h
    rw [hR2_z, hR2_xz_pmf, hR2_yz_pmf] at h
    exact h
  -- For each `x₂`, choose `u₂*(x₂)` minimizing `∑ x₁ u₁, Qwz(x₁, x₂, u₁) * d₁(x₁, g₁(u₁, u₂))`.
  let sliceCost (x₂ : X₂) (u₂ : Fin kU₂) : ℝ :=
    ∑ p : X₁ × Fin kU₁, Qwz.pmf (p.1, x₂, p.2) * d₁.dist p.1 (g₁ (p.2, u₂))
  have hex_min : ∀ x₂ : X₂, ∃ u₂ : Fin kU₂, ∀ u₂' : Fin kU₂, sliceCost x₂ u₂ ≤ sliceCost x₂ u₂' := by
    intro x₂
    have hne : (Finset.univ : Finset (Fin kU₂)).Nonempty := ⟨u2_def, Finset.mem_univ _⟩
    obtain ⟨u₂, _, hmin⟩ := Finset.exists_min_image Finset.univ (sliceCost x₂) hne
    exact ⟨u₂, fun u₂' => hmin u₂' (Finset.mem_univ u₂')⟩
  let u2star : X₂ → Fin kU₂ := fun x₂ => Classical.choose (hex_min x₂)
  have hu2star : ∀ x₂ u₂', sliceCost x₂ (u2star x₂) ≤ sliceCost x₂ u₂' :=
    fun x₂ => Classical.choose_spec (hex_min x₂)
  let gwz : Fin kU₁ × X₂ → Xh₁ := fun ux => g₁ (ux.1, u2star ux.2)
  -- Expected distortion under `gwz` is at most `E_Q[d₁(X₁, g₁(U₁, U₂))] ≤ D₁`.
  have hQwz_dist : (∑ t : X₁ × X₂ × Fin kU₁, Qwz.pmf t * d₁.dist t.1 (gwz (t.2.2, t.2.1))) ≤ D₁ := by
    have hL : (∑ t : X₁ × X₂ × Fin kU₁, Qwz.pmf t * d₁.dist t.1 (gwz (t.2.2, t.2.1))) =
        ∑ x₂ : X₂, sliceCost x₂ (u2star x₂) := by
      let e : (X₁ × X₂ × Fin kU₁) ≃ (X₂ × (X₁ × Fin kU₁)) :=
        { toFun := fun t => (t.2.1, (t.1, t.2.2))
          invFun := fun s => (s.2.1, s.1, s.2.2)
          left_inv := fun ⟨_, _, _⟩ => rfl
          right_inv := fun ⟨_, ⟨_, _⟩⟩ => rfl }
      have heq := Fintype.sum_equiv e
        (fun t : X₁ × X₂ × Fin kU₁ => Qwz.pmf t * d₁.dist t.1 (gwz (t.2.2, t.2.1)))
        (fun s : X₂ × (X₁ × Fin kU₁) => Qwz.pmf (s.2.1, s.1, s.2.2) * d₁.dist s.2.1 (gwz (s.2.2, s.1)))
        (fun _ => rfl)
      rw [heq, Fintype.sum_prod_type]
    have hR : (∑ t : X₁ × X₂ × Fin kU₁ × Fin kU₂, Q.pmf t * d₁.dist t.1 (g₁ (t.2.2.1, t.2.2.2))) =
        ∑ x₂ : X₂, if P.snd.pmf x₂ = 0 then 0
          else (∑ u₂ : Fin kU₂, (Q.map (fun t => (t.2.2.2, t.2.1))).pmf (u₂, x₂) * sliceCost x₂ u₂) /
            P.snd.pmf x₂ := by
      let e : (X₁ × X₂ × Fin kU₁ × Fin kU₂) ≃ (X₂ × Fin kU₂ × (X₁ × Fin kU₁)) :=
        { toFun := fun t => (t.2.1, t.2.2.2, (t.1, t.2.2.1))
          invFun := fun s => (s.2.2.1, s.1, s.2.2.2, s.2.1)
          left_inv := fun ⟨_, _, _, _⟩ => rfl
          right_inv := fun ⟨_, _, ⟨_, _⟩⟩ => rfl }
      have heq := Fintype.sum_equiv e
        (fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => Q.pmf t * d₁.dist t.1 (g₁ (t.2.2.1, t.2.2.2)))
        (fun s : X₂ × Fin kU₂ × (X₁ × Fin kU₁) => Q.pmf (s.2.2.1, s.1, s.2.2.2, s.2.1) *
          d₁.dist s.2.2.1 (g₁ (s.2.2.2, s.2.1)))
        (fun _ => rfl)
      rw [heq, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun x₂ _ => ?_
      rw [Fintype.sum_prod_type]
      by_cases hpx : P.snd.pmf x₂ = 0
      · simp only [hpx, ↓reduceIte]
        refine Finset.sum_eq_zero fun u₂ _ => Finset.sum_eq_zero fun p _ => ?_
        rw [hQ_fac]; simp [hpx]
      · simp only [hpx, ↓reduceIte]
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun u₂ _ => ?_
        dsimp only [sliceCost]
        rw [Finset.mul_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [hQ_fac]; simp only [hpx, ↓reduceIte]; ring
    rw [hL]
    refine le_trans ?_ hd₁
    rw [hR]
    refine Finset.sum_le_sum fun x₂ _ => ?_
    by_cases hpx : P.snd.pmf x₂ = 0
    · simp only [hpx, ↓reduceIte]
      have hsc0 : sliceCost x₂ (u2star x₂) = 0 := by
        refine Finset.sum_eq_zero fun p _ => ?_
        have hq0 : Qwz.pmf (p.1, x₂, p.2) = 0 := by
          have hmarg2 : Qwz.map (fun t => t.2.1) = P.snd := by
            rw [← bt_probDist_map_snd, ← hQwz_marg, map_comp_eq Qwz]; rfl
          have hle : Qwz.pmf (p.1, x₂, p.2) ≤ P.snd.pmf x₂ := by
            rw [← hmarg2]; unfold ProbDist.map; dsimp only
            have h1 := Finset.single_le_sum
              (f := fun t : X₁ × X₂ × Fin kU₁ => if t.2.1 = x₂ then Qwz.pmf t else 0)
              (fun t _ => by split_ifs <;> [exact Qwz.nonneg t; exact le_rfl])
              (Finset.mem_univ (p.1, x₂, p.2))
            simpa using h1
          exact le_antisymm (by linarith) (Qwz.nonneg _)
        simp [hq0]
      linarith
    · simp only [hpx, ↓reduceIte]
      have hpx_pos : 0 < P.snd.pmf x₂ := lt_of_le_of_ne (P.snd.nonneg x₂) (Ne.symm hpx)
      have hsum_u2 : ∑ u₂ : Fin kU₂, (Q.map (fun t => (t.2.2.2, t.2.1))).pmf (u₂, x₂) =
          P.snd.pmf x₂ := by
        have h1 : (Q.map (fun t => (t.2.2.2, t.2.1))).snd = P.snd := by
          rw [← bt_probDist_map_snd, ← bt_probDist_map_snd, ← hmarg, map_comp_eq, map_comp_eq]; rfl
        rw [← h1]; rfl
      rw [le_div_iff₀ hpx_pos]
      calc sliceCost x₂ (u2star x₂) * P.snd.pmf x₂
        _ = (∑ u₂ : Fin kU₂, (Q.map (fun t => (t.2.2.2, t.2.1))).pmf (u₂, x₂)) *
              sliceCost x₂ (u2star x₂) := by rw [hsum_u2, mul_comm]
        _ = ∑ u₂ : Fin kU₂, (Q.map (fun t => (t.2.2.2, t.2.1))).pmf (u₂, x₂) *
              sliceCost x₂ (u2star x₂) := Finset.sum_mul ..
        _ ≤ ∑ u₂ : Fin kU₂, (Q.map (fun t => (t.2.2.2, t.2.1))).pmf (u₂, x₂) *
              sliceCost x₂ u₂ := Finset.sum_le_sum fun u₂ _ =>
                mul_le_mul_of_nonneg_left (hu2star x₂ u₂) ((Q.map _).nonneg _)
  -- Compare rates: `I(X₁; U₁ | X₂) ≤ I(X₁; U₁ | U₂) ≤ R₁`.
  have hrate : condMutualInfo (Qwz.map (fun t => (t.1, t.2.2, t.2.1))) ≤
      condMutualInfo (Q.map (fun t => (t.1, t.2.2.1, t.2.2.2))) := by
    let R1 : ProbDist (Fin kU₁ × X₂ × Fin kU₂ × X₁) :=
      Q.map (fun t => (t.2.2.1, t.2.1, t.2.2.2, t.1))
    have hR1 : condMutualInfo (R1.map (fun t => (t.1, (t.2.1, t.2.2.1), t.2.2.2))) = 0 := by
      unfold R1; rw [map_comp_eq]; exact hmk1
    have hU1_U2_X1 : condMutualInfo (Q.map (fun t => (t.2.2.1, t.2.2.2, t.1))) = 0 := by
      have h := (bt_condMutualInfo_zero_split_swap R1 hR1).1
      unfold R1 at h; rw [map_comp_eq] at h; exact h
    have hU1_X2_X1 : condMutualInfo (Q.map (fun t => (t.2.2.1, t.2.1, t.1))) = 0 := by
      have h := (bt_condMutualInfo_zero_split R1 hR1).1
      unfold R1 at h; rw [map_comp_eq] at h; exact h
    have hLHS : condMutualInfo (Qwz.map (fun t => (t.1, t.2.2, t.2.1))) =
        mutualInfo (Q.map (fun t => (t.1, t.2.2.1))) -
        mutualInfo (Q.map (fun t => (t.2.2.1, t.2.1))) := by
      have h := bt_cmi_eq_sub_of_markov (Qwz.map (fun t => (t.1, t.2.2, t.2.1))) (by
        unfold Qwz; rw [map_comp_eq, map_comp_eq]; exact hU1_X2_X1)
      rw [h]; unfold Qwz; simp_rw [map_comp_eq]; rfl
    have hRHS : condMutualInfo (Q.map (fun t => (t.1, t.2.2.1, t.2.2.2))) =
        mutualInfo (Q.map (fun t => (t.1, t.2.2.1))) -
        mutualInfo (Q.map (fun t => (t.2.2.1, t.2.2.2))) := by
      have h := bt_cmi_eq_sub_of_markov (Q.map (fun t => (t.1, t.2.2.1, t.2.2.2))) (by
        rw [map_comp_eq]; exact hU1_U2_X1)
      rw [h, map_comp_eq, map_comp_eq]; rfl
    let R2' : ProbDist (Fin kU₂ × X₁ × Fin kU₁ × X₂) :=
      Q.map (fun t => (t.2.2.2, t.1, t.2.2.1, t.2.1))
    have hR2' : condMutualInfo (R2'.map (fun t => (t.1, (t.2.1, t.2.2.1), t.2.2.2))) = 0 := by
      unfold R2'; rw [map_comp_eq]; exact hmk2
    have hU2_U1_X2 : condMutualInfo (Q.map (fun t => (t.2.2.2, t.2.2.1, t.2.1))) = 0 := by
      have h := (bt_condMutualInfo_zero_split_swap R2' hR2').1
      unfold R2' at h; rw [map_comp_eq] at h; exact h
    have hdpi : mutualInfo (Q.map (fun t => (t.2.2.1, t.2.2.2))) ≤
        mutualInfo (Q.map (fun t => (t.2.2.1, t.2.1))) := by
      have h0 : 0 ≤ condMutualInfo (Q.map (fun t => (t.2.1, t.2.2.1, t.2.2.2))) :=
        condMutualInfo_nonneg _
      have hU1_U2_X2 : condMutualInfo (Q.map (fun t => (t.2.2.1, t.2.2.2, t.2.1))) = 0 := by
        rw [← bt_condMutualInfo_symm (Q.map (fun t => (t.2.2.2, t.2.2.1, t.2.1))), map_comp_eq] at hU2_U1_X2
        exact hU2_U1_X2
      have heq := bt_cmi_eq_sub_of_markov (Q.map (fun t => (t.2.1, t.2.2.1, t.2.2.2))) (by
        rw [map_comp_eq]; exact hU1_U2_X2)
      rw [map_comp_eq, map_comp_eq] at heq
      have hsym : mutualInfo (Q.map ((fun t : X₂ × Fin kU₁ × Fin kU₂ => (t.1, t.2.1)) ∘
            fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => (t.2.1, t.2.2.1, t.2.2.2))) =
          mutualInfo (Q.map (fun t => (t.2.2.1, t.2.1))) := by
        have hmap : Q.map ((fun t : X₂ × Fin kU₁ × Fin kU₂ => (t.1, t.2.1)) ∘
            fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => (t.2.1, t.2.2.1, t.2.2.2)) =
            (Q.map (fun t => (t.2.2.1, t.2.1))).map Prod.swap := by
          rw [map_comp_eq]; rfl
        rw [hmap, bt_mutualInfo_symm]
      have hsnd_eq : Q.map ((fun t : X₂ × Fin kU₁ × Fin kU₂ => (t.2.1, t.2.2)) ∘
            fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => (t.2.1, t.2.2.1, t.2.2.2)) =
          Q.map (fun t => (t.2.2.1, t.2.2.2)) := rfl
      rw [hsym, hsnd_eq] at heq
      linarith
    linarith
  exact le_trans (wynerZivRateDistortion_le hkU₁ hQwz_marg hQwz_mk hQwz_dist) (le_trans hrate hR₁)

/-- **Special Case 2b (Wyner–Ziv Achievability Inside Berger–Tung Inner Bound)**:
    when encoder 2 transmits `X₂` losslessly (`R₂ ≥ H(X₂)`) and `D₂` is achievable from `X₂`
    alone (e.g. `d₂ = hammingDistortion X₂, D₂ = 0` or `D₂` large enough for a constant
    reconstruction), every rate `R₁ > wynerZivRateDistortion P d₁ D₁` yields
    `(R₁, R₂) ∈ bergerTungInnerBound P d₁ d₂ D₁ D₂`. -/
theorem mem_bergerTungInnerBound_of_wynerZiv
    {P : ProbDist (X₁ × X₂)} {d₁ : Distortion X₁ Xh₁} {d₂ : Distortion X₂ Xh₂}
    {R₁ R₂ D₁ D₂ : ℝ}
    (hfeas₁ : IsWynerZivFeasible P d₁ D₁)
    (hfeas₂ : ∃ f : X₂ → Xh₂, (∑ xy : X₁ × X₂, P.pmf xy * d₂.dist xy.2 (f xy.2)) ≤ D₂)
    (hR₁ : wynerZivRateDistortion P d₁ D₁ < R₁)
    (hR₂ : shannonEntropy P.snd ≤ R₂) :
    (R₁, R₂) ∈ bergerTungInnerBound P d₁ d₂ D₁ D₂ := by
  classical
  -- Extract a Wyner–Ziv witness `(kU₁, Qwz, g₁)` with `I(X₁; U₁ | X₂) < R₁`.
  have hS_ne : { r : ℝ | ∃ (kU : ℕ) (Q : ProbDist (X₁ × X₂ × Fin kU)) (g : Fin kU × X₂ → Xh₁),
      0 < kU ∧ Q.map (fun t => (t.1, t.2.1)) = P ∧
      condMutualInfo (Q.map (fun t => (t.2.2, t.2.1, t.1))) = 0 ∧
      (∑ t : X₁ × X₂ × Fin kU, Q.pmf t * d₁.dist t.1 (g (t.2.2, t.2.1))) ≤ D₁ ∧
      r = condMutualInfo (Q.map (fun t => (t.1, t.2.2, t.2.1))) }.Nonempty := by
    rcases hfeas₁ with ⟨kU, Q, g, hk, hmarg, hmk, hd⟩
    exact ⟨_, kU, Q, g, hk, hmarg, hmk, hd, rfl⟩
  obtain ⟨r, ⟨kU₁, Qwz, gwz, _hkU₁, hmarg, hmk, hd₁, rfl⟩, hr_lt⟩ :=
    exists_lt_of_csInf_lt hS_ne hR₁
  rcases hfeas₂ with ⟨f₂, hf₂⟩
  -- Embed `U₂ = e₂(X₂)` with `kU₂ = Fintype.card X₂`.
  let kU₂ := Fintype.card X₂
  let e₂ : X₂ ≃ Fin kU₂ := Fintype.equivFin X₂
  let Q : ProbDist (X₁ × X₂ × Fin kU₁ × Fin kU₂) :=
    Qwz.map (fun t => (t.1, t.2.1, t.2.2, e₂ t.2.1))
  let g₁ : Fin kU₁ × Fin kU₂ → Xh₁ := fun u => gwz (u.1, e₂.symm u.2)
  let g₂ : Fin kU₁ × Fin kU₂ → Xh₂ := fun u => f₂ (e₂.symm u.2)
  have hR₁_nn : 0 ≤ R₁ := le_trans (condMutualInfo_nonneg _) (le_of_lt hr_lt)
  have hR₂_nn : 0 ≤ R₂ := le_trans (shannonEntropy_nonneg P.snd) hR₂
  refine ⟨hR₁_nn, hR₂_nn, kU₁, kU₂, Q, g₁, g₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Marginal `(X₁, X₂) = P`.
    unfold Q; rw [map_comp_eq]; exact hmarg
  · -- `U₁ — X₁ — (X₂, e₂(X₂))`: equivalent to `U₁ — X₁ — X₂`.
    unfold Q; rw [map_comp_eq]
    have h1 : condMutualInfo (Qwz.map ((fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => (t.2.2.1, (t.2.1, t.2.2.2), t.1)) ∘
        fun t : X₁ × X₂ × Fin kU₁ => (t.1, t.2.1, t.2.2, e₂ t.2.1))) =
        condMutualInfo (Qwz.map (fun t => (t.2.2, t.2.1, t.1))) := by
      unfold condMutualInfo; dsimp only; simp_rw [map_comp_eq]
      have hA : shannonEntropy (Qwz.map ((fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => (t.2.2.1, (t.2.1, t.2.2.2), t.1)) ∘
          fun t : X₁ × X₂ × Fin kU₁ => (t.1, t.2.1, t.2.2, e₂ t.2.1))) =
          shannonEntropy (Qwz.map (fun t => (t.2.2, t.2.1, t.1))) :=
        bt_shannonEntropy_map_eq_of_bij Qwz _ _
          ⟨fun s => (s.1, s.2.1.1, s.2.2), fun _ => rfl⟩
          ⟨fun s => (s.1, (s.2.1, e₂ s.2.1), s.2.2), fun _ => rfl⟩
      have hB : shannonEntropy (Qwz.map ((fun t : Fin kU₁ × (X₂ × Fin kU₂) × X₁ => (t.2.1, t.2.2)) ∘
          (fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => (t.2.2.1, (t.2.1, t.2.2.2), t.1)) ∘
          fun t : X₁ × X₂ × Fin kU₁ => (t.1, t.2.1, t.2.2, e₂ t.2.1))) =
          shannonEntropy (Qwz.map ((fun t : Fin kU₁ × X₂ × X₁ => (t.2.1, t.2.2)) ∘
          fun t : X₁ × X₂ × Fin kU₁ => (t.2.2, t.2.1, t.1))) :=
        bt_shannonEntropy_map_eq_of_bij Qwz _ _
          ⟨fun p => (p.1.1, p.2), fun _ => rfl⟩
          ⟨fun p => ((p.1, e₂ p.1), p.2), fun _ => rfl⟩
      rw [hA, hB]; rfl
    rw [h1, hmk]
  · -- `e₂(X₂) — X₂ — (X₁, U₁)`: deterministic in `X₂`.
    unfold Q; rw [map_comp_eq]
    let P' : ProbDist ((X₁ × Fin kU₁) × X₂) := Qwz.map (fun t => ((t.1, t.2.2), t.2.1))
    have hrew : Qwz.map ((fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => (t.2.2.2, (t.1, t.2.2.1), t.2.1)) ∘
        fun t : X₁ × X₂ × Fin kU₁ => (t.1, t.2.1, t.2.2, e₂ t.2.1)) =
        P'.map (fun bc => (e₂ bc.2, bc.1, bc.2)) := by
      unfold P'; rw [map_comp_eq]; rfl
    rw [hrew]
    exact bt_condMutualInfo_eq_zero_of_det_left P' e₂
  · -- Distortion 1: equals `E_{Qwz}[d₁(X₁, gwz(U₁, X₂))] ≤ D₁`.
    unfold Q; rw [← sum_pmf_mul_comp Qwz]
    have heq : ∑ t : X₁ × X₂ × Fin kU₁, Qwz.pmf t * d₁.dist t.1 (g₁ (t.2.2, e₂ t.2.1)) =
        ∑ t : X₁ × X₂ × Fin kU₁, Qwz.pmf t * d₁.dist t.1 (gwz (t.2.2, t.2.1)) :=
      Finset.sum_congr rfl fun t _ => by simp [g₁]
    linarith
  · -- Distortion 2: equals `E_P[d₂(X₂, f₂(X₂))] ≤ D₂`.
    unfold Q; rw [← sum_pmf_mul_comp Qwz]
    have heq : ∑ t : X₁ × X₂ × Fin kU₁, Qwz.pmf t * d₂.dist t.2.1 (g₂ (t.2.2, e₂ t.2.1)) =
        ∑ xy : X₁ × X₂, P.pmf xy * d₂.dist xy.2 (f₂ xy.2) := by
      rw [← hmarg, ← sum_pmf_mul_comp Qwz]
      exact Finset.sum_congr rfl fun t _ => by simp [g₂]
    linarith
  · -- Rate 1: `I(X₁; U₁ | e₂(X₂)) = I(X₁; U₁ | X₂) ≤ R₁`.
    have heq : condMutualInfo (Q.map (fun t => (t.1, t.2.2.1, t.2.2.2))) =
        condMutualInfo (Qwz.map (fun t => (t.1, t.2.2, t.2.1))) := by
      unfold Q; rw [map_comp_eq]
      have hcomp : ((fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => (t.1, t.2.2.1, t.2.2.2)) ∘
          fun t : X₁ × X₂ × Fin kU₁ => (t.1, t.2.1, t.2.2, e₂ t.2.1)) =
          (fun t : X₁ × Fin kU₁ × X₂ => (t.1, t.2.1, e₂ t.2.2)) ∘
            fun t : X₁ × X₂ × Fin kU₁ => (t.1, t.2.2, t.2.1) := rfl
      rw [hcomp, ← map_comp_eq, bt_condMutualInfo_map_thd_equiv]
    linarith
  · -- Rate 2: `I(X₂; e₂(X₂) | U₁) = H(X₂ | U₁) ≤ H(X₂) ≤ R₂`.
    have hle : condMutualInfo (Q.map (fun t => (t.2.1, t.2.2.2, t.2.2.1))) ≤ shannonEntropy P.snd := by
      unfold Q; rw [map_comp_eq]
      unfold condMutualInfo; dsimp only; simp_rw [map_comp_eq]
      have h1 : shannonEntropy (Qwz.map ((fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => (t.2.1, t.2.2.2, t.2.2.1)) ∘
          fun t : X₁ × X₂ × Fin kU₁ => (t.1, t.2.1, t.2.2, e₂ t.2.1))) =
          shannonEntropy (Qwz.map (fun t => (t.2.1, t.2.2))) :=
        bt_shannonEntropy_map_eq_of_bij Qwz _ _
          ⟨fun s => (s.1, s.2.2), fun _ => rfl⟩
          ⟨fun s => (s.1, e₂ s.1, s.2), fun _ => rfl⟩
      have h2 : shannonEntropy (Qwz.map ((fun t : X₂ × Fin kU₂ × Fin kU₁ => (t.2.1, t.2.2)) ∘
          (fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => (t.2.1, t.2.2.2, t.2.2.1)) ∘
          fun t : X₁ × X₂ × Fin kU₁ => (t.1, t.2.1, t.2.2, e₂ t.2.1))) =
          shannonEntropy (Qwz.map (fun t => (t.2.1, t.2.2))) :=
        bt_shannonEntropy_map_eq_of_bij Qwz _ _
          ⟨fun p => (e₂.symm p.1, p.2), fun t => by simp⟩
          ⟨fun p => (e₂ p.1, p.2), fun _ => rfl⟩
      have h3 : (Qwz.map ((fun t : X₂ × Fin kU₂ × Fin kU₁ => (t.1, t.2.2)) ∘
          (fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => (t.2.1, t.2.2.2, t.2.2.1)) ∘
          fun t : X₁ × X₂ × Fin kU₁ => (t.1, t.2.1, t.2.2, e₂ t.2.1))) =
          Qwz.map (fun t => (t.2.1, t.2.2)) := rfl
      have h4 : (Qwz.map ((fun t : X₂ × Fin kU₂ × Fin kU₁ => t.2.2) ∘
          (fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => (t.2.1, t.2.2.2, t.2.2.1)) ∘
          fun t : X₁ × X₂ × Fin kU₁ => (t.1, t.2.1, t.2.2, e₂ t.2.1))) =
          (Qwz.map (fun t => (t.2.1, t.2.2))).snd := by
        rw [← bt_probDist_map_snd, map_comp_eq]; rfl
      rw [h1, h2, h3, h4]
      have hce : shannonEntropy (Qwz.map (fun t => (t.2.1, t.2.2))) -
          shannonEntropy (Qwz.map (fun t => (t.2.1, t.2.2))).snd =
          condEntropy (Qwz.map (fun t => (t.2.1, t.2.2))) := rfl
      have hfst : (Qwz.map (fun t => (t.2.1, t.2.2))).fst = P.snd := by
        rw [← bt_probDist_map_fst, ← bt_probDist_map_snd, ← hmarg, map_comp_eq, map_comp_eq]; rfl
      have hbd := condEntropy_le_shannonEntropy (Qwz.map (fun t => (t.2.1, t.2.2)))
      rw [hfst] at hbd
      linarith
    linarith
  · -- Sum-rate: `I(X₁, X₂; U₁, e₂(X₂)) = H(X₂) + I(X₁; U₁ | X₂) ≤ R₂ + R₁`.
    have hsum_eq : mutualInfo (Q.map (fun t => ((t.1, t.2.1), (t.2.2.1, t.2.2.2)))) =
        shannonEntropy P.snd + condMutualInfo (Qwz.map (fun t => (t.1, t.2.2, t.2.1))) := by
      unfold Q; rw [map_comp_eq]
      unfold mutualInfo condMutualInfo; dsimp only; simp_rw [map_comp_eq]
      have h1 : (Qwz.map ((fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => ((t.1, t.2.1), (t.2.2.1, t.2.2.2))) ∘
          fun t : X₁ × X₂ × Fin kU₁ => (t.1, t.2.1, t.2.2, e₂ t.2.1))).fst = P := by
        rw [← bt_probDist_map_fst, map_comp_eq]; exact hmarg
      have h2 : shannonEntropy (Qwz.map ((fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => ((t.1, t.2.1), (t.2.2.1, t.2.2.2))) ∘
          fun t : X₁ × X₂ × Fin kU₁ => (t.1, t.2.1, t.2.2, e₂ t.2.1))).snd =
          shannonEntropy (Qwz.map (fun t => (t.2.2, t.2.1))) := by
        rw [← bt_probDist_map_snd, map_comp_eq]
        exact bt_shannonEntropy_map_eq_of_bij Qwz _ _
          ⟨fun p => (p.1, e₂.symm p.2), fun t => by simp⟩
          ⟨fun p => (p.1, e₂ p.2), fun _ => rfl⟩
      have h3 : shannonEntropy (Qwz.map ((fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => ((t.1, t.2.1), (t.2.2.1, t.2.2.2))) ∘
          fun t : X₁ × X₂ × Fin kU₁ => (t.1, t.2.1, t.2.2, e₂ t.2.1))) =
          shannonEntropy (Qwz.map (fun t => (t.1, t.2.2, t.2.1))) :=
        bt_shannonEntropy_map_eq_of_bij Qwz _ _
          ⟨fun s => (s.1.1, s.2.1, s.1.2), fun _ => rfl⟩
          ⟨fun s => ((s.1, s.2.2), (s.2.1, e₂ s.2.2)), fun _ => rfl⟩
      have h4 : Qwz.map ((fun t : X₁ × Fin kU₁ × X₂ => (t.1, t.2.2)) ∘
          fun t : X₁ × X₂ × Fin kU₁ => (t.1, t.2.2, t.2.1)) = P := hmarg
      have h5 : Qwz.map ((fun t : X₁ × Fin kU₁ × X₂ => (t.2.1, t.2.2)) ∘
          fun t : X₁ × X₂ × Fin kU₁ => (t.1, t.2.2, t.2.1)) =
          Qwz.map (fun t => (t.2.2, t.2.1)) := rfl
      have h6 : Qwz.map ((fun t : X₁ × Fin kU₁ × X₂ => t.2.2) ∘
          fun t : X₁ × X₂ × Fin kU₁ => (t.1, t.2.2, t.2.1)) = P.snd := by
        rw [← bt_probDist_map_snd, ← hmarg, map_comp_eq]; rfl
      rw [h1, h2, h3, h4, h5, h6]; ring
    linarith

/-- **One-Sided Collapse of Berger–Tung Inner Bound to Wyner–Ziv**:
    when `R₂ ≥ H(X₂)` and `D₂` is achievable from `X₂` alone, the infimum of `R₁` such that
    `(R₁, R₂) ∈ bergerTungInnerBound P d₁ d₂ D₁ D₂` equals `wynerZivRateDistortion P d₁ D₁`. -/
theorem sInf_bergerTungInnerBound_eq_wynerZiv
    {P : ProbDist (X₁ × X₂)} {d₁ : Distortion X₁ Xh₁} {d₂ : Distortion X₂ Xh₂}
    {R₂ D₁ D₂ : ℝ}
    (hfeas₁ : IsWynerZivFeasible P d₁ D₁)
    (hfeas₂ : ∃ f : X₂ → Xh₂, (∑ xy : X₁ × X₂, P.pmf xy * d₂.dist xy.2 (f xy.2)) ≤ D₂)
    (hR₂ : shannonEntropy P.snd ≤ R₂) :
    sInf { R₁ : ℝ | (R₁, R₂) ∈ bergerTungInnerBound P d₁ d₂ D₁ D₂ } =
      wynerZivRateDistortion P d₁ D₁ := by
  have hne : { R₁ : ℝ | (R₁, R₂) ∈ bergerTungInnerBound P d₁ d₂ D₁ D₂ }.Nonempty :=
    ⟨wynerZivRateDistortion P d₁ D₁ + 1,
      mem_bergerTungInnerBound_of_wynerZiv hfeas₁ hfeas₂ (by linarith) hR₂⟩
  have hlb : ∀ R₁ ∈ { R₁ : ℝ | (R₁, R₂) ∈ bergerTungInnerBound P d₁ d₂ D₁ D₂ },
      wynerZivRateDistortion P d₁ D₁ ≤ R₁ :=
    fun _ h => wynerZivRateDistortion_le_of_mem_bergerTungInnerBound h
  refine le_antisymm ?_ (le_csInf hne hlb)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  exact csInf_le ⟨wynerZivRateDistortion P d₁ D₁, hlb⟩
    (mem_bergerTungInnerBound_of_wynerZiv hfeas₁ hfeas₂ (by linarith) hR₂)

/-- **Operational Wyner–Ziv Reduction**:
    any operationally achievable Berger–Tung 4-tuple `(R₁, R₂, D₁, D₂)` satisfies the
    Wyner–Ziv single-letter lower bound `wynerZivRateDistortion P d₁ (D₁ + ε) ≤ R₁ + ε`
    for every `ε > 0`. -/
theorem wynerZiv_converse_of_isBergerTungAchievable
    {P : ProbDist (X₁ × X₂)} {d₁ : Distortion X₁ Xh₁} {d₂ : Distortion X₂ Xh₂}
    {R₁ R₂ D₁ D₂ : ℝ}
    (h : IsBergerTungAchievable P d₁ d₂ R₁ R₂ D₁ D₂) :
    ∀ ε > 0, wynerZivRateDistortion P d₁ (D₁ + ε) ≤ R₁ + ε := by
  intro ε hε
  rcases h with ⟨hR₁, _, hach⟩
  obtain ⟨N, hN⟩ := hach ε hε
  let n := max N 1
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_max_right N 1)
  obtain ⟨enc₁, enc₂, dec₁, _, hd₁, _⟩ := hN n (le_max_left N 1)
  let M₁ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * (R₁ + ε))))
  have hM₁ : 0 < M₁ := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
  let decWZ : Fin M₁ → (Fin n → X₂) → (Fin n → Xh₁) := fun m₁ x₂ => dec₁ (m₁, enc₂ x₂)
  have hconv := wynerZiv_converse P d₁ hn hM₁ enc₁ decWZ hd₁
  have hM₁_le : (M₁ : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * (R₁ + ε)) :=
    bt_max_one_floor_two_rpow_le n (by linarith)
  have hlog : log2 (M₁ : ℝ) ≤ (n : ℝ) * (R₁ + ε) := by
    calc log2 (M₁ : ℝ)
      _ ≤ log2 ((2 : ℝ) ^ ((n : ℝ) * (R₁ + ε))) :=
          bt_log2_mono_le (Nat.cast_pos.mpr hM₁) hM₁_le
      _ = (n : ℝ) * (R₁ + ε) := bt_log2_two_rpow_eq _
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hdiv : log2 (M₁ : ℝ) / (n : ℝ) ≤ R₁ + ε := by
    rw [div_le_iff₀ hn_pos]; linarith
  exact le_trans hconv hdiv

end SingleLetterBounds

/-! ### 2. Operational Berger–Tung Outer Bound Converse (El Gamal & Kim §12.1.3) -/

section BergerTungConverse

variable {X₁ X₂ Xh₁ Xh₂ : Type*}
  [Fintype X₁] [Fintype X₂] [Fintype Xh₁] [Fintype Xh₂]

/-- Mask a length-`n` sequence to keep only coordinates strictly before `k`. -/
private def maskPrefix {α : Type*} {n : ℕ} (k : ℕ) (z : Fin n → α) : Fin n → Option α :=
  fun j => if j.1 < k then some (z j) else none

/-- Equivalence splitting coordinate `i` from the remaining `n - 1` coordinates. -/
private def btSplitCoord {α : Type*} {n : ℕ} (i : Fin n) :
    (Fin n → α) ≃ α × ({ j : Fin n // j ≠ i } → α) where
  toFun := fun x => (x i, fun j => x j.1)
  invFun := fun p j => if h : j = i then p.1 else p.2 ⟨j, h⟩
  left_inv := fun x => by funext j; by_cases h : j = i <;> simp [h]
  right_inv := fun ⟨a, r⟩ => by
    refine Prod.ext (by simp) ?_
    funext ⟨j, hj⟩; simp [hj]

omit [Fintype Xh₁] [Fintype Xh₂] in
/-- **Finite-Blocklength Berger–Tung Outer Bound Converse** (Berger 1978; Tung 1978;
    El Gamal & Kim §12.1.3):
    for any blocklength `n ≥ 1`, codebook sizes `M₁, M₂ ≥ 1`, encoders `enc₁, enc₂`, and
    decoders `dec₁, dec₂` achieving expected per-symbol distortions `≤ D₁` and `≤ D₂`,
    `(log₂ M₁ / n, log₂ M₂ / n) ∈ bergerTungOuterBound P d₁ d₂ D₁ D₂`. -/
theorem bergerTung_outer_converse_block
    (P : ProbDist (X₁ × X₂)) (d₁ : Distortion X₁ Xh₁) (d₂ : Distortion X₂ Xh₂)
    {n M₁ M₂ : ℕ} (hn : 0 < n) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (enc₁ : (Fin n → X₁) → Fin M₁) (enc₂ : (Fin n → X₂) → Fin M₂)
    (dec₁ : Fin M₁ × Fin M₂ → Fin n → Xh₁) (dec₂ : Fin M₁ × Fin M₂ → Fin n → Xh₂)
    {D₁ D₂ : ℝ}
    (hd₁ : ∑ x : Fin n → X₁ × X₂, (∏ i : Fin n, P.pmf (x i)) *
      ((1 / (n : ℝ)) * ∑ i : Fin n,
        d₁.dist (x i).1 (dec₁ (enc₁ (fun j => (x j).1), enc₂ (fun j => (x j).2)) i)) ≤ D₁)
    (hd₂ : ∑ x : Fin n → X₁ × X₂, (∏ i : Fin n, P.pmf (x i)) *
      ((1 / (n : ℝ)) * ∑ i : Fin n,
        d₂.dist (x i).2 (dec₂ (enc₁ (fun j => (x j).1), enc₂ (fun j => (x j).2)) i)) ≤ D₂) :
    (log2 (M₁ : ℝ) / (n : ℝ), log2 (M₂ : ℝ) / (n : ℝ)) ∈
      bergerTungOuterBound P d₁ d₂ D₁ D₂ := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have : Nonempty (Fin M₁) := ⟨⟨0, hM₁⟩⟩
  have : Nonempty (Fin M₂) := ⟨⟨0, hM₂⟩⟩
  let Pn : ProbDist (Fin n → X₁ × X₂) := iidDist P n
  let xs : (Fin n → X₁ × X₂) → (Fin n → X₁) := fun z i => (z i).1
  let ys : (Fin n → X₁ × X₂) → (Fin n → X₂) := fun z i => (z i).2
  let U1raw := Fin n × Fin M₁ × (Fin n → Option (X₁ × X₂))
  let U2raw := Fin n × Fin M₂ × (Fin n → Option (X₁ × X₂))
  let kU₁ : ℕ := Fintype.card U1raw
  let kU₂ : ℕ := Fintype.card U2raw
  let e₁ : U1raw ≃ Fin kU₁ := Fintype.equivFin U1raw
  let e₂ : U2raw ≃ Fin kU₂ := Fintype.equivFin U2raw
  let UnifN : ProbDist (Fin n) := ProbDist.uniform
  let Qraw : ProbDist (X₁ × X₂ × U1raw × U2raw) :=
    (UnifN.prod Pn).map (fun qz =>
      ((qz.2 qz.1).1, (qz.2 qz.1).2,
       (qz.1, enc₁ (xs qz.2), maskPrefix qz.1.1 qz.2),
       (qz.1, enc₂ (ys qz.2), maskPrefix qz.1.1 qz.2)))
  let Q : ProbDist (X₁ × X₂ × Fin kU₁ × Fin kU₂) :=
    Qraw.map (fun t => (t.1, t.2.1, e₁ t.2.2.1, e₂ t.2.2.2))
  let g₁ : Fin kU₁ × Fin kU₂ → Xh₁ := fun u =>
    dec₁ ((e₁.symm u.1).2.1, (e₂.symm u.2).2.1) (e₁.symm u.1).1
  let g₂ : Fin kU₁ × Fin kU₂ → Xh₂ := fun u =>
    dec₂ ((e₁.symm u.1).2.1, (e₂.symm u.2).2.1) (e₁.symm u.1).1
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hlog1_nn : 0 ≤ log2 (M₁ : ℝ) / (n : ℝ) := by
    have h1 : (1 : ℝ) ≤ (M₁ : ℝ) := by exact_mod_cast hM₁
    have hl : 0 ≤ log2 (M₁ : ℝ) := by
      unfold log2
      exact div_nonneg (Real.log_nonneg h1) (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
    exact div_nonneg hl (le_of_lt hn_pos)
  have hlog2_nn : 0 ≤ log2 (M₂ : ℝ) / (n : ℝ) := by
    have h1 : (1 : ℝ) ≤ (M₂ : ℝ) := by exact_mod_cast hM₂
    have hl : 0 ≤ log2 (M₂ : ℝ) := by
      unfold log2
      exact div_nonneg (Real.log_nonneg h1) (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
    exact div_nonneg hl (le_of_lt hn_pos)
  -- Step 1: Marginal `(X₁, X₂) = P`.
  have hQraw_marg : Qraw.map (fun t => (t.1, t.2.1)) = P := by
    unfold Qraw; rw [map_comp_eq]
    unfold ProbDist.map ProbDist.prod
    congr; funext xy; dsimp only [Function.comp_apply]
    rw [Fintype.sum_prod_type]
    have hinner : ∀ q : Fin n,
        (∑ z : Fin n → X₁ × X₂, if ((z q).1, (z q).2) = xy then UnifN.pmf q * Pn.pmf z else 0) =
          UnifN.pmf q * P.pmf xy := fun q => by
      have h1 : (∑ z : Fin n → X₁ × X₂, if ((z q).1, (z q).2) = xy then UnifN.pmf q * Pn.pmf z else 0) =
          UnifN.pmf q * (Pn.map (fun z => z q)).pmf xy := by
        unfold ProbDist.map; dsimp only; rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun z _ => by
          have heta : ((z q).1, (z q).2) = z q := Prod.mk.eta
          rw [heta]; split_ifs <;> ring
      rw [h1, bt_iidDist_map_coord]
    simp_rw [hinner]
    rw [← Finset.sum_mul, UnifN.sum_one, one_mul]
  have hQ_marg : Q.map (fun t => (t.1, t.2.1)) = P := by
    unfold Q; rw [map_comp_eq]; exact hQraw_marg
  -- Step 2: Expected distortions `≤ D₁` and `≤ D₂`.
  have hQ_dist₁ : (∑ t : X₁ × X₂ × Fin kU₁ × Fin kU₂, Q.pmf t * d₁.dist t.1 (g₁ (t.2.2.1, t.2.2.2))) ≤ D₁ := by
    unfold Q Qraw; rw [map_comp_eq, ← sum_pmf_mul_comp (UnifN.prod Pn)]
    dsimp only [Function.comp_apply]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    have hrew : (∑ z : Fin n → X₁ × X₂, ∑ q : Fin n,
        (UnifN.prod Pn).pmf (q, z) *
          d₁.dist (z q).1 (g₁ (e₁ (q, enc₁ (xs z), maskPrefix q.1 z),
            e₂ (q, enc₂ (ys z), maskPrefix q.1 z)))) =
        ∑ z : Fin n → X₁ × X₂, (∏ i : Fin n, P.pmf (z i)) *
          ((1 / (n : ℝ)) * ∑ q : Fin n, d₁.dist (z q).1 (dec₁ (enc₁ (xs z), enc₂ (ys z)) q)) := by
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [g₁, Equiv.symm_apply_apply, ProbDist.prod, UnifN, ProbDist.uniform, Fintype.card_fin,
        Pn, iidDist]
      ring
    exact le_trans (le_of_eq hrew) hd₁
  have hQ_dist₂ : (∑ t : X₁ × X₂ × Fin kU₁ × Fin kU₂, Q.pmf t * d₂.dist t.2.1 (g₂ (t.2.2.1, t.2.2.2))) ≤ D₂ := by
    unfold Q Qraw; rw [map_comp_eq, ← sum_pmf_mul_comp (UnifN.prod Pn)]
    dsimp only [Function.comp_apply]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    have hrew : (∑ z : Fin n → X₁ × X₂, ∑ q : Fin n,
        (UnifN.prod Pn).pmf (q, z) *
          d₂.dist (z q).2 (g₂ (e₁ (q, enc₁ (xs z), maskPrefix q.1 z),
            e₂ (q, enc₂ (ys z), maskPrefix q.1 z)))) =
        ∑ z : Fin n → X₁ × X₂, (∏ i : Fin n, P.pmf (z i)) *
          ((1 / (n : ℝ)) * ∑ q : Fin n, d₂.dist (z q).2 (dec₂ (enc₁ (xs z), enc₂ (ys z)) q)) := by
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [g₂, Equiv.symm_apply_apply, ProbDist.prod, UnifN, ProbDist.uniform, Fintype.card_fin,
        Pn, iidDist]
      ring
    exact le_trans (le_of_eq hrew) hd₂
  -- Helper to factor `Pn.pmf z` at coordinate `i` via `btSplitCoord i`.
  have hPn_split : ∀ (i : Fin n) (xy : X₁ × X₂) (r : { j : Fin n // j ≠ i } → X₁ × X₂),
      Pn.pmf ((btSplitCoord i).symm (xy, r)) =
        P.pmf xy * ∏ j : { j : Fin n // j ≠ i }, P.pmf (r j) := by
    intro i xy r
    set z := (btSplitCoord i).symm (xy, r)
    have hzi : z i = xy := by simp [z, btSplitCoord]
    unfold Pn iidDist; dsimp only
    rw [← Finset.mul_prod_erase Finset.univ (fun j => P.pmf (z j)) (Finset.mem_univ i), hzi]
    congr 1
    let eErase : { j : Fin n // j ≠ i } ≃ Finset.univ.erase i :=
      { toFun := fun j => ⟨j.1, Finset.mem_erase.mpr ⟨j.2, Finset.mem_univ j.1⟩⟩
        invFun := fun j => ⟨j.1, (Finset.mem_erase.mp j.2).1⟩
        left_inv := fun ⟨_, _⟩ => rfl
        right_inv := fun ⟨_, _⟩ => rfl }
    rw [← Finset.prod_coe_sort (Finset.univ.erase i)]
    exact (Fintype.prod_equiv eErase _ _ (fun j => by
      simp [eErase, z, btSplitCoord, j.2])).symm
  -- Step 3a: Markov chain `U₁ — X₁ — X₂`.
  have hQraw_mk1 : condMutualInfo (Qraw.map (fun t => (t.2.2.1, t.2.1, t.1))) = 0 := by
    let R := Qraw.map (fun t => (t.2.2.1, t.2.1, t.1))
    let restSum₁ (i : Fin n) (m₁ : Fin M₁) (o : Fin n → Option (X₁ × X₂)) (x₁ : X₁) : ℝ :=
      ∑ r : { j : Fin n // j ≠ i } → X₁ × X₂,
        if enc₁ (fun j => if h : j = i then x₁ else (r ⟨j, h⟩).1) = m₁ ∧
           (fun j : Fin n => if h : j.1 < i.1 then
             some (r ⟨j, fun heq => by subst heq; omega⟩) else none) = o
        then ∏ j : { j : Fin n // j ≠ i }, P.pmf (r j) else 0
    have hR_pmf : ∀ i m₁ o x₂ x₁,
        R.pmf ((i, m₁, o), x₂, x₁) = UnifN.pmf i * P.pmf (x₁, x₂) * restSum₁ i m₁ o x₁ := by
      intro i m₁ o x₂ x₁
      unfold R Qraw; rw [map_comp_eq]
      unfold ProbDist.map ProbDist.prod; dsimp only
      rw [Fintype.sum_prod_type]; dsimp only [Function.comp_apply]
      rw [Finset.sum_eq_single i]
      · have hsum_z := Fintype.sum_equiv (btSplitCoord (α := X₁ × X₂) i)
          (fun z : Fin n → X₁ × X₂ =>
            if ((i, enc₁ (xs z), maskPrefix i.1 z), (z i).2, (z i).1) = ((i, m₁, o), x₂, x₁)
            then UnifN.pmf i * Pn.pmf z else 0)
          (fun pr : (X₁ × X₂) × ({ j : Fin n // j ≠ i } → X₁ × X₂) =>
            let z := (btSplitCoord (α := X₁ × X₂) i).symm pr
            if ((i, enc₁ (xs z), maskPrefix i.1 z), (z i).2, (z i).1) = ((i, m₁, o), x₂, x₁)
            then UnifN.pmf i * Pn.pmf z else 0)
          (fun z => by simp)
        trans (∑ z : Fin n → X₁ × X₂,
            if ((i, enc₁ (xs z), maskPrefix i.1 z), (z i).2, (z i).1) = ((i, m₁, o), x₂, x₁)
            then UnifN.pmf i * Pn.pmf z else 0)
        · refine Finset.sum_congr rfl fun z _ => ?_
          by_cases h : ((i, enc₁ (xs z), maskPrefix i.1 z), (z i).2, (z i).1) = ((i, m₁, o), x₂, x₁) <;>
            simp [h]
        rw [hsum_z, Fintype.sum_prod_type]
        rw [Finset.sum_eq_single (x₁, x₂)]
        · unfold restSum₁; rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_
          set z := (btSplitCoord (α := X₁ × X₂) i).symm ((x₁, x₂), r)
          have hzi : z i = (x₁, x₂) := by simp [z, btSplitCoord]
          have hxs : xs z = fun j => if h : j = i then x₁ else (r ⟨j, h⟩).1 := by
            funext j; by_cases h : j = i <;> simp [xs, z, btSplitCoord, h]
          have hmp : maskPrefix i.1 z =
              fun j : Fin n => if h : j.1 < i.1 then
                some (r ⟨j, fun heq => by subst heq; omega⟩) else none := by
            funext j
            by_cases hlt : j.1 < i.1
            · have hne : j ≠ i := fun heq => by subst heq; omega
              simp [maskPrefix, hlt, z, btSplitCoord, hne]
            · simp [maskPrefix, hlt]
          have hiff : (((i, enc₁ (xs z), maskPrefix i.1 z), (z i).2, (z i).1) = ((i, m₁, o), x₂, x₁)) ↔
              (enc₁ (fun j => if h : j = i then x₁ else (r ⟨j, h⟩).1) = m₁ ∧
               (fun j : Fin n => if h : j.1 < i.1 then
                 some (r ⟨j, fun heq => by subst heq; omega⟩) else none) = o) := by
            rw [hzi, hxs, hmp]; simp
          rw [if_congr hiff rfl rfl, hPn_split i (x₁, x₂) r]
          split_ifs <;> ring
        · intro ⟨a', b'⟩ _ hne
          refine Finset.sum_eq_zero fun r _ => ?_
          have hzi : (btSplitCoord (α := X₁ × X₂) i).symm ((a', b'), r) i = (a', b') := by
            simp [btSplitCoord]
          have hne' : ¬ (b' = x₂ ∧ a' = x₁) := fun ⟨hb, ha⟩ => hne (Prod.ext ha hb)
          simp [hzi, hne']
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro q _ hne
        refine Finset.sum_eq_zero fun z _ => ?_
        by_cases h : ((q, enc₁ (xs z), maskPrefix q.1 z), (z q).2, (z q).1) = ((i, m₁, o), x₂, x₁)
        · exact absurd (congrArg (fun a => a.1.1) h) hne
        · simp [h]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hR_xz : ∀ i m₁ o x₁,
        (R.map (fun s => (s.1, s.2.2))).pmf ((i, m₁, o), x₁) =
          UnifN.pmf i * P.fst.pmf x₁ * restSum₁ i m₁ o x₁ := by
      intro i m₁ o x₁
      unfold ProbDist.map; dsimp only
      rw [Fintype.sum_prod_type, Finset.sum_eq_single (i, m₁, o)]
      · rw [Fintype.sum_prod_type]
        have hinner : ∀ x₂ : X₂,
            (∑ x₁' : X₁, if x₁' = x₁ then R.pmf ((i, m₁, o), x₂, x₁') else 0) =
              UnifN.pmf i * P.pmf (x₁, x₂) * restSum₁ i m₁ o x₁ := fun x₂ => by
          rw [Finset.sum_eq_single x₁]
          · simp [hR_pmf]
          · intro x₁' _ hne; simp [hne]
          · intro h; exact absurd (Finset.mem_univ _) h
        simp only [Prod.mk.injEq, true_and, hinner]
        rw [← Finset.sum_mul, ← Finset.mul_sum]; rfl
      · intro u' _ hne
        rw [Fintype.sum_prod_type]
        exact Finset.sum_eq_zero fun x₂ _ => Finset.sum_eq_zero fun x₁' _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hR_yz_pmf : ∀ x₂ x₁, (R.map (fun s => (s.2.1, s.2.2))).pmf (x₂, x₁) = P.pmf (x₁, x₂) := by
      intro x₂ x₁
      have hR_yz : R.map (fun s => (s.2.1, s.2.2)) = P.map Prod.swap := by
        unfold R; rw [map_comp_eq Qraw, ← hQraw_marg, map_comp_eq Qraw]; rfl
      rw [hR_yz]; exact bt_probDist_map_equiv_pmf (Equiv.prodComm X₁ X₂) P (x₂, x₁)
    have hR_z : R.map (fun s => s.2.2) = P.fst := by
      unfold R; rw [map_comp_eq Qraw, ← bt_probDist_map_fst, ← hQraw_marg, map_comp_eq Qraw]; rfl
    rw [condMutualInfo_eq_zero_iff]
    refine bt_probDist_ext fun ⟨⟨i, m₁, o⟩, x₂, x₁⟩ => ?_
    change R.pmf ((i, m₁, o), x₂, x₁) = if (R.map (fun s => s.2.2)).pmf x₁ = 0 then 0
      else (R.map (fun s => (s.1, s.2.2))).pmf ((i, m₁, o), x₁) *
        (R.map (fun s => (s.2.1, s.2.2))).pmf (x₂, x₁) / (R.map (fun s => s.2.2)).pmf x₁
    rw [hR_pmf, hR_xz, hR_yz_pmf, hR_z]
    by_cases hpx : P.fst.pmf x₁ = 0
    · simp only [hpx, ↓reduceIte]
      have hle : P.pmf (x₁, x₂) ≤ P.fst.pmf x₁ :=
        Finset.single_le_sum (fun y' _ => P.nonneg (x₁, y')) (Finset.mem_univ x₂)
      have hpxy0 : P.pmf (x₁, x₂) = 0 := le_antisymm (by linarith) (P.nonneg (x₁, x₂))
      simp [hpxy0]
    · simp only [ite_eq_right_iff.mpr (fun h => absurd h hpx)]
      field_simp [hpx]
  have hQ_mk1 : condMutualInfo (Q.map (fun t => (t.2.2.1, t.2.1, t.1))) = 0 := by
    unfold Q; rw [map_comp_eq]
    have hcomp : ((fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => (t.2.2.1, t.2.1, t.1)) ∘
        fun t : X₁ × X₂ × U1raw × U2raw => (t.1, t.2.1, e₁ t.2.2.1, e₂ t.2.2.2)) =
        (fun t : U1raw × X₂ × X₁ => (e₁ t.1, t.2.1, t.2.2)) ∘
          fun t : X₁ × X₂ × U1raw × U2raw => (t.2.2.1, t.2.1, t.1) := rfl
    rw [hcomp, ← map_comp_eq, bt_condMutualInfo_map_fst_equiv, hQraw_mk1]
  -- Step 3b: Markov chain `U₂ — X₂ — X₁`.
  have hQraw_mk2 : condMutualInfo (Qraw.map (fun t => (t.2.2.2, t.1, t.2.1))) = 0 := by
    let R := Qraw.map (fun t => (t.2.2.2, t.1, t.2.1))
    let restSum₂ (i : Fin n) (m₂ : Fin M₂) (o : Fin n → Option (X₁ × X₂)) (x₂ : X₂) : ℝ :=
      ∑ r : { j : Fin n // j ≠ i } → X₁ × X₂,
        if enc₂ (fun j => if h : j = i then x₂ else (r ⟨j, h⟩).2) = m₂ ∧
           (fun j : Fin n => if h : j.1 < i.1 then
             some (r ⟨j, fun heq => by subst heq; omega⟩) else none) = o
        then ∏ j : { j : Fin n // j ≠ i }, P.pmf (r j) else 0
    have hR_pmf : ∀ i m₂ o x₁ x₂,
        R.pmf ((i, m₂, o), x₁, x₂) = UnifN.pmf i * P.pmf (x₁, x₂) * restSum₂ i m₂ o x₂ := by
      intro i m₂ o x₁ x₂
      unfold R Qraw; rw [map_comp_eq]
      unfold ProbDist.map ProbDist.prod; dsimp only
      rw [Fintype.sum_prod_type]; dsimp only [Function.comp_apply]
      rw [Finset.sum_eq_single i]
      · have hsum_z := Fintype.sum_equiv (btSplitCoord (α := X₁ × X₂) i)
          (fun z : Fin n → X₁ × X₂ =>
            if ((i, enc₂ (ys z), maskPrefix i.1 z), (z i).1, (z i).2) = ((i, m₂, o), x₁, x₂)
            then UnifN.pmf i * Pn.pmf z else 0)
          (fun pr : (X₁ × X₂) × ({ j : Fin n // j ≠ i } → X₁ × X₂) =>
            let z := (btSplitCoord (α := X₁ × X₂) i).symm pr
            if ((i, enc₂ (ys z), maskPrefix i.1 z), (z i).1, (z i).2) = ((i, m₂, o), x₁, x₂)
            then UnifN.pmf i * Pn.pmf z else 0)
          (fun z => by simp)
        trans (∑ z : Fin n → X₁ × X₂,
            if ((i, enc₂ (ys z), maskPrefix i.1 z), (z i).1, (z i).2) = ((i, m₂, o), x₁, x₂)
            then UnifN.pmf i * Pn.pmf z else 0)
        · refine Finset.sum_congr rfl fun z _ => ?_
          by_cases h : ((i, enc₂ (ys z), maskPrefix i.1 z), (z i).1, (z i).2) = ((i, m₂, o), x₁, x₂) <;>
            simp [h]
        rw [hsum_z, Fintype.sum_prod_type]
        rw [Finset.sum_eq_single (x₁, x₂)]
        · unfold restSum₂; rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_
          set z := (btSplitCoord (α := X₁ × X₂) i).symm ((x₁, x₂), r)
          have hzi : z i = (x₁, x₂) := by simp [z, btSplitCoord]
          have hys : ys z = fun j => if h : j = i then x₂ else (r ⟨j, h⟩).2 := by
            funext j; by_cases h : j = i <;> simp [ys, z, btSplitCoord, h]
          have hmp : maskPrefix i.1 z =
              fun j : Fin n => if h : j.1 < i.1 then
                some (r ⟨j, fun heq => by subst heq; omega⟩) else none := by
            funext j
            by_cases hlt : j.1 < i.1
            · have hne : j ≠ i := fun heq => by subst heq; omega
              simp [maskPrefix, hlt, z, btSplitCoord, hne]
            · simp [maskPrefix, hlt]
          have hiff : (((i, enc₂ (ys z), maskPrefix i.1 z), (z i).1, (z i).2) = ((i, m₂, o), x₁, x₂)) ↔
              (enc₂ (fun j => if h : j = i then x₂ else (r ⟨j, h⟩).2) = m₂ ∧
               (fun j : Fin n => if h : j.1 < i.1 then
                 some (r ⟨j, fun heq => by subst heq; omega⟩) else none) = o) := by
            rw [hzi, hys, hmp]; simp
          rw [if_congr hiff rfl rfl, hPn_split i (x₁, x₂) r]
          split_ifs <;> ring
        · intro ⟨a', b'⟩ _ hne
          refine Finset.sum_eq_zero fun r _ => ?_
          have hzi : (btSplitCoord (α := X₁ × X₂) i).symm ((a', b'), r) i = (a', b') := by
            simp [btSplitCoord]
          have hne' : ¬ (a' = x₁ ∧ b' = x₂) := fun ⟨ha, hb⟩ => hne (Prod.ext ha hb)
          simp [hzi, hne']
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro q _ hne
        refine Finset.sum_eq_zero fun z _ => ?_
        by_cases h : ((q, enc₂ (ys z), maskPrefix q.1 z), (z q).1, (z q).2) = ((i, m₂, o), x₁, x₂)
        · exact absurd (congrArg (fun a => a.1.1) h) hne
        · simp [h]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hR_xz : ∀ i m₂ o x₂,
        (R.map (fun s => (s.1, s.2.2))).pmf ((i, m₂, o), x₂) =
          UnifN.pmf i * P.snd.pmf x₂ * restSum₂ i m₂ o x₂ := by
      intro i m₂ o x₂
      unfold ProbDist.map; dsimp only
      rw [Fintype.sum_prod_type, Finset.sum_eq_single (i, m₂, o)]
      · rw [Fintype.sum_prod_type]
        have hinner : ∀ x₁ : X₁,
            (∑ x₂' : X₂, if x₂' = x₂ then R.pmf ((i, m₂, o), x₁, x₂') else 0) =
              UnifN.pmf i * P.pmf (x₁, x₂) * restSum₂ i m₂ o x₂ := fun x₁ => by
          rw [Finset.sum_eq_single x₂]
          · simp [hR_pmf]
          · intro x₂' _ hne; simp [hne]
          · intro h; exact absurd (Finset.mem_univ _) h
        simp only [Prod.mk.injEq, true_and, hinner]
        rw [← Finset.sum_mul, ← Finset.mul_sum]; rfl
      · intro u' _ hne
        rw [Fintype.sum_prod_type]
        exact Finset.sum_eq_zero fun x₁ _ => Finset.sum_eq_zero fun x₂' _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hR_yz : R.map (fun s => (s.2.1, s.2.2)) = P := by
      unfold R; rw [map_comp_eq Qraw]; exact hQraw_marg
    have hR_z : R.map (fun s => s.2.2) = P.snd := by
      unfold R; rw [map_comp_eq Qraw, ← bt_probDist_map_snd, ← hQraw_marg, map_comp_eq Qraw]; rfl
    rw [condMutualInfo_eq_zero_iff]
    refine bt_probDist_ext fun ⟨⟨i, m₂, o⟩, x₁, x₂⟩ => ?_
    change R.pmf ((i, m₂, o), x₁, x₂) = if (R.map (fun s => s.2.2)).pmf x₂ = 0 then 0
      else (R.map (fun s => (s.1, s.2.2))).pmf ((i, m₂, o), x₂) *
        (R.map (fun s => (s.2.1, s.2.2))).pmf (x₁, x₂) / (R.map (fun s => s.2.2)).pmf x₂
    rw [hR_pmf, hR_xz, hR_yz, hR_z]
    by_cases hpx : P.snd.pmf x₂ = 0
    · simp only [hpx, ↓reduceIte]
      have hle : P.pmf (x₁, x₂) ≤ P.snd.pmf x₂ :=
        Finset.single_le_sum (fun x' _ => P.nonneg (x', x₂)) (Finset.mem_univ x₁)
      have hpxy0 : P.pmf (x₁, x₂) = 0 := le_antisymm (by linarith) (P.nonneg (x₁, x₂))
      simp [hpxy0]
    · simp only [ite_eq_right_iff.mpr (fun h => absurd h hpx)]
      field_simp [hpx]
  have hQ_mk2 : condMutualInfo (Q.map (fun t => (t.2.2.2, t.1, t.2.1))) = 0 := by
    unfold Q; rw [map_comp_eq]
    have hcomp : ((fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => (t.2.2.2, t.1, t.2.1)) ∘
        fun t : X₁ × X₂ × U1raw × U2raw => (t.1, t.2.1, e₁ t.2.2.1, e₂ t.2.2.2)) =
        (fun t : U2raw × X₁ × X₂ => (e₂ t.1, t.2.1, t.2.2)) ∘
          fun t : X₁ × X₂ × U1raw × U2raw => (t.2.2.2, t.1, t.2.1) := rfl
    rw [hcomp, ← map_comp_eq, bt_condMutualInfo_map_fst_equiv, hQraw_mk2]
  -- Step 4: Exact telescoping rate identities on `Qraw`.
  have hXY_ne : Nonempty (X₁ × X₂) := bt_nonempty_of_probDist P
  let xy0 : X₁ × X₂ := Classical.choice hXY_ne
  -- Specialized helpers with `γ : Type` (avoiding extra universe parameters).
  have hH_unif_split : ∀ {γ : Type} [Fintype γ]
      (F : Fin n → (Fin n → X₁ × X₂) → (X₁ × X₂) × γ × (Fin n → Option (X₁ × X₂))),
      shannonEntropy ((UnifN.prod Pn).map (fun qz => (qz.1, F qz.1 qz.2))) =
        shannonEntropy UnifN + (1 / (n : ℝ)) * ∑ q : Fin n, shannonEntropy (Pn.map (F q)) := by
    intro γ _ F
    let W : DMC (Fin n) ((X₁ × X₂) × γ × (Fin n → Option (X₁ × X₂))) :=
      { trans := fun q b => (Pn.map (F q)).pmf b
        nonneg := fun q b => (Pn.map (F q)).nonneg b
        sum_one := fun q => (Pn.map (F q)).sum_one }
    have hW : (UnifN.prod Pn).map (fun qz => (qz.1, F qz.1 qz.2)) = W.joint UnifN := by
      refine bt_probDist_ext fun ⟨q, b⟩ => ?_
      unfold ProbDist.map ProbDist.prod DMC.joint W; dsimp only
      rw [Fintype.sum_prod_type, Finset.sum_eq_single q]
      · simp only [ProbDist.map]; rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun z _ => by split_ifs <;> simp_all
      · intro q' _ hne; exact Finset.sum_eq_zero fun z _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hW, dmc_joint_shannonEntropy]
    have hUnif : ∀ q : Fin n, UnifN.pmf q = 1 / (n : ℝ) := fun q => by
      dsimp only [UnifN, ProbDist.uniform]; rw [Fintype.card_fin]
    simp_rw [hUnif, ← Finset.mul_sum]; rfl
  have hH_unif_split₂ : ∀ {γ : Type} [Fintype γ]
      (F : Fin n → (Fin n → X₁ × X₂) → γ × (Fin n → Option (X₁ × X₂))),
      shannonEntropy ((UnifN.prod Pn).map (fun qz => (qz.1, F qz.1 qz.2))) =
        shannonEntropy UnifN + (1 / (n : ℝ)) * ∑ q : Fin n, shannonEntropy (Pn.map (F q)) := by
    intro γ _ F
    let W : DMC (Fin n) (γ × (Fin n → Option (X₁ × X₂))) :=
      { trans := fun q b => (Pn.map (F q)).pmf b
        nonneg := fun q b => (Pn.map (F q)).nonneg b
        sum_one := fun q => (Pn.map (F q)).sum_one }
    have hW : (UnifN.prod Pn).map (fun qz => (qz.1, F qz.1 qz.2)) = W.joint UnifN := by
      refine bt_probDist_ext fun ⟨q, b⟩ => ?_
      unfold ProbDist.map ProbDist.prod DMC.joint W; dsimp only
      rw [Fintype.sum_prod_type, Finset.sum_eq_single q]
      · simp only [ProbDist.map]; rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun z _ => by split_ifs <;> simp_all
      · intro q' _ hne; exact Finset.sum_eq_zero fun z _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hW, dmc_joint_shannonEntropy]
    have hUnif : ∀ q : Fin n, UnifN.pmf q = 1 / (n : ℝ) := fun q => by
      dsimp only [UnifN, ProbDist.uniform]; rw [Fintype.card_fin]
    simp_rw [hUnif, ← Finset.mul_sum]; rfl
  have hprefix_step : ∀ {γ : Type} [Fintype γ] (h : (Fin n → X₁ × X₂) → γ) (q : Fin n),
      shannonEntropy (Pn.map (fun z => (z q, h z, maskPrefix q.1 z))) =
        shannonEntropy (Pn.map (fun z => (h z, maskPrefix (q.1 + 1) z))) := by
    intro γ _ h q
    refine bt_shannonEntropy_map_eq_of_bij Pn _ _
      ⟨fun p => (p.2.1, fun j => if j = q then some p.1 else p.2.2 j), fun z => ?_⟩
      ⟨fun p => ((p.2 q).getD xy0, p.1, fun j => if j = q then none else p.2 j), fun z => ?_⟩
    · refine Prod.ext rfl (funext fun j => ?_)
      by_cases hjq : j = q
      · subst hjq; simp [maskPrefix]
      · have hiff : j.1 < q.1 ↔ j.1 < q.1 + 1 := by
          have hne : j.1 ≠ q.1 := fun heq => hjq (Fin.ext heq)
          omega
        simp [maskPrefix, hjq, hiff]
    · refine Prod.ext (by simp [maskPrefix]) (Prod.ext rfl (funext fun j => ?_))
      by_cases hjq : j = q
      · subst hjq; simp [maskPrefix]
      · have hiff : j.1 < q.1 + 1 ↔ j.1 < q.1 := by
          have hne : j.1 ≠ q.1 := fun heq => hjq (Fin.ext heq)
          omega
        simp [maskPrefix, hjq, hiff]
  have hprefix_zero : ∀ {γ : Type} [Fintype γ] (h : (Fin n → X₁ × X₂) → γ),
      shannonEntropy (Pn.map (fun z => (h z, maskPrefix 0 z))) =
        shannonEntropy (Pn.map h) := by
    intro γ _ h
    refine bt_shannonEntropy_map_eq_of_bij Pn _ _
      ⟨Prod.fst, fun _ => rfl⟩
      ⟨fun c => (c, fun _ => none), fun z => by
        refine Prod.ext rfl (funext fun j => ?_); simp [maskPrefix]⟩
  have hprefix_full : ∀ {γ : Type} [Fintype γ] (h : (Fin n → X₁ × X₂) → γ),
      shannonEntropy (Pn.map (fun z => (h z, maskPrefix n z))) = (n : ℝ) * shannonEntropy P := by
    intro γ _ h
    have hinj : Function.Injective (fun z : Fin n → X₁ × X₂ => (h z, maskPrefix n z)) := by
      intro z₁ z₂ heq
      have hm : maskPrefix n z₁ = maskPrefix n z₂ := congrArg Prod.snd heq
      funext j
      have hj := congrFun hm j
      simp only [maskPrefix, j.2, ↓reduceIte, Option.some.injEq] at hj
      exact hj
    rw [bt_shannonEntropy_map_injective Pn hinj]
    have heq : Pn = piProdDist (fun _ : Fin n => P) := rfl
    rw [heq, shannonEntropy_piProdDist]; simp
  have htelescope_diff : ∀ {γ : Type} [Fintype γ] (h : (Fin n → X₁ × X₂) → γ),
      shannonEntropy ((UnifN.prod Pn).map (fun qz => (qz.1, (qz.2 qz.1, h qz.2, maskPrefix qz.1.1 qz.2)))) -
      shannonEntropy ((UnifN.prod Pn).map (fun qz => (qz.1, (h qz.2, maskPrefix qz.1.1 qz.2)))) =
        shannonEntropy P - (1 / (n : ℝ)) * shannonEntropy (Pn.map h) := by
    intro γ _ h
    rw [hH_unif_split (fun q z => (z q, h z, maskPrefix q.1 z)),
        hH_unif_split₂ (fun q z => (h z, maskPrefix q.1 z))]
    let f : ℕ → ℝ := fun k => shannonEntropy (Pn.map (fun z => (h z, maskPrefix k z)))
    have hsum : (∑ q : Fin n, shannonEntropy (Pn.map (fun z => (z q, h z, maskPrefix q.1 z)))) -
        (∑ q : Fin n, shannonEntropy (Pn.map (fun z => (h z, maskPrefix q.1 z)))) =
        (n : ℝ) * shannonEntropy P - shannonEntropy (Pn.map h) := by
      rw [← Finset.sum_sub_distrib]
      have hterm : ∀ q : Fin n,
          shannonEntropy (Pn.map (fun z => (z q, h z, maskPrefix q.1 z))) -
            shannonEntropy (Pn.map (fun z => (h z, maskPrefix q.1 z))) =
          f (q.1 + 1) - f q.1 := fun q => by dsimp [f]; rw [hprefix_step h q]
      simp_rw [hterm, bt_fin_sum_telescope f n]
      dsimp [f]; rw [hprefix_full h, hprefix_zero h]
    have hcalc : (1 / (n : ℝ)) * ((n : ℝ) * shannonEntropy P - shannonEntropy (Pn.map h)) =
        shannonEntropy P - (1 / (n : ℝ)) * shannonEntropy (Pn.map h) := by
      field_simp [ne_of_gt hn_pos]
    have hdiff : (shannonEntropy UnifN + (1 / (n : ℝ)) * ∑ q : Fin n, shannonEntropy (Pn.map (fun z => (z q, h z, maskPrefix q.1 z)))) -
        (shannonEntropy UnifN + (1 / (n : ℝ)) * ∑ q : Fin n, shannonEntropy (Pn.map (fun z => (h z, maskPrefix q.1 z)))) =
        (1 / (n : ℝ)) * ((∑ q : Fin n, shannonEntropy (Pn.map (fun z => (z q, h z, maskPrefix q.1 z)))) -
          (∑ q : Fin n, shannonEntropy (Pn.map (fun z => (h z, maskPrefix q.1 z))))) := by ring
    rw [hdiff, hsum, hcalc]
  -- Apply `htelescope_diff` to `M₁`, `M₂`, and `(M₁, M₂)`.
  let D_M1M2 : ProbDist (Fin M₁ × Fin M₂) := Pn.map (fun z => (enc₁ (xs z), enc₂ (ys z)))
  have hM1M2_fst : D_M1M2.fst = Pn.map (fun z => enc₁ (xs z)) := by
    rw [← bt_probDist_map_fst]; unfold D_M1M2; rw [map_comp_eq]; rfl
  have hM1M2_snd : D_M1M2.snd = Pn.map (fun z => enc₂ (ys z)) := by
    rw [← bt_probDist_map_snd]; unfold D_M1M2; rw [map_comp_eq]; rfl
  have hH_M1_le : shannonEntropy (Pn.map (fun z => enc₁ (xs z))) ≤ log2 (M₁ : ℝ) := by
    calc shannonEntropy (Pn.map (fun z => enc₁ (xs z)))
      _ ≤ log2 (Fintype.card (Fin M₁) : ℝ) := shannonEntropy_le_log2_card _
      _ = log2 (M₁ : ℝ) := by rw [Fintype.card_fin]
  have hH_M2_le : shannonEntropy (Pn.map (fun z => enc₂ (ys z))) ≤ log2 (M₂ : ℝ) := by
    calc shannonEntropy (Pn.map (fun z => enc₂ (ys z)))
      _ ≤ log2 (Fintype.card (Fin M₂) : ℝ) := shannonEntropy_le_log2_card _
      _ = log2 (M₂ : ℝ) := by rw [Fintype.card_fin]
  -- Entropy identifications between `Qraw` marginals and `(UnifN.prod Pn)` maps.
  have hH_ZU2 : shannonEntropy (Qraw.map (fun t => ((t.1, t.2.1), t.2.2.2))) =
      shannonEntropy ((UnifN.prod Pn).map (fun qz => (qz.1, (qz.2 qz.1, enc₂ (ys qz.2), maskPrefix qz.1.1 qz.2)))) := by
    unfold Qraw; rw [map_comp_eq]
    exact bt_shannonEntropy_map_eq_of_bij (UnifN.prod Pn) _ _
      ⟨fun p => (p.2.1, (p.1, p.2.2.1, p.2.2.2)), fun _ => rfl⟩
      ⟨fun s => (s.2.1, (s.1, s.2.2.1, s.2.2.2)), fun _ => rfl⟩
  have hH_U2 : shannonEntropy (Qraw.map (fun t => t.2.2.2)) =
      shannonEntropy ((UnifN.prod Pn).map (fun qz => (qz.1, (enc₂ (ys qz.2), maskPrefix qz.1.1 qz.2)))) := by
    unfold Qraw; rw [map_comp_eq]
    exact bt_shannonEntropy_map_eq_of_bij (UnifN.prod Pn) _ _
      ⟨fun u => (u.1, (u.2.1, u.2.2)), fun _ => rfl⟩
      ⟨fun s => (s.1, s.2.1, s.2.2), fun _ => rfl⟩
  have hH_ZU1 : shannonEntropy (Qraw.map (fun t => ((t.1, t.2.1), t.2.2.1))) =
      shannonEntropy ((UnifN.prod Pn).map (fun qz => (qz.1, (qz.2 qz.1, enc₁ (xs qz.2), maskPrefix qz.1.1 qz.2)))) := by
    unfold Qraw; rw [map_comp_eq]
    exact bt_shannonEntropy_map_eq_of_bij (UnifN.prod Pn) _ _
      ⟨fun p => (p.2.1, (p.1, p.2.2.1, p.2.2.2)), fun _ => rfl⟩
      ⟨fun s => (s.2.1, (s.1, s.2.2.1, s.2.2.2)), fun _ => rfl⟩
  have hH_U1 : shannonEntropy (Qraw.map (fun t => t.2.2.1)) =
      shannonEntropy ((UnifN.prod Pn).map (fun qz => (qz.1, (enc₁ (xs qz.2), maskPrefix qz.1.1 qz.2)))) := by
    unfold Qraw; rw [map_comp_eq]
    exact bt_shannonEntropy_map_eq_of_bij (UnifN.prod Pn) _ _
      ⟨fun u => (u.1, (u.2.1, u.2.2)), fun _ => rfl⟩
      ⟨fun s => (s.1, s.2.1, s.2.2), fun _ => rfl⟩
  have hH_ZU1U2 : shannonEntropy (Qraw.map (fun t => ((t.1, t.2.1), t.2.2.1, t.2.2.2))) =
      shannonEntropy ((UnifN.prod Pn).map (fun qz => (qz.1, (qz.2 qz.1, (enc₁ (xs qz.2), enc₂ (ys qz.2)), maskPrefix qz.1.1 qz.2)))) := by
    unfold Qraw; rw [map_comp_eq]
    exact bt_shannonEntropy_map_eq_of_bij (UnifN.prod Pn) _ _
      ⟨fun p => (p.2.1.1, (p.1, (p.2.1.2.1, p.2.2.2.1), p.2.1.2.2)), fun _ => rfl⟩
      ⟨fun s => (s.2.1, (s.1, s.2.2.1.1, s.2.2.2), (s.1, s.2.2.1.2, s.2.2.2)), fun _ => rfl⟩
  have hH_U1U2 : shannonEntropy (Qraw.map (fun t => (t.2.2.1, t.2.2.2))) =
      shannonEntropy ((UnifN.prod Pn).map (fun qz => (qz.1, ((enc₁ (xs qz.2), enc₂ (ys qz.2)), maskPrefix qz.1.1 qz.2)))) := by
    unfold Qraw; rw [map_comp_eq]
    exact bt_shannonEntropy_map_eq_of_bij (UnifN.prod Pn) _ _
      ⟨fun p => (p.1.1, ((p.1.2.1, p.2.2.1), p.1.2.2)), fun _ => rfl⟩
      ⟨fun s => ((s.1, s.2.1.1, s.2.2), (s.1, s.2.1.2, s.2.2)), fun _ => rfl⟩
  -- Rate 1 bound: `I(X₁, X₂; U₁ | U₂) = (1/n) H(M₁ | M₂) ≤ log₂ M₁ / n`.
  have hrate1 : condMutualInfo (Q.map (fun t => ((t.1, t.2.1), t.2.2.1, t.2.2.2))) ≤
      log2 (M₁ : ℝ) / (n : ℝ) := by
    have hQeq : condMutualInfo (Q.map (fun t => ((t.1, t.2.1), t.2.2.1, t.2.2.2))) =
        condMutualInfo (Qraw.map (fun t => ((t.1, t.2.1), t.2.2.1, t.2.2.2))) := by
      have h1 : Q.map (fun t => ((t.1, t.2.1), t.2.2.1, t.2.2.2)) =
          ((Qraw.map (fun t => ((t.1, t.2.1), t.2.2.1, t.2.2.2))).map (fun s => (s.1, e₁ s.2.1, s.2.2))).map
            (fun s => (s.1, s.2.1, e₂ s.2.2)) := by
        dsimp only [Q]
        rw [map_comp_eq Qraw, map_comp_eq (Qraw.map _), map_comp_eq Qraw]
        rfl
      rw [h1, bt_condMutualInfo_map_thd_equiv, bt_condMutualInfo_map_snd_equiv]
    rw [hQeq]
    unfold condMutualInfo; dsimp only; simp_rw [map_comp_eq]
    change shannonEntropy (Qraw.map (fun t => ((t.1, t.2.1), t.2.2.2))) +
        shannonEntropy (Qraw.map (fun t => (t.2.2.1, t.2.2.2))) -
        shannonEntropy (Qraw.map (fun t => ((t.1, t.2.1), t.2.2.1, t.2.2.2))) -
        shannonEntropy (Qraw.map (fun t => t.2.2.2)) ≤ _
    rw [hH_ZU2, hH_U2, hH_ZU1U2, hH_U1U2]
    have ht2 := htelescope_diff (fun z => enc₂ (ys z))
    have ht12 := htelescope_diff (fun z => (enc₁ (xs z), enc₂ (ys z)))
    have hce : shannonEntropy D_M1M2 - shannonEntropy D_M1M2.snd ≤ log2 (M₁ : ℝ) := by
      have h1 : condEntropy D_M1M2 ≤ shannonEntropy D_M1M2.fst := condEntropy_le_shannonEntropy D_M1M2
      rw [hM1M2_fst] at h1
      unfold condEntropy at h1
      linarith
    rw [hM1M2_snd] at hce
    have hdiv : (1 / (n : ℝ)) * (shannonEntropy D_M1M2 - shannonEntropy (Pn.map (fun z => enc₂ (ys z)))) ≤
        log2 (M₁ : ℝ) / (n : ℝ) := by
      rw [one_div_mul_eq_div]
      exact div_le_div_of_nonneg_right hce (le_of_lt hn_pos)
    dsimp only [D_M1M2] at hdiv
    linarith
  -- Rate 2 bound: `I(X₁, X₂; U₂ | U₁) = (1/n) H(M₂ | M₁) ≤ log₂ M₂ / n`.
  have hrate2 : condMutualInfo (Q.map (fun t => ((t.1, t.2.1), t.2.2.2, t.2.2.1))) ≤
      log2 (M₂ : ℝ) / (n : ℝ) := by
    have hQeq : condMutualInfo (Q.map (fun t => ((t.1, t.2.1), t.2.2.2, t.2.2.1))) =
        condMutualInfo (Qraw.map (fun t => ((t.1, t.2.1), t.2.2.2, t.2.2.1))) := by
      have h1 : Q.map (fun t => ((t.1, t.2.1), t.2.2.2, t.2.2.1)) =
          ((Qraw.map (fun t => ((t.1, t.2.1), t.2.2.2, t.2.2.1))).map (fun s => (s.1, e₂ s.2.1, s.2.2))).map
            (fun s => (s.1, s.2.1, e₁ s.2.2)) := by
        dsimp only [Q]
        rw [map_comp_eq Qraw, map_comp_eq (Qraw.map _), map_comp_eq Qraw]
        rfl
      rw [h1, bt_condMutualInfo_map_thd_equiv, bt_condMutualInfo_map_snd_equiv]
    rw [hQeq]
    unfold condMutualInfo; dsimp only; simp_rw [map_comp_eq]
    have hU2U1 : shannonEntropy (Qraw.map ((fun t : (X₁ × X₂) × U2raw × U1raw => (t.2.1, t.2.2)) ∘
        fun t : X₁ × X₂ × U1raw × U2raw => ((t.1, t.2.1), t.2.2.2, t.2.2.1))) =
        shannonEntropy (Qraw.map (fun t => (t.2.2.1, t.2.2.2))) :=
      bt_shannonEntropy_map_eq_of_bij Qraw _ _
        ⟨Prod.swap, fun _ => rfl⟩ ⟨Prod.swap, fun _ => rfl⟩
    have hZU2U1 : shannonEntropy (Qraw.map (fun t => ((t.1, t.2.1), t.2.2.2, t.2.2.1))) =
        shannonEntropy (Qraw.map (fun t => ((t.1, t.2.1), t.2.2.1, t.2.2.2))) :=
      bt_shannonEntropy_map_eq_of_bij Qraw _ _
        ⟨fun s => (s.1, s.2.2, s.2.1), fun _ => rfl⟩
        ⟨fun s => (s.1, s.2.2, s.2.1), fun _ => rfl⟩
    rw [hU2U1, hZU2U1]
    change shannonEntropy (Qraw.map (fun t => ((t.1, t.2.1), t.2.2.1))) +
        shannonEntropy (Qraw.map (fun t => (t.2.2.1, t.2.2.2))) -
        shannonEntropy (Qraw.map (fun t => ((t.1, t.2.1), t.2.2.1, t.2.2.2))) -
        shannonEntropy (Qraw.map (fun t => t.2.2.1)) ≤ _
    rw [hH_ZU1, hH_U1, hH_ZU1U2, hH_U1U2]
    have ht1 := htelescope_diff (fun z => enc₁ (xs z))
    have ht12 := htelescope_diff (fun z => (enc₁ (xs z), enc₂ (ys z)))
    have hce : shannonEntropy D_M1M2 - shannonEntropy D_M1M2.fst ≤ log2 (M₂ : ℝ) := by
      have h1 : condEntropy (D_M1M2.map Prod.swap) ≤ shannonEntropy (D_M1M2.map Prod.swap).fst :=
        condEntropy_le_shannonEntropy _
      have hsw_ent : shannonEntropy (D_M1M2.map Prod.swap) = shannonEntropy D_M1M2 :=
        shannonEntropy_map_equiv (Equiv.prodComm _ _) D_M1M2
      have hsw_fst : (D_M1M2.map Prod.swap).fst = D_M1M2.snd := by
        rw [← bt_probDist_map_fst, ← bt_probDist_map_snd, map_comp_eq]; rfl
      have hsw_snd : (D_M1M2.map Prod.swap).snd = D_M1M2.fst := by
        rw [← bt_probDist_map_snd, ← bt_probDist_map_fst, map_comp_eq]; rfl
      unfold condEntropy at h1
      rw [hsw_ent, hsw_fst, hsw_snd, hM1M2_snd] at h1
      linarith
    rw [hM1M2_fst] at hce
    have hdiv : (1 / (n : ℝ)) * (shannonEntropy D_M1M2 - shannonEntropy (Pn.map (fun z => enc₁ (xs z)))) ≤
        log2 (M₂ : ℝ) / (n : ℝ) := by
      rw [one_div_mul_eq_div]
      exact div_le_div_of_nonneg_right hce (le_of_lt hn_pos)
    dsimp only [D_M1M2] at hdiv
    linarith
  -- Sum-rate bound: `I(X₁, X₂; U₁, U₂) = (1/n) H(M₁, M₂) ≤ (log₂ M₁ + log₂ M₂) / n`.
  have hrate12 : mutualInfo (Q.map (fun t => ((t.1, t.2.1), (t.2.2.1, t.2.2.2)))) ≤
      log2 (M₁ : ℝ) / (n : ℝ) + log2 (M₂ : ℝ) / (n : ℝ) := by
    unfold mutualInfo
    have hfst : (Q.map (fun t => ((t.1, t.2.1), (t.2.2.1, t.2.2.2)))).fst = P := by
      rw [← bt_probDist_map_fst, map_comp_eq]; exact hQ_marg
    have hsnd : shannonEntropy (Q.map (fun t => ((t.1, t.2.1), (t.2.2.1, t.2.2.2)))).snd =
        shannonEntropy (Qraw.map (fun t => (t.2.2.1, t.2.2.2))) := by
      rw [← bt_probDist_map_snd]; unfold Q; rw [map_comp_eq, map_comp_eq]
      exact bt_shannonEntropy_map_eq_of_bij Qraw _ _
        ⟨fun p => (e₁.symm p.1, e₂.symm p.2), fun t => by simp⟩
        ⟨fun p => (e₁ p.1, e₂ p.2), fun _ => rfl⟩
    have hall : shannonEntropy (Q.map (fun t => ((t.1, t.2.1), (t.2.2.1, t.2.2.2)))) =
        shannonEntropy (Qraw.map (fun t => ((t.1, t.2.1), t.2.2.1, t.2.2.2))) := by
      unfold Q; rw [map_comp_eq]
      exact bt_shannonEntropy_map_eq_of_bij Qraw _ _
        ⟨fun s => (s.1, e₁.symm s.2.1, e₂.symm s.2.2), fun t => by simp⟩
        ⟨fun s => (s.1, (e₁ s.2.1, e₂ s.2.2)), fun _ => rfl⟩
    rw [hfst, hsnd, hall, hH_ZU1U2, hH_U1U2]
    have ht12 := htelescope_diff (fun z => (enc₁ (xs z), enc₂ (ys z)))
    have hsub : shannonEntropy D_M1M2 ≤ log2 (M₁ : ℝ) + log2 (M₂ : ℝ) := by
      have hmi := mutualInfo_nonneg D_M1M2
      unfold mutualInfo at hmi
      rw [hM1M2_fst, hM1M2_snd] at hmi
      linarith
    have hdiv : (1 / (n : ℝ)) * shannonEntropy D_M1M2 ≤
        log2 (M₁ : ℝ) / (n : ℝ) + log2 (M₂ : ℝ) / (n : ℝ) := by
      rw [one_div_mul_eq_div, ← add_div]
      exact div_le_div_of_nonneg_right hsub (le_of_lt hn_pos)
    dsimp only [D_M1M2] at hdiv
    linarith
  exact ⟨hlog1_nn, hlog2_nn, kU₁, kU₂, Q, g₁, g₂, hQ_marg, hQ_mk1, hQ_mk2,
    hQ_dist₁, hQ_dist₂, hrate1, hrate2, hrate12⟩

/-- **Operational Berger–Tung Outer Bound Converse** (Berger 1978; Tung 1978;
    El Gamal & Kim §12.1.3):
    every operationally achievable 4-tuple `(R₁, R₂, D₁, D₂)` satisfies
    `(R₁ + ε, R₂ + ε) ∈ bergerTungOuterBound P d₁ d₂ (D₁ + ε) (D₂ + ε)` for every `ε > 0`. -/
theorem bergerTung_outer_converse
    (P : ProbDist (X₁ × X₂)) (d₁ : Distortion X₁ Xh₁) (d₂ : Distortion X₂ Xh₂)
    {R₁ R₂ D₁ D₂ : ℝ}
    (h : IsBergerTungAchievable P d₁ d₂ R₁ R₂ D₁ D₂) :
    0 ≤ R₁ ∧ 0 ≤ R₂ ∧
    ∀ ε > 0, (R₁ + ε, R₂ + ε) ∈ bergerTungOuterBound P d₁ d₂ (D₁ + ε) (D₂ + ε) := by
  rcases h with ⟨hR₁, hR₂, hach⟩
  refine ⟨hR₁, hR₂, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hach ε hε
  let n := max N 1
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_max_right N 1)
  obtain ⟨enc₁, enc₂, dec₁, dec₂, hd₁, hd₂⟩ := hN n (le_max_left N 1)
  let M₁ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * (R₁ + ε))))
  let M₂ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * (R₂ + ε))))
  have hM₁ : 0 < M₁ := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
  have hM₂ : 0 < M₂ := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
  have hblk := bergerTung_outer_converse_block P d₁ d₂ hn hM₁ hM₂ enc₁ enc₂ dec₁ dec₂ hd₁ hd₂
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have h1 : log2 (M₁ : ℝ) / (n : ℝ) ≤ R₁ + ε := by
    rw [div_le_iff₀ hn_pos]
    calc log2 (M₁ : ℝ)
      _ ≤ log2 ((2 : ℝ) ^ ((n : ℝ) * (R₁ + ε))) :=
          bt_log2_mono_le (Nat.cast_pos.mpr hM₁) (bt_max_one_floor_two_rpow_le n (by linarith))
      _ = (n : ℝ) * (R₁ + ε) := bt_log2_two_rpow_eq _
      _ = (R₁ + ε) * (n : ℝ) := mul_comm _ _
  have h2 : log2 (M₂ : ℝ) / (n : ℝ) ≤ R₂ + ε := by
    rw [div_le_iff₀ hn_pos]
    calc log2 (M₂ : ℝ)
      _ ≤ log2 ((2 : ℝ) ^ ((n : ℝ) * (R₂ + ε))) :=
          bt_log2_mono_le (Nat.cast_pos.mpr hM₂) (bt_max_one_floor_two_rpow_le n (by linarith))
      _ = (n : ℝ) * (R₂ + ε) := bt_log2_two_rpow_eq _
      _ = (R₂ + ε) * (n : ℝ) := mul_comm _ _
  exact bergerTungOuterBound_mono hblk h1 h2 le_rfl le_rfl

end BergerTungConverse

/-! ### 3. Two-Encoder (Permutation-Orbit) Markov Lemma
(El Gamal & Kim Lemma 12.1; Berger 1978; Tung 1978) -/

section TwoEncoderMarkovLemma

variable {X₁ X₂ U₁ U₂ : Type*}

/-- Finset of permutations `π` of `Fin n` preserving every fiber of `x₂ : Fin n → X₂`. -/
def fiberPermSet [DecidableEq X₂] {n : ℕ} (x₂ : Fin n → X₂) :
    Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter fun π => ∀ i : Fin n, x₂ (π i) = x₂ i

private lemma mem_fiberPermSet [DecidableEq X₂] {n : ℕ} {x₂ : Fin n → X₂}
    {π : Equiv.Perm (Fin n)} :
    π ∈ fiberPermSet x₂ ↔ ∀ i : Fin n, x₂ (π i) = x₂ i := by
  simp [fiberPermSet]

private lemma one_mem_fiberPermSet [DecidableEq X₂] {n : ℕ} (x₂ : Fin n → X₂) :
    (1 : Equiv.Perm (Fin n)) ∈ fiberPermSet x₂ := by
  simp [mem_fiberPermSet]

private lemma fiberPermSet_card_pos [DecidableEq X₂] {n : ℕ} (x₂ : Fin n → X₂) :
    0 < (fiberPermSet x₂).card :=
  Finset.card_pos.mpr ⟨1, one_mem_fiberPermSet x₂⟩

private lemma mul_mem_fiberPermSet [DecidableEq X₂] {n : ℕ} {x₂ : Fin n → X₂}
    {σ π : Equiv.Perm (Fin n)} (hσ : σ ∈ fiberPermSet x₂) (hπ : π ∈ fiberPermSet x₂) :
    σ * π ∈ fiberPermSet x₂ := by
  rw [mem_fiberPermSet] at hσ hπ ⊢
  intro i; simp [hσ (π i), hπ i]

private lemma inv_mem_fiberPermSet [DecidableEq X₂] {n : ℕ} {x₂ : Fin n → X₂}
    {σ : Equiv.Perm (Fin n)} (hσ : σ ∈ fiberPermSet x₂) :
    σ⁻¹ ∈ fiberPermSet x₂ := by
  rw [mem_fiberPermSet] at hσ ⊢
  intro i
  have h := hσ (σ⁻¹ i)
  have hinv : σ (σ⁻¹ i) = i := Equiv.apply_symm_apply σ i
  rw [hinv] at h
  exact h.symm

private lemma swap_mem_fiberPermSet [DecidableEq X₂] {n : ℕ} {x₂ : Fin n → X₂}
    {j₁ j₂ : Fin n} (h : x₂ j₁ = x₂ j₂) :
    Equiv.swap j₁ j₂ ∈ fiberPermSet x₂ := by
  rw [mem_fiberPermSet]
  intro i
  by_cases hi1 : i = j₁
  · subst hi1; simp [h]
  · by_cases hi2 : i = j₂
    · subst hi2; simp [h]
    · simp [Equiv.swap_apply_of_ne_of_ne hi1 hi2]

/-- 1-transitivity on a fiber `I_b = {k | x₂ k = b}`:
    for `i, j ∈ I_b`, `|{π ∈ G | π i = j}| * |I_b| = |G|`. -/
private lemma fiberPermSet_card_apply_eq [DecidableEq X₂] {n : ℕ} (x₂ : Fin n → X₂)
    (b : X₂) {i j : Fin n} (hi : x₂ i = b) (hj : x₂ j = b) :
    let G := fiberPermSet x₂
    let Ib := Finset.univ.filter fun k : Fin n => x₂ k = b
    ((G.filter fun π => π i = j).card : ℝ) * (Ib.card : ℝ) = (G.card : ℝ) := by
  classical
  dsimp only
  let G := fiberPermSet x₂
  let Ib := Finset.univ.filter fun k : Fin n => x₂ k = b
  -- Every `j' ∈ Ib` has the same fiber count via left-multiplication by `Equiv.swap j j'`.
  have heq_card : ∀ j' ∈ Ib, (G.filter fun π => π i = j').card = (G.filter fun π => π i = j).card := by
    intro j' hj'
    have hj'_eq : x₂ j' = b := (Finset.mem_filter.mp hj').2
    let σ := Equiv.swap j j'
    have hσ : σ ∈ G := swap_mem_fiberPermSet (hj.trans hj'_eq.symm)
    refine Finset.card_bij (fun π _ => σ * π) ?_ ?_ ?_
    · intro π hπ
      rcases Finset.mem_filter.mp hπ with ⟨hπG, hπi⟩
      refine Finset.mem_filter.mpr ⟨mul_mem_fiberPermSet hσ hπG, ?_⟩
      simp [σ, hπi]
    · intro π₁ _ π₂ _ h
      exact mul_left_cancel h
    · intro π hπ
      rcases Finset.mem_filter.mp hπ with ⟨hπG, hπi⟩
      refine ⟨σ * π, Finset.mem_filter.mpr ⟨mul_mem_fiberPermSet hσ hπG, ?_⟩, ?_⟩
      · simp [σ, hπi]
      · simp [σ, ← mul_assoc]
  have hpart : (G.card : ℕ) = ∑ j' ∈ Ib, (G.filter fun π => π i = j').card := by
    have h1 : G.card = ∑ j' ∈ Ib, (G.filter fun π => π i = j').card := by
      rw [← Finset.card_biUnion]
      · congr 1; ext π
        simp only [Finset.mem_biUnion, Finset.mem_filter, Ib, Finset.mem_univ, true_and]
        constructor
        · intro hπ
          refine ⟨π i, ?_, hπ, rfl⟩
          exact (mem_fiberPermSet.mp hπ i).trans hi
        · rintro ⟨_, _, hπ, _⟩; exact hπ
      · intro a _ c _ hac
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro π h1 h2
        exact hac ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    exact h1
  have hnat : (G.filter fun π => π i = j).card * Ib.card = G.card := by
    rw [hpart, Finset.sum_congr rfl heq_card, Finset.sum_const, smul_eq_mul, mul_comm]
  exact_mod_cast hnat

/-- First moment of indicator `1_{π i ∈ R}` over uniform `π ∈ fiberPermSet x₂`. -/
private lemma fiberPermSet_sum_mem [DecidableEq X₂] {n : ℕ} (x₂ : Fin n → X₂)
    (b : X₂) {i : Fin n} (hi : x₂ i = b) (R : Finset (Fin n))
    (hR : R ⊆ Finset.univ.filter fun k : Fin n => x₂ k = b) :
    let G := fiberPermSet x₂
    let Ib := Finset.univ.filter fun k : Fin n => x₂ k = b
    ∑ π ∈ G, (if π i ∈ R then (1 : ℝ) else 0) =
      (G.card : ℝ) * ((R.card : ℝ) / (Ib.card : ℝ)) := by
  classical
  dsimp only
  let G := fiberPermSet x₂
  let Ib := Finset.univ.filter fun k : Fin n => x₂ k = b
  have hIb_pos : (0 : ℝ) < (Ib.card : ℝ) :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩)
  have hind : ∀ π ∈ G, (if π i ∈ R then (1 : ℝ) else 0) =
      ∑ j ∈ R, if π i = j then (1 : ℝ) else 0 := fun π _ => by
    by_cases h : π i ∈ R
    · simp only [h, ↓reduceIte]
      rw [Finset.sum_eq_single (π i)]
      · simp
      · intro j _ hne; simp [hne.symm]
      · intro hn; exact absurd h hn
    · simp only [h, ↓reduceIte]
      exact (Finset.sum_eq_zero fun j hj => by
        have hne : π i ≠ j := fun heq => h (heq ▸ hj)
        simp [hne]).symm
  rw [Finset.sum_congr rfl hind, Finset.sum_comm]
  have heach : ∀ j ∈ R, (∑ π ∈ G, if π i = j then (1 : ℝ) else 0) =
      (G.card : ℝ) / (Ib.card : ℝ) := by
    intro j hj
    have hj_b : x₂ j = b := (Finset.mem_filter.mp (hR hj)).2
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hmul := fiberPermSet_card_apply_eq x₂ b hi hj_b
    exact eq_div_of_mul_eq (ne_of_gt hIb_pos) hmul
  rw [Finset.sum_congr rfl heach, Finset.sum_const, nsmul_eq_mul]
  ring

/-- 2-transitivity on a fiber `I_b`:
    for distinct `i₁ ≠ i₂` in `I_b` and distinct `j₁ ≠ j₂` in `I_b`,
    `|{π ∈ G | π i₁ = j₁ ∧ π i₂ = j₂}| * |I_b| * (|I_b| - 1) = |G|`. -/
private lemma fiberPermSet_card_apply_pair_eq [DecidableEq X₂] {n : ℕ} (x₂ : Fin n → X₂)
    (b : X₂) {i₁ i₂ j₁ j₂ : Fin n}
    (hi₁ : x₂ i₁ = b) (hi₂ : x₂ i₂ = b) (hi_ne : i₁ ≠ i₂)
    (hj₁ : x₂ j₁ = b) (hj₂ : x₂ j₂ = b) (hj_ne : j₁ ≠ j₂) :
    let G := fiberPermSet x₂
    let Ib := Finset.univ.filter fun k : Fin n => x₂ k = b
    ((G.filter fun π => π i₁ = j₁ ∧ π i₂ = j₂).card : ℝ) *
      ((Ib.card : ℝ) * ((Ib.card : ℝ) - 1)) = (G.card : ℝ) := by
  classical
  dsimp only
  let G := fiberPermSet x₂
  let Ib := Finset.univ.filter fun k : Fin n => x₂ k = b
  have heq_card : ∀ p ∈ Ib.offDiag,
      (G.filter fun π => π i₁ = p.1 ∧ π i₂ = p.2).card =
        (G.filter fun π => π i₁ = j₁ ∧ π i₂ = j₂).card := by
    rintro ⟨j₁', j₂'⟩ hp
    rcases Finset.mem_offDiag.mp hp with ⟨hj1', hj2', hne'⟩
    have hj1'_eq : x₂ j₁' = b := (Finset.mem_filter.mp hj1').2
    have hj2'_eq : x₂ j₂' = b := (Finset.mem_filter.mp hj2').2
    -- Construct `σ ∈ G` sending `j₁' ↦ j₁` and `j₂' ↦ j₂` as a product of two swaps.
    let τ₁ := Equiv.swap j₁' j₁
    have hτ₁ : τ₁ ∈ G := swap_mem_fiberPermSet (hj1'_eq.trans hj₁.symm)
    let k := τ₁ j₂'
    have hk_ne : k ≠ j₁ := by
      intro hk
      have h1 : τ₁ j₂' = τ₁ j₁' := by simp [k, hk, τ₁]
      exact hne' (τ₁.injective h1).symm
    have hk_eq : x₂ k = b := (mem_fiberPermSet.mp hτ₁ j₂').trans hj2'_eq
    let τ₂ := Equiv.swap k j₂
    have hτ₂ : τ₂ ∈ G := swap_mem_fiberPermSet (hk_eq.trans hj₂.symm)
    let σ := τ₂ * τ₁
    have hσ : σ ∈ G := mul_mem_fiberPermSet hτ₂ hτ₁
    have hσ1 : σ j₁' = j₁ := by
      change τ₂ (τ₁ j₁') = j₁
      have h1 : τ₁ j₁' = j₁ := Equiv.swap_apply_left j₁' j₁
      rw [h1]
      exact Equiv.swap_apply_of_ne_of_ne hk_ne.symm hj_ne
    have hσ2 : σ j₂' = j₂ := by
      change τ₂ (τ₁ j₂') = j₂
      exact Equiv.swap_apply_left k j₂
    have hσinv1 : σ⁻¹ j₁ = j₁' := (Equiv.Perm.inv_eq_iff_eq.mpr hσ1.symm)
    have hσinv2 : σ⁻¹ j₂ = j₂' := (Equiv.Perm.inv_eq_iff_eq.mpr hσ2.symm)
    refine Finset.card_bij (fun π _ => σ * π) ?_ ?_ ?_
    · intro π hπ
      rcases Finset.mem_filter.mp hπ with ⟨hπG, hπ1, hπ2⟩
      refine Finset.mem_filter.mpr ⟨mul_mem_fiberPermSet hσ hπG, ?_, ?_⟩
      · simp [hπ1, hσ1]
      · simp [hπ2, hσ2]
    · intro π₁ _ π₂ _ h; exact mul_left_cancel h
    · intro π hπ
      rcases Finset.mem_filter.mp hπ with ⟨hπG, hπ1, hπ2⟩
      refine ⟨σ⁻¹ * π, Finset.mem_filter.mpr ⟨mul_mem_fiberPermSet (inv_mem_fiberPermSet hσ) hπG, ?_, ?_⟩, ?_⟩
      · change σ⁻¹ (π i₁) = j₁'; rw [hπ1, hσinv1]
      · change σ⁻¹ (π i₂) = j₂'; rw [hπ2, hσinv2]
      · simp [← mul_assoc]
  have hpart : G.card = ∑ p ∈ Ib.offDiag, (G.filter fun π => π i₁ = p.1 ∧ π i₂ = p.2).card := by
    rw [← Finset.card_biUnion]
    · congr 1; ext π
      simp only [Finset.mem_biUnion, Finset.mem_offDiag, Finset.mem_filter, Ib,
        Finset.mem_univ, true_and]
      constructor
      · intro hπ
        refine ⟨(π i₁, π i₂), ⟨(mem_fiberPermSet.mp hπ i₁).trans hi₁,
          (mem_fiberPermSet.mp hπ i₂).trans hi₂, fun h => hi_ne (π.injective h)⟩, hπ, rfl, rfl⟩
      · rintro ⟨_, _, hπ, _, _⟩; exact hπ
    · intro p _ q _ hpq
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro π h1 h2
      rcases Finset.mem_filter.mp h1 with ⟨_, h11, h12⟩
      rcases Finset.mem_filter.mp h2 with ⟨_, h21, h22⟩
      exact hpq (Prod.ext (h11.symm.trans h21) (h12.symm.trans h22))
  have hnat : (G.filter fun π => π i₁ = j₁ ∧ π i₂ = j₂).card * Ib.offDiag.card = G.card := by
    rw [hpart, Finset.sum_congr rfl heq_card, Finset.sum_const, smul_eq_mul, mul_comm]
  have hoff : (Ib.offDiag.card : ℝ) = (Ib.card : ℝ) * ((Ib.card : ℝ) - 1) := by
    rw [Finset.offDiag_card]
    have h1 : Ib.card ≤ Ib.card * Ib.card := Nat.le_mul_self Ib.card
    rw [Nat.cast_sub h1, Nat.cast_mul]; ring
  have hcast : ((G.filter fun π => π i₁ = j₁ ∧ π i₂ = j₂).card : ℝ) * (Ib.offDiag.card : ℝ) = (G.card : ℝ) := by
    exact_mod_cast hnat
  rw [← hoff]; exact hcast

/-- Negative correlation for pairs in hypergeometric sampling on `fiberPermSet x₂`:
    for distinct `i₁ ≠ i₂` in `I_b` and `R ⊆ I_b`,
    `E_{π ∈ G}[1_{π i₁ ∈ R ∧ π i₂ ∈ R}] ≤ (|R| / |I_b|)²`. -/
private lemma fiberPermSet_sum_mem_pair_le [DecidableEq X₂] {n : ℕ} (x₂ : Fin n → X₂)
    (b : X₂) {i₁ i₂ : Fin n} (hi₁ : x₂ i₁ = b) (hi₂ : x₂ i₂ = b) (hi_ne : i₁ ≠ i₂)
    (R : Finset (Fin n)) (hR : R ⊆ Finset.univ.filter fun k : Fin n => x₂ k = b) :
    let G := fiberPermSet x₂
    let Ib := Finset.univ.filter fun k : Fin n => x₂ k = b
    ∑ π ∈ G, (if π i₁ ∈ R ∧ π i₂ ∈ R then (1 : ℝ) else 0) ≤
      (G.card : ℝ) * ((R.card : ℝ) / (Ib.card : ℝ)) ^ 2 := by
  classical
  dsimp only
  let G := fiberPermSet x₂
  let Ib := Finset.univ.filter fun k : Fin n => x₂ k = b
  have hIb_ge2 : 2 ≤ Ib.card := by
    have hsub : ({i₁, i₂} : Finset (Fin n)) ⊆ Ib := by
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk2
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi₁⟩
      · rw [Finset.mem_singleton.mp hk2]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi₂⟩
    have h2 : ({i₁, i₂} : Finset (Fin n)).card = 2 := Finset.card_pair hi_ne
    linarith [Finset.card_le_card hsub]
  have hIb_pos : (0 : ℝ) < (Ib.card : ℝ) := by exact_mod_cast (by omega : 0 < Ib.card)
  have hIb_sub1_pos : (0 : ℝ) < (Ib.card : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (Ib.card : ℝ) := by exact_mod_cast hIb_ge2
    linarith
  have hden_pos : (0 : ℝ) < (Ib.card : ℝ) * ((Ib.card : ℝ) - 1) := mul_pos hIb_pos hIb_sub1_pos
  have hind : ∀ π ∈ G, (if π i₁ ∈ R ∧ π i₂ ∈ R then (1 : ℝ) else 0) =
      ∑ p ∈ R.offDiag, if π i₁ = p.1 ∧ π i₂ = p.2 then (1 : ℝ) else 0 := by
    intro π _
    have hne_pi : π i₁ ≠ π i₂ := fun h => hi_ne (π.injective h)
    by_cases h : π i₁ ∈ R ∧ π i₂ ∈ R
    · simp only [h]
      have hmem : (π i₁, π i₂) ∈ R.offDiag := Finset.mem_offDiag.mpr ⟨h.1, h.2, hne_pi⟩
      rw [Finset.sum_eq_single (π i₁, π i₂)]
      · simp
      · intro p _ hne_p
        have hnot : ¬ (π i₁ = p.1 ∧ π i₂ = p.2) := fun ⟨h1, h2⟩ => hne_p (Prod.ext h1.symm h2.symm)
        simp [hnot]
      · intro hn; exact absurd hmem hn
    · simp only [h]
      exact (Finset.sum_eq_zero fun p hp => by
        rcases Finset.mem_offDiag.mp hp with ⟨hp1, hp2, _⟩
        have hnot : ¬ (π i₁ = p.1 ∧ π i₂ = p.2) := fun ⟨h1, h2⟩ => h ⟨h1 ▸ hp1, h2 ▸ hp2⟩
        simp [hnot]).symm
  rw [Finset.sum_congr rfl hind, Finset.sum_comm]
  have heach : ∀ p ∈ R.offDiag, (∑ π ∈ G, if π i₁ = p.1 ∧ π i₂ = p.2 then (1 : ℝ) else 0) =
      (G.card : ℝ) / ((Ib.card : ℝ) * ((Ib.card : ℝ) - 1)) := by
    rintro ⟨j₁, j₂⟩ hp
    rcases Finset.mem_offDiag.mp hp with ⟨hj1, hj2, hj_ne⟩
    have hj1_b : x₂ j₁ = b := (Finset.mem_filter.mp (hR hj1)).2
    have hj2_b : x₂ j₂ = b := (Finset.mem_filter.mp (hR hj2)).2
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact eq_div_of_mul_eq (ne_of_gt hden_pos)
      (fiberPermSet_card_apply_pair_eq x₂ b hi₁ hi₂ hi_ne hj1_b hj2_b hj_ne)
  rw [Finset.sum_congr rfl heach, Finset.sum_const, nsmul_eq_mul]
  have hRoff : (R.offDiag.card : ℝ) = (R.card : ℝ) * ((R.card : ℝ) - 1) := by
    rw [Finset.offDiag_card]
    have h1 : R.card ≤ R.card * R.card := Nat.le_mul_self R.card
    rw [Nat.cast_sub h1, Nat.cast_mul]; ring
  rw [hRoff]
  have hR_le : (R.card : ℝ) ≤ (Ib.card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hR)
  have hR_nn : (0 : ℝ) ≤ (R.card : ℝ) := Nat.cast_nonneg _
  have hG_nn : (0 : ℝ) ≤ (G.card : ℝ) := Nat.cast_nonneg _
  -- `(K * (K - 1)) / (N * (N - 1)) ≤ (K / N)^2` since `K ≤ N` and `N ≥ 2`.
  have hratio : ((R.card : ℝ) * ((R.card : ℝ) - 1)) / ((Ib.card : ℝ) * ((Ib.card : ℝ) - 1)) ≤
      ((R.card : ℝ) / (Ib.card : ℝ)) ^ 2 := by
    rw [div_pow, div_le_div_iff₀ hden_pos (pow_pos hIb_pos 2)]
    have hdiff : (R.card : ℝ) * ((R.card : ℝ) - 1) * (Ib.card : ℝ) ^ 2 -
        (R.card : ℝ) ^ 2 * ((Ib.card : ℝ) * ((Ib.card : ℝ) - 1)) =
        ((R.card : ℝ) * (Ib.card : ℝ)) * ((R.card : ℝ) - (Ib.card : ℝ)) := by ring
    have hprod_nn : 0 ≤ (R.card : ℝ) * (Ib.card : ℝ) := mul_nonneg hR_nn (le_of_lt hIb_pos)
    have hnonpos : ((R.card : ℝ) * (Ib.card : ℝ)) * ((R.card : ℝ) - (Ib.card : ℝ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hprod_nn (by linarith)
    linarith
  have hrew : (R.card : ℝ) * ((R.card : ℝ) - 1) * ((G.card : ℝ) / ((Ib.card : ℝ) * ((Ib.card : ℝ) - 1))) =
      (G.card : ℝ) * (((R.card : ℝ) * ((R.card : ℝ) - 1)) / ((Ib.card : ℝ) * ((Ib.card : ℝ) - 1))) := by
    ring
  rw [hrew]
  exact mul_le_mul_of_nonneg_left hratio hG_nn

/-- Hypergeometric variance bound on `fiberPermSet x₂`:
    `∑ π ∈ G, (∑ i ∈ S, (1_{π i ∈ R} - |R|/|I_b|))² ≤ |G| * |S|`. -/
private lemma fiberPermSet_var_le [DecidableEq X₂] {n : ℕ} (x₂ : Fin n → X₂)
    (b : X₂) (S R : Finset (Fin n))
    (hS : S ⊆ Finset.univ.filter fun k : Fin n => x₂ k = b)
    (hR : R ⊆ Finset.univ.filter fun k : Fin n => x₂ k = b) :
    let G := fiberPermSet x₂
    let Ib := Finset.univ.filter fun k : Fin n => x₂ k = b
    let p : ℝ := (R.card : ℝ) / (Ib.card : ℝ)
    ∑ π ∈ G, (∑ i ∈ S, ((if π i ∈ R then (1 : ℝ) else 0) - p)) ^ 2 ≤
      (G.card : ℝ) * (S.card : ℝ) := by
  classical
  dsimp only
  let G := fiberPermSet x₂
  let Ib := Finset.univ.filter fun k : Fin n => x₂ k = b
  let p : ℝ := (R.card : ℝ) / (Ib.card : ℝ)
  let Z : Fin n → Equiv.Perm (Fin n) → ℝ := fun i π => (if π i ∈ R then (1 : ℝ) else 0) - p
  have hsq : ∀ π ∈ G, (∑ i ∈ S, Z i π) ^ 2 =
      ∑ i ∈ S, ∑ j ∈ S, Z i π * Z j π := fun π _ => by
    rw [sq, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl hsq, Finset.sum_comm]
  trans (∑ i ∈ S, ∑ j ∈ S, ∑ π ∈ G, Z i π * Z j π)
  · exact le_of_eq (Finset.sum_congr rfl fun i _ => Finset.sum_comm)
  -- Bound diagonal `i = j` by `|G|` and off-diagonal `i ≠ j` by `0`.
  have hdiag : ∀ i ∈ S, ∑ π ∈ G, Z i π * Z i π ≤ (G.card : ℝ) := by
    intro i hi
    have hIb_pos : (0 : ℝ) < (Ib.card : ℝ) :=
      Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨i, hS hi⟩)
    have hp0 : 0 ≤ p := div_nonneg (Nat.cast_nonneg _) (le_of_lt hIb_pos)
    have hp1 : p ≤ 1 := (div_le_one hIb_pos).mpr (Nat.cast_le.mpr (Finset.card_le_card hR))
    calc ∑ π ∈ G, Z i π * Z i π
      _ ≤ ∑ _π ∈ G, (1 : ℝ) := Finset.sum_le_sum fun π _ => by
          dsimp [Z]; split_ifs <;> nlinarith
      _ = (G.card : ℝ) := by simp
  have hoff : ∀ i ∈ S, ∀ j ∈ S, j ≠ i → ∑ π ∈ G, Z i π * Z j π ≤ 0 := by
    intro i hi j hj hji
    have hi_b : x₂ i = b := (Finset.mem_filter.mp (hS hi)).2
    have hj_b : x₂ j = b := (Finset.mem_filter.mp (hS hj)).2
    have hexpand : ∀ π ∈ G, Z i π * Z j π =
        (if π i ∈ R ∧ π j ∈ R then (1 : ℝ) else 0) -
        p * (if π i ∈ R then (1 : ℝ) else 0) -
        p * (if π j ∈ R then (1 : ℝ) else 0) + p ^ 2 := fun π _ => by
      dsimp [Z]
      by_cases h1 : π i ∈ R <;> by_cases h2 : π j ∈ R <;> simp [h1, h2] <;> ring
    rw [Finset.sum_congr rfl hexpand, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h1 := fiberPermSet_sum_mem x₂ b hi_b R hR
    have h2 := fiberPermSet_sum_mem x₂ b hj_b R hR
    have h12 := fiberPermSet_sum_mem_pair_le x₂ b hi_b hj_b hji.symm R hR
    dsimp only at h1 h2 h12
    have hconst : ∑ _π ∈ G, p ^ 2 = (G.card : ℝ) * p ^ 2 := by simp
    change (∑ π ∈ G, if π i ∈ R ∧ π j ∈ R then (1 : ℝ) else 0) -
      p * (∑ π ∈ G, if π i ∈ R then (1 : ℝ) else 0) -
      p * (∑ π ∈ G, if π j ∈ R then (1 : ℝ) else 0) + ∑ _π ∈ G, p ^ 2 ≤ 0
    rw [h1, h2, hconst]
    nlinarith
  calc ∑ i ∈ S, ∑ j ∈ S, ∑ π ∈ G, Z i π * Z j π
    _ ≤ ∑ i ∈ S, (G.card : ℝ) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [← Finset.add_sum_erase S (fun j => ∑ π ∈ G, Z i π * Z j π) hi]
        have hrest : ∑ j ∈ S.erase i, ∑ π ∈ G, Z i π * Z j π ≤ 0 :=
          Finset.sum_nonpos fun j hj =>
            hoff i hi j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)
        linarith [hdiag i hi]
    _ = (G.card : ℝ) * (S.card : ℝ) := by simp [mul_comm]

/-- Helper: Markov factorization of a 4-variable distribution `Q` on `X₁ × X₂ × U₁ × U₂`
    under `U₂ — X₂ — (X₁, U₁)`. -/
private lemma bt_markov4_factorization
    [Fintype X₁] [Fintype X₂] [Fintype U₁] [Fintype U₂]
    (Q : ProbDist (X₁ × X₂ × U₁ × U₂))
    (hmk2 : condMutualInfo (Q.map (fun t => (t.2.2.2, (t.1, t.2.2.1), t.2.1))) = 0)
    (a : X₁) (b : X₂) (c₁ : U₁) (c₂ : U₂) :
    Q.pmf (a, b, c₁, c₂) * (Q.map (fun t => t.2.1)).pmf b =
      (Q.map (fun t => (t.1, t.2.1, t.2.2.1))).pmf (a, b, c₁) *
      (Q.map (fun t => (t.2.1, t.2.2.2))).pmf (b, c₂) := by
  classical
  let R : ProbDist (U₂ × (X₁ × U₁) × X₂) := Q.map (fun t => (t.2.2.2, (t.1, t.2.2.1), t.2.1))
  have hci : R = condIndepDist R := (condMutualInfo_eq_zero_iff R).mp hmk2
  have hR_pmf : R.pmf (c₂, (a, c₁), b) = Q.pmf (a, b, c₁, c₂) := by
    let e : (X₁ × X₂ × U₁ × U₂) ≃ (U₂ × (X₁ × U₁) × X₂) :=
      { toFun := fun t => (t.2.2.2, (t.1, t.2.2.1), t.2.1)
        invFun := fun s => (s.2.1.1, s.2.2, s.2.1.2, s.1)
        left_inv := fun ⟨_, _, _, _⟩ => rfl
        right_inv := fun ⟨_, ⟨_, _⟩, _⟩ => rfl }
    exact bt_probDist_map_equiv_pmf e Q (c₂, (a, c₁), b)
  have hR_xz : (R.map (fun s => (s.1, s.2.2))).pmf (c₂, b) =
      (Q.map (fun t => (t.2.1, t.2.2.2))).pmf (b, c₂) := by
    have hmap : R.map (fun s => (s.1, s.2.2)) = (Q.map (fun t => (t.2.1, t.2.2.2))).map Prod.swap := by
      unfold R; rw [map_comp_eq, map_comp_eq]; rfl
    rw [hmap]
    exact bt_probDist_map_equiv_pmf (Equiv.prodComm X₂ U₂) _ (c₂, b)
  have hR_yz : (R.map (fun s => (s.2.1, s.2.2))).pmf ((a, c₁), b) =
      (Q.map (fun t => (t.1, t.2.1, t.2.2.1))).pmf (a, b, c₁) := by
    let e : (X₁ × X₂ × U₁) ≃ ((X₁ × U₁) × X₂) :=
      { toFun := fun t => ((t.1, t.2.2), t.2.1)
        invFun := fun s => (s.1.1, s.2, s.1.2)
        left_inv := fun ⟨_, _, _⟩ => rfl
        right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
    have hmap : R.map (fun s => (s.2.1, s.2.2)) = (Q.map (fun t => (t.1, t.2.1, t.2.2.1))).map e := by
      unfold R; rw [map_comp_eq, map_comp_eq]; rfl
    rw [hmap]
    exact bt_probDist_map_equiv_pmf e _ ((a, c₁), b)
  have hR_z : R.map (fun s => s.2.2) = Q.map (fun t => t.2.1) := by
    unfold R; rw [map_comp_eq]; rfl
  have h := congrFun (congrArg ProbDist.pmf hci) (c₂, (a, c₁), b)
  dsimp only [condIndepDist] at h
  rw [hR_pmf, hR_xz, hR_yz, hR_z] at h
  by_cases hb : (Q.map (fun t => t.2.1)).pmf b = 0
  · rw [hb, mul_zero]
    have h2 : (Q.map (fun t => (t.2.1, t.2.2.2))).pmf (b, c₂) = 0 := by
      have hmarg : (Q.map (fun t => (t.2.1, t.2.2.2))).fst = Q.map (fun t => t.2.1) := by
        rw [← bt_probDist_map_fst, map_comp_eq]; rfl
      have hle : (Q.map (fun t => (t.2.1, t.2.2.2))).pmf (b, c₂) ≤ (Q.map (fun t => t.2.1)).pmf b := by
        rw [← hmarg]; exact Finset.single_le_sum (fun c _ => (Q.map _).nonneg (b, c)) (Finset.mem_univ c₂)
      exact le_antisymm (by linarith) ((Q.map _).nonneg _)
    simp [h2]
  · simp only [hb, ↓reduceIte] at h
    rw [h]; field_simp [hb]

open Classical in
/-- **Conditional-Type Permutation Markov Lemma** (Two-Encoder Stage 2):
    for any distribution `Q` on `X₁ × X₂ × U₁ × U₂` satisfying `U₂ — X₂ — (X₁, U₁)`,
    any `0 < n`, any `0 < ε₃ ≤ 1`, any fixed `(x₁, x₂, u₁) ∈ T_{ε₃/4}(Q_{X₁ X₂ U₁})`,
    and any fixed `u₂` with `(x₂, u₂) ∈ T_{ε₃/16}(Q_{X₂ U₂})`, if `π` is drawn uniformly
    from the fiber-preserving permutation group `G(x₂) = {π | ∀ i, x₂ (π i) = x₂ i}`, then
    `P_{π ∈ G(x₂)}((x₁, x₂, u₁, u₂ ∘ π) ∉ T_{ε₃}(Q)) ≤ (4 ∑_{Q(t)>0} 1/Q(t)²) / (n ε₃²)`. -/
theorem markov_lemma_conditional_type_perm
    [Fintype X₁] [Fintype X₂] [Fintype U₁] [Fintype U₂]
    (Q : ProbDist (X₁ × X₂ × U₁ × U₂))
    (hmk2 : condMutualInfo (Q.map (fun t => (t.2.2.2, (t.1, t.2.2.1), t.2.1))) = 0)
    {n : ℕ} (hn : 0 < n) {ε₃ : ℝ} (hε₃ : 0 < ε₃) (hε₃_le : ε₃ ≤ 1)
    {x₁ : Fin n → X₁} {x₂ : Fin n → X₂} {u₁ : Fin n → U₁} {u₂ : Fin n → U₂}
    (hx12u1 : (fun i => (x₁ i, x₂ i, u₁ i)) ∈
      strongTypicalSet (Q.map (fun t => (t.1, t.2.1, t.2.2.1))) n (ε₃ / 4))
    (hx2u2 : (fun i => (x₂ i, u₂ i)) ∈
      strongTypicalSet (Q.map (fun t => (t.2.1, t.2.2.2))) n (ε₃ / 16)) :
    (∑ π ∈ fiberPermSet x₂,
      if (fun i => (x₁ i, x₂ i, u₁ i, u₂ (π i))) ∉ strongTypicalSet Q n ε₃ then (1 : ℝ) else 0) /
      ((fiberPermSet x₂).card : ℝ) ≤
      (4 * ∑ t : X₁ × X₂ × U₁ × U₂, if 0 < Q.pmf t then 1 / Q.pmf t ^ 2 else 0) /
        ((n : ℝ) * ε₃ ^ 2) := by
  classical
  let G := fiberPermSet x₂
  have hG_pos : (0 : ℝ) < (G.card : ℝ) := Nat.cast_pos.mpr (fiberPermSet_card_pos x₂)
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  let Q121 := Q.map (fun t => (t.1, t.2.1, t.2.2.1))
  let Q22 := Q.map (fun t => (t.2.1, t.2.2.2))
  let Q2 := Q.map (fun t => t.2.1)
  have hx2 : x₂ ∈ strongTypicalSet Q2 n (ε₃ / 16) := by
    have hmap : Q22.map Prod.fst = Q2 := by unfold Q22 Q2; rw [map_comp_eq]; rfl
    rw [← hmap]
    exact strongTypicalSet_map Q22 Prod.fst n (ε₃ / 16) hx2u2
  rw [mem_strongTypicalSet] at hx12u1 hx2u2 hx2
  -- Union bound over 4-tuples `t = (a, b, c₁, c₂)`.
  have hunion : ∀ π ∈ G,
      (if (fun i => (x₁ i, x₂ i, u₁ i, u₂ (π i))) ∉ strongTypicalSet Q n ε₃ then (1 : ℝ) else 0) ≤
        ∑ t : X₁ × X₂ × U₁ × U₂,
          if ¬ (|empFreq (fun i => (x₁ i, x₂ i, u₁ i, u₂ (π i))) t - Q.pmf t| ≤ ε₃ * Q.pmf t)
          then (1 : ℝ) else 0 := by
    intro π _
    by_cases hmem : (fun i => (x₁ i, x₂ i, u₁ i, u₂ (π i))) ∈ strongTypicalSet Q n ε₃
    · simp only [hmem, not_true_eq_false, ↓reduceIte]
      exact Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
    · simp only [hmem, not_false_eq_true, ↓reduceIte]
      rw [mem_strongTypicalSet] at hmem; push Not at hmem
      rcases hmem with ⟨t₀, ht₀⟩
      have hnot : ¬ (|empFreq (fun i => (x₁ i, x₂ i, u₁ i, u₂ (π i))) t₀ - Q.pmf t₀| ≤ ε₃ * Q.pmf t₀) :=
        not_le.mpr ht₀
      calc (1 : ℝ)
        _ = (if ¬ (|empFreq (fun i => (x₁ i, x₂ i, u₁ i, u₂ (π i))) t₀ - Q.pmf t₀| ≤ ε₃ * Q.pmf t₀)
              then (1 : ℝ) else 0) := by simp [hnot]
        _ ≤ _ := Finset.single_le_sum
            (f := fun t => if ¬ (|empFreq (fun i => (x₁ i, x₂ i, u₁ i, u₂ (π i))) t - Q.pmf t| ≤ ε₃ * Q.pmf t)
              then (1 : ℝ) else 0)
            (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ t₀)
  -- Per-4-tuple Chebyshev bound.
  have hper_t : ∀ t : X₁ × X₂ × U₁ × U₂,
      (∑ π ∈ G, if ¬ (|empFreq (fun i => (x₁ i, x₂ i, u₁ i, u₂ (π i))) t - Q.pmf t| ≤ ε₃ * Q.pmf t)
          then (1 : ℝ) else 0) / (G.card : ℝ) ≤
        (if 0 < Q.pmf t then 4 * (1 / Q.pmf t ^ 2) else 0) / ((n : ℝ) * ε₃ ^ 2) := by
    rintro ⟨a, b, c₁, c₂⟩
    have hfac := bt_markov4_factorization Q hmk2 a b c₁ c₂
    let Ib := Finset.univ.filter fun i : Fin n => x₂ i = b
    let S := Finset.univ.filter fun i : Fin n => x₁ i = a ∧ x₂ i = b ∧ u₁ i = c₁
    let R := Finset.univ.filter fun j : Fin n => x₂ j = b ∧ u₂ j = c₂
    have hS_sub : S ⊆ Ib := fun i hi =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2.2.1⟩
    have hR_sub : R ⊆ Ib := fun j hj =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, (Finset.mem_filter.mp hj).2.1⟩
    -- Relate `empFreq` to `S`, `R`, `Ib`.
    have hS_freq : empFreq (fun i => (x₁ i, x₂ i, u₁ i)) (a, b, c₁) = (S.card : ℝ) / (n : ℝ) := by
      unfold empFreq
      have hfilt : (Finset.univ.filter fun i : Fin n => (x₁ i, x₂ i, u₁ i) = (a, b, c₁)) = S := by
        ext i; simp [S]
      rw [hfilt]
    have hR_freq : empFreq (fun j => (x₂ j, u₂ j)) (b, c₂) = (R.card : ℝ) / (n : ℝ) := by
      unfold empFreq
      have hfilt : (Finset.univ.filter fun j : Fin n => (x₂ j, u₂ j) = (b, c₂)) = R := by
        ext j; simp [R]
      rw [hfilt]
    have hIb_freq : empFreq x₂ b = (Ib.card : ℝ) / (n : ℝ) := by
      unfold empFreq; rfl
    have hcount_pi : ∀ π ∈ G,
        (n : ℝ) * empFreq (fun i => (x₁ i, x₂ i, u₁ i, u₂ (π i))) (a, b, c₁, c₂) =
          ∑ i ∈ S, if π i ∈ R then (1 : ℝ) else 0 := by
      intro π hπ
      unfold empFreq
      rw [mul_div_cancel₀ _ (ne_of_gt hn_pos), ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      have hfilt : (Finset.univ.filter fun i : Fin n => (x₁ i, x₂ i, u₁ i, u₂ (π i)) = (a, b, c₁, c₂)) =
          S.filter (fun i : Fin n => π i ∈ R) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, S, R, Prod.mk.injEq]
        have hpi : x₂ (π i) = x₂ i := mem_fiberPermSet.mp hπ i
        constructor
        · rintro ⟨ha, hb, hc1, hc2⟩
          exact ⟨⟨ha, hb, hc1⟩, hpi.trans hb, hc2⟩
        · rintro ⟨⟨ha, hb, hc1⟩, _, hc2⟩
          exact ⟨ha, hb, hc1, hc2⟩
      rw [hfilt]
    by_cases hqt : 0 < Q.pmf (a, b, c₁, c₂)
    · simp only [hqt, ↓reduceIte]
      have hQ2_pos : 0 < Q2.pmf b := by
        have hle : Q.pmf (a, b, c₁, c₂) ≤ Q2.pmf b := by
          unfold Q2 ProbDist.map; dsimp only
          have h1 := Finset.single_le_sum
            (f := fun t : X₁ × X₂ × U₁ × U₂ => if t.2.1 = b then Q.pmf t else 0)
            (fun t _ => by split_ifs <;> [exact Q.nonneg t; exact le_rfl])
            (Finset.mem_univ (a, b, c₁, c₂))
          simpa using h1
        linarith
      have hQ121_pos : 0 < Q121.pmf (a, b, c₁) := by
        have hle : Q.pmf (a, b, c₁, c₂) ≤ Q121.pmf (a, b, c₁) := by
          unfold Q121 ProbDist.map; dsimp only
          have h1 := Finset.single_le_sum
            (f := fun t : X₁ × X₂ × U₁ × U₂ => if (t.1, t.2.1, t.2.2.1) = (a, b, c₁) then Q.pmf t else 0)
            (fun t _ => by split_ifs <;> [exact Q.nonneg t; exact le_rfl])
            (Finset.mem_univ (a, b, c₁, c₂))
          simpa using h1
        linarith
      have hQ22_pos : 0 < Q22.pmf (b, c₂) := by
        have hle : Q.pmf (a, b, c₁, c₂) ≤ Q22.pmf (b, c₂) := by
          unfold Q22 ProbDist.map; dsimp only
          have h1 := Finset.single_le_sum
            (f := fun t : X₁ × X₂ × U₁ × U₂ => if (t.2.1, t.2.2.2) = (b, c₂) then Q.pmf t else 0)
            (fun t _ => by split_ifs <;> [exact Q.nonneg t; exact le_rfl])
            (Finset.mem_univ (a, b, c₁, c₂))
          simpa using h1
        linarith
      -- Bounds from strong typicality.
      have hS_bd := hx12u1 (a, b, c₁); rw [hS_freq] at hS_bd
      have hR_bd := hx2u2 (b, c₂); rw [hR_freq] at hR_bd
      have hIb_bd := hx2 b; rw [hIb_freq] at hIb_bd
      have hS_lo : (1 - ε₃ / 4) * Q121.pmf (a, b, c₁) ≤ (S.card : ℝ) / (n : ℝ) := by
        have := (abs_le.mp hS_bd).1; linarith
      have hS_hi : (S.card : ℝ) / (n : ℝ) ≤ (1 + ε₃ / 4) * Q121.pmf (a, b, c₁) := by
        have := (abs_le.mp hS_bd).2; linarith
      have hR_lo : (1 - ε₃ / 16) * Q22.pmf (b, c₂) ≤ (R.card : ℝ) / (n : ℝ) := by
        have := (abs_le.mp hR_bd).1; linarith
      have hR_hi : (R.card : ℝ) / (n : ℝ) ≤ (1 + ε₃ / 16) * Q22.pmf (b, c₂) := by
        have := (abs_le.mp hR_bd).2; linarith
      have hIb_lo : (1 - ε₃ / 16) * Q2.pmf b ≤ (Ib.card : ℝ) / (n : ℝ) := by
        have := (abs_le.mp hIb_bd).1; linarith
      have hIb_hi : (Ib.card : ℝ) / (n : ℝ) ≤ (1 + ε₃ / 16) * Q2.pmf b := by
        have := (abs_le.mp hIb_bd).2; linarith
      have hIb_pos : (0 : ℝ) < (Ib.card : ℝ) := by
        have hpos : 0 < (Ib.card : ℝ) / (n : ℝ) := by nlinarith
        exact (div_pos_iff_of_pos_right hn_pos).mp hpos
      -- Show `|((S.card / n) * (R.card / Ib.card)) - Q(a, b, c₁, c₂)| ≤ (ε₃ / 2) * Q(a, b, c₁, c₂)`.
      let p : ℝ := (R.card : ℝ) / (Ib.card : ℝ)
      let μ_hat : ℝ := ((S.card : ℝ) / (n : ℝ)) * p
      have hmu_eq : μ_hat * ((Ib.card : ℝ) / (n : ℝ)) = ((S.card : ℝ) / (n : ℝ)) * ((R.card : ℝ) / (n : ℝ)) := by
        dsimp [μ_hat, p]; field_simp [ne_of_gt hIb_pos, ne_of_gt hn_pos]
      have hmu_hi : μ_hat ≤ (1 + ε₃ / 2) * Q.pmf (a, b, c₁, c₂) := by
        have hmu_nn : 0 ≤ μ_hat := by dsimp [μ_hat, p]; positivity
        have h1 : μ_hat * ((1 - ε₃ / 16) * Q2.pmf b) ≤
            ((1 + ε₃ / 4) * Q121.pmf (a, b, c₁)) * ((1 + ε₃ / 16) * Q22.pmf (b, c₂)) :=
          calc μ_hat * ((1 - ε₃ / 16) * Q2.pmf b)
            _ ≤ μ_hat * ((Ib.card : ℝ) / (n : ℝ)) := mul_le_mul_of_nonneg_left hIb_lo hmu_nn
            _ = ((S.card : ℝ) / (n : ℝ)) * ((R.card : ℝ) / (n : ℝ)) := hmu_eq
            _ ≤ ((1 + ε₃ / 4) * Q121.pmf (a, b, c₁)) * ((1 + ε₃ / 16) * Q22.pmf (b, c₂)) :=
                mul_le_mul hS_hi hR_hi (by positivity) (by positivity)
        have h2 : ((1 + ε₃ / 4) * Q121.pmf (a, b, c₁)) * ((1 + ε₃ / 16) * Q22.pmf (b, c₂)) =
            (1 + ε₃ / 4) * (1 + ε₃ / 16) * (Q.pmf (a, b, c₁, c₂) * Q2.pmf b) := by
          calc ((1 + ε₃ / 4) * Q121.pmf (a, b, c₁)) * ((1 + ε₃ / 16) * Q22.pmf (b, c₂))
            _ = (1 + ε₃ / 4) * (1 + ε₃ / 16) * (Q121.pmf (a, b, c₁) * Q22.pmf (b, c₂)) := by ring
            _ = (1 + ε₃ / 4) * (1 + ε₃ / 16) * (Q.pmf (a, b, c₁, c₂) * Q2.pmf b) := by rw [← hfac]
        have h3 : (1 + ε₃ / 4) * (1 + ε₃ / 16) ≤ (1 + ε₃ / 2) * (1 - ε₃ / 16) := by
          have hd : (1 + ε₃ / 2) * (1 - ε₃ / 16) - (1 + ε₃ / 4) * (1 + ε₃ / 16) =
              ε₃ * (8 - 3 * ε₃) / 64 := by ring
          have hpos : 0 ≤ ε₃ * (8 - 3 * ε₃) / 64 := by nlinarith only [hε₃, hε₃_le]
          linarith
        have h4 : (1 + ε₃ / 4) * (1 + ε₃ / 16) * (Q.pmf (a, b, c₁, c₂) * Q2.pmf b) ≤
            ((1 + ε₃ / 2) * Q.pmf (a, b, c₁, c₂)) * ((1 - ε₃ / 16) * Q2.pmf b) := by
          have hq_nn : 0 ≤ Q.pmf (a, b, c₁, c₂) * Q2.pmf b := mul_nonneg (le_of_lt hqt) (le_of_lt hQ2_pos)
          calc (1 + ε₃ / 4) * (1 + ε₃ / 16) * (Q.pmf (a, b, c₁, c₂) * Q2.pmf b)
            _ ≤ (1 + ε₃ / 2) * (1 - ε₃ / 16) * (Q.pmf (a, b, c₁, c₂) * Q2.pmf b) :=
                mul_le_mul_of_nonneg_right h3 hq_nn
            _ = ((1 + ε₃ / 2) * Q.pmf (a, b, c₁, c₂)) * ((1 - ε₃ / 16) * Q2.pmf b) := by ring
        have hfac_pos : 0 < (1 - ε₃ / 16) * Q2.pmf b := mul_pos (by linarith) hQ2_pos
        exact le_of_mul_le_mul_right (le_trans h1 (h2.symm ▸ h4)) hfac_pos
      have hmu_lo : (1 - ε₃ / 2) * Q.pmf (a, b, c₁, c₂) ≤ μ_hat := by
        have hmu_nn : 0 ≤ μ_hat := by dsimp [μ_hat, p]; positivity
        have h1 : ((1 - ε₃ / 4) * Q121.pmf (a, b, c₁)) * ((1 - ε₃ / 16) * Q22.pmf (b, c₂)) ≤
            μ_hat * ((1 + ε₃ / 16) * Q2.pmf b) :=
          calc ((1 - ε₃ / 4) * Q121.pmf (a, b, c₁)) * ((1 - ε₃ / 16) * Q22.pmf (b, c₂))
            _ ≤ ((S.card : ℝ) / (n : ℝ)) * ((R.card : ℝ) / (n : ℝ)) :=
                mul_le_mul hS_lo hR_lo (mul_nonneg (by linarith) (le_of_lt hQ22_pos)) (by positivity)
            _ = μ_hat * ((Ib.card : ℝ) / (n : ℝ)) := hmu_eq.symm
            _ ≤ μ_hat * ((1 + ε₃ / 16) * Q2.pmf b) := mul_le_mul_of_nonneg_left hIb_hi hmu_nn
        have h2 : ((1 - ε₃ / 4) * Q121.pmf (a, b, c₁)) * ((1 - ε₃ / 16) * Q22.pmf (b, c₂)) =
            (1 - ε₃ / 4) * (1 - ε₃ / 16) * (Q.pmf (a, b, c₁, c₂) * Q2.pmf b) := by
          calc ((1 - ε₃ / 4) * Q121.pmf (a, b, c₁)) * ((1 - ε₃ / 16) * Q22.pmf (b, c₂))
            _ = (1 - ε₃ / 4) * (1 - ε₃ / 16) * (Q121.pmf (a, b, c₁) * Q22.pmf (b, c₂)) := by ring
            _ = (1 - ε₃ / 4) * (1 - ε₃ / 16) * (Q.pmf (a, b, c₁, c₂) * Q2.pmf b) := by rw [← hfac]
        have h3 : (1 - ε₃ / 2) * (1 + ε₃ / 16) ≤ (1 - ε₃ / 4) * (1 - ε₃ / 16) := by
          have hd : (1 - ε₃ / 4) * (1 - ε₃ / 16) - (1 - ε₃ / 2) * (1 + ε₃ / 16) =
              ε₃ * (8 + 3 * ε₃) / 64 := by ring
          have hpos : 0 ≤ ε₃ * (8 + 3 * ε₃) / 64 := by nlinarith only [hε₃]
          linarith
        have h4 : ((1 - ε₃ / 2) * Q.pmf (a, b, c₁, c₂)) * ((1 + ε₃ / 16) * Q2.pmf b) ≤
            (1 - ε₃ / 4) * (1 - ε₃ / 16) * (Q.pmf (a, b, c₁, c₂) * Q2.pmf b) := by
          have hq_nn : 0 ≤ Q.pmf (a, b, c₁, c₂) * Q2.pmf b := mul_nonneg (le_of_lt hqt) (le_of_lt hQ2_pos)
          calc ((1 - ε₃ / 2) * Q.pmf (a, b, c₁, c₂)) * ((1 + ε₃ / 16) * Q2.pmf b)
            _ = (1 - ε₃ / 2) * (1 + ε₃ / 16) * (Q.pmf (a, b, c₁, c₂) * Q2.pmf b) := by ring
            _ ≤ (1 - ε₃ / 4) * (1 - ε₃ / 16) * (Q.pmf (a, b, c₁, c₂) * Q2.pmf b) :=
                mul_le_mul_of_nonneg_right h3 hq_nn
        have hfac_pos : 0 < (1 + ε₃ / 16) * Q2.pmf b := mul_pos (by linarith) hQ2_pos
        exact le_of_mul_le_mul_right (le_trans h4 (h2 ▸ h1)) hfac_pos
      have hmu_abs : |μ_hat - Q.pmf (a, b, c₁, c₂)| ≤ (ε₃ / 2) * Q.pmf (a, b, c₁, c₂) :=
        abs_le.mpr ⟨by linarith, by linarith⟩
      -- Variance bound on `∑ i ∈ S, (1_{π i ∈ R} - p)`.
      have hVar := fiberPermSet_var_le x₂ b S R hS_sub hR_sub
      have hS_le_n : (S.card : ℝ) ≤ (n : ℝ) := by
        have hle : S.card ≤ Fintype.card (Fin n) := Finset.card_le_univ S
        simpa using (Nat.cast_le (α := ℝ)).mpr hle
      have hVar_n : ∑ π ∈ G, (∑ i ∈ S, ((if π i ∈ R then (1 : ℝ) else 0) - p)) ^ 2 ≤
          (G.card : ℝ) * (n : ℝ) :=
        le_trans hVar (mul_le_mul_of_nonneg_left hS_le_n (le_of_lt hG_pos))
      -- Relate centered sum to `empFreq - μ_hat`.
      have hcenter : ∀ π ∈ G,
          ∑ i ∈ S, ((if π i ∈ R then (1 : ℝ) else 0) - p) =
            (n : ℝ) * (empFreq (fun i => (x₁ i, x₂ i, u₁ i, u₂ (π i))) (a, b, c₁, c₂) - μ_hat) := by
        intro π hπ
        rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← hcount_pi π hπ]
        dsimp [μ_hat]; field_simp [ne_of_gt hn_pos]
      -- Chebyshev inequality.
      have hcheb : ((n : ℝ) * ((ε₃ / 2) * Q.pmf (a, b, c₁, c₂))) ^ 2 *
          (∑ π ∈ G, if ¬ (|empFreq (fun i => (x₁ i, x₂ i, u₁ i, u₂ (π i))) (a, b, c₁, c₂) - Q.pmf (a, b, c₁, c₂)| ≤
              ε₃ * Q.pmf (a, b, c₁, c₂)) then (1 : ℝ) else 0) ≤ (G.card : ℝ) * (n : ℝ) := by
        rw [Finset.mul_sum]
        refine le_trans (Finset.sum_le_sum fun π hπ => ?_) hVar_n
        by_cases hle : |empFreq (fun i => (x₁ i, x₂ i, u₁ i, u₂ (π i))) (a, b, c₁, c₂) - Q.pmf (a, b, c₁, c₂)| ≤
            ε₃ * Q.pmf (a, b, c₁, c₂)
        · simp only [hle, not_true_eq_false, ↓reduceIte, mul_zero]; exact sq_nonneg _
        · simp only [hle, not_false_eq_true, ↓reduceIte, mul_one]
          have hgt : ε₃ * Q.pmf (a, b, c₁, c₂) <
              |empFreq (fun i => (x₁ i, x₂ i, u₁ i, u₂ (π i))) (a, b, c₁, c₂) - Q.pmf (a, b, c₁, c₂)| :=
            lt_of_not_ge hle
          have htri : |empFreq (fun i => (x₁ i, x₂ i, u₁ i, u₂ (π i))) (a, b, c₁, c₂) - Q.pmf (a, b, c₁, c₂)| ≤
              |empFreq (fun i => (x₁ i, x₂ i, u₁ i, u₂ (π i))) (a, b, c₁, c₂) - μ_hat| +
              |μ_hat - Q.pmf (a, b, c₁, c₂)| := by
            have hsub : empFreq (fun i => (x₁ i, x₂ i, u₁ i, u₂ (π i))) (a, b, c₁, c₂) - Q.pmf (a, b, c₁, c₂) =
                (empFreq (fun i => (x₁ i, x₂ i, u₁ i, u₂ (π i))) (a, b, c₁, c₂) - μ_hat) +
                (μ_hat - Q.pmf (a, b, c₁, c₂)) := by ring
            rw [hsub]; exact abs_add_le _ _
          have hdev : (ε₃ / 2) * Q.pmf (a, b, c₁, c₂) <
              |empFreq (fun i => (x₁ i, x₂ i, u₁ i, u₂ (π i))) (a, b, c₁, c₂) - μ_hat| := by linarith
          have habs : (n : ℝ) * ((ε₃ / 2) * Q.pmf (a, b, c₁, c₂)) <
              |∑ i ∈ S, ((if π i ∈ R then (1 : ℝ) else 0) - p)| := by
            rw [hcenter π hπ, abs_mul, abs_of_pos hn_pos]
            exact mul_lt_mul_of_pos_left hdev hn_pos
          rw [← sq_abs (∑ i ∈ S, ((if π i ∈ R then (1 : ℝ) else 0) - p))]
          have hnn : 0 ≤ (n : ℝ) * ((ε₃ / 2) * Q.pmf (a, b, c₁, c₂)) := by positivity
          exact pow_le_pow_left₀ hnn (le_of_lt habs) 2
      have hden_pos : (0 : ℝ) < ((n : ℝ) * ((ε₃ / 2) * Q.pmf (a, b, c₁, c₂))) ^ 2 := by positivity
      have h1 := (le_div_iff₀' hden_pos).mpr hcheb
      have h2 := div_le_div_of_nonneg_right h1 (le_of_lt hG_pos)
      have hsimp : ((G.card : ℝ) * (n : ℝ)) / ((n : ℝ) * ((ε₃ / 2) * Q.pmf (a, b, c₁, c₂))) ^ 2 / (G.card : ℝ) =
          (4 * (1 / Q.pmf (a, b, c₁, c₂) ^ 2)) / ((n : ℝ) * ε₃ ^ 2) := by
        field_simp [ne_of_gt hG_pos, ne_of_gt hn_pos, ne_of_gt hε₃, ne_of_gt hqt]
        ring
      linarith
    · -- Zero-probability 4-tuple: count is identically 0 for every `π ∈ G`.
      simp only [hqt, ↓reduceIte, zero_div]
      have hqt0 : Q.pmf (a, b, c₁, c₂) = 0 := le_antisymm (not_lt.mp hqt) (Q.nonneg _)
      rw [hqt0, zero_mul] at hfac
      have hzero : ∑ π ∈ G,
          (if ¬ (|empFreq (fun i => (x₁ i, x₂ i, u₁ i, u₂ (π i))) (a, b, c₁, c₂) - Q.pmf (a, b, c₁, c₂)| ≤
              ε₃ * Q.pmf (a, b, c₁, c₂)) then (1 : ℝ) else 0) = 0 := by
        refine Finset.sum_eq_zero fun π hπ => ?_
        have hf0 : empFreq (fun i => (x₁ i, x₂ i, u₁ i, u₂ (π i))) (a, b, c₁, c₂) = 0 := by
          have hc := hcount_pi π hπ
          rcases mul_eq_zero.mp hfac.symm with hQ121_0 | hQ22_0
          · -- `Q121(a, b, c₁) = 0` ⇒ `S = ∅`.
            have hSbd := hx12u1 (a, b, c₁)
            rw [hQ121_0, sub_zero, mul_zero, hS_freq] at hSbd
            have hSc0 : (S.card : ℝ) / (n : ℝ) = 0 := abs_nonpos_iff.mp hSbd
            have hSc : S.card = 0 := by
              have h1 : (S.card : ℝ) = 0 := (div_eq_zero_iff.mp hSc0).resolve_right (ne_of_gt hn_pos)
              exact_mod_cast h1
            rw [Finset.card_eq_zero.mp hSc, Finset.sum_empty] at hc
            exact (mul_eq_zero.mp hc).resolve_left (ne_of_gt hn_pos)
          · -- `Q22(b, c₂) = 0` ⇒ `R = ∅`.
            have hRbd := hx2u2 (b, c₂)
            rw [hQ22_0, sub_zero, mul_zero, hR_freq] at hRbd
            have hRc0 : (R.card : ℝ) / (n : ℝ) = 0 := abs_nonpos_iff.mp hRbd
            have hRc : R.card = 0 := by
              have h1 : (R.card : ℝ) = 0 := (div_eq_zero_iff.mp hRc0).resolve_right (ne_of_gt hn_pos)
              exact_mod_cast h1
            rw [Finset.card_eq_zero.mp hRc] at hc
            have hsum0 : ∑ i ∈ S, (if π i ∈ (∅ : Finset (Fin n)) then (1 : ℝ) else 0) = 0 := by simp
            rw [hsum0] at hc
            exact (mul_eq_zero.mp hc).resolve_left (ne_of_gt hn_pos)
        simp [hqt0, hf0]
      rw [hzero, zero_div]
  calc (∑ π ∈ G, if (fun i => (x₁ i, x₂ i, u₁ i, u₂ (π i))) ∉ strongTypicalSet Q n ε₃ then (1 : ℝ) else 0) /
        (G.card : ℝ)
    _ ≤ (∑ π ∈ G, ∑ t : X₁ × X₂ × U₁ × U₂,
          if ¬ (|empFreq (fun i => (x₁ i, x₂ i, u₁ i, u₂ (π i))) t - Q.pmf t| ≤ ε₃ * Q.pmf t)
          then (1 : ℝ) else 0) / (G.card : ℝ) :=
        div_le_div_of_nonneg_right (Finset.sum_le_sum hunion) (le_of_lt hG_pos)
    _ = ∑ t : X₁ × X₂ × U₁ × U₂,
          (∑ π ∈ G, if ¬ (|empFreq (fun i => (x₁ i, x₂ i, u₁ i, u₂ (π i))) t - Q.pmf t| ≤ ε₃ * Q.pmf t)
            then (1 : ℝ) else 0) / (G.card : ℝ) := by
        rw [Finset.sum_comm, Finset.sum_div]
    _ ≤ ∑ t : X₁ × X₂ × U₁ × U₂,
          (if 0 < Q.pmf t then 4 * (1 / Q.pmf t ^ 2) else 0) / ((n : ℝ) * ε₃ ^ 2) :=
        Finset.sum_le_sum fun t _ => hper_t t
    _ = (4 * ∑ t : X₁ × X₂ × U₁ × U₂, if 0 < Q.pmf t then 1 / Q.pmf t ^ 2 else 0) /
          ((n : ℝ) * ε₃ ^ 2) := by
        rw [← Finset.sum_div, Finset.mul_sum]
        congr 1; refine Finset.sum_congr rfl fun t _ => by split_ifs <;> ring

/-- First index in `Fin M` whose codeword lies in a target finset `A` (defaults to `⟨0, hM⟩`). -/
noncomputable def firstCoveringIdx {Ω : Type*} {M : ℕ} (hM : 0 < M)
    (A : Finset Ω) (C : Fin M → Ω) : Fin M := by
  classical
  exact if h : ∃ ℓ : Fin M, C ℓ ∈ A then
    (Finset.univ.filter fun ℓ : Fin M => C ℓ ∈ A).min'
      (by rcases h with ⟨ℓ, hℓ⟩; exact ⟨ℓ, Finset.mem_filter.mpr ⟨Finset.mem_univ ℓ, hℓ⟩⟩)
  else ⟨0, hM⟩

private lemma firstCoveringIdx_mem {Ω : Type*} {M : ℕ} (hM : 0 < M)
    (A : Finset Ω) (C : Fin M → Ω) (h : ∃ ℓ : Fin M, C ℓ ∈ A) :
    C (firstCoveringIdx hM A C) ∈ A := by
  classical
  simp only [firstCoveringIdx, h, ↓reduceDIte]
  exact (Finset.mem_filter.mp (Finset.min'_mem (Finset.univ.filter fun ℓ : Fin M => C ℓ ∈ A) _)).2

private lemma firstCoveringIdx_le {Ω : Type*} {M : ℕ} (hM : 0 < M)
    (A : Finset Ω) (C : Fin M → Ω) (j : Fin M) (hj : C j ∈ A) :
    firstCoveringIdx hM A C ≤ j := by
  classical
  have hex : ∃ ℓ : Fin M, C ℓ ∈ A := ⟨j, hj⟩
  simp only [firstCoveringIdx, hex, ↓reduceDIte]
  exact Finset.min'_le (Finset.univ.filter fun ℓ : Fin M => C ℓ ∈ A) j
    (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)

open Classical in
/-- Exact first-hit bound for an i.i.d. random codebook:
    if `μ(A ∩ B) ≤ η * μ(A)` with `0 ≤ η`, then the probability that the first codeword
    hitting `A` also lands in `B` is at most `η`. -/
private lemma firstCoveringIdx_bad_prob_le {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (μ : ProbDist Ω)
    {M : ℕ} (hM : 0 < M) (A B : Finset Ω) {η : ℝ} (hη : 0 ≤ η)
    (hratio : (∑ ω ∈ A, μ.pmf ω * (if ω ∈ B then (1 : ℝ) else 0)) ≤ η * ∑ ω ∈ A, μ.pmf ω) :
    ∑ C : Fin M → Ω, (iidDist μ M).pmf C *
        (if (∃ ℓ : Fin M, C ℓ ∈ A) ∧ C (firstCoveringIdx hM A C) ∈ B then (1 : ℝ) else 0) ≤ η := by
  classical
  -- Decompose by the exact first hitting index `k : Fin M`.
  have hdecomp : ∀ C : Fin M → Ω,
      (if (∃ ℓ : Fin M, C ℓ ∈ A) ∧ C (firstCoveringIdx hM A C) ∈ B then (1 : ℝ) else 0) =
        ∑ k : Fin M, if (∀ j : Fin M, j < k → C j ∉ A) ∧ C k ∈ A ∧ C k ∈ B then (1 : ℝ) else 0 := by
    intro C
    by_cases hex : ∃ ℓ : Fin M, C ℓ ∈ A
    · set k₀ := firstCoveringIdx hM A C
      have hk₀_A : C k₀ ∈ A := firstCoveringIdx_mem hM A C hex
      have hk₀_min : ∀ j : Fin M, j < k₀ → C j ∉ A :=
        fun j hj hjA => not_lt_of_ge (firstCoveringIdx_le hM A C j hjA) hj
      rw [Finset.sum_eq_single k₀]
      · by_cases hB : C k₀ ∈ B
        · have hgood : (∀ j : Fin M, j < k₀ → C j ∉ A) ∧ C k₀ ∈ A ∧ C k₀ ∈ B := ⟨hk₀_min, hk₀_A, hB⟩
          have h1 : (∃ ℓ : Fin M, C ℓ ∈ A) ∧ C k₀ ∈ B := ⟨hex, hB⟩
          rw [ite_eq_left_iff.mpr (fun h => absurd h1 h), ite_eq_left_iff.mpr (fun h => absurd hgood h)]
        · have h1 : ¬ ((∃ ℓ : Fin M, C ℓ ∈ A) ∧ C k₀ ∈ B) := fun h => hB h.2
          have h2 : ¬ ((∀ j : Fin M, j < k₀ → C j ∉ A) ∧ C k₀ ∈ A ∧ C k₀ ∈ B) := fun h => hB h.2.2
          rw [ite_eq_right_iff.mpr (fun h => absurd h h1), ite_eq_right_iff.mpr (fun h => absurd h h2)]
      · intro k _ hne
        have hnot : ¬ ((∀ j : Fin M, j < k → C j ∉ A) ∧ C k ∈ A ∧ C k ∈ B) := by
          rintro ⟨hpre, hkA, _⟩
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · exact hk₀_min k hlt hkA
          · exact hpre k₀ hgt hk₀_A
        simp [hnot]
      · intro h; exact absurd (Finset.mem_univ _) h
    · simp only [hex, false_and, ↓reduceIte]
      exact (Finset.sum_eq_zero fun k _ => by
        have hkA : C k ∉ A := fun h => hex ⟨k, h⟩
        simp [hkA]).symm
  simp_rw [hdecomp, Finset.mul_sum]
  rw [Finset.sum_comm]
  let pA : ℝ := ∑ ω ∈ A, μ.pmf ω
  let pAB : ℝ := ∑ ω ∈ A, μ.pmf ω * (if ω ∈ B then (1 : ℝ) else 0)
  have hpA_nn : 0 ≤ pA := Finset.sum_nonneg fun ω _ => μ.nonneg ω
  have hpA_le1 : pA ≤ 1 := by
    calc pA = ∑ ω ∈ A, μ.pmf ω := rfl
      _ ≤ ∑ ω : Ω, μ.pmf ω := Finset.sum_le_univ_sum_of_nonneg fun ω => μ.nonneg ω
      _ = 1 := μ.sum_one
  have h1sub_eq : ∑ ω : Ω, μ.pmf ω * (if ω ∉ A then (1 : ℝ) else 0) = 1 - pA := by
    have hsplit : ∑ ω : Ω, μ.pmf ω * (if ω ∈ A then (1 : ℝ) else 0) +
        ∑ ω : Ω, μ.pmf ω * (if ω ∉ A then (1 : ℝ) else 0) = 1 := by
      rw [← Finset.sum_add_distrib]
      trans (∑ ω : Ω, μ.pmf ω)
      · refine Finset.sum_congr rfl fun ω _ => by split_ifs <;> ring
      · exact μ.sum_one
    have hA_eq : ∑ ω : Ω, μ.pmf ω * (if ω ∈ A then (1 : ℝ) else 0) = pA := by
      trans (∑ ω : Ω, if ω ∈ A then μ.pmf ω else 0)
      · refine Finset.sum_congr rfl fun ω _ => by split_ifs <;> ring
      · rw [← Finset.sum_filter]; congr 1; ext ω; simp
    linarith
  have hpAB_eq : ∑ ω : Ω, μ.pmf ω * (if ω ∈ A ∧ ω ∈ B then (1 : ℝ) else 0) = pAB := by
    dsimp [pAB]
    trans (∑ ω : Ω, if ω ∈ A then μ.pmf ω * (if ω ∈ B then (1 : ℝ) else 0) else 0)
    · refine Finset.sum_congr rfl fun ω _ => by
        by_cases h1 : ω ∈ A <;> by_cases h2 : ω ∈ B <;> simp [h1, h2]
    · rw [← Finset.sum_filter]; congr 1; ext ω; simp
  -- Evaluate each term `k : Fin M` by `Fintype.prod_sum`.
  have heach : ∀ k : Fin M,
      ∑ C : Fin M → Ω, (iidDist μ M).pmf C *
          (if (∀ j : Fin M, j < k → C j ∉ A) ∧ C k ∈ A ∧ C k ∈ B then (1 : ℝ) else 0) =
        (1 - pA) ^ k.1 * pAB := by
    intro k
    let F : Fin M → Ω → ℝ := fun j ω =>
      if j < k then μ.pmf ω * (if ω ∉ A then (1 : ℝ) else 0)
      else if j = k then μ.pmf ω * (if ω ∈ A ∧ ω ∈ B then (1 : ℝ) else 0)
      else μ.pmf ω
    have hfun : ∀ C : Fin M → Ω,
        (iidDist μ M).pmf C *
          (if (∀ j : Fin M, j < k → C j ∉ A) ∧ C k ∈ A ∧ C k ∈ B then (1 : ℝ) else 0) =
        ∏ j : Fin M, F j (C j) := by
      intro C
      by_cases hgood : (∀ j : Fin M, j < k → C j ∉ A) ∧ C k ∈ A ∧ C k ∈ B
      · rw [ite_eq_left_iff.mpr (fun h => absurd hgood h), mul_one]
        unfold iidDist; dsimp only
        refine Finset.prod_congr rfl fun j _ => ?_
        dsimp only [F]
        by_cases hlt : j < k
        · have hna : C j ∉ A := hgood.1 j hlt
          rw [ite_eq_left_iff.mpr (fun h => absurd hlt h), ite_eq_left_iff.mpr (fun h => absurd hna h), mul_one]
        · by_cases heq : j = k
          · subst heq
            have hab : C j ∈ A ∧ C j ∈ B := ⟨hgood.2.1, hgood.2.2⟩
            rw [ite_eq_right_iff.mpr (fun h => absurd h hlt), ite_eq_left_iff.mpr (fun h => absurd rfl h),
                ite_eq_left_iff.mpr (fun h => absurd hab h), mul_one]
          · rw [ite_eq_right_iff.mpr (fun h => absurd h hlt), ite_eq_right_iff.mpr (fun h => absurd h heq)]
      · rw [ite_eq_right_iff.mpr (fun h => absurd h hgood), mul_zero]
        symm
        by_cases hpre : ∀ j : Fin M, j < k → C j ∉ A
        · have hk_bad : ¬ (C k ∈ A ∧ C k ∈ B) := fun hk => hgood ⟨hpre, hk⟩
          exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [F, hk_bad])
        · push Not at hpre
          rcases hpre with ⟨j₀, hj₀_lt, hj₀_A⟩
          exact Finset.prod_eq_zero (Finset.mem_univ j₀) (by simp [F, hj₀_lt, hj₀_A])
    simp_rw [hfun, ← Fintype.prod_sum F]
    have hfactor : ∀ j : Fin M, ∑ ω : Ω, F j ω =
        if j < k then (1 - pA) else if j = k then pAB else 1 := by
      intro j; dsimp only [F]
      by_cases hlt : j < k
      · simp only [hlt, ite_true]; exact h1sub_eq
      · by_cases heq : j = k
        · simp only [hlt, ite_false]; simp only [heq, ite_true]; exact hpAB_eq
        · simp only [hlt, heq, ite_false]; exact μ.sum_one
    simp_rw [hfactor]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
    have hk_val : (if k < k then 1 - pA else if k = k then pAB else 1) = pAB := by simp
    rw [hk_val]
    have hrest : ∏ j ∈ Finset.univ.erase k, (if j < k then 1 - pA else if j = k then pAB else 1) =
        (1 - pA) ^ k.1 := by
      have hfilt : ∏ j ∈ Finset.univ.erase k, (if j < k then 1 - pA else if j = k then pAB else 1) =
          ∏ j ∈ (Finset.univ.erase k).filter (fun j : Fin M => j < k), (1 - pA) := by
        rw [Finset.prod_filter]
        refine Finset.prod_congr rfl fun j hj => ?_
        have hne : j ≠ k := (Finset.mem_erase.mp hj).1
        by_cases hlt : j < k <;> simp [hlt, hne]
      rw [hfilt, Finset.prod_const]
      congr 1
      have hcard : ((Finset.univ.erase k).filter (fun j : Fin M => j < k)).card = k.1 := by
        have heq : (Finset.univ.erase k).filter (fun j : Fin M => j < k) =
            Finset.univ.filter (fun j : Fin M => j.1 < k.1) := by
          ext j; simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
          constructor
          · rintro ⟨_, hlt⟩; exact hlt
          · intro hlt; exact ⟨ne_of_lt (Fin.lt_def.mpr hlt), hlt⟩
        rw [heq]
        trans (Finset.range k.1).card
        · refine Finset.card_bij (fun (j : Fin M) _ => j.1) ?_ ?_ ?_
          · intro j hj; exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
          · intro a _ b _ h; exact Fin.ext h
          · intro m hm
            have hlt : m < k.1 := Finset.mem_range.mp hm
            exact ⟨⟨m, lt_trans hlt k.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, rfl⟩
        · exact Finset.card_range k.1
      exact hcard
    rw [hrest, mul_comm]
  simp_rw [heach, ← Finset.sum_mul]
  -- Telescoping geometric sum: `pA * ∑ k : Fin M, (1 - pA)^k.1 = 1 - (1 - pA)^M ≤ 1`.
  have hgeom_nn : 0 ≤ ∑ k : Fin M, (1 - pA) ^ k.1 :=
    Finset.sum_nonneg fun k _ => pow_nonneg (by linarith) k.1
  have hgeom : (∑ k : Fin M, (1 - pA) ^ k.1) * pA = 1 - (1 - pA) ^ M := by
    have htele : (∑ k : Fin M, (1 - pA) ^ k.1) * pA =
        ∑ k : Fin M, ((1 - pA) ^ k.1 - (1 - pA) ^ (k.1 + 1)) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => by ring
    rw [htele]
    have hneg := bt_fin_sum_telescope (fun m => -((1 - pA) ^ m)) M
    have heq : ∑ k : Fin M, ((1 - pA) ^ k.1 - (1 - pA) ^ (k.1 + 1)) =
        ∑ k : Fin M, (-((1 - pA) ^ (k.1 + 1)) - -((1 - pA) ^ k.1)) :=
      Finset.sum_congr rfl fun k _ => by ring
    rw [heq, hneg]; simp; ring
  have hpow_nn : 0 ≤ (1 - pA) ^ M := pow_nonneg (by linarith) M
  calc (∑ k : Fin M, (1 - pA) ^ k.1) * pAB
    _ ≤ (∑ k : Fin M, (1 - pA) ^ k.1) * (η * pA) :=
        mul_le_mul_of_nonneg_left hratio hgeom_nn
    _ = η * ((∑ k : Fin M, (1 - pA) ^ k.1) * pA) := by ring
    _ = η * (1 - (1 - pA) ^ M) := by rw [hgeom]
    _ ≤ η * 1 := mul_le_mul_of_nonneg_left (by linarith) hη
    _ = η := mul_one η

open Classical in
/-- **Two-Encoder Second-Stage Markov Lemma (First Covering Codeword)**
    (El Gamal & Kim Lemma 12.1; Berger 1978; Tung 1978):
    for any joint distribution `Q` on `X₁ × X₂ × U₁ × U₂` satisfying `U₂ — X₂ — (X₁, U₁)`,
    any `0 < n`, `0 < M_c`, `0 < ε₃ ≤ 1`, and any **fixed** strongly typical triple
    `(x₁, x₂, u₁) ∈ T_{ε₃/4}(Q_{X₁ X₂ U₁})`, when an independent i.i.d. codebook
    `C₂ ~ codebookDist Q_{U₂} n M_c` is drawn and Encoder 2 picks the first index `ℓ₂` with
    `(x₂, C₂ ℓ₂) ∈ T_{ε₃/16}(Q_{X₂ U₂})`, the probability that a covering codeword exists yet
    `(x₁, x₂, u₁, C₂ ℓ₂)` fails to be strongly `ε₃`-typical under `Q` satisfies the uniform bound
    `(4 ∑_{Q(t)>0} 1/Q(t)²) / (n ε₃²)`. -/
theorem markov_lemma_first_covering_codeword
    [Fintype X₁] [Fintype X₂] [Fintype U₁] [Fintype U₂]
    (Q : ProbDist (X₁ × X₂ × U₁ × U₂))
    (hmk2 : condMutualInfo (Q.map (fun t => (t.2.2.2, (t.1, t.2.2.1), t.2.1))) = 0)
    {n M_c : ℕ} (hn : 0 < n) (hMc : 0 < M_c)
    {ε₃ : ℝ} (hε₃ : 0 < ε₃) (hε₃_le : ε₃ ≤ 1)
    {x₁ : Fin n → X₁} {x₂ : Fin n → X₂} {u₁ : Fin n → U₁}
    (hx12u1 : (fun i => (x₁ i, x₂ i, u₁ i)) ∈
      strongTypicalSet (Q.map (fun t => (t.1, t.2.1, t.2.2.1))) n (ε₃ / 4)) :
    let Q₂ := Q.map (fun t => (t.2.1, t.2.2.2))
    let A : Finset (Fin n → U₂) :=
      Finset.univ.filter fun u₂ => (fun i => (x₂ i, u₂ i)) ∈ strongTypicalSet Q₂ n (ε₃ / 16)
    ∑ C : Fin M_c → Fin n → U₂, (codebookDist Q₂.snd n M_c).pmf C *
        (if (∃ ℓ : Fin M_c, C ℓ ∈ A) ∧
            (fun i => (x₁ i, x₂ i, u₁ i, C (firstCoveringIdx hMc A C) i)) ∉ strongTypicalSet Q n ε₃
         then (1 : ℝ) else 0) ≤
      (4 * ∑ t : X₁ × X₂ × U₁ × U₂, if 0 < Q.pmf t then 1 / Q.pmf t ^ 2 else 0) /
        ((n : ℝ) * ε₃ ^ 2) := by
  dsimp only
  let Q₂ := Q.map (fun t => (t.2.1, t.2.2.2))
  let μ : ProbDist (Fin n → U₂) := iidDist Q₂.snd n
  let A : Finset (Fin n → U₂) :=
    Finset.univ.filter fun u₂ => (fun i => (x₂ i, u₂ i)) ∈ strongTypicalSet Q₂ n (ε₃ / 16)
  let B : Finset (Fin n → U₂) :=
    Finset.univ.filter fun u₂ => (fun i => (x₁ i, x₂ i, u₁ i, u₂ i)) ∉ strongTypicalSet Q n ε₃
  let η : ℝ := (4 * ∑ t : X₁ × X₂ × U₁ × U₂, if 0 < Q.pmf t then 1 / Q.pmf t ^ 2 else 0) /
    ((n : ℝ) * ε₃ ^ 2)
  have hη_nn : 0 ≤ η := by
    dsimp [η]
    refine div_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg fun t _ => ?_)) (by positivity)
    split_ifs <;> positivity
  -- Prove `μ(A ∩ B) ≤ η * μ(A)` by averaging over `G = fiberPermSet x₂`.
  have hratio : (∑ u₂ ∈ A, μ.pmf u₂ * (if u₂ ∈ B then (1 : ℝ) else 0)) ≤ η * ∑ u₂ ∈ A, μ.pmf u₂ := by
    let G := fiberPermSet x₂
    have hG_pos : (0 : ℝ) < (G.card : ℝ) := Nat.cast_pos.mpr (fiberPermSet_card_pos x₂)
    -- Every `π ∈ G` preserves `μ` and preserves membership in `A`.
    have hμ_inv : ∀ (π : Equiv.Perm (Fin n)) (u₂ : Fin n → U₂), μ.pmf (u₂ ∘ π) = μ.pmf u₂ := by
      intro π u₂
      unfold μ iidDist; dsimp only
      exact Fintype.prod_equiv π (fun i => Q₂.snd.pmf (u₂ (π i))) (fun j => Q₂.snd.pmf (u₂ j)) (fun _ => rfl)
    have hA_inv : ∀ {π : Equiv.Perm (Fin n)}, π ∈ G → ∀ u₂ : Fin n → U₂, u₂ ∘ π ∈ A ↔ u₂ ∈ A := by
      intro π hπ u₂
      have hfreq : ∀ p : X₂ × U₂, empFreq (fun i => (x₂ i, u₂ (π i))) p = empFreq (fun i => (x₂ i, u₂ i)) p := by
        intro p
        unfold empFreq; congr 2
        refine Finset.card_bij (fun i _ => π i) ?_ ?_ ?_
        · intro i hi
          have h1 : (x₂ i, u₂ (π i)) = p := (Finset.mem_filter.mp hi).2
          have h2 : x₂ (π i) = x₂ i := mem_fiberPermSet.mp hπ i
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          dsimp only; rw [h2]; exact h1
        · intro i₁ _ i₂ _ h; exact π.injective h
        · intro j hj
          have h1 : (x₂ j, u₂ j) = p := (Finset.mem_filter.mp hj).2
          have h2 : x₂ (π⁻¹ j) = x₂ j := mem_fiberPermSet.mp (inv_mem_fiberPermSet hπ) j
          have h3 : π (π⁻¹ j) = j := Equiv.apply_symm_apply π j
          refine ⟨π⁻¹ j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, h3⟩
          dsimp only; rw [h2, h3]; exact h1
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, mem_strongTypicalSet,
        Function.comp_apply, hfreq]
    -- Average over `π ∈ G`: for each `π ∈ G`, `∑ u₂ ∈ A, μ(u₂) 1_{u₂ ∈ B} = ∑ u₂ ∈ A, μ(u₂) 1_{u₂ ∘ π ∈ B}`.
    have hshift : ∀ π ∈ G,
        (∑ u₂ ∈ A, μ.pmf u₂ * (if u₂ ∈ B then (1 : ℝ) else 0)) =
          ∑ u₂ ∈ A, μ.pmf u₂ * (if u₂ ∘ π ∈ B then (1 : ℝ) else 0) := by
      intro π hπ
      refine (Finset.sum_bij (fun u₂ _ => u₂ ∘ π) ?_ ?_ ?_ ?_).symm
      · intro u₂ hu₂; exact (hA_inv hπ u₂).mpr hu₂
      · intro u₂ _ v₂ _ h
        funext i; have hi := congrFun h (π⁻¹ i); simpa [Equiv.apply_symm_apply] using hi
      · intro u₂ hu₂
        refine ⟨u₂ ∘ (π⁻¹ : Equiv.Perm (Fin n)), (hA_inv (inv_mem_fiberPermSet hπ) u₂).mpr hu₂, ?_⟩
        funext i; exact congrArg u₂ (Equiv.symm_apply_apply π i)
      · intro u₂ _; rw [hμ_inv π u₂]
    have havg : (G.card : ℝ) * (∑ u₂ ∈ A, μ.pmf u₂ * (if u₂ ∈ B then (1 : ℝ) else 0)) =
        ∑ u₂ ∈ A, μ.pmf u₂ * ∑ π ∈ G, (if u₂ ∘ π ∈ B then (1 : ℝ) else 0) := by
      calc (G.card : ℝ) * (∑ u₂ ∈ A, μ.pmf u₂ * (if u₂ ∈ B then (1 : ℝ) else 0))
        _ = ∑ _π ∈ G, ∑ u₂ ∈ A, μ.pmf u₂ * (if u₂ ∈ B then (1 : ℝ) else 0) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = ∑ π ∈ G, ∑ u₂ ∈ A, μ.pmf u₂ * (if u₂ ∘ π ∈ B then (1 : ℝ) else 0) :=
            Finset.sum_congr rfl hshift
        _ = ∑ u₂ ∈ A, ∑ π ∈ G, μ.pmf u₂ * (if u₂ ∘ π ∈ B then (1 : ℝ) else 0) := Finset.sum_comm
        _ = ∑ u₂ ∈ A, μ.pmf u₂ * ∑ π ∈ G, (if u₂ ∘ π ∈ B then (1 : ℝ) else 0) :=
            Finset.sum_congr rfl fun u₂ _ => (Finset.mul_sum ..).symm
    have hper_u2 : ∀ u₂ ∈ A,
        (∑ π ∈ G, if u₂ ∘ π ∈ B then (1 : ℝ) else 0) ≤ (G.card : ℝ) * η := by
      intro u₂ hu₂
      have hu2_typ : (fun i => (x₂ i, u₂ i)) ∈ strongTypicalSet Q₂ n (ε₃ / 16) :=
        (Finset.mem_filter.mp hu₂).2
      have hmk := markov_lemma_conditional_type_perm Q hmk2 hn hε₃ hε₃_le hx12u1 hu2_typ
      have heq : (∑ π ∈ G, if u₂ ∘ π ∈ B then (1 : ℝ) else 0) =
          ∑ π ∈ fiberPermSet x₂,
            if (fun i => (x₁ i, x₂ i, u₁ i, u₂ (π i))) ∉ strongTypicalSet Q n ε₃ then (1 : ℝ) else 0 :=
        Finset.sum_congr rfl fun π _ => by simp [B]
      rw [heq]
      have h1 := (div_le_iff₀ hG_pos).mp hmk
      linarith
    have hmul_le : (G.card : ℝ) * (∑ u₂ ∈ A, μ.pmf u₂ * (if u₂ ∈ B then (1 : ℝ) else 0)) ≤
        (G.card : ℝ) * (η * ∑ u₂ ∈ A, μ.pmf u₂) := by
      rw [havg]
      calc ∑ u₂ ∈ A, μ.pmf u₂ * ∑ π ∈ G, (if u₂ ∘ π ∈ B then (1 : ℝ) else 0)
        _ ≤ ∑ u₂ ∈ A, μ.pmf u₂ * ((G.card : ℝ) * η) :=
            Finset.sum_le_sum fun u₂ hu₂ => mul_le_mul_of_nonneg_left (hper_u2 u₂ hu₂) (μ.nonneg u₂)
        _ = (G.card : ℝ) * (η * ∑ u₂ ∈ A, μ.pmf u₂) := by
            rw [← Finset.sum_mul]; ring
    exact le_of_mul_le_mul_left hmul_le hG_pos
  have hbd := firstCoveringIdx_bad_prob_le μ hMc A B hη_nn hratio
  refine le_trans (le_of_eq ?_) hbd
  refine Finset.sum_congr rfl fun C _ => ?_
  congr 1
  have hiff : ((∃ ℓ : Fin M_c, C ℓ ∈ A) ∧
      (fun i => (x₁ i, x₂ i, u₁ i, C (firstCoveringIdx hMc A C) i)) ∉ strongTypicalSet Q n ε₃) ↔
      ((∃ ℓ : Fin M_c, C ℓ ∈ A) ∧ C (firstCoveringIdx hMc A C) ∈ B) := by
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
  exact if_congr hiff rfl rfl

end TwoEncoderMarkovLemma

/-! ### 4. Operational Berger–Tung Inner Bound Achievability
(Berger 1978; Tung 1978; El Gamal & Kim Theorem 12.1) -/

section BergerTungAchievability

variable {X₁ X₂ Xh₁ Xh₂ : Type*}
  [Fintype X₁] [Fintype X₂] [Fintype Xh₁] [Fintype Xh₂]

open Classical in
/-- Right-slice symmetric form of `jointTypicalSet_slice_indep_prob_le`:
    for every fixed `x : Fin n → α`,
    `P_Y^n({y : (x, y) ∈ A_ε^(n)(P)}) ≤ 2^{-n (I(X; Y) - 3ε)}`. -/
private lemma bt_jointTypicalSet_right_slice_indep_prob_le
    {α β : Type*} [Fintype α] [Fintype β]
    (P : ProbDist (α × β)) (n : ℕ) (ε : ℝ) (x : Fin n → α) :
    ∑ y : Fin n → β, (iidDist P.snd n).pmf y *
        (if (x, y) ∈ jointTypicalSet P n ε then (1 : ℝ) else 0) ≤
      (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo P - 3 * ε))) := by
  let Psw := P.map Prod.swap
  have hfst : Psw.fst = P.snd := by
    rw [← bt_probDist_map_fst, ← bt_probDist_map_snd]; unfold Psw; rw [map_comp_eq]; rfl
  have hsnd : Psw.snd = P.fst := by
    rw [← bt_probDist_map_snd, ← bt_probDist_map_fst]; unfold Psw; rw [map_comp_eq]; rfl
  have hmi : mutualInfo Psw = mutualInfo P := bt_mutualInfo_symm P
  have hH : shannonEntropy Psw = shannonEntropy P :=
    shannonEntropy_map_equiv (Equiv.prodComm α β) P
  have hpmf : ∀ a b, Psw.pmf (b, a) = P.pmf (a, b) := fun a b =>
    bt_probDist_map_equiv_pmf (Equiv.prodComm α β) P (b, a)
  have hiff : ∀ y : Fin n → β, (x, y) ∈ jointTypicalSet P n ε ↔ (y, x) ∈ jointTypicalSet Psw n ε := by
    intro y
    rw [mem_jointTypicalSet, mem_jointTypicalSet]
    dsimp only [zipEquiv]
    have hzip : ((fun i => (x i, y i)) ∈ weakTypicalSet P n ε) ↔
        ((fun i => (y i, x i)) ∈ weakTypicalSet Psw n ε) := by
      simp only [weakTypicalSet, Finset.mem_filter, Finset.mem_univ, true_and, hH]
      have hprod : (iidDist Psw n).pmf (fun i => (y i, x i)) =
          (iidDist P n).pmf (fun i => (x i, y i)) := by
        unfold iidDist; dsimp only
        exact Finset.prod_congr rfl fun i _ => hpmf (x i) (y i)
      rw [hprod]
    rw [hfst, hsnd, hzip]
    tauto
  have hbase := jointTypicalSet_slice_indep_prob_le Psw n ε x
  rw [hfst, hmi] at hbase
  refine le_trans (le_of_eq ?_) hbase
  refine Finset.sum_congr rfl fun y _ => ?_
  congr 1; exact if_congr (hiff y) rfl rfl

/-- Helper: equate two `Finset.univ` sums that differ only in their `Fintype` instance,
    avoiding expensive `whnf` unification of `Pi.instFintype` under `classical`. -/
private lemma bt_sum_fintype_congr {α : Type*} {inst1 inst2 : Fintype α}
    {f g : α → ℝ} (h : ∀ a, f a = g a) :
    @Finset.sum α ℝ _ (@Finset.univ α inst1) f = @Finset.sum α ℝ _ (@Finset.univ α inst2) g := by
  obtain rfl : inst1 = inst2 := Subsingleton.elim _ _
  exact Finset.sum_congr rfl fun a _ => h a

/-- Helper: ensemble covering error bound for the first source `x₁` under `jointIidDist P n`. -/
private lemma bt_achiev_covering_bound_fst
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (P : ProbDist (α × β)) (Q : ProbDist (α × γ)) (hQfst : Q.fst = P.fst)
    (n M : ℕ) {ε_c : ℝ} (hε_c : 0 ≤ ε_c)
    (S : Finset ((Fin n → α) × (Fin n → γ))) (hS_sub : S ⊆ jointTypicalSet Q n ε_c)
    (E : (Fin M → Fin n → γ) → (Fin n → α) → ℝ)
    (hE1 : ∀ C x, (∀ ℓ : Fin M, (x, C ℓ) ∉ S) → E C x = 1)
    (hE0 : ∀ C x, ¬(∀ ℓ : Fin M, (x, C ℓ) ∉ S) → E C x = 0) :
    ∑ C : Fin M → Fin n → γ, (codebookDist Q.snd n M).pmf C *
      (∑ xy : (Fin n → α) × (Fin n → β), (jointIidDist P n).pmf xy * E C xy.1) ≤
      (1 - ∑ xu ∈ S, (jointIidDist Q n).pmf xu) +
        Real.exp (-((M : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Q + 3 * ε_c))))) := by
  have hmarg : ∀ C : Fin M → Fin n → γ,
      (∑ xy : (Fin n → α) × (Fin n → β), (jointIidDist P n).pmf xy * E C xy.1) =
      ∑ x : Fin n → α, (iidDist Q.fst n).pmf x * E C x := fun C => by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    dsimp only; rw [← Finset.sum_mul]
    change (jointIidDist P n).fst.pmf x * E C x = _
    rw [jointIidDist_fst, hQfst]
  simp_rw [hmarg]
  refine le_trans (le_of_eq ?_) (covering_lemma_subset Q n M hε_c S hS_sub)
  refine bt_sum_fintype_congr fun C => congrArg ((codebookDist Q.snd n M).pmf C * ·)
    (bt_sum_fintype_congr fun x => congrArg ((iidDist Q.fst n).pmf x * ·) ?_)
  split_ifs with hc
  · exact hE1 C x hc
  · exact hE0 C x hc

/-- Helper: ensemble covering error bound for the second source `x₂` under `jointIidDist P n`. -/
private lemma bt_achiev_covering_bound_snd
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (P : ProbDist (α × β)) (Q : ProbDist (β × γ)) (hQfst : Q.fst = P.snd)
    (n M : ℕ) {ε_c : ℝ} (hε_c : 0 ≤ ε_c)
    (S : Finset ((Fin n → β) × (Fin n → γ))) (hS_sub : S ⊆ jointTypicalSet Q n ε_c)
    (E : (Fin M → Fin n → γ) → (Fin n → β) → ℝ)
    (hE1 : ∀ C y, (∀ ℓ : Fin M, (y, C ℓ) ∉ S) → E C y = 1)
    (hE0 : ∀ C y, ¬(∀ ℓ : Fin M, (y, C ℓ) ∉ S) → E C y = 0) :
    ∑ C : Fin M → Fin n → γ, (codebookDist Q.snd n M).pmf C *
      (∑ xy : (Fin n → α) × (Fin n → β), (jointIidDist P n).pmf xy * E C xy.2) ≤
      (1 - ∑ xu ∈ S, (jointIidDist Q n).pmf xu) +
        Real.exp (-((M : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Q + 3 * ε_c))))) := by
  have hmarg : ∀ C : Fin M → Fin n → γ,
      (∑ xy : (Fin n → α) × (Fin n → β), (jointIidDist P n).pmf xy * E C xy.2) =
      ∑ y : Fin n → β, (iidDist Q.fst n).pmf y * E C y := fun C => by
    rw [Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun y _ => ?_
    dsimp only; rw [← Finset.sum_mul]
    change (jointIidDist P n).snd.pmf y * E C y = _
    rw [jointIidDist_snd, hQfst]
  simp_rw [hmarg]
  refine le_trans (le_of_eq ?_) (covering_lemma_subset Q n M hε_c S hS_sub)
  refine bt_sum_fintype_congr fun C => congrArg ((codebookDist Q.snd n M).pmf C * ·)
    (bt_sum_fintype_congr fun y => congrArg ((iidDist Q.fst n).pmf y * ·) ?_)
  split_ifs with hc
  · exact hE1 C y hc
  · exact hE0 C y hc

/-- Helper: probability of the zipped strong typical set under `jointIidDist Q n`. -/
private lemma bt_strongTypicalSet_zip_prob {α γ : Type*} [Fintype α] [Fintype γ]
    (Q : ProbDist (α × γ)) (n : ℕ) (ε : ℝ)
    (S : Finset ((Fin n → α) × (Fin n → γ)))
    (hS : ∀ xu, xu ∈ S ↔ zipEquiv α γ n xu ∈ strongTypicalSet Q n ε) :
    ∑ xu ∈ S, (jointIidDist Q n).pmf xu =
      ∑ z ∈ strongTypicalSet Q n ε, (iidDist Q n).pmf z := by
  classical
  have h1 : (∑ xu ∈ S, (jointIidDist Q n).pmf xu) =
      ∑ xu : (Fin n → α) × (Fin n → γ),
        if zipEquiv α γ n xu ∈ strongTypicalSet Q n ε then (jointIidDist Q n).pmf xu else 0 := by
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext xu; simp [hS]
  have h2 : (∑ z ∈ strongTypicalSet Q n ε, (iidDist Q n).pmf z) =
      ∑ z : Fin n → α × γ,
        if z ∈ strongTypicalSet Q n ε then (iidDist Q n).pmf z else 0 := by
    rw [← Finset.sum_filter]; congr 1; ext z; simp
  rw [h1, h2]
  exact Fintype.sum_equiv (zipEquiv α γ n) _ _ (fun _ => rfl)

/-- Helper: single-sided random binning collision bound (used for both `E_bin1` and `E_bin2`). -/
private lemma bt_achiev_binning_single_bound
    {γ : Type*} [Fintype γ]
    (Qu : ProbDist γ) (n M_c M_b : ℕ) (hMb_pos : 0 < M_b)
    (good : (Fin n → γ) → Prop) [DecidablePred good]
    (idx0 : (Fin M_c → Fin n → γ) → Fin M_c)
    {p_slice : ℝ}
    (hslice : ∑ u : Fin n → γ, (iidDist Qu n).pmf u * (if good u then (1 : ℝ) else 0) ≤ p_slice) :
    haveI : Nonempty (Fin M_b) := ⟨⟨0, hMb_pos⟩⟩
    ∑ C : Fin M_c → Fin n → γ, (codebookDist Qu n M_c).pmf C *
      ∑ b : Fin M_c → Fin M_b, (iidDist (ProbDist.uniform (α := Fin M_b)) M_c).pmf b *
        (∑ ℓ' ∈ Finset.univ.erase (idx0 C),
          if b ℓ' = b (idx0 C) ∧ good (C ℓ') then (1 : ℝ) else 0) ≤
      ((M_c : ℝ) / (M_b : ℝ)) * p_slice := by
  have : Nonempty (Fin M_b) := ⟨⟨0, hMb_pos⟩⟩
  let W_C := codebookDist Qu n M_c
  let W_b := iidDist (ProbDist.uniform (α := Fin M_b)) M_c
  have hper_C : ∀ C : Fin M_c → Fin n → γ,
      (∑ b : Fin M_c → Fin M_b, W_b.pmf b *
        ∑ ℓ' ∈ Finset.univ.erase (idx0 C),
          if b ℓ' = b (idx0 C) ∧ good (C ℓ') then (1 : ℝ) else 0) ≤
        (1 / (M_b : ℝ)) * ∑ ℓ' : Fin M_c, if good (C ℓ') then (1 : ℝ) else 0 := by
    intro C
    have hsw : (∑ b : Fin M_c → Fin M_b, W_b.pmf b *
        ∑ ℓ' ∈ Finset.univ.erase (idx0 C),
          if b ℓ' = b (idx0 C) ∧ good (C ℓ') then (1 : ℝ) else 0) =
        ∑ ℓ' ∈ Finset.univ.erase (idx0 C), ∑ b : Fin M_c → Fin M_b, W_b.pmf b *
          (if b ℓ' = b (idx0 C) ∧ good (C ℓ') then (1 : ℝ) else 0) := by
      simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
    rw [hsw]
    have heach : ∀ ℓ' ∈ Finset.univ.erase (idx0 C),
        ∑ b : Fin M_c → Fin M_b, W_b.pmf b *
          (if b ℓ' = b (idx0 C) ∧ good (C ℓ') then (1 : ℝ) else 0) =
          if good (C ℓ') then (1 : ℝ) / (M_b : ℝ) else 0 := fun ℓ' hℓ => by
      by_cases hg : good (C ℓ')
      · simp only [hg, and_true]
        exact bt_uniform_binning_collision_prob hMb_pos (idx0 C) ℓ' (Finset.mem_erase.mp hℓ).1
      · simp [hg]
    rw [Finset.sum_congr rfl heach]
    calc ∑ ℓ' ∈ Finset.univ.erase (idx0 C), (if good (C ℓ') then (1 : ℝ) / (M_b : ℝ) else 0)
      _ ≤ ∑ ℓ' : Fin M_c, (if good (C ℓ') then (1 : ℝ) / (M_b : ℝ) else 0) :=
          Finset.sum_le_univ_sum_of_nonneg fun _ => by split_ifs <;> positivity
      _ = (1 / (M_b : ℝ)) * ∑ ℓ' : Fin M_c, if good (C ℓ') then (1 : ℝ) else 0 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by split_ifs <;> ring
  have hC_bound : (∑ C : Fin M_c → Fin n → γ, W_C.pmf C *
      ((1 / (M_b : ℝ)) * ∑ ℓ' : Fin M_c, if good (C ℓ') then (1 : ℝ) else 0)) ≤
      ((M_c : ℝ) / (M_b : ℝ)) * p_slice := by
    have hswap : (∑ C : Fin M_c → Fin n → γ, W_C.pmf C *
        ((1 / (M_b : ℝ)) * ∑ ℓ' : Fin M_c, if good (C ℓ') then (1 : ℝ) else 0)) =
        (1 / (M_b : ℝ)) * ∑ ℓ' : Fin M_c, ∑ C : Fin M_c → Fin n → γ,
          W_C.pmf C * (if good (C ℓ') then (1 : ℝ) else 0) := by
      rw [Finset.mul_sum]; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ℓ' _ => Finset.sum_congr rfl fun C _ => by ring
    rw [hswap]
    have hcoord : ∀ ℓ' : Fin M_c,
        (∑ C : Fin M_c → Fin n → γ, W_C.pmf C * (if good (C ℓ') then (1 : ℝ) else 0)) =
          ∑ u : Fin n → γ, (iidDist Qu n).pmf u * (if good u then (1 : ℝ) else 0) :=
      fun ℓ' => iidDist_sum_coord (iidDist Qu n) (fun u => if good u then (1 : ℝ) else 0) ℓ'
    simp_rw [hcoord, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hrew : (1 / (M_b : ℝ)) * ((M_c : ℝ) *
        ∑ u : Fin n → γ, (iidDist Qu n).pmf u * (if good u then (1 : ℝ) else 0)) =
        ((M_c : ℝ) / (M_b : ℝ)) *
        ∑ u : Fin n → γ, (iidDist Qu n).pmf u * (if good u then (1 : ℝ) else 0) := by ring
    rw [hrew]
    exact mul_le_mul_of_nonneg_left hslice (by positivity)
  exact le_trans (Finset.sum_le_sum fun C _ => mul_le_mul_of_nonneg_left (hper_C C) (W_C.nonneg C)) hC_bound

/-- Helper: joint two-sided random binning collision bound (used for `E_bin12`). -/
private lemma bt_achiev_binning_joint_bound
    {γ₁ γ₂ : Type*} [Fintype γ₁] [Fintype γ₂] [DecidableEq γ₁] [DecidableEq γ₂]
    (Q₁₂ : ProbDist (γ₁ × γ₂)) (n M_c1 M_c2 M_b1 M_b2 : ℕ)
    (hMb1_pos : 0 < M_b1) (hMb2_pos : 0 < M_b2)
    (A_b : Finset ((Fin n → γ₁) × (Fin n → γ₂)))
    (idx1 : (Fin M_c1 → Fin n → γ₁) → Fin M_c1)
    (idx2 : (Fin M_c2 → Fin n → γ₂) → Fin M_c2) :
    haveI : Nonempty (Fin M_b1) := ⟨⟨0, hMb1_pos⟩⟩
    haveI : Nonempty (Fin M_b2) := ⟨⟨0, hMb2_pos⟩⟩
    ∑ C₁ : Fin M_c1 → Fin n → γ₁, (codebookDist Q₁₂.fst n M_c1).pmf C₁ *
      ∑ C₂ : Fin M_c2 → Fin n → γ₂, (codebookDist Q₁₂.snd n M_c2).pmf C₂ *
        ∑ b₁ : Fin M_c1 → Fin M_b1, (iidDist (ProbDist.uniform (α := Fin M_b1)) M_c1).pmf b₁ *
          ∑ b₂ : Fin M_c2 → Fin M_b2, (iidDist (ProbDist.uniform (α := Fin M_b2)) M_c2).pmf b₂ *
            (∑ ℓ₁' ∈ Finset.univ.erase (idx1 C₁), ∑ ℓ₂' ∈ Finset.univ.erase (idx2 C₂),
              if b₁ ℓ₁' = b₁ (idx1 C₁) ∧ b₂ ℓ₂' = b₂ (idx2 C₂) ∧ (C₁ ℓ₁', C₂ ℓ₂') ∈ A_b
              then (1 : ℝ) else 0) ≤
      (((M_c1 : ℝ) / (M_b1 : ℝ)) * ((M_c2 : ℝ) / (M_b2 : ℝ))) *
        ∑ u ∈ A_b, ((iidDist Q₁₂.fst n).prod (iidDist Q₁₂.snd n)).pmf u := by
  have : Nonempty (Fin M_b1) := ⟨⟨0, hMb1_pos⟩⟩
  have : Nonempty (Fin M_b2) := ⟨⟨0, hMb2_pos⟩⟩
  let W_C1 := codebookDist Q₁₂.fst n M_c1
  let W_C2 := codebookDist Q₁₂.snd n M_c2
  let W_b1 := iidDist (ProbDist.uniform (α := Fin M_b1)) M_c1
  let W_b2 := iidDist (ProbDist.uniform (α := Fin M_b2)) M_c2
  have hper_C : ∀ C₁ C₂,
      (∑ b₁, W_b1.pmf b₁ * ∑ b₂, W_b2.pmf b₂ *
        ∑ ℓ₁' ∈ Finset.univ.erase (idx1 C₁), ∑ ℓ₂' ∈ Finset.univ.erase (idx2 C₂),
          if b₁ ℓ₁' = b₁ (idx1 C₁) ∧ b₂ ℓ₂' = b₂ (idx2 C₂) ∧ (C₁ ℓ₁', C₂ ℓ₂') ∈ A_b
          then (1 : ℝ) else 0) ≤
        (1 / ((M_b1 : ℝ) * (M_b2 : ℝ))) *
          ∑ ℓ₁' : Fin M_c1, ∑ ℓ₂' : Fin M_c2, if (C₁ ℓ₁', C₂ ℓ₂') ∈ A_b then (1 : ℝ) else 0 := by
    intro C₁ C₂
    have hrew : (∑ b₁, W_b1.pmf b₁ * ∑ b₂, W_b2.pmf b₂ *
        ∑ ℓ₁' ∈ Finset.univ.erase (idx1 C₁), ∑ ℓ₂' ∈ Finset.univ.erase (idx2 C₂),
          if b₁ ℓ₁' = b₁ (idx1 C₁) ∧ b₂ ℓ₂' = b₂ (idx2 C₂) ∧ (C₁ ℓ₁', C₂ ℓ₂') ∈ A_b
          then (1 : ℝ) else 0) =
        ∑ ℓ₁' ∈ Finset.univ.erase (idx1 C₁), ∑ ℓ₂' ∈ Finset.univ.erase (idx2 C₂),
          (∑ b₁, W_b1.pmf b₁ * (if b₁ ℓ₁' = b₁ (idx1 C₁) then (1 : ℝ) else 0)) *
          (∑ b₂, W_b2.pmf b₂ * (if b₂ ℓ₂' = b₂ (idx2 C₂) then (1 : ℝ) else 0)) *
          (if (C₁ ℓ₁', C₂ ℓ₂') ∈ A_b then (1 : ℝ) else 0) := by
      have h1 : ∀ b₁ : Fin M_c1 → Fin M_b1, (∑ b₂, W_b2.pmf b₂ * ∑ ℓ₁' ∈ Finset.univ.erase (idx1 C₁),
          ∑ ℓ₂' ∈ Finset.univ.erase (idx2 C₂),
            if b₁ ℓ₁' = b₁ (idx1 C₁) ∧ b₂ ℓ₂' = b₂ (idx2 C₂) ∧ (C₁ ℓ₁', C₂ ℓ₂') ∈ A_b
            then (1 : ℝ) else 0) =
          ∑ ℓ₁' ∈ Finset.univ.erase (idx1 C₁), ∑ ℓ₂' ∈ Finset.univ.erase (idx2 C₂),
            (if b₁ ℓ₁' = b₁ (idx1 C₁) then (1 : ℝ) else 0) *
            (∑ b₂, W_b2.pmf b₂ * (if b₂ ℓ₂' = b₂ (idx2 C₂) then (1 : ℝ) else 0)) *
            (if (C₁ ℓ₁', C₂ ℓ₂') ∈ A_b then (1 : ℝ) else 0) := by
        intro b₁
        have hpush : ∀ b₂ : Fin M_c2 → Fin M_b2,
            W_b2.pmf b₂ * ∑ ℓ₁' ∈ Finset.univ.erase (idx1 C₁), ∑ ℓ₂' ∈ Finset.univ.erase (idx2 C₂),
              (if b₁ ℓ₁' = b₁ (idx1 C₁) ∧ b₂ ℓ₂' = b₂ (idx2 C₂) ∧ (C₁ ℓ₁', C₂ ℓ₂') ∈ A_b then (1 : ℝ) else 0) =
            ∑ ℓ₁' ∈ Finset.univ.erase (idx1 C₁), ∑ ℓ₂' ∈ Finset.univ.erase (idx2 C₂),
              W_b2.pmf b₂ *
                (if b₁ ℓ₁' = b₁ (idx1 C₁) ∧ b₂ ℓ₂' = b₂ (idx2 C₂) ∧ (C₁ ℓ₁', C₂ ℓ₂') ∈ A_b then (1 : ℝ) else 0) :=
          fun b₂ => by rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => Finset.mul_sum ..
        simp_rw [hpush]; rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ℓ₁' _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ℓ₂' _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun b₂ _ => ?_
        by_cases hA : b₁ ℓ₁' = b₁ (idx1 C₁) <;>
          by_cases hB : b₂ ℓ₂' = b₂ (idx2 C₂) <;>
          by_cases hC : (C₁ ℓ₁', C₂ ℓ₂') ∈ A_b <;> simp [hA, hB, hC]
      have hpush1 : ∀ b₁ : Fin M_c1 → Fin M_b1,
          W_b1.pmf b₁ * ∑ ℓ₁' ∈ Finset.univ.erase (idx1 C₁), ∑ ℓ₂' ∈ Finset.univ.erase (idx2 C₂),
            (if b₁ ℓ₁' = b₁ (idx1 C₁) then (1 : ℝ) else 0) *
            (∑ b₂, W_b2.pmf b₂ * (if b₂ ℓ₂' = b₂ (idx2 C₂) then (1 : ℝ) else 0)) *
            (if (C₁ ℓ₁', C₂ ℓ₂') ∈ A_b then (1 : ℝ) else 0) =
          ∑ ℓ₁' ∈ Finset.univ.erase (idx1 C₁), ∑ ℓ₂' ∈ Finset.univ.erase (idx2 C₂),
            W_b1.pmf b₁ *
              ((if b₁ ℓ₁' = b₁ (idx1 C₁) then (1 : ℝ) else 0) *
              (∑ b₂, W_b2.pmf b₂ * (if b₂ ℓ₂' = b₂ (idx2 C₂) then (1 : ℝ) else 0)) *
              (if (C₁ ℓ₁', C₂ ℓ₂') ∈ A_b then (1 : ℝ) else 0)) :=
        fun b₁ => by rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => Finset.mul_sum ..
      simp_rw [h1, hpush1]; rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ℓ₁' _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ℓ₂' _ => ?_
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun b₁ _ => by ring
    rw [hrew]
    have hstep : (∑ ℓ₁' ∈ Finset.univ.erase (idx1 C₁), ∑ ℓ₂' ∈ Finset.univ.erase (idx2 C₂),
        (∑ b₁, W_b1.pmf b₁ * (if b₁ ℓ₁' = b₁ (idx1 C₁) then (1 : ℝ) else 0)) *
        (∑ b₂, W_b2.pmf b₂ * (if b₂ ℓ₂' = b₂ (idx2 C₂) then (1 : ℝ) else 0)) *
        (if (C₁ ℓ₁', C₂ ℓ₂') ∈ A_b then (1 : ℝ) else 0)) =
        ∑ ℓ₁' ∈ Finset.univ.erase (idx1 C₁), ∑ ℓ₂' ∈ Finset.univ.erase (idx2 C₂),
          (1 / ((M_b1 : ℝ) * (M_b2 : ℝ))) * (if (C₁ ℓ₁', C₂ ℓ₂') ∈ A_b then (1 : ℝ) else 0) :=
      Finset.sum_congr rfl fun ℓ₁' h1 => Finset.sum_congr rfl fun ℓ₂' h2 => by
        rw [bt_uniform_binning_collision_prob hMb1_pos (idx1 C₁) ℓ₁' (Finset.mem_erase.mp h1).1,
            bt_uniform_binning_collision_prob hMb2_pos (idx2 C₂) ℓ₂' (Finset.mem_erase.mp h2).1]
        ring
    rw [hstep]
    calc ∑ ℓ₁' ∈ Finset.univ.erase (idx1 C₁), ∑ ℓ₂' ∈ Finset.univ.erase (idx2 C₂),
          (1 / ((M_b1 : ℝ) * (M_b2 : ℝ))) * (if (C₁ ℓ₁', C₂ ℓ₂') ∈ A_b then (1 : ℝ) else 0)
      _ ≤ ∑ ℓ₁' ∈ Finset.univ.erase (idx1 C₁), ∑ ℓ₂' : Fin M_c2,
          (1 / ((M_b1 : ℝ) * (M_b2 : ℝ))) * (if (C₁ ℓ₁', C₂ ℓ₂') ∈ A_b then (1 : ℝ) else 0) :=
          Finset.sum_le_sum fun ℓ₁' _ =>
            Finset.sum_le_univ_sum_of_nonneg fun _ => by split_ifs <;> positivity
      _ ≤ ∑ ℓ₁' : Fin M_c1, ∑ ℓ₂' : Fin M_c2,
          (1 / ((M_b1 : ℝ) * (M_b2 : ℝ))) * (if (C₁ ℓ₁', C₂ ℓ₂') ∈ A_b then (1 : ℝ) else 0) :=
          Finset.sum_le_univ_sum_of_nonneg fun _ =>
            Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity
      _ = (1 / ((M_b1 : ℝ) * (M_b2 : ℝ))) *
          ∑ ℓ₁' : Fin M_c1, ∑ ℓ₂' : Fin M_c2, if (C₁ ℓ₁', C₂ ℓ₂') ∈ A_b then (1 : ℝ) else 0 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => (Finset.mul_sum ..).symm
  have hC12_eval : (∑ C₁, W_C1.pmf C₁ * ∑ C₂, W_C2.pmf C₂ *
      ((1 / ((M_b1 : ℝ) * (M_b2 : ℝ))) *
        ∑ ℓ₁' : Fin M_c1, ∑ ℓ₂' : Fin M_c2, if (C₁ ℓ₁', C₂ ℓ₂') ∈ A_b then (1 : ℝ) else 0)) =
      (((M_c1 : ℝ) / (M_b1 : ℝ)) * ((M_c2 : ℝ) / (M_b2 : ℝ))) *
        ∑ u ∈ A_b, ((iidDist Q₁₂.fst n).prod (iidDist Q₁₂.snd n)).pmf u := by
    have hinner_C2 : ∀ C₁ : Fin M_c1 → Fin n → γ₁, (∑ C₂, W_C2.pmf C₂ *
        ((1 / ((M_b1 : ℝ) * (M_b2 : ℝ))) *
          ∑ ℓ₁' : Fin M_c1, ∑ ℓ₂' : Fin M_c2, if (C₁ ℓ₁', C₂ ℓ₂') ∈ A_b then (1 : ℝ) else 0)) =
        (1 / ((M_b1 : ℝ) * (M_b2 : ℝ))) * (M_c2 : ℝ) *
          ∑ ℓ₁' : Fin M_c1, ∑ u₂ : Fin n → γ₂, (iidDist Q₁₂.snd n).pmf u₂ *
            (if (C₁ ℓ₁', u₂) ∈ A_b then (1 : ℝ) else 0) := by
      intro C₁
      have hs1 : (∑ C₂, W_C2.pmf C₂ * ((1 / ((M_b1 : ℝ) * (M_b2 : ℝ))) *
          ∑ ℓ₁' : Fin M_c1, ∑ ℓ₂' : Fin M_c2, if (C₁ ℓ₁', C₂ ℓ₂') ∈ A_b then (1 : ℝ) else 0)) =
          (1 / ((M_b1 : ℝ) * (M_b2 : ℝ))) * ∑ ℓ₁' : Fin M_c1, ∑ ℓ₂' : Fin M_c2,
            ∑ C₂, W_C2.pmf C₂ * (if (C₁ ℓ₁', C₂ ℓ₂') ∈ A_b then (1 : ℝ) else 0) := by
        rw [Finset.mul_sum]; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ℓ₁' _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ℓ₂' _ => Finset.sum_congr rfl fun C₂ _ => by ring
      rw [hs1]
      have hc2 : ∀ ℓ₁' ℓ₂', (∑ C₂, W_C2.pmf C₂ * (if (C₁ ℓ₁', C₂ ℓ₂') ∈ A_b then (1 : ℝ) else 0)) =
          ∑ u₂ : Fin n → γ₂, (iidDist Q₁₂.snd n).pmf u₂ * (if (C₁ ℓ₁', u₂) ∈ A_b then (1 : ℝ) else 0) :=
        fun ℓ₁' ℓ₂' => iidDist_sum_coord (iidDist Q₁₂.snd n)
          (fun u₂ => if (C₁ ℓ₁', u₂) ∈ A_b then (1 : ℝ) else 0) ℓ₂'
      simp_rw [hc2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← Finset.mul_sum]; ring
    simp_rw [hinner_C2]
    have hs2 : (∑ C₁, W_C1.pmf C₁ * ((1 / ((M_b1 : ℝ) * (M_b2 : ℝ))) * (M_c2 : ℝ) *
        ∑ ℓ₁' : Fin M_c1, ∑ u₂ : Fin n → γ₂, (iidDist Q₁₂.snd n).pmf u₂ *
          (if (C₁ ℓ₁', u₂) ∈ A_b then (1 : ℝ) else 0))) =
        (1 / ((M_b1 : ℝ) * (M_b2 : ℝ))) * (M_c2 : ℝ) *
          ∑ ℓ₁' : Fin M_c1, ∑ C₁, W_C1.pmf C₁ *
            (∑ u₂ : Fin n → γ₂, (iidDist Q₁₂.snd n).pmf u₂ *
              (if (C₁ ℓ₁', u₂) ∈ A_b then (1 : ℝ) else 0)) := by
      calc ∑ C₁, W_C1.pmf C₁ * ((1 / ((M_b1 : ℝ) * (M_b2 : ℝ))) * (M_c2 : ℝ) *
            ∑ ℓ₁' : Fin M_c1, ∑ u₂ : Fin n → γ₂, (iidDist Q₁₂.snd n).pmf u₂ *
              (if (C₁ ℓ₁', u₂) ∈ A_b then (1 : ℝ) else 0))
        _ = ∑ C₁, ∑ ℓ₁' : Fin M_c1, (1 / ((M_b1 : ℝ) * (M_b2 : ℝ))) * (M_c2 : ℝ) *
              (W_C1.pmf C₁ * ∑ u₂ : Fin n → γ₂, (iidDist Q₁₂.snd n).pmf u₂ *
                (if (C₁ ℓ₁', u₂) ∈ A_b then (1 : ℝ) else 0)) := by
            refine Finset.sum_congr rfl fun C₁ _ => ?_
            rw [← mul_assoc, Finset.mul_sum]
            refine Finset.sum_congr rfl fun ℓ₁' _ => by ring
        _ = ∑ ℓ₁' : Fin M_c1, ∑ C₁, (1 / ((M_b1 : ℝ) * (M_b2 : ℝ))) * (M_c2 : ℝ) *
              (W_C1.pmf C₁ * ∑ u₂ : Fin n → γ₂, (iidDist Q₁₂.snd n).pmf u₂ *
                (if (C₁ ℓ₁', u₂) ∈ A_b then (1 : ℝ) else 0)) := Finset.sum_comm
        _ = _ := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun ℓ₁' _ => (Finset.mul_sum ..).symm
    rw [hs2]
    have hc1 : ∀ ℓ₁' : Fin M_c1,
        (∑ C₁, W_C1.pmf C₁ * ∑ u₂ : Fin n → γ₂, (iidDist Q₁₂.snd n).pmf u₂ *
          (if (C₁ ℓ₁', u₂) ∈ A_b then (1 : ℝ) else 0)) =
        ∑ u ∈ A_b, ((iidDist Q₁₂.fst n).prod (iidDist Q₁₂.snd n)).pmf u := by
      intro ℓ₁'
      dsimp only [W_C1]; unfold codebookDist
      rw [iidDist_sum_coord (iidDist Q₁₂.fst n)
        (fun u₁ => ∑ u₂ : Fin n → γ₂, (iidDist Q₁₂.snd n).pmf u₂ * (if (u₁, u₂) ∈ A_b then (1 : ℝ) else 0)) ℓ₁']
      have hrew : (∑ u ∈ A_b, ((iidDist Q₁₂.fst n).prod (iidDist Q₁₂.snd n)).pmf u) =
          ∑ u : (Fin n → γ₁) × (Fin n → γ₂),
            if u ∈ A_b then ((iidDist Q₁₂.fst n).prod (iidDist Q₁₂.snd n)).pmf u else 0 := by
        rw [← Finset.sum_filter]; congr 1; ext u; simp
      rw [hrew, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun u₁ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u₂ _ => by dsimp only [ProbDist.prod]; split_ifs <;> ring
    simp_rw [hc1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  exact le_trans
    (Finset.sum_le_sum fun C₁ _ => mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun C₂ _ => mul_le_mul_of_nonneg_left (hper_C C₁ C₂) (W_C2.nonneg C₂))
      (W_C1.nonneg C₁))
    (le_of_eq hC12_eval)

/-- Helper: combine the 7 independent ensemble error bounds over the product distribution
    `(W_C1.prod W_C2).prod (W_b1.prod W_b2)` into the total `9 * c` bound. -/
private lemma bt_achiev_combine_ensemble
    {α₁ α₂ β₁ β₂ γ : Type*} [Fintype α₁] [Fintype α₂] [Fintype β₁] [Fintype β₂] [Fintype γ]
    (W_C1 : ProbDist α₁) (W_C2 : ProbDist α₂) (W_b1 : ProbDist β₁) (W_b2 : ProbDist β₂)
    (W_xy : ProbDist γ)
    (E1 : α₁ → γ → ℝ) (E2 : α₂ → γ → ℝ) (E3 : α₁ → γ → ℝ)
    (E4 : α₁ → α₂ → γ → ℝ) (E5 : α₁ → α₂ → β₁ → γ → ℝ)
    (E6 : α₁ → α₂ → β₂ → γ → ℝ) (E7 : α₁ → α₂ → β₁ → β₂ → γ → ℝ)
    {c : ℝ}
    (h1 : ∑ C₁, W_C1.pmf C₁ * ∑ xy, W_xy.pmf xy * E1 C₁ xy ≤ c + c)
    (h2 : ∑ C₂, W_C2.pmf C₂ * ∑ xy, W_xy.pmf xy * E2 C₂ xy ≤ c + c)
    (h3 : ∀ C₁, ∑ xy, W_xy.pmf xy * E3 C₁ xy ≤ c)
    (h4 : ∀ C₁ xy, ∑ C₂, W_C2.pmf C₂ * E4 C₁ C₂ xy ≤ c)
    (h5 : ∀ C₂ xy, ∑ C₁, W_C1.pmf C₁ * ∑ b₁, W_b1.pmf b₁ * E5 C₁ C₂ b₁ xy ≤ c)
    (h6 : ∀ C₁ xy, ∑ C₂, W_C2.pmf C₂ * ∑ b₂, W_b2.pmf b₂ * E6 C₁ C₂ b₂ xy ≤ c)
    (h7 : ∀ xy, ∑ C₁, W_C1.pmf C₁ * ∑ C₂, W_C2.pmf C₂ *
      ∑ b₁, W_b1.pmf b₁ * ∑ b₂, W_b2.pmf b₂ * E7 C₁ C₂ b₁ b₂ xy ≤ c) :
    ∑ ω : (α₁ × α₂) × (β₁ × β₂), ((W_C1.prod W_C2).prod (W_b1.prod W_b2)).pmf ω *
      (∑ xy : γ, W_xy.pmf xy *
        (E1 ω.1.1 xy + E2 ω.1.2 xy + E3 ω.1.1 xy + E4 ω.1.1 ω.1.2 xy +
         E5 ω.1.1 ω.1.2 ω.2.1 xy + E6 ω.1.1 ω.1.2 ω.2.2 xy +
         E7 ω.1.1 ω.1.2 ω.2.1 ω.2.2 xy)) ≤ 9 * c := by
  let W_ens := (W_C1.prod W_C2).prod (W_b1.prod W_b2)
  have hW_ens_exp : ∀ f : (α₁ × α₂) × (β₁ × β₂) → ℝ,
      ∑ ω, W_ens.pmf ω * f ω =
        ∑ C₁, W_C1.pmf C₁ * ∑ C₂, W_C2.pmf C₂ * ∑ b₁, W_b1.pmf b₁ * ∑ b₂, W_b2.pmf b₂ *
          f ((C₁, C₂), (b₁, b₂)) := by
    intro f
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun C₁ _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun C₂ _ => ?_
    rw [← mul_assoc, Finset.mul_sum]; refine Finset.sum_congr rfl fun b₁ _ => ?_
    rw [← mul_assoc, Finset.mul_sum]; refine Finset.sum_congr rfl fun b₂ _ => ?_
    dsimp [W_ens, ProbDist.prod]; ring
  have hsplit : ∀ ω : (α₁ × α₂) × (β₁ × β₂),
      (∑ xy : γ, W_xy.pmf xy *
        (E1 ω.1.1 xy + E2 ω.1.2 xy + E3 ω.1.1 xy + E4 ω.1.1 ω.1.2 xy +
         E5 ω.1.1 ω.1.2 ω.2.1 xy + E6 ω.1.1 ω.1.2 ω.2.2 xy +
         E7 ω.1.1 ω.1.2 ω.2.1 ω.2.2 xy)) =
      (∑ xy, W_xy.pmf xy * E1 ω.1.1 xy) + (∑ xy, W_xy.pmf xy * E2 ω.1.2 xy) +
      (∑ xy, W_xy.pmf xy * E3 ω.1.1 xy) + (∑ xy, W_xy.pmf xy * E4 ω.1.1 ω.1.2 xy) +
      (∑ xy, W_xy.pmf xy * E5 ω.1.1 ω.1.2 ω.2.1 xy) +
      (∑ xy, W_xy.pmf xy * E6 ω.1.1 ω.1.2 ω.2.2 xy) +
      (∑ xy, W_xy.pmf xy * E7 ω.1.1 ω.1.2 ω.2.1 ω.2.2 xy) := by
    intro ω; simp_rw [mul_add, Finset.sum_add_distrib]
  simp_rw [hsplit, mul_add, Finset.sum_add_distrib]
  have hT1 : (∑ ω, W_ens.pmf ω * ∑ xy, W_xy.pmf xy * E1 ω.1.1 xy) ≤ c + c := by
    rw [hW_ens_exp]
    have hs : ∀ C₁, (∑ C₂, W_C2.pmf C₂ * ∑ b₁, W_b1.pmf b₁ * ∑ b₂, W_b2.pmf b₂ *
        ∑ xy, W_xy.pmf xy * E1 C₁ xy) = ∑ xy, W_xy.pmf xy * E1 C₁ xy := fun C₁ => by
      simp_rw [← Finset.sum_mul, W_b2.sum_one, one_mul, W_b1.sum_one, one_mul, W_C2.sum_one, one_mul]
    simp_rw [hs]; exact h1
  have hT2 : (∑ ω, W_ens.pmf ω * ∑ xy, W_xy.pmf xy * E2 ω.1.2 xy) ≤ c + c := by
    rw [hW_ens_exp]
    have hs : ∀ C₂ : α₂, (∑ b₁, W_b1.pmf b₁ * ∑ b₂, W_b2.pmf b₂ *
        ∑ xy, W_xy.pmf xy * E2 C₂ xy) = ∑ xy, W_xy.pmf xy * E2 C₂ xy := fun _ => by
      simp_rw [← Finset.sum_mul, W_b2.sum_one, one_mul, W_b1.sum_one, one_mul]
    simp_rw [hs, ← Finset.sum_mul, W_C1.sum_one, one_mul]; exact h2
  have hT3 : (∑ ω, W_ens.pmf ω * ∑ xy, W_xy.pmf xy * E3 ω.1.1 xy) ≤ c := by
    rw [hW_ens_exp]
    have hs : ∀ C₁ : α₁, (∑ C₂, W_C2.pmf C₂ * ∑ b₁, W_b1.pmf b₁ * ∑ b₂, W_b2.pmf b₂ *
        ∑ xy, W_xy.pmf xy * E3 C₁ xy) = ∑ xy, W_xy.pmf xy * E3 C₁ xy := fun C₁ => by
      simp_rw [← Finset.sum_mul, W_b2.sum_one, one_mul, W_b1.sum_one, one_mul, W_C2.sum_one, one_mul]
    simp_rw [hs]
    calc ∑ C₁, W_C1.pmf C₁ * ∑ xy, W_xy.pmf xy * E3 C₁ xy
      _ ≤ ∑ C₁, W_C1.pmf C₁ * c := Finset.sum_le_sum fun C₁ _ => mul_le_mul_of_nonneg_left (h3 C₁) (W_C1.nonneg C₁)
      _ = c := by rw [← Finset.sum_mul, W_C1.sum_one, one_mul]
  have hT4 : (∑ ω, W_ens.pmf ω * ∑ xy, W_xy.pmf xy * E4 ω.1.1 ω.1.2 xy) ≤ c := by
    rw [hW_ens_exp]
    have hs : ∀ (C₁ : α₁) (C₂ : α₂), (∑ b₁, W_b1.pmf b₁ * ∑ b₂, W_b2.pmf b₂ *
        ∑ xy, W_xy.pmf xy * E4 C₁ C₂ xy) = ∑ xy, W_xy.pmf xy * E4 C₁ C₂ xy := fun _ _ => by
      simp_rw [← Finset.sum_mul, W_b2.sum_one, one_mul, W_b1.sum_one, one_mul]
    simp_rw [hs]
    have hper : ∀ C₁ : α₁, (∑ C₂, W_C2.pmf C₂ * ∑ xy, W_xy.pmf xy * E4 C₁ C₂ xy) ≤ c := by
      intro C₁
      have hsw : (∑ C₂, W_C2.pmf C₂ * ∑ xy, W_xy.pmf xy * E4 C₁ C₂ xy) =
          ∑ xy, W_xy.pmf xy * ∑ C₂, W_C2.pmf C₂ * E4 C₁ C₂ xy := by
        simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun xy _ => Finset.sum_congr rfl fun C₂ _ => by ring
      rw [hsw]
      calc ∑ xy, W_xy.pmf xy * ∑ C₂, W_C2.pmf C₂ * E4 C₁ C₂ xy
        _ ≤ ∑ xy, W_xy.pmf xy * c :=
            Finset.sum_le_sum fun xy _ => mul_le_mul_of_nonneg_left (h4 C₁ xy) (W_xy.nonneg xy)
        _ = c := by rw [← Finset.sum_mul, W_xy.sum_one, one_mul]
    calc ∑ C₁, W_C1.pmf C₁ * ∑ C₂, W_C2.pmf C₂ * ∑ xy, W_xy.pmf xy * E4 C₁ C₂ xy
      _ ≤ ∑ C₁, W_C1.pmf C₁ * c := Finset.sum_le_sum fun C₁ _ => mul_le_mul_of_nonneg_left (hper C₁) (W_C1.nonneg C₁)
      _ = c := by rw [← Finset.sum_mul, W_C1.sum_one, one_mul]
  have hT5 : (∑ ω, W_ens.pmf ω * ∑ xy, W_xy.pmf xy * E5 ω.1.1 ω.1.2 ω.2.1 xy) ≤ c := by
    rw [hW_ens_exp]
    have hs : ∀ (C₁ : α₁) (C₂ : α₂) (b₁ : β₁), (∑ b₂, W_b2.pmf b₂ * ∑ xy, W_xy.pmf xy * E5 C₁ C₂ b₁ xy) =
        ∑ xy, W_xy.pmf xy * E5 C₁ C₂ b₁ xy := fun _ _ _ => by rw [← Finset.sum_mul, W_b2.sum_one, one_mul]
    simp_rw [hs]
    have hsw : (∑ C₁, W_C1.pmf C₁ * ∑ C₂, W_C2.pmf C₂ * ∑ b₁, W_b1.pmf b₁ *
        ∑ xy, W_xy.pmf xy * E5 C₁ C₂ b₁ xy) =
        ∑ C₂, W_C2.pmf C₂ * ∑ xy, W_xy.pmf xy *
          ∑ C₁, W_C1.pmf C₁ * ∑ b₁, W_b1.pmf b₁ * E5 C₁ C₂ b₁ xy := by
      simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun C₂ _ => ?_
      trans (∑ C₁, ∑ xy, ∑ b₁, W_C1.pmf C₁ * (W_C2.pmf C₂ * (W_b1.pmf b₁ * (W_xy.pmf xy * E5 C₁ C₂ b₁ xy))))
      · refine Finset.sum_congr rfl fun C₁ _ => ?_
        rw [Finset.sum_comm]
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun xy _ => Finset.sum_congr rfl fun C₁ _ =>
          Finset.sum_congr rfl fun b₁ _ => by ring
    rw [hsw]
    calc ∑ C₂, W_C2.pmf C₂ * ∑ xy, W_xy.pmf xy *
          ∑ C₁, W_C1.pmf C₁ * ∑ b₁, W_b1.pmf b₁ * E5 C₁ C₂ b₁ xy
      _ ≤ ∑ C₂, W_C2.pmf C₂ * ∑ xy, W_xy.pmf xy * c :=
          Finset.sum_le_sum fun C₂ _ => mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun xy _ => mul_le_mul_of_nonneg_left (h5 C₂ xy) (W_xy.nonneg xy))
            (W_C2.nonneg C₂)
      _ = c := by simp_rw [← Finset.sum_mul, W_xy.sum_one, one_mul, W_C2.sum_one, one_mul]
  have hT6 : (∑ ω, W_ens.pmf ω * ∑ xy, W_xy.pmf xy * E6 ω.1.1 ω.1.2 ω.2.2 xy) ≤ c := by
    rw [hW_ens_exp]
    have hs : ∀ (C₁ : α₁) (C₂ : α₂), (∑ b₁, W_b1.pmf b₁ * ∑ b₂, W_b2.pmf b₂ *
        ∑ xy, W_xy.pmf xy * E6 C₁ C₂ b₂ xy) =
        ∑ b₂, W_b2.pmf b₂ * ∑ xy, W_xy.pmf xy * E6 C₁ C₂ b₂ xy := fun _ _ => by
      rw [← Finset.sum_mul, W_b1.sum_one, one_mul]
    simp_rw [hs]
    have hsw : (∑ C₁, W_C1.pmf C₁ * ∑ C₂, W_C2.pmf C₂ * ∑ b₂, W_b2.pmf b₂ *
        ∑ xy, W_xy.pmf xy * E6 C₁ C₂ b₂ xy) =
        ∑ C₁, W_C1.pmf C₁ * ∑ xy, W_xy.pmf xy *
          ∑ C₂, W_C2.pmf C₂ * ∑ b₂, W_b2.pmf b₂ * E6 C₁ C₂ b₂ xy := by
      refine Finset.sum_congr rfl fun C₁ _ => congrArg _ ?_
      simp_rw [Finset.mul_sum]
      trans (∑ C₂, ∑ xy, ∑ b₂, W_C2.pmf C₂ * (W_b2.pmf b₂ * (W_xy.pmf xy * E6 C₁ C₂ b₂ xy)))
      · refine Finset.sum_congr rfl fun C₂ _ => ?_
        rw [Finset.sum_comm]
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun xy _ => Finset.sum_congr rfl fun C₂ _ =>
          Finset.sum_congr rfl fun b₂ _ => by ring
    rw [hsw]
    calc ∑ C₁, W_C1.pmf C₁ * ∑ xy, W_xy.pmf xy *
          ∑ C₂, W_C2.pmf C₂ * ∑ b₂, W_b2.pmf b₂ * E6 C₁ C₂ b₂ xy
      _ ≤ ∑ C₁, W_C1.pmf C₁ * ∑ xy, W_xy.pmf xy * c :=
          Finset.sum_le_sum fun C₁ _ => mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun xy _ => mul_le_mul_of_nonneg_left (h6 C₁ xy) (W_xy.nonneg xy))
            (W_C1.nonneg C₁)
      _ = c := by simp_rw [← Finset.sum_mul, W_xy.sum_one, one_mul, W_C1.sum_one, one_mul]
  have hT7 : (∑ ω, W_ens.pmf ω * ∑ xy, W_xy.pmf xy * E7 ω.1.1 ω.1.2 ω.2.1 ω.2.2 xy) ≤ c := by
    have hsw : (∑ ω, W_ens.pmf ω * ∑ xy, W_xy.pmf xy * E7 ω.1.1 ω.1.2 ω.2.1 ω.2.2 xy) =
        ∑ xy, W_xy.pmf xy *
          ∑ C₁, W_C1.pmf C₁ * ∑ C₂, W_C2.pmf C₂ *
            ∑ b₁, W_b1.pmf b₁ * ∑ b₂, W_b2.pmf b₂ * E7 C₁ C₂ b₁ b₂ xy := by
      calc ∑ ω, W_ens.pmf ω * ∑ xy, W_xy.pmf xy * E7 ω.1.1 ω.1.2 ω.2.1 ω.2.2 xy
        _ = ∑ ω, ∑ xy, W_ens.pmf ω * (W_xy.pmf xy * E7 ω.1.1 ω.1.2 ω.2.1 ω.2.2 xy) :=
            Finset.sum_congr rfl fun ω _ => Finset.mul_sum ..
        _ = ∑ xy, ∑ ω, W_ens.pmf ω * (W_xy.pmf xy * E7 ω.1.1 ω.1.2 ω.2.1 ω.2.2 xy) :=
            Finset.sum_comm
        _ = ∑ xy, W_xy.pmf xy *
              ∑ C₁, W_C1.pmf C₁ * ∑ C₂, W_C2.pmf C₂ *
                ∑ b₁, W_b1.pmf b₁ * ∑ b₂, W_b2.pmf b₂ * E7 C₁ C₂ b₁ b₂ xy := by
            refine Finset.sum_congr rfl fun xy _ => ?_
            have ha : (∑ ω, W_ens.pmf ω * (W_xy.pmf xy * E7 ω.1.1 ω.1.2 ω.2.1 ω.2.2 xy)) =
                W_xy.pmf xy * ∑ ω, W_ens.pmf ω * E7 ω.1.1 ω.1.2 ω.2.1 ω.2.2 xy := by
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun ω _ => by ring
            rw [ha, hW_ens_exp]
    rw [hsw]
    calc ∑ xy, W_xy.pmf xy *
          ∑ C₁, W_C1.pmf C₁ * ∑ C₂, W_C2.pmf C₂ *
            ∑ b₁, W_b1.pmf b₁ * ∑ b₂, W_b2.pmf b₂ * E7 C₁ C₂ b₁ b₂ xy
      _ ≤ ∑ xy, W_xy.pmf xy * c :=
          Finset.sum_le_sum fun xy _ => mul_le_mul_of_nonneg_left (h7 xy) (W_xy.nonneg xy)
      _ = c := by rw [← Finset.sum_mul, W_xy.sum_one, one_mul]
  linarith only [hT1, hT2, hT3, hT4, hT5, hT6, hT7]

open scoped Classical in
omit [Fintype Xh₁] [Fintype Xh₂] in
/-- Helper: deterministic pointwise distortion bound for BOTH distortions simultaneously
    in the Berger–Tung random-binning / covering scheme. -/
private lemma bt_achiev_pointwise_dist
    {kU₁ kU₂ : ℕ}
    (d₁ : Distortion X₁ Xh₁) (d₂ : Distortion X₂ Xh₂)
    (Q : ProbDist (X₁ × X₂ × Fin kU₁ × Fin kU₂))
    (g₁ : Fin kU₁ × Fin kU₂ → Xh₁) (g₂ : Fin kU₁ × Fin kU₂ → Xh₂)
    {n M_c1 M_c2 M_b1 M_b2 : ℕ} (hn_pos : 0 < n) (hMc1_pos : 0 < M_c1) (hMc2_pos : 0 < M_c2)
    {ε₂ ε₃ δ dmax : ℝ} (hδ0 : 0 ≤ δ) (hdmax0 : 0 ≤ dmax)
    (hd1_le : ∀ x xh, d₁.dist x xh ≤ dmax) (hd2_le : ∀ x xh, d₂.dist x xh ≤ dmax)
    (hε₃_Ed₁ : ε₃ * (∑ t, Q.pmf t * d₁.dist t.1 (g₁ (t.2.2.1, t.2.2.2))) ≤ δ / 2)
    (hε₃_Ed₂ : ε₃ * (∑ t, Q.pmf t * d₂.dist t.2.1 (g₂ (t.2.2.1, t.2.2.2))) ≤ δ / 2)
    (S₁ : Finset ((Fin n → X₁) × (Fin n → Fin kU₁)))
    (S₂ : Finset ((Fin n → X₂) × (Fin n → Fin kU₂)))
    (A₁ : (Fin n → X₁) → Finset (Fin n → Fin kU₁))
    (A₂ : (Fin n → X₂) → Finset (Fin n → Fin kU₂))
    (A_b : Finset ((Fin n → Fin kU₁) × (Fin n → Fin kU₂)))
    (hS1_A1 : ∀ x₁ u₁, (x₁, u₁) ∈ S₁ → u₁ ∈ A₁ x₁)
    (hS2_A2 : ∀ x₂ u₂, (x₂, u₂) ∈ S₂ → u₂ ∈ A₂ x₂)
    (hU12_Ab : ∀ u₁ u₂,
      (fun i => (u₁ i, u₂ i)) ∈ strongTypicalSet (Q.map (fun t => (t.2.2.1, t.2.2.2))) n ε₃ →
      (u₁, u₂) ∈ A_b)
    (C₁ : Fin M_c1 → Fin n → Fin kU₁) (C₂ : Fin M_c2 → Fin n → Fin kU₂)
    (b₁ : Fin M_c1 → Fin M_b1) (b₂ : Fin M_c2 → Fin M_b2)
    (x₁ : Fin n → X₁) (x₂ : Fin n → X₂) :
    let idx₁ := firstCoveringIdx hMc1_pos (A₁ x₁) C₁
    let idx₂ := firstCoveringIdx hMc2_pos (A₂ x₂) C₂
    let decIdx :=
      if h : ∃! p : Fin M_c1 × Fin M_c2, b₁ p.1 = b₁ idx₁ ∧ b₂ p.2 = b₂ idx₂ ∧ (C₁ p.1, C₂ p.2) ∈ A_b
      then Classical.choose h else (⟨0, hMc1_pos⟩, ⟨0, hMc2_pos⟩)
    let E_tot : ℝ :=
      (if ∀ ℓ : Fin M_c1, (x₁, C₁ ℓ) ∉ S₁ then (1 : ℝ) else 0) +
      (if ∀ ℓ : Fin M_c2, (x₂, C₂ ℓ) ∉ S₂ then (1 : ℝ) else 0) +
      (if (∃ ℓ : Fin M_c1, C₁ ℓ ∈ A₁ x₁) ∧
          (fun i => (x₁ i, x₂ i, C₁ idx₁ i)) ∉ strongTypicalSet (Q.map (fun t => (t.1, t.2.1, t.2.2.1))) n ε₂
       then (1 : ℝ) else 0) +
      (if (fun i => (x₁ i, x₂ i, C₁ idx₁ i)) ∈ strongTypicalSet (Q.map (fun t => (t.1, t.2.1, t.2.2.1))) n ε₂ ∧
          (∃ ℓ : Fin M_c2, C₂ ℓ ∈ A₂ x₂) ∧
          (fun i => (x₁ i, x₂ i, C₁ idx₁ i, C₂ idx₂ i)) ∉ strongTypicalSet Q n ε₃
       then (1 : ℝ) else 0) +
      (∑ ℓ₁' ∈ Finset.univ.erase idx₁,
        if b₁ ℓ₁' = b₁ idx₁ ∧ (C₁ ℓ₁', C₂ idx₂) ∈ A_b then (1 : ℝ) else 0) +
      (∑ ℓ₂' ∈ Finset.univ.erase idx₂,
        if b₂ ℓ₂' = b₂ idx₂ ∧ (C₁ idx₁, C₂ ℓ₂') ∈ A_b then (1 : ℝ) else 0) +
      (∑ ℓ₁' ∈ Finset.univ.erase idx₁, ∑ ℓ₂' ∈ Finset.univ.erase idx₂,
        if b₁ ℓ₁' = b₁ idx₁ ∧ b₂ ℓ₂' = b₂ idx₂ ∧ (C₁ ℓ₁', C₂ ℓ₂') ∈ A_b then (1 : ℝ) else 0)
    blockDist d₁ x₁ (fun i => g₁ (C₁ decIdx.1 i, C₂ decIdx.2 i)) ≤
      ((∑ t, Q.pmf t * d₁.dist t.1 (g₁ (t.2.2.1, t.2.2.2))) + δ / 2) + dmax * E_tot ∧
    blockDist d₂ x₂ (fun i => g₂ (C₁ decIdx.1 i, C₂ decIdx.2 i)) ≤
      ((∑ t, Q.pmf t * d₂.dist t.2.1 (g₂ (t.2.2.1, t.2.2.2))) + δ / 2) + dmax * E_tot := by
  dsimp only
  set idx₁ := firstCoveringIdx hMc1_pos (A₁ x₁) C₁
  set idx₂ := firstCoveringIdx hMc2_pos (A₂ x₂) C₂
  set decIdx :=
    if h : ∃! p : Fin M_c1 × Fin M_c2, b₁ p.1 = b₁ idx₁ ∧ b₂ p.2 = b₂ idx₂ ∧ (C₁ p.1, C₂ p.2) ∈ A_b
    then Classical.choose h else (⟨0, hMc1_pos⟩, ⟨0, hMc2_pos⟩)
  set Ed₁ := ∑ t, Q.pmf t * d₁.dist t.1 (g₁ (t.2.2.1, t.2.2.2))
  set Ed₂ := ∑ t, Q.pmf t * d₂.dist t.2.1 (g₂ (t.2.2.1, t.2.2.2))
  set Q₁₂₁ := Q.map (fun t => (t.1, t.2.1, t.2.2.1))
  set e1 : ℝ := if ∀ ℓ : Fin M_c1, (x₁, C₁ ℓ) ∉ S₁ then 1 else 0
  set e2 : ℝ := if ∀ ℓ : Fin M_c2, (x₂, C₂ ℓ) ∉ S₂ then 1 else 0
  set e3 : ℝ := if (∃ ℓ : Fin M_c1, C₁ ℓ ∈ A₁ x₁) ∧
      (fun i => (x₁ i, x₂ i, C₁ idx₁ i)) ∉ strongTypicalSet Q₁₂₁ n ε₂ then 1 else 0
  set e4 : ℝ := if (fun i => (x₁ i, x₂ i, C₁ idx₁ i)) ∈ strongTypicalSet Q₁₂₁ n ε₂ ∧
      (∃ ℓ : Fin M_c2, C₂ ℓ ∈ A₂ x₂) ∧
      (fun i => (x₁ i, x₂ i, C₁ idx₁ i, C₂ idx₂ i)) ∉ strongTypicalSet Q n ε₃ then 1 else 0
  set e5 : ℝ := ∑ ℓ₁' ∈ Finset.univ.erase idx₁,
      if b₁ ℓ₁' = b₁ idx₁ ∧ (C₁ ℓ₁', C₂ idx₂) ∈ A_b then (1 : ℝ) else 0
  set e6 : ℝ := ∑ ℓ₂' ∈ Finset.univ.erase idx₂,
      if b₂ ℓ₂' = b₂ idx₂ ∧ (C₁ idx₁, C₂ ℓ₂') ∈ A_b then (1 : ℝ) else 0
  set e7 : ℝ := ∑ ℓ₁' ∈ Finset.univ.erase idx₁, ∑ ℓ₂' ∈ Finset.univ.erase idx₂,
      if b₁ ℓ₁' = b₁ idx₁ ∧ b₂ ℓ₂' = b₂ idx₂ ∧ (C₁ ℓ₁', C₂ ℓ₂') ∈ A_b then (1 : ℝ) else 0
  have hn_r : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  have h01 : 0 ≤ e1 := by dsimp [e1]; split_ifs <;> norm_num
  have h02 : 0 ≤ e2 := by dsimp [e2]; split_ifs <;> norm_num
  have h03 : 0 ≤ e3 := by dsimp [e3]; split_ifs <;> norm_num
  have h04 : 0 ≤ e4 := by dsimp [e4]; split_ifs <;> norm_num
  have h05 : 0 ≤ e5 := Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  have h06 : 0 ≤ e6 := Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  have h07 : 0 ≤ e7 := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  have hEd1_nn : 0 ≤ Ed₁ := Finset.sum_nonneg fun t _ => mul_nonneg (Q.nonneg t) (d₁.nonneg _ _)
  have hEd2_nn : 0 ≤ Ed₂ := Finset.sum_nonneg fun t _ => mul_nonneg (Q.nonneg t) (d₂.nonneg _ _)
  have hδ_nn : 0 ≤ δ / 2 := by linarith only [hδ0]
  have hbd1 : blockDist d₁ x₁ (fun i => g₁ (C₁ decIdx.1 i, C₂ decIdx.2 i)) ≤ dmax := by
    unfold blockDist
    calc (1 / (n : ℝ)) * ∑ i : Fin n, d₁.dist (x₁ i) (g₁ (C₁ decIdx.1 i, C₂ decIdx.2 i))
      _ ≤ (1 / (n : ℝ)) * ∑ _i : Fin n, dmax :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hd1_le _ _) (by positivity)
      _ = dmax := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← mul_assoc, one_div_mul_cancel (ne_of_gt hn_r), one_mul]
  have hbd2 : blockDist d₂ x₂ (fun i => g₂ (C₁ decIdx.1 i, C₂ decIdx.2 i)) ≤ dmax := by
    unfold blockDist
    calc (1 / (n : ℝ)) * ∑ i : Fin n, d₂.dist (x₂ i) (g₂ (C₁ decIdx.1 i, C₂ decIdx.2 i))
      _ ≤ (1 / (n : ℝ)) * ∑ _i : Fin n, dmax :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hd2_le _ _) (by positivity)
      _ = dmax := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← mul_assoc, one_div_mul_cancel (ne_of_gt hn_r), one_mul]
  have hfail : (1 : ℝ) ≤ e1 + e2 + e3 + e4 + e5 + e6 + e7 →
      blockDist d₁ x₁ (fun i => g₁ (C₁ decIdx.1 i, C₂ decIdx.2 i)) ≤
        (Ed₁ + δ / 2) + dmax * (e1 + e2 + e3 + e4 + e5 + e6 + e7) ∧
      blockDist d₂ x₂ (fun i => g₂ (C₁ decIdx.1 i, C₂ decIdx.2 i)) ≤
        (Ed₂ + δ / 2) + dmax * (e1 + e2 + e3 + e4 + e5 + e6 + e7) := by
    intro hge1
    have hd_ge : dmax ≤ dmax * (e1 + e2 + e3 + e4 + e5 + e6 + e7) := by
      simpa using mul_le_mul_of_nonneg_left hge1 hdmax0
    exact ⟨by linarith only [hbd1, hEd1_nn, hδ_nn, hd_ge],
           by linarith only [hbd2, hEd2_nn, hδ_nn, hd_ge]⟩
  by_cases hc1 : ∀ ℓ : Fin M_c1, (x₁, C₁ ℓ) ∉ S₁
  · apply hfail
    have he1 : e1 = 1 := ite_eq_left_iff.mpr (fun h => absurd hc1 h)
    linarith only [he1, h02, h03, h04, h05, h06, h07]
  push Not at hc1
  have hex1 : ∃ ℓ : Fin M_c1, C₁ ℓ ∈ A₁ x₁ := let ⟨ℓ, hℓ⟩ := hc1; ⟨ℓ, hS1_A1 x₁ (C₁ ℓ) hℓ⟩
  by_cases hc2 : ∀ ℓ : Fin M_c2, (x₂, C₂ ℓ) ∉ S₂
  · apply hfail
    have he2 : e2 = 1 := ite_eq_left_iff.mpr (fun h => absurd hc2 h)
    linarith only [h01, he2, h03, h04, h05, h06, h07]
  push Not at hc2
  have hex2 : ∃ ℓ : Fin M_c2, C₂ ℓ ∈ A₂ x₂ := let ⟨ℓ, hℓ⟩ := hc2; ⟨ℓ, hS2_A2 x₂ (C₂ ℓ) hℓ⟩
  by_cases hmk1_ok : (fun i => (x₁ i, x₂ i, C₁ idx₁ i)) ∈ strongTypicalSet Q₁₂₁ n ε₂
  · by_cases hmk2_ok : (fun i => (x₁ i, x₂ i, C₁ idx₁ i, C₂ idx₂ i)) ∈ strongTypicalSet Q n ε₃
    · by_cases hcoll : ∃ p : Fin M_c1 × Fin M_c2,
          p ≠ (idx₁, idx₂) ∧ b₁ p.1 = b₁ idx₁ ∧ b₂ p.2 = b₂ idx₂ ∧ (C₁ p.1, C₂ p.2) ∈ A_b
      · rcases hcoll with ⟨⟨ℓ₁', ℓ₂'⟩, hne, hb1, hb2, hAb⟩
        apply hfail
        by_cases h1 : ℓ₁' = idx₁
        · have h2 : ℓ₂' ≠ idx₂ := fun h2 => hne (Prod.ext h1 h2)
          have hge : (1 : ℝ) ≤ e6 := by
            calc (1 : ℝ) = (if b₂ ℓ₂' = b₂ idx₂ ∧ (C₁ idx₁, C₂ ℓ₂') ∈ A_b then 1 else 0) := by
                  rw [← h1, ite_eq_left_iff.mpr (fun h => absurd ⟨hb2, hAb⟩ h)]
              _ ≤ e6 := Finset.single_le_sum
                  (f := fun j => if b₂ j = b₂ idx₂ ∧ (C₁ idx₁, C₂ j) ∈ A_b then (1 : ℝ) else 0)
                  (fun _ _ => by split_ifs <;> norm_num)
                  (Finset.mem_erase.mpr ⟨h2, Finset.mem_univ ℓ₂'⟩)
          linarith only [h01, h02, h03, h04, h05, hge, h07]
        · by_cases h2 : ℓ₂' = idx₂
          · have hge : (1 : ℝ) ≤ e5 := by
              calc (1 : ℝ) = (if b₁ ℓ₁' = b₁ idx₁ ∧ (C₁ ℓ₁', C₂ idx₂) ∈ A_b then 1 else 0) := by
                    rw [← h2, ite_eq_left_iff.mpr (fun h => absurd ⟨hb1, hAb⟩ h)]
                _ ≤ e5 := Finset.single_le_sum
                    (f := fun j => if b₁ j = b₁ idx₁ ∧ (C₁ j, C₂ idx₂) ∈ A_b then (1 : ℝ) else 0)
                    (fun _ _ => by split_ifs <;> norm_num)
                    (Finset.mem_erase.mpr ⟨h1, Finset.mem_univ ℓ₁'⟩)
            linarith only [h01, h02, h03, h04, hge, h06, h07]
          · have hge : (1 : ℝ) ≤ e7 := by
              have hinner : (1 : ℝ) ≤ ∑ j₂ ∈ Finset.univ.erase idx₂,
                  if b₁ ℓ₁' = b₁ idx₁ ∧ b₂ j₂ = b₂ idx₂ ∧ (C₁ ℓ₁', C₂ j₂) ∈ A_b then (1 : ℝ) else 0 := by
                calc (1 : ℝ) = (if b₁ ℓ₁' = b₁ idx₁ ∧ b₂ ℓ₂' = b₂ idx₂ ∧ (C₁ ℓ₁', C₂ ℓ₂') ∈ A_b
                      then (1 : ℝ) else 0) := (ite_eq_left_iff.mpr (fun h => absurd ⟨hb1, hb2, hAb⟩ h)).symm
                  _ ≤ _ := Finset.single_le_sum
                      (f := fun j₂ => if b₁ ℓ₁' = b₁ idx₁ ∧ b₂ j₂ = b₂ idx₂ ∧ (C₁ ℓ₁', C₂ j₂) ∈ A_b
                        then (1 : ℝ) else 0)
                      (fun _ _ => by split_ifs <;> norm_num)
                      (Finset.mem_erase.mpr ⟨h2, Finset.mem_univ ℓ₂'⟩)
              calc (1 : ℝ) ≤ _ := hinner
                _ ≤ e7 := Finset.single_le_sum
                    (f := fun j₁ => ∑ j₂ ∈ Finset.univ.erase idx₂,
                      if b₁ j₁ = b₁ idx₁ ∧ b₂ j₂ = b₂ idx₂ ∧ (C₁ j₁, C₂ j₂) ∈ A_b then (1 : ℝ) else 0)
                    (fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num)
                    (Finset.mem_erase.mpr ⟨h1, Finset.mem_univ ℓ₁'⟩)
            linarith only [h01, h02, h03, h04, h05, h06, hge]
      · push Not at hcoll
        have hU12_weak : (C₁ idx₁, C₂ idx₂) ∈ A_b :=
          hU12_Ab (C₁ idx₁) (C₂ idx₂) (strongTypicalSet_map Q (fun t => (t.2.2.1, t.2.2.2)) n ε₃ hmk2_ok)
        have huniq : ∃! p : Fin M_c1 × Fin M_c2,
            b₁ p.1 = b₁ idx₁ ∧ b₂ p.2 = b₂ idx₂ ∧ (C₁ p.1, C₂ p.2) ∈ A_b := by
          refine ⟨(idx₁, idx₂), ⟨rfl, rfl, hU12_weak⟩, fun p ⟨hb1', hb2', hAb'⟩ => ?_⟩
          by_contra hne; exact hcoll p hne hb1' hb2' hAb'
        have hdec_eq : decIdx = (idx₁, idx₂) := by
          simp only [decIdx, huniq, ↓reduceDIte]
          exact (Classical.choose_spec huniq).2 (idx₁, idx₂) ⟨rfl, rfl, hU12_weak⟩ |>.symm
        have havg1 := strongTypicalSet_typical_average Q hn_pos hmk2_ok
          (fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => d₁.dist t.1 (g₁ (t.2.2.1, t.2.2.2))) (fun t => d₁.nonneg _ _)
        have havg2 := strongTypicalSet_typical_average Q hn_pos hmk2_ok
          (fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => d₂.dist t.2.1 (g₂ (t.2.2.1, t.2.2.2))) (fun t => d₂.nonneg _ _)
        have hEtot_nn : 0 ≤ dmax * (e1 + e2 + e3 + e4 + e5 + e6 + e7) :=
          mul_nonneg hdmax0 (by linarith only [h01, h02, h03, h04, h05, h06, h07])
        rw [hdec_eq]
        have hbd1' : blockDist d₁ x₁ (fun i => g₁ (C₁ idx₁ i, C₂ idx₂ i)) ≤ Ed₁ + ε₃ * Ed₁ :=
          le_trans havg1 (le_of_eq (by ring))
        have hbd2' : blockDist d₂ x₂ (fun i => g₂ (C₁ idx₁ i, C₂ idx₂ i)) ≤ Ed₂ + ε₃ * Ed₂ :=
          le_trans havg2 (le_of_eq (by ring))
        exact ⟨by linarith only [hbd1', hε₃_Ed₁, hEtot_nn], by linarith only [hbd2', hε₃_Ed₂, hEtot_nn]⟩
    · apply hfail
      have he4 : e4 = 1 := ite_eq_left_iff.mpr (fun h => absurd ⟨hmk1_ok, hex2, hmk2_ok⟩ h)
      linarith only [h01, h02, h03, he4, h05, h06, h07]
  · apply hfail
    have he3 : e3 = 1 := ite_eq_left_iff.mpr (fun h => absurd ⟨hex1, hmk1_ok⟩ h)
    linarith only [h01, h02, he3, h04, h05, h06, h07]

/-- Helper: congruence for `if` across possibly distinct `Decidable` instances, taking the
    `Decidable` arguments implicitly (no typeclass re-synthesis) so it never unfolds `Decidable`
    or postpones synthesis across binders. -/
private lemma bt_ite_congr {p q : Prop} {dp : Decidable p} {dq : Decidable q} {α : Type*} {a b : α}
    (h : p ↔ q) : @ite α p dp a b = @ite α q dq a b := by
  by_cases hp : p
  · exact ((@ite_eq_left_iff α p dp a b).mpr (fun hn => absurd hp hn)).trans
      ((@ite_eq_left_iff α q dq a b).mpr (fun hn => absurd (h.mp hp) hn)).symm
  · exact ((@ite_eq_right_iff α p dp a b).mpr (fun h' => absurd h' hp)).trans
      ((@ite_eq_right_iff α q dq a b).mpr (fun h' => absurd (h.mpr h') hp)).symm

open scoped Classical in
omit [Fintype Xh₁] [Fintype Xh₂] in
/-- Helper: fixed-blocklength random-codebook existence with **opaque** codebook and bin sizes
    `M_b1, M_b2, M_c1, M_c2 : ℕ`, so the Lean kernel never unfolds `Nat.max 1 (Nat.floor (2 ^ ...))`
    inside `Fin`-indexed random ensembles. Side-conditions are bundled into a single conjunction
    to keep binder count small. -/
private lemma bt_achiev_fixed_n
    (P : ProbDist (X₁ × X₂)) (d₁ : Distortion X₁ Xh₁) (d₂ : Distortion X₂ Xh₂)
    {kU₁ kU₂ : ℕ} (Q : ProbDist (X₁ × X₂ × Fin kU₁ × Fin kU₂))
    (g₁ : Fin kU₁ × Fin kU₂ → Xh₁) (g₂ : Fin kU₁ × Fin kU₂ → Xh₂)
    {n M_b1 M_b2 M_c1 M_c2 : ℕ}
    {ε₁ ε₂ ε₃ ε_c ε_b δ c dmax B : ℝ}
    (hcond :
      let Q₁ : ProbDist (X₁ × Fin kU₁) := Q.map (fun t => (t.1, t.2.2.1))
      let Q₂ : ProbDist (X₂ × Fin kU₂) := Q.map (fun t => (t.2.1, t.2.2.2))
      let Q₁₂ : ProbDist (Fin kU₁ × Fin kU₂) := Q.map (fun t => (t.2.2.1, t.2.2.2))
      let Q₁₂₁ : ProbDist (X₁ × X₂ × Fin kU₁) := Q.map (fun t => (t.1, t.2.1, t.2.2.1))
      (Q.map (fun t => (t.1, t.2.1)) = P) ∧
      (condMutualInfo (Q.map (fun t => (t.2.2.1, (t.2.1, t.2.2.2), t.1))) = 0) ∧
      (condMutualInfo (Q.map (fun t => (t.2.2.2, (t.1, t.2.2.1), t.2.1))) = 0) ∧
      (0 < n ∧ 0 < M_b1 ∧ 0 < M_b2 ∧ 0 < M_c1 ∧ 0 < M_c2) ∧
      (0 < δ ∧ 0 < c ∧ 0 ≤ dmax ∧ dmax ≤ B ∧ B * (9 * c) = δ / 2) ∧
      ((∀ x xh, d₁.dist x xh ≤ dmax) ∧ (∀ x xh, d₂.dist x xh ≤ dmax)) ∧
      (0 < ε₁ ∧ ε₁ < ε₂ ∧ 0 < ε₃ ∧ ε₃ ≤ 1 ∧ 0 < ε_c ∧ ε₂ = ε₃ / 4 ∧ ε₁ = ε₃ / 16) ∧
      (ε₃ * (∑ t, Q.pmf t * d₁.dist t.1 (g₁ (t.2.2.1, t.2.2.2))) ≤ δ / 2 ∧
       ε₃ * (∑ t, Q.pmf t * d₂.dist t.2.1 (g₂ (t.2.2.1, t.2.2.2))) ≤ δ / 2) ∧
      (ε₁ * shannonEntropy Q₁.fst ≤ ε_c ∧ ε₁ * shannonEntropy Q₁.snd ≤ ε_c ∧ ε₁ * shannonEntropy Q₁ ≤ ε_c ∧
       ε₁ * shannonEntropy Q₂.fst ≤ ε_c ∧ ε₁ * shannonEntropy Q₂.snd ≤ ε_c ∧ ε₁ * shannonEntropy Q₂ ≤ ε_c ∧
       ε₃ * shannonEntropy Q₁₂.fst ≤ ε_b ∧ ε₃ * shannonEntropy Q₁₂.snd ≤ ε_b ∧ ε₃ * shannonEntropy Q₁₂ ≤ ε_b) ∧
      (1 - ∑ z ∈ strongTypicalSet Q₁ n ε₁, (iidDist Q₁ n).pmf z ≤ c ∧
       1 - ∑ z ∈ strongTypicalSet Q₂ n ε₁, (iidDist Q₂ n).pmf z ≤ c ∧
       Real.exp (-((M_c1 : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Q₁ + 3 * ε_c))))) ≤ c ∧
       Real.exp (-((M_c2 : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Q₂ + 3 * ε_c))))) ≤ c) ∧
      ((∑ t : X₁ × X₂ × Fin kU₁, if 0 < Q₁₂₁.pmf t then 1 / Q₁₂₁.pmf t ^ 2 else 0) /
          ((n : ℝ) * (ε₂ - ε₁) ^ 2) ≤ c ∧
       (4 * ∑ t : X₁ × X₂ × Fin kU₁ × Fin kU₂, if 0 < Q.pmf t then 1 / Q.pmf t ^ 2 else 0) /
          ((n : ℝ) * ε₃ ^ 2) ≤ c) ∧
      (((M_c1 : ℝ) / (M_b1 : ℝ)) * (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Q₁₂ - 3 * ε_b))) ≤ c ∧
       ((M_c2 : ℝ) / (M_b2 : ℝ)) * (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Q₁₂ - 3 * ε_b))) ≤ c ∧
       (((M_c1 : ℝ) / (M_b1 : ℝ)) * ((M_c2 : ℝ) / (M_b2 : ℝ))) *
          (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Q₁₂ - 3 * ε_b))) ≤ c)) :
    ∃ (enc₁ : (Fin n → X₁) → Fin M_b1)
      (enc₂ : (Fin n → X₂) → Fin M_b2)
      (dec₁ : Fin M_b1 × Fin M_b2 → Fin n → Xh₁)
      (dec₂ : Fin M_b1 × Fin M_b2 → Fin n → Xh₂),
      let Pn (x : Fin n → X₁ × X₂) : ℝ := ∏ i : Fin n, P.pmf (x i)
      (∑ x : Fin n → X₁ × X₂, Pn x *
        ((1 / (n : ℝ)) * ∑ i : Fin n,
          d₁.dist (x i).1 (dec₁ (enc₁ (fun j => (x j).1), enc₂ (fun j => (x j).2)) i))) ≤
        (∑ t, Q.pmf t * d₁.dist t.1 (g₁ (t.2.2.1, t.2.2.2))) + δ ∧
      (∑ x : Fin n → X₁ × X₂, Pn x *
        ((1 / (n : ℝ)) * ∑ i : Fin n,
          d₂.dist (x i).2 (dec₂ (enc₁ (fun j => (x j).1), enc₂ (fun j => (x j).2)) i))) ≤
        (∑ t, Q.pmf t * d₂.dist t.2.1 (g₂ (t.2.2.1, t.2.2.2))) + δ := by
  rcases hcond with ⟨hmarg, hmk1, hmk2, ⟨hn_pos, hMb1_pos, hMb2_pos, hMc1_pos, hMc2_pos⟩,
    ⟨hδ, hc, hdmax0, hdB, hBc⟩, ⟨hd1_le, hd2_le⟩,
    ⟨hε₁, hε₁_lt_ε₂, hε₃, hε₃_le1, hε_c, hε₂_eq, hε₁_eq⟩,
    ⟨hε₃_Ed₁, hε₃_Ed₂⟩,
    ⟨hH1f_c, hH1s_c, hH1_c, hH2f_c, hH2s_c, hH2_c, hH12f_b, hH12s_b, hH12_b⟩,
    ⟨hcov1_tail, hcov2_tail, hcov1_exp, hcov2_exp⟩,
    ⟨hmk1_bd, hmk2_bd⟩, ⟨hbin1_bd, hbin2_bd, hbin12_bd⟩⟩
  let Q₁ : ProbDist (X₁ × Fin kU₁) := Q.map (fun t => (t.1, t.2.2.1))
  let Q₂ : ProbDist (X₂ × Fin kU₂) := Q.map (fun t => (t.2.1, t.2.2.2))
  let Q₁₂ : ProbDist (Fin kU₁ × Fin kU₂) := Q.map (fun t => (t.2.2.1, t.2.2.2))
  let Q₁₂₁ : ProbDist (X₁ × X₂ × Fin kU₁) := Q.map (fun t => (t.1, t.2.1, t.2.2.1))
  let Qu₁ : ProbDist (Fin kU₁) := Q₁.snd
  let Qu₂ : ProbDist (Fin kU₂) := Q₂.snd
  let Ed₁ : ℝ := ∑ t, Q.pmf t * d₁.dist t.1 (g₁ (t.2.2.1, t.2.2.2))
  let Ed₂ : ℝ := ∑ t, Q.pmf t * d₂.dist t.2.1 (g₂ (t.2.2.1, t.2.2.2))
  have hQ₁_fst : Q₁.fst = P.fst := by
    rw [← bt_probDist_map_fst, ← bt_probDist_map_fst, ← hmarg]; unfold Q₁; rw [map_comp_eq, map_comp_eq]; rfl
  have hQ₂_fst : Q₂.fst = P.snd := by
    rw [← bt_probDist_map_fst, ← bt_probDist_map_snd, ← hmarg]; unfold Q₂; rw [map_comp_eq, map_comp_eq]; rfl
  have hQ₁₂_fst : Q₁₂.fst = Qu₁ := by
    unfold Qu₁; rw [← bt_probDist_map_fst, ← bt_probDist_map_snd]; unfold Q₁₂ Q₁; rw [map_comp_eq, map_comp_eq]; rfl
  have hQ₁₂_snd : Q₁₂.snd = Qu₂ := by
    unfold Qu₂; rw [← bt_probDist_map_snd, ← bt_probDist_map_snd]; unfold Q₁₂ Q₂; rw [map_comp_eq, map_comp_eq]; rfl
  have hQ₁₂₁_marg : Q₁₂₁.map (fun t => (t.1, t.2.1)) = P := by
    unfold Q₁₂₁; rw [map_comp_eq]; exact hmarg
  have hQ₁₂₁_xu : Q₁₂₁.map (fun t => (t.1, t.2.2)) = Q₁ := by
    unfold Q₁₂₁ Q₁; rw [map_comp_eq]; rfl
  have hU1_X2_X1 : condMutualInfo (Q₁₂₁.map (fun t => (t.2.2, t.2.1, t.1))) = 0 := by
    let R1 : ProbDist (Fin kU₁ × X₂ × Fin kU₂ × X₁) := Q.map (fun t => (t.2.2.1, t.2.1, t.2.2.2, t.1))
    have hR1 : condMutualInfo (R1.map (fun t => (t.1, (t.2.1, t.2.2.1), t.2.2.2))) = 0 := by
      unfold R1; rw [map_comp_eq]; exact hmk1
    have h := (bt_condMutualInfo_zero_split R1 hR1).1
    unfold R1 at h; rw [map_comp_eq] at h
    unfold Q₁₂₁; rw [map_comp_eq]; exact h
  have : Nonempty (Fin M_b1) := ⟨⟨0, hMb1_pos⟩⟩
  have : Nonempty (Fin M_b2) := ⟨⟨0, hMb2_pos⟩⟩
  have : Nonempty (Fin M_c1) := ⟨⟨0, hMc1_pos⟩⟩
  have : Nonempty (Fin M_c2) := ⟨⟨0, hMc2_pos⟩⟩
  let W_C1 : ProbDist (Fin M_c1 → Fin n → Fin kU₁) := codebookDist Qu₁ n M_c1
  let W_C2 : ProbDist (Fin M_c2 → Fin n → Fin kU₂) := codebookDist Qu₂ n M_c2
  let W_b1 : ProbDist (Fin M_c1 → Fin M_b1) := iidDist (ProbDist.uniform (α := Fin M_b1)) M_c1
  let W_b2 : ProbDist (Fin M_c2 → Fin M_b2) := iidDist (ProbDist.uniform (α := Fin M_b2)) M_c2
  let W_ens := (W_C1.prod W_C2).prod (W_b1.prod W_b2)
  let S₁ : Finset ((Fin n → X₁) × (Fin n → Fin kU₁)) :=
    Finset.univ.filter fun xu => zipEquiv X₁ (Fin kU₁) n xu ∈ strongTypicalSet Q₁ n ε₁
  let S₂ : Finset ((Fin n → X₂) × (Fin n → Fin kU₂)) :=
    Finset.univ.filter fun xu => zipEquiv X₂ (Fin kU₂) n xu ∈ strongTypicalSet Q₂ n ε₁
  let A₂ : (Fin n → X₂) → Finset (Fin n → Fin kU₂) := fun x₂ =>
    Finset.univ.filter fun u₂ => (fun i => (x₂ i, u₂ i)) ∈ strongTypicalSet Q₂ n ε₁
  let A₁ : (Fin n → X₁) → Finset (Fin n → Fin kU₁) := fun x₁ =>
    Finset.univ.filter fun u₁ => (fun i => (x₁ i, u₁ i)) ∈ strongTypicalSet Q₁ n ε₁
  let A_b : Finset ((Fin n → Fin kU₁) × (Fin n → Fin kU₂)) := jointTypicalSet Q₁₂ n ε_b
  have hS1_sub : S₁ ⊆ jointTypicalSet Q₁ n ε_c := fun _ hxu =>
    strongTypicalSet_mem_jointTypicalSet Q₁ hn_pos (le_of_lt hε₁) hH1f_c hH1s_c hH1_c
      (Finset.mem_filter.mp hxu).2
  have hS2_sub : S₂ ⊆ jointTypicalSet Q₂ n ε_c := fun _ hxu =>
    strongTypicalSet_mem_jointTypicalSet Q₂ hn_pos (le_of_lt hε₁) hH2f_c hH2s_c hH2_c
      (Finset.mem_filter.mp hxu).2
  have hU12_Ab : ∀ u₁ u₂, (fun i => (u₁ i, u₂ i)) ∈ strongTypicalSet Q₁₂ n ε₃ → (u₁, u₂) ∈ A_b :=
    fun _ _ hmem => strongTypicalSet_mem_jointTypicalSet Q₁₂ hn_pos (le_of_lt hε₃)
      hH12f_b hH12s_b hH12_b hmem
  let idx₁ : (Fin M_c1 → Fin n → Fin kU₁) → (Fin n → X₁) → Fin M_c1 := fun C₁ x₁ =>
    firstCoveringIdx hMc1_pos (A₁ x₁) C₁
  let idx₂ : (Fin M_c2 → Fin n → Fin kU₂) → (Fin n → X₂) → Fin M_c2 := fun C₂ x₂ =>
    firstCoveringIdx hMc2_pos (A₂ x₂) C₂
  let enc₁Of := fun (C₁ : Fin M_c1 → Fin n → Fin kU₁) (b₁ : Fin M_c1 → Fin M_b1) (x₁ : Fin n → X₁) =>
    b₁ (idx₁ C₁ x₁)
  let enc₂Of := fun (C₂ : Fin M_c2 → Fin n → Fin kU₂) (b₂ : Fin M_c2 → Fin M_b2) (x₂ : Fin n → X₂) =>
    b₂ (idx₂ C₂ x₂)
  let decIdx := fun (C₁ : Fin M_c1 → Fin n → Fin kU₁) (C₂ : Fin M_c2 → Fin n → Fin kU₂)
      (b₁ : Fin M_c1 → Fin M_b1) (b₂ : Fin M_c2 → Fin M_b2) (m : Fin M_b1 × Fin M_b2) =>
    if h : ∃! p : Fin M_c1 × Fin M_c2, b₁ p.1 = m.1 ∧ b₂ p.2 = m.2 ∧ (C₁ p.1, C₂ p.2) ∈ A_b
    then Classical.choose h else (⟨0, hMc1_pos⟩, ⟨0, hMc2_pos⟩)
  let dec₁Of := fun C₁ C₂ b₁ b₂ m i =>
    let p := decIdx C₁ C₂ b₁ b₂ m; g₁ (C₁ p.1 i, C₂ p.2 i)
  let dec₂Of := fun C₁ C₂ b₁ b₂ m i =>
    let p := decIdx C₁ C₂ b₁ b₂ m; g₂ (C₁ p.1 i, C₂ p.2 i)
  let E_cov1 := fun (C₁ : Fin M_c1 → Fin n → Fin kU₁) (x₁ : Fin n → X₁) =>
    if ∀ ℓ : Fin M_c1, (x₁, C₁ ℓ) ∉ S₁ then (1 : ℝ) else 0
  let E_cov2 := fun (C₂ : Fin M_c2 → Fin n → Fin kU₂) (x₂ : Fin n → X₂) =>
    if ∀ ℓ : Fin M_c2, (x₂, C₂ ℓ) ∉ S₂ then (1 : ℝ) else 0
  let E_mk1 := fun (C₁ : Fin M_c1 → Fin n → Fin kU₁) (x₁ : Fin n → X₁) (x₂ : Fin n → X₂) =>
    if (∃ ℓ : Fin M_c1, C₁ ℓ ∈ A₁ x₁) ∧
       (fun i => (x₁ i, x₂ i, C₁ (idx₁ C₁ x₁) i)) ∉ strongTypicalSet Q₁₂₁ n ε₂
    then (1 : ℝ) else 0
  let E_mk2 := fun (C₁ : Fin M_c1 → Fin n → Fin kU₁) (C₂ : Fin M_c2 → Fin n → Fin kU₂)
      (x₁ : Fin n → X₁) (x₂ : Fin n → X₂) =>
    if (fun i => (x₁ i, x₂ i, C₁ (idx₁ C₁ x₁) i)) ∈ strongTypicalSet Q₁₂₁ n ε₂ ∧
       (∃ ℓ : Fin M_c2, C₂ ℓ ∈ A₂ x₂) ∧
       (fun i => (x₁ i, x₂ i, C₁ (idx₁ C₁ x₁) i, C₂ (idx₂ C₂ x₂) i)) ∉ strongTypicalSet Q n ε₃
    then (1 : ℝ) else 0
  let E_bin1 := fun (C₁ : Fin M_c1 → Fin n → Fin kU₁) (C₂ : Fin M_c2 → Fin n → Fin kU₂)
      (b₁ : Fin M_c1 → Fin M_b1) (x₁ : Fin n → X₁) (x₂ : Fin n → X₂) =>
    ∑ ℓ₁' ∈ Finset.univ.erase (idx₁ C₁ x₁),
      if b₁ ℓ₁' = b₁ (idx₁ C₁ x₁) ∧ (C₁ ℓ₁', C₂ (idx₂ C₂ x₂)) ∈ A_b then (1 : ℝ) else 0
  let E_bin2 := fun (C₁ : Fin M_c1 → Fin n → Fin kU₁) (C₂ : Fin M_c2 → Fin n → Fin kU₂)
      (b₂ : Fin M_c2 → Fin M_b2) (x₁ : Fin n → X₁) (x₂ : Fin n → X₂) =>
    ∑ ℓ₂' ∈ Finset.univ.erase (idx₂ C₂ x₂),
      if b₂ ℓ₂' = b₂ (idx₂ C₂ x₂) ∧ (C₁ (idx₁ C₁ x₁), C₂ ℓ₂') ∈ A_b then (1 : ℝ) else 0
  let E_bin12 := fun (C₁ : Fin M_c1 → Fin n → Fin kU₁) (C₂ : Fin M_c2 → Fin n → Fin kU₂)
      (b₁ : Fin M_c1 → Fin M_b1) (b₂ : Fin M_c2 → Fin M_b2) (x₁ : Fin n → X₁) (x₂ : Fin n → X₂) =>
    ∑ ℓ₁' ∈ Finset.univ.erase (idx₁ C₁ x₁), ∑ ℓ₂' ∈ Finset.univ.erase (idx₂ C₂ x₂),
      if b₁ ℓ₁' = b₁ (idx₁ C₁ x₁) ∧ b₂ ℓ₂' = b₂ (idx₂ C₂ x₂) ∧ (C₁ ℓ₁', C₂ ℓ₂') ∈ A_b
      then (1 : ℝ) else 0
  let E_tot := fun C₁ C₂ b₁ b₂ x₁ x₂ =>
    E_cov1 C₁ x₁ + E_cov2 C₂ x₂ + E_mk1 C₁ x₁ x₂ + E_mk2 C₁ C₂ x₁ x₂ +
    E_bin1 C₁ C₂ b₁ x₁ x₂ + E_bin2 C₁ C₂ b₂ x₁ x₂ + E_bin12 C₁ C₂ b₁ b₂ x₁ x₂
  have hpt_dist : ∀ C₁ C₂ b₁ b₂ (x₁ : Fin n → X₁) (x₂ : Fin n → X₂),
      blockDist d₁ x₁ (dec₁Of C₁ C₂ b₁ b₂ (enc₁Of C₁ b₁ x₁, enc₂Of C₂ b₂ x₂)) ≤
        (Ed₁ + δ / 2) + dmax * E_tot C₁ C₂ b₁ b₂ x₁ x₂ ∧
      blockDist d₂ x₂ (dec₂Of C₁ C₂ b₁ b₂ (enc₁Of C₁ b₁ x₁, enc₂Of C₂ b₂ x₂)) ≤
        (Ed₂ + δ / 2) + dmax * E_tot C₁ C₂ b₁ b₂ x₁ x₂ := fun C₁ C₂ b₁ b₂ x₁ x₂ =>
    bt_achiev_pointwise_dist d₁ d₂ Q g₁ g₂ hn_pos hMc1_pos hMc2_pos (le_of_lt hδ) hdmax0 hd1_le hd2_le
      hε₃_Ed₁ hε₃_Ed₂ S₁ S₂ A₁ A₂ A_b
      (fun _ _ h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h).2⟩)
      (fun _ _ h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h).2⟩)
      hU12_Ab C₁ C₂ b₁ b₂ x₁ x₂
  have hAvg_cov1 : ∑ C₁, W_C1.pmf C₁ *
      (∑ xy : (Fin n → X₁) × (Fin n → X₂), (jointIidDist P n).pmf xy * E_cov1 C₁ xy.1) ≤ c + c := by
    have hcov := bt_achiev_covering_bound_fst P Q₁ hQ₁_fst n M_c1 (le_of_lt hε_c) S₁ hS1_sub E_cov1
      (fun C₁ x₁ h => by dsimp only [E_cov1]; exact ite_eq_left_iff.mpr fun hc => absurd h hc)
      (fun C₁ x₁ h => by dsimp only [E_cov1]; exact ite_eq_right_iff.mpr fun hc => absurd hc h)
    have hS1_prob := bt_strongTypicalSet_zip_prob Q₁ n ε₁ S₁ (fun xu => by simp [S₁])
    refine le_trans (le_of_eq ?_) (le_trans hcov ?_)
    · exact bt_sum_fintype_congr fun C₁ =>
        congrArg (W_C1.pmf C₁ * ·) (bt_sum_fintype_congr fun _ => rfl)
    · rw [hS1_prob]; linarith only [hcov1_tail, hcov1_exp]
  have hAvg_cov2 : ∑ C₂, W_C2.pmf C₂ *
      (∑ xy : (Fin n → X₁) × (Fin n → X₂), (jointIidDist P n).pmf xy * E_cov2 C₂ xy.2) ≤ c + c := by
    have hcov := bt_achiev_covering_bound_snd P Q₂ hQ₂_fst n M_c2 (le_of_lt hε_c) S₂ hS2_sub E_cov2
      (fun C₂ x₂ h => by dsimp only [E_cov2]; exact ite_eq_left_iff.mpr fun hc => absurd h hc)
      (fun C₂ x₂ h => by dsimp only [E_cov2]; exact ite_eq_right_iff.mpr fun hc => absurd hc h)
    have hS2_prob := bt_strongTypicalSet_zip_prob Q₂ n ε₁ S₂ (fun xu => by simp [S₂])
    refine le_trans (le_of_eq ?_) (le_trans hcov ?_)
    · exact bt_sum_fintype_congr fun C₂ =>
        congrArg (W_C2.pmf C₂ * ·) (bt_sum_fintype_congr fun _ => rfl)
    · rw [hS2_prob]; linarith only [hcov2_tail, hcov2_exp]
  have hAvg_mk1 : ∀ C₁,
      (∑ xy : (Fin n → X₁) × (Fin n → X₂), (jointIidDist P n).pmf xy * E_mk1 C₁ xy.1 xy.2) ≤ c := by
    intro C₁
    rw [Fintype.sum_prod_type]
    have hinner : ∀ x₁ : Fin n → X₁,
        (∑ x₂ : Fin n → X₂, (jointIidDist P n).pmf (x₁, x₂) * E_mk1 C₁ x₁ x₂) ≤
          (iidDist P.fst n).pmf x₁ * c := by
      intro x₁
      simp_rw [jointIidDist_eq_fst_mul_condChannelPower P n x₁, mul_assoc, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ ((iidDist P.fst n).nonneg x₁)
      by_cases hex1 : ∃ ℓ : Fin M_c1, C₁ ℓ ∈ A₁ x₁
      · have hxu : (fun i => (x₁ i, C₁ (idx₁ C₁ x₁) i)) ∈
            strongTypicalSet (Q₁₂₁.map (fun t => (t.1, t.2.2))) n ε₁ := by
          rw [hQ₁₂₁_xu]
          exact (Finset.mem_filter.mp (firstCoveringIdx_mem hMc1_pos (A₁ x₁) C₁ hex1)).2
        have hmk := markov_lemma Q₁₂₁ hU1_X2_X1 hn_pos (le_of_lt hε₁) hε₁_lt_ε₂ hxu
        dsimp only at hmk
        rw [hQ₁₂₁_marg] at hmk
        refine le_trans (le_of_eq ?_) (le_trans hmk (le_trans (le_of_eq ?_) hmk1_bd))
        · exact bt_sum_fintype_congr fun x₂ => congrArg (((condChannelOfJoint P).power n).trans x₁ x₂ * ·)
            (bt_ite_congr ⟨fun h => h.2, fun h => ⟨hex1, h⟩⟩)
        · refine congrArg (· / ((n : ℝ) * (ε₂ - ε₁) ^ 2)) (Finset.sum_congr rfl fun t _ => ?_)
          exact bt_ite_congr Iff.rfl
      · have h0 : ∀ x₂, E_mk1 C₁ x₁ x₂ = 0 := fun x₂ => by
          dsimp only [E_mk1]; exact ite_eq_right_iff.mpr fun h => absurd h.1 hex1
        simp_rw [h0, mul_zero, Finset.sum_const_zero]; exact le_of_lt hc
    calc ∑ x₁ : Fin n → X₁, ∑ x₂ : Fin n → X₂, (jointIidDist P n).pmf (x₁, x₂) * E_mk1 C₁ x₁ x₂
      _ ≤ ∑ x₁ : Fin n → X₁, (iidDist P.fst n).pmf x₁ * c := Finset.sum_le_sum fun x₁ _ => hinner x₁
      _ = c := by rw [← Finset.sum_mul, (iidDist P.fst n).sum_one, one_mul]
  have hAvg_mk2 : ∀ C₁ (x₁ : Fin n → X₁) (x₂ : Fin n → X₂),
      (∑ C₂, W_C2.pmf C₂ * E_mk2 C₁ C₂ x₁ x₂) ≤ c := by
    intro C₁ x₁ x₂
    by_cases h121 : (fun i => (x₁ i, x₂ i, C₁ (idx₁ C₁ x₁) i)) ∈ strongTypicalSet Q₁₂₁ n ε₂
    · have h121' : (fun i => (x₁ i, x₂ i, C₁ (idx₁ C₁ x₁) i)) ∈ strongTypicalSet Q₁₂₁ n (ε₃ / 4) := by
        rwa [← hε₂_eq]
      have hmk := markov_lemma_first_covering_codeword Q hmk2 hn_pos hMc2_pos hε₃ hε₃_le1 h121'
      dsimp only at hmk
      rw [← hε₁_eq] at hmk
      have hA₂_eq : ∀ (d : DecidablePred (fun u₂ : Fin n → Fin kU₂ =>
          (fun i => (x₂ i, u₂ i)) ∈ strongTypicalSet (Q.map (fun t => (t.2.1, t.2.2.2))) n ε₁)),
          A₂ x₂ = @Finset.filter _ _ d Finset.univ := fun d => by
        ext u₂; simp only [A₂, Q₂, Finset.mem_filter, Finset.mem_univ, true_and]
      refine le_trans (le_of_eq ?_) (le_trans hmk (le_trans (le_of_eq ?_) hmk2_bd))
      · refine bt_sum_fintype_congr fun C₂ => congrArg (W_C2.pmf C₂ * ·) ?_
        refine bt_ite_congr ?_
        dsimp only [idx₂]; rw [hA₂_eq _]; exact ⟨fun h => h.2, fun h => ⟨h121, h⟩⟩
      · refine congrArg (· / ((n : ℝ) * ε₃ ^ 2)) (congrArg (4 * ·) (Finset.sum_congr rfl fun t _ => ?_))
        exact bt_ite_congr Iff.rfl
    · have h0 : ∀ C₂, E_mk2 C₁ C₂ x₁ x₂ = 0 := fun C₂ => by
        dsimp only [E_mk2]; exact ite_eq_right_iff.mpr fun h => absurd h.1 h121
      simp_rw [h0, mul_zero, Finset.sum_const_zero]; exact le_of_lt hc
  have hAvg_bin1 : ∀ C₂ (x₁ : Fin n → X₁) (x₂ : Fin n → X₂),
      (∑ C₁, W_C1.pmf C₁ * ∑ b₁, W_b1.pmf b₁ * E_bin1 C₁ C₂ b₁ x₁ x₂) ≤ c := by
    intro C₂ x₁ x₂
    let u₂ := C₂ (idx₂ C₂ x₂)
    have hslice := jointTypicalSet_slice_indep_prob_le Q₁₂ n ε_b u₂
    rw [hQ₁₂_fst] at hslice
    have hslice' : ∑ u₁ : Fin n → Fin kU₁, (iidDist Qu₁ n).pmf u₁ *
        (if (u₁, u₂) ∈ A_b then (1 : ℝ) else 0) ≤
        (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Q₁₂ - 3 * ε_b))) := by
      refine le_trans (le_of_eq ?_) hslice
      exact bt_sum_fintype_congr fun u₁ => congrArg ((iidDist Qu₁ n).pmf u₁ * ·) (bt_ite_congr Iff.rfl)
    have hbase := bt_achiev_binning_single_bound Qu₁ n M_c1 M_b1 hMb1_pos
      (fun u₁ => (u₁, u₂) ∈ A_b) (fun C₁ => idx₁ C₁ x₁) hslice'
    refine le_trans (le_of_eq ?_) (le_trans hbase hbin1_bd)
    refine bt_sum_fintype_congr fun C₁ => congrArg (W_C1.pmf C₁ * ·)
      (bt_sum_fintype_congr fun b₁ => congrArg (W_b1.pmf b₁ * ·) ?_)
    refine Finset.sum_congr rfl fun ℓ₁' _ => bt_ite_congr Iff.rfl
  have hAvg_bin2 : ∀ C₁ (x₁ : Fin n → X₁) (x₂ : Fin n → X₂),
      (∑ C₂, W_C2.pmf C₂ * ∑ b₂, W_b2.pmf b₂ * E_bin2 C₁ C₂ b₂ x₁ x₂) ≤ c := by
    intro C₁ x₁ x₂
    let u₁ := C₁ (idx₁ C₁ x₁)
    have hslice := bt_jointTypicalSet_right_slice_indep_prob_le Q₁₂ n ε_b u₁
    rw [hQ₁₂_snd] at hslice
    have hslice' : ∑ u₂ : Fin n → Fin kU₂, (iidDist Qu₂ n).pmf u₂ *
        (if (u₁, u₂) ∈ A_b then (1 : ℝ) else 0) ≤
        (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Q₁₂ - 3 * ε_b))) := by
      refine le_trans (le_of_eq ?_) hslice
      exact bt_sum_fintype_congr fun u₂ => congrArg ((iidDist Qu₂ n).pmf u₂ * ·) (bt_ite_congr Iff.rfl)
    have hbase := bt_achiev_binning_single_bound Qu₂ n M_c2 M_b2 hMb2_pos
      (fun u₂ => (u₁, u₂) ∈ A_b) (fun C₂ => idx₂ C₂ x₂) hslice'
    refine le_trans (le_of_eq ?_) (le_trans hbase hbin2_bd)
    refine bt_sum_fintype_congr fun C₂ => congrArg (W_C2.pmf C₂ * ·)
      (bt_sum_fintype_congr fun b₂ => congrArg (W_b2.pmf b₂ * ·) ?_)
    refine Finset.sum_congr rfl fun ℓ₂' _ => bt_ite_congr Iff.rfl
  have hAvg_bin12 : ∀ (x₁ : Fin n → X₁) (x₂ : Fin n → X₂),
      (∑ C₁, W_C1.pmf C₁ * ∑ C₂, W_C2.pmf C₂ *
        ∑ b₁, W_b1.pmf b₁ * ∑ b₂, W_b2.pmf b₂ * E_bin12 C₁ C₂ b₁ b₂ x₁ x₂) ≤ c := by
    intro x₁ x₂
    have hbase := bt_achiev_binning_joint_bound Q₁₂ n M_c1 M_c2 M_b1 M_b2 hMb1_pos hMb2_pos A_b
      (fun C₁ => idx₁ C₁ x₁) (fun C₂ => idx₂ C₂ x₂)
    rw [hQ₁₂_fst, hQ₁₂_snd] at hbase
    have hC12_le : (∑ C₁, W_C1.pmf C₁ * ∑ C₂, W_C2.pmf C₂ *
        ∑ b₁, W_b1.pmf b₁ * ∑ b₂, W_b2.pmf b₂ * E_bin12 C₁ C₂ b₁ b₂ x₁ x₂) ≤
        (((M_c1 : ℝ) / (M_b1 : ℝ)) * ((M_c2 : ℝ) / (M_b2 : ℝ))) *
          ∑ u ∈ A_b, ((iidDist Qu₁ n).prod (iidDist Qu₂ n)).pmf u := by
      refine le_trans (le_of_eq ?_) hbase
      refine bt_sum_fintype_congr fun C₁ => congrArg (W_C1.pmf C₁ * ·)
        (bt_sum_fintype_congr fun C₂ => congrArg (W_C2.pmf C₂ * ·)
          (bt_sum_fintype_congr fun b₁ => congrArg (W_b1.pmf b₁ * ·)
            (bt_sum_fintype_congr fun b₂ => congrArg (W_b2.pmf b₂ * ·) ?_)))
      refine Finset.sum_congr rfl fun ℓ₁' _ => Finset.sum_congr rfl fun ℓ₂' _ =>
        bt_ite_congr Iff.rfl
    have hpack := jointTypicalSet_indep_prob_le Q₁₂ n ε_b
    rw [hQ₁₂_fst, hQ₁₂_snd] at hpack
    exact le_trans hC12_le (le_trans (mul_le_mul_of_nonneg_left hpack (by positivity)) hbin12_bd)
  let codeErr :
      ((Fin M_c1 → Fin n → Fin kU₁) × (Fin M_c2 → Fin n → Fin kU₂)) ×
      ((Fin M_c1 → Fin M_b1) × (Fin M_c2 → Fin M_b2)) → ℝ := fun ω =>
    ∑ xy : (Fin n → X₁) × (Fin n → X₂), (jointIidDist P n).pmf xy *
      E_tot ω.1.1 ω.1.2 ω.2.1 ω.2.2 xy.1 xy.2
  have havg_err : ∑ ω, W_ens.pmf ω * codeErr ω ≤ 9 * c :=
    bt_achiev_combine_ensemble W_C1 W_C2 W_b1 W_b2 (jointIidDist P n)
      (fun C₁ xy => E_cov1 C₁ xy.1) (fun C₂ xy => E_cov2 C₂ xy.2)
      (fun C₁ xy => E_mk1 C₁ xy.1 xy.2) (fun C₁ C₂ xy => E_mk2 C₁ C₂ xy.1 xy.2)
      (fun C₁ C₂ b₁ xy => E_bin1 C₁ C₂ b₁ xy.1 xy.2) (fun C₁ C₂ b₂ xy => E_bin2 C₁ C₂ b₂ xy.1 xy.2)
      (fun C₁ C₂ b₁ b₂ xy => E_bin12 C₁ C₂ b₁ b₂ xy.1 xy.2)
      hAvg_cov1 hAvg_cov2 hAvg_mk1
      (fun C₁ xy => hAvg_mk2 C₁ xy.1 xy.2)
      (fun C₂ xy => hAvg_bin1 C₂ xy.1 xy.2)
      (fun C₁ xy => hAvg_bin2 C₁ xy.1 xy.2)
      (fun xy => hAvg_bin12 xy.1 xy.2)
  obtain ⟨⟨⟨C₁, C₂⟩, ⟨b₁, b₂⟩⟩, hcode⟩ := bt_exists_le_of_expectation_le W_ens codeErr havg_err
  refine ⟨enc₁Of C₁ b₁, enc₂Of C₂ b₂, dec₁Of C₁ C₂ b₁ b₂, dec₂Of C₁ C₂ b₁ b₂, ?_, ?_⟩
  · have heq : (∑ x : Fin n → X₁ × X₂, (∏ i : Fin n, P.pmf (x i)) *
        ((1 / (n : ℝ)) * ∑ i : Fin n,
          d₁.dist (x i).1 (dec₁Of C₁ C₂ b₁ b₂ (enc₁Of C₁ b₁ (fun j => (x j).1),
            enc₂Of C₂ b₂ (fun j => (x j).2)) i))) =
        ∑ xy : (Fin n → X₁) × (Fin n → X₂), (jointIidDist P n).pmf xy *
          blockDist d₁ xy.1 (dec₁Of C₁ C₂ b₁ b₂ (enc₁Of C₁ b₁ xy.1, enc₂Of C₂ b₂ xy.2)) :=
      (Fintype.sum_equiv (zipEquiv X₁ X₂ n) _ _ (fun _ => rfl)).symm
    refine le_trans (le_of_eq ((bt_sum_fintype_congr fun _ => rfl).trans heq)) ?_
    have hsum_le : ∑ xy : (Fin n → X₁) × (Fin n → X₂), (jointIidDist P n).pmf xy *
          blockDist d₁ xy.1 (dec₁Of C₁ C₂ b₁ b₂ (enc₁Of C₁ b₁ xy.1, enc₂Of C₂ b₂ xy.2)) ≤
        (Ed₁ + δ / 2) + dmax * codeErr ((C₁, C₂), (b₁, b₂)) := by
      calc ∑ xy, (jointIidDist P n).pmf xy *
            blockDist d₁ xy.1 (dec₁Of C₁ C₂ b₁ b₂ (enc₁Of C₁ b₁ xy.1, enc₂Of C₂ b₂ xy.2))
        _ ≤ ∑ xy, (jointIidDist P n).pmf xy *
              ((Ed₁ + δ / 2) + dmax * E_tot C₁ C₂ b₁ b₂ xy.1 xy.2) :=
            Finset.sum_le_sum fun xy _ =>
              mul_le_mul_of_nonneg_left (hpt_dist C₁ C₂ b₁ b₂ xy.1 xy.2).1 ((jointIidDist P n).nonneg xy)
        _ = (Ed₁ + δ / 2) + dmax * codeErr ((C₁, C₂), (b₁, b₂)) := by
            dsimp only [codeErr]
            simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, (jointIidDist P n).sum_one,
              one_mul, Finset.mul_sum]
            congr 1; refine Finset.sum_congr rfl fun xy _ => by ring
    have h9c_nn : 0 ≤ 9 * c := by positivity
    have hmul1 : dmax * codeErr ((C₁, C₂), (b₁, b₂)) ≤ dmax * (9 * c) :=
      mul_le_mul_of_nonneg_left hcode hdmax0
    have hmul2 : dmax * (9 * c) ≤ B * (9 * c) := mul_le_mul_of_nonneg_right hdB h9c_nn
    linarith only [hsum_le, hBc, hmul1, hmul2]
  · have heq : (∑ x : Fin n → X₁ × X₂, (∏ i : Fin n, P.pmf (x i)) *
        ((1 / (n : ℝ)) * ∑ i : Fin n,
          d₂.dist (x i).2 (dec₂Of C₁ C₂ b₁ b₂ (enc₁Of C₁ b₁ (fun j => (x j).1),
            enc₂Of C₂ b₂ (fun j => (x j).2)) i))) =
        ∑ xy : (Fin n → X₁) × (Fin n → X₂), (jointIidDist P n).pmf xy *
          blockDist d₂ xy.2 (dec₂Of C₁ C₂ b₁ b₂ (enc₁Of C₁ b₁ xy.1, enc₂Of C₂ b₂ xy.2)) :=
      (Fintype.sum_equiv (zipEquiv X₁ X₂ n) _ _ (fun _ => rfl)).symm
    refine le_trans (le_of_eq ((bt_sum_fintype_congr fun _ => rfl).trans heq)) ?_
    have hsum_le : ∑ xy : (Fin n → X₁) × (Fin n → X₂), (jointIidDist P n).pmf xy *
          blockDist d₂ xy.2 (dec₂Of C₁ C₂ b₁ b₂ (enc₁Of C₁ b₁ xy.1, enc₂Of C₂ b₂ xy.2)) ≤
        (Ed₂ + δ / 2) + dmax * codeErr ((C₁, C₂), (b₁, b₂)) := by
      calc ∑ xy, (jointIidDist P n).pmf xy *
            blockDist d₂ xy.2 (dec₂Of C₁ C₂ b₁ b₂ (enc₁Of C₁ b₁ xy.1, enc₂Of C₂ b₂ xy.2))
        _ ≤ ∑ xy, (jointIidDist P n).pmf xy *
              ((Ed₂ + δ / 2) + dmax * E_tot C₁ C₂ b₁ b₂ xy.1 xy.2) :=
            Finset.sum_le_sum fun xy _ =>
              mul_le_mul_of_nonneg_left (hpt_dist C₁ C₂ b₁ b₂ xy.1 xy.2).2 ((jointIidDist P n).nonneg xy)
        _ = (Ed₂ + δ / 2) + dmax * codeErr ((C₁, C₂), (b₁, b₂)) := by
            dsimp only [codeErr]
            simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, (jointIidDist P n).sum_one,
              one_mul, Finset.mul_sum]
            congr 1; refine Finset.sum_congr rfl fun xy _ => by ring
    have h9c_nn : 0 ≤ 9 * c := by positivity
    have hmul1 : dmax * codeErr ((C₁, C₂), (b₁, b₂)) ≤ dmax * (9 * c) :=
      mul_le_mul_of_nonneg_left hcode hdmax0
    have hmul2 : dmax * (9 * c) ≤ B * (9 * c) := mul_le_mul_of_nonneg_right hdB h9c_nn
    linarith only [hsum_le, hBc, hmul1, hmul2]

open scoped Classical in
/-- **Single-Witness Berger–Tung Inner Bound Achievability** (Berger 1978; Tung 1978;
    El Gamal & Kim Theorem 12.1):
    for any valid single-letter witness `(kU₁, kU₂, Q, g₁, g₂)` satisfying `Q.map (X₁, X₂) = P`,
    `U₁ — X₁ — (X₂, U₂)`, and `U₂ — X₂ — (X₁, U₁)`, any rate pair `(R₁, R₂)` strictly inside
    the Berger–Tung pentagon (`R₁ > I(X₁; U₁ | U₂)`, `R₂ > I(X₂; U₂ | U₁)`,
    `R₁ + R₂ > I(X₁, X₂; U₁, U₂)`), and any `δ > 0`, for all sufficiently large `n` there exist
    encoders `enc₁, enc₂` and decoders `dec₁, dec₂` of sizes `Mᵢ = max 1 ⌊2^(n Rᵢ)⌋` achieving
    expected per-symbol distortions at most `E_Q[d₁(X₁, g₁(U₁, U₂))] + δ` and
    `E_Q[d₂(X₂, g₂(U₁, U₂))] + δ`. -/
theorem bergerTung_inner_achievability_of_dist
    (P : ProbDist (X₁ × X₂)) (d₁ : Distortion X₁ Xh₁) (d₂ : Distortion X₂ Xh₂)
    {kU₁ kU₂ : ℕ} (Q : ProbDist (X₁ × X₂ × Fin kU₁ × Fin kU₂))
    (g₁ : Fin kU₁ × Fin kU₂ → Xh₁) (g₂ : Fin kU₁ × Fin kU₂ → Xh₂)
    (hmarg : Q.map (fun t => (t.1, t.2.1)) = P)
    (hmk1 : condMutualInfo (Q.map (fun t => (t.2.2.1, (t.2.1, t.2.2.2), t.1))) = 0)
    (hmk2 : condMutualInfo (Q.map (fun t => (t.2.2.2, (t.1, t.2.2.1), t.2.1))) = 0)
    {R₁ R₂ δ : ℝ}
    (hR₁ : condMutualInfo (Q.map (fun t => (t.1, t.2.2.1, t.2.2.2))) < R₁)
    (hR₂ : condMutualInfo (Q.map (fun t => (t.2.1, t.2.2.2, t.2.2.1))) < R₂)
    (hR₁₂ : mutualInfo (Q.map (fun t => ((t.1, t.2.1), (t.2.2.1, t.2.2.2)))) < R₁ + R₂)
    (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N,
      let M₁ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁)))
      let M₂ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₂)))
      ∃ (enc₁ : (Fin n → X₁) → Fin M₁) (enc₂ : (Fin n → X₂) → Fin M₂)
        (dec₁ : Fin M₁ × Fin M₂ → Fin n → Xh₁)
        (dec₂ : Fin M₁ × Fin M₂ → Fin n → Xh₂),
        let Pn (x : Fin n → X₁ × X₂) : ℝ := ∏ i : Fin n, P.pmf (x i)
        (∑ x : Fin n → X₁ × X₂, Pn x *
          ((1 / (n : ℝ)) * ∑ i : Fin n,
            d₁.dist (x i).1 (dec₁ (enc₁ (fun j => (x j).1), enc₂ (fun j => (x j).2)) i))) ≤
          (∑ t, Q.pmf t * d₁.dist t.1 (g₁ (t.2.2.1, t.2.2.2))) + δ ∧
        (∑ x : Fin n → X₁ × X₂, Pn x *
          ((1 / (n : ℝ)) * ∑ i : Fin n,
            d₂.dist (x i).2 (dec₂ (enc₁ (fun j => (x j).1), enc₂ (fun j => (x j).2)) i))) ≤
          (∑ t, Q.pmf t * d₂.dist t.2.1 (g₂ (t.2.2.1, t.2.2.2))) + δ := by
  -- Marginals of `Q`.
  let Q₁ : ProbDist (X₁ × Fin kU₁) := Q.map (fun t => (t.1, t.2.2.1))
  let Q₂ : ProbDist (X₂ × Fin kU₂) := Q.map (fun t => (t.2.1, t.2.2.2))
  let Q₁₂ : ProbDist (Fin kU₁ × Fin kU₂) := Q.map (fun t => (t.2.2.1, t.2.2.2))
  let Q₁₂₁ : ProbDist (X₁ × X₂ × Fin kU₁) := Q.map (fun t => (t.1, t.2.1, t.2.2.1))
  let Qu₁ : ProbDist (Fin kU₁) := Q₁.snd
  let Qu₂ : ProbDist (Fin kU₂) := Q₂.snd
  have hQ₁_fst : Q₁.fst = P.fst := by
    rw [← bt_probDist_map_fst, ← bt_probDist_map_fst, ← hmarg]; unfold Q₁; rw [map_comp_eq, map_comp_eq]; rfl
  have hQ₂_fst : Q₂.fst = P.snd := by
    rw [← bt_probDist_map_fst, ← bt_probDist_map_snd, ← hmarg]; unfold Q₂; rw [map_comp_eq, map_comp_eq]; rfl
  have hQ₁₂_fst : Q₁₂.fst = Qu₁ := by
    unfold Qu₁; rw [← bt_probDist_map_fst, ← bt_probDist_map_snd]; unfold Q₁₂ Q₁; rw [map_comp_eq, map_comp_eq]; rfl
  have hQ₁₂_snd : Q₁₂.snd = Qu₂ := by
    unfold Qu₂; rw [← bt_probDist_map_snd, ← bt_probDist_map_snd]; unfold Q₁₂ Q₂; rw [map_comp_eq, map_comp_eq]; rfl
  have hQ₁₂₁_marg : Q₁₂₁.map (fun t => (t.1, t.2.1)) = P := by
    unfold Q₁₂₁; rw [map_comp_eq]; exact hmarg
  have hQ₁₂₁_xu : Q₁₂₁.map (fun t => (t.1, t.2.2)) = Q₁ := by
    unfold Q₁₂₁ Q₁; rw [map_comp_eq]; rfl
  -- Sub-Markov chains extracted from `hmk1` and `hmk2`.
  have hU1_X2_X1 : condMutualInfo (Q₁₂₁.map (fun t => (t.2.2, t.2.1, t.1))) = 0 := by
    let R1 : ProbDist (Fin kU₁ × X₂ × Fin kU₂ × X₁) := Q.map (fun t => (t.2.2.1, t.2.1, t.2.2.2, t.1))
    have hR1 : condMutualInfo (R1.map (fun t => (t.1, (t.2.1, t.2.2.1), t.2.2.2))) = 0 := by
      unfold R1; rw [map_comp_eq]; exact hmk1
    have h := (bt_condMutualInfo_zero_split R1 hR1).1
    unfold R1 at h; rw [map_comp_eq] at h
    unfold Q₁₂₁; rw [map_comp_eq]; exact h
  have hU1_U2_X1 : condMutualInfo (Q.map (fun t => (t.2.2.1, t.2.2.2, t.1))) = 0 := by
    let R1 : ProbDist (Fin kU₁ × X₂ × Fin kU₂ × X₁) := Q.map (fun t => (t.2.2.1, t.2.1, t.2.2.2, t.1))
    have hR1 : condMutualInfo (R1.map (fun t => (t.1, (t.2.1, t.2.2.1), t.2.2.2))) = 0 := by
      unfold R1; rw [map_comp_eq]; exact hmk1
    have h := (bt_condMutualInfo_zero_split_swap R1 hR1).1
    unfold R1 at h; rw [map_comp_eq] at h; exact h
  have hU2_U1_X2 : condMutualInfo (Q.map (fun t => (t.2.2.2, t.2.2.1, t.2.1))) = 0 := by
    let R2 : ProbDist (Fin kU₂ × X₁ × Fin kU₁ × X₂) := Q.map (fun t => (t.2.2.2, t.1, t.2.2.1, t.2.1))
    have hR2 : condMutualInfo (R2.map (fun t => (t.1, (t.2.1, t.2.2.1), t.2.2.2))) = 0 := by
      unfold R2; rw [map_comp_eq]; exact hmk2
    have h := (bt_condMutualInfo_zero_split_swap R2 hR2).1
    unfold R2 at h; rw [map_comp_eq] at h; exact h
  -- Exact mutual-information identities for the 3 Berger–Tung rate bounds.
  have hI1_eq : condMutualInfo (Q.map (fun t => (t.1, t.2.2.1, t.2.2.2))) =
      mutualInfo Q₁ - mutualInfo Q₁₂ := by
    have h := bt_cmi_eq_sub_of_markov (Q.map (fun t => (t.1, t.2.2.1, t.2.2.2))) (by
      rw [map_comp_eq]; exact hU1_U2_X1)
    rw [h, map_comp_eq, map_comp_eq]; rfl
  have hI2_eq : condMutualInfo (Q.map (fun t => (t.2.1, t.2.2.2, t.2.2.1))) =
      mutualInfo Q₂ - mutualInfo Q₁₂ := by
    have h := bt_cmi_eq_sub_of_markov (Q.map (fun t => (t.2.1, t.2.2.2, t.2.2.1))) (by
      rw [map_comp_eq]; exact hU2_U1_X2)
    rw [h, map_comp_eq, map_comp_eq]
    have hsw : mutualInfo (Q.map ((fun t : X₂ × Fin kU₂ × Fin kU₁ => (t.2.1, t.2.2)) ∘
        fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => (t.2.1, t.2.2.2, t.2.2.1))) = mutualInfo Q₁₂ := by
      have heq : Q.map ((fun t : X₂ × Fin kU₂ × Fin kU₁ => (t.2.1, t.2.2)) ∘
          fun t : X₁ × X₂ × Fin kU₁ × Fin kU₂ => (t.2.1, t.2.2.2, t.2.2.1)) = Q₁₂.map Prod.swap := by
        unfold Q₁₂; rw [map_comp_eq]; rfl
      rw [heq, bt_mutualInfo_symm]
    rw [hsw]; rfl
  have hI12_eq : mutualInfo (Q.map (fun t => ((t.1, t.2.1), (t.2.2.1, t.2.2.2)))) =
      mutualInfo Q₁ + mutualInfo Q₂ - mutualInfo Q₁₂ :=
    bt_mi_X1X2_U1U2_eq_sum_sub Q hmk1 hmk2
  have hR₁_pos : 0 < R₁ := lt_of_le_of_lt (condMutualInfo_nonneg _) hR₁
  have hR₂_pos : 0 < R₂ := lt_of_le_of_lt (condMutualInfo_nonneg _) hR₂
  -- Parameters.
  let gap : ℝ := min (R₁ - condMutualInfo (Q.map (fun t => (t.1, t.2.2.1, t.2.2.2))))
    (min (R₂ - condMutualInfo (Q.map (fun t => (t.2.1, t.2.2.2, t.2.2.1))))
      (R₁ + R₂ - mutualInfo (Q.map (fun t => ((t.1, t.2.1), (t.2.2.1, t.2.2.2))))))
  have hgap : 0 < gap := lt_min (by linarith only [hR₁]) (lt_min (by linarith only [hR₂]) (by linarith only [hR₁₂]))
  have hgap1 : gap ≤ R₁ - (mutualInfo Q₁ - mutualInfo Q₁₂) := by
    rw [← hI1_eq]; exact min_le_left _ _
  have hgap2 : gap ≤ R₂ - (mutualInfo Q₂ - mutualInfo Q₁₂) := by
    rw [← hI2_eq]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hgap12 : gap ≤ R₁ + R₂ - (mutualInfo Q₁ + mutualInfo Q₂ - mutualInfo Q₁₂) := by
    rw [← hI12_eq]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  let Ed₁ : ℝ := ∑ t, Q.pmf t * d₁.dist t.1 (g₁ (t.2.2.1, t.2.2.2))
  let Ed₂ : ℝ := ∑ t, Q.pmf t * d₂.dist t.2.1 (g₂ (t.2.2.1, t.2.2.2))
  have hEd₁0 : 0 ≤ Ed₁ := Finset.sum_nonneg fun t _ => mul_nonneg (Q.nonneg t) (d₁.nonneg _ _)
  have hEd₂0 : 0 ≤ Ed₂ := Finset.sum_nonneg fun t _ => mul_nonneg (Q.nonneg t) (d₂.nonneg _ _)
  let dmax₁ : ℝ := ∑ p : X₁ × Xh₁, d₁.dist p.1 p.2
  let dmax₂ : ℝ := ∑ p : X₂ × Xh₂, d₂.dist p.1 p.2
  let dmax : ℝ := max dmax₁ dmax₂
  have hdmax₁0 : 0 ≤ dmax₁ := Finset.sum_nonneg fun p _ => d₁.nonneg p.1 p.2
  have hdmax₂0 : 0 ≤ dmax₂ := Finset.sum_nonneg fun p _ => d₂.nonneg p.1 p.2
  have hdmax0 : 0 ≤ dmax := le_trans hdmax₁0 (le_max_left _ _)
  have hd1_le : ∀ x xh, d₁.dist x xh ≤ dmax := fun x xh =>
    le_trans (Finset.single_le_sum (f := fun p : X₁ × Xh₁ => d₁.dist p.1 p.2)
      (fun p _ => d₁.nonneg p.1 p.2) (Finset.mem_univ (x, xh)))
      (le_max_left _ _)
  have hd2_le : ∀ x xh, d₂.dist x xh ≤ dmax := fun x xh =>
    le_trans (Finset.single_le_sum (f := fun p : X₂ × Xh₂ => d₂.dist p.1 p.2)
      (fun p _ => d₂.nonneg p.1 p.2) (Finset.mem_univ (x, xh)))
      (le_max_right _ _)
  let B : ℝ := dmax + 1
  have hB : 0 < B := by dsimp only [B]; linarith only [hdmax0]
  let Hmax : ℝ :=
    shannonEntropy Q₁.fst + shannonEntropy Q₁.snd + shannonEntropy Q₁ +
    shannonEntropy Q₂.fst + shannonEntropy Q₂.snd + shannonEntropy Q₂ +
    shannonEntropy Q₁₂.fst + shannonEntropy Q₁₂.snd + shannonEntropy Q₁₂ + 1
  have hHmax : 1 ≤ Hmax := by
    dsimp only [Hmax]
    linarith only [shannonEntropy_nonneg Q₁.fst, shannonEntropy_nonneg Q₁.snd, shannonEntropy_nonneg Q₁,
      shannonEntropy_nonneg Q₂.fst, shannonEntropy_nonneg Q₂.snd, shannonEntropy_nonneg Q₂,
      shannonEntropy_nonneg Q₁₂.fst, shannonEntropy_nonneg Q₁₂.snd, shannonEntropy_nonneg Q₁₂]
  have hHmax_pos : 0 < Hmax := by linarith only [hHmax]
  let ε₃ : ℝ := min 1 (min (δ / (2 * (Ed₁ + Ed₂ + 1))) (gap / (40 * Hmax)))
  have hε₃ : 0 < ε₃ := lt_min zero_lt_one (lt_min
    (div_pos hδ (by linarith only [hEd₁0, hEd₂0]))
    (div_pos hgap (by linarith only [hHmax_pos])))
  have hε₃_le1 : ε₃ ≤ 1 := min_le_left _ _
  have hε₃_Ed : ε₃ * (Ed₁ + Ed₂ + 1) ≤ δ / 2 := by
    have h1 : ε₃ ≤ δ / (2 * (Ed₁ + Ed₂ + 1)) := le_trans (min_le_right _ _) (min_le_left _ _)
    have hpos : (0 : ℝ) < Ed₁ + Ed₂ + 1 := by linarith only [hEd₁0, hEd₂0]
    calc ε₃ * (Ed₁ + Ed₂ + 1)
      _ ≤ (δ / (2 * (Ed₁ + Ed₂ + 1))) * (Ed₁ + Ed₂ + 1) := mul_le_mul_of_nonneg_right h1 (le_of_lt hpos)
      _ = δ / 2 := by field_simp [ne_of_gt hpos]
  have hε₃_Ed₁ : ε₃ * Ed₁ ≤ δ / 2 :=
    le_trans (mul_le_mul_of_nonneg_left (by linarith only [hEd₂0]) (le_of_lt hε₃)) hε₃_Ed
  have hε₃_Ed₂ : ε₃ * Ed₂ ≤ δ / 2 :=
    le_trans (mul_le_mul_of_nonneg_left (by linarith only [hEd₁0]) (le_of_lt hε₃)) hε₃_Ed
  have hε₃_gap : ε₃ * Hmax ≤ gap / 40 := by
    have h1 : ε₃ ≤ gap / (40 * Hmax) := le_trans (min_le_right _ _) (min_le_right _ _)
    calc ε₃ * Hmax ≤ (gap / (40 * Hmax)) * Hmax := mul_le_mul_of_nonneg_right h1 (le_of_lt hHmax_pos)
      _ = gap / 40 := by field_simp [ne_of_gt hHmax_pos]
  let ε₂ : ℝ := ε₃ / 4
  let ε₁ : ℝ := ε₃ / 16
  have hε₁ : 0 < ε₁ := by dsimp only [ε₁]; linarith only [hε₃]
  have hε₁_lt_ε₂ : ε₁ < ε₂ := by dsimp only [ε₁, ε₂]; linarith only [hε₃]
  let ε_c : ℝ := ε₁ * Hmax
  let ε_b : ℝ := ε₃ * Hmax
  have hε_c : 0 < ε_c := mul_pos hε₁ hHmax_pos
  have hε_b : 0 < ε_b := mul_pos hε₃ hHmax_pos
  let R₁' : ℝ := mutualInfo Q₁ + 3 * ε_c + gap / 8
  let R₂' : ℝ := mutualInfo Q₂ + 3 * ε_c + gap / 8
  have hR1'_gt : mutualInfo Q₁ + 3 * ε_c < R₁' := by dsimp only [R₁']; linarith only [hgap]
  have hR2'_gt : mutualInfo Q₂ + 3 * ε_c < R₂' := by dsimp only [R₂']; linarith only [hgap]
  have hR1'_nn : 0 ≤ R₁' := by dsimp only [R₁']; linarith only [mutualInfo_nonneg Q₁, hε_c, hgap]
  have hR2'_nn : 0 ≤ R₂' := by dsimp only [R₂']; linarith only [mutualInfo_nonneg Q₂, hε_c, hgap]
  -- Threshold `c := δ / (18 * B)` so that `9 * c * B = δ / 2`.
  let c : ℝ := δ / (18 * B)
  have hc : 0 < c := div_pos hδ (by linarith only [hB])
  -- Thresholds for all decaying terms.
  obtain ⟨N₁, hN₁⟩ := strongTypicalSet_prob_tendsto_one Q₁ hε₁ hc
  obtain ⟨N₂, hN₂⟩ := strongTypicalSet_prob_tendsto_one Q₂ hε₁ hc
  obtain ⟨N₃, hN₃⟩ := bt_covering_exp_le (mutualInfo_nonneg Q₁) (le_of_lt hε_c) hR1'_gt hc
  obtain ⟨N₄, hN₄⟩ := bt_covering_exp_le (mutualInfo_nonneg Q₂) (le_of_lt hε_c) hR2'_gt hc
  let C_M1 : ℝ := ∑ t : X₁ × X₂ × Fin kU₁, if 0 < Q₁₂₁.pmf t then 1 / Q₁₂₁.pmf t ^ 2 else 0
  let C_M2 : ℝ := 4 * ∑ t : X₁ × X₂ × Fin kU₁ × Fin kU₂, if 0 < Q.pmf t then 1 / Q.pmf t ^ 2 else 0
  obtain ⟨N₅, hN₅⟩ := exists_nat_gt (C_M1 / (c * (ε₂ - ε₁) ^ 2))
  obtain ⟨N₆, hN₆⟩ := exists_nat_gt (C_M2 / (c * ε₃ ^ 2))
  obtain ⟨N₇, hN₇⟩ := exists_nat_gt (log2 (1 / (c / 4)) / (gap / 2))
  let Nall : ℕ := max (max (max N₁ N₂) (max N₃ N₄)) (max (max N₅ N₆) (max N₇ 1))
  refine ⟨Nall, fun n hn => ?_⟩
  dsimp only
  have hn_pos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one
    (le_trans (le_max_right N₇ 1) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn)))
  have hn_r : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  have hn1 : N₁ ≤ n := le_trans (le_max_left N₁ N₂) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn))
  have hn2 : N₂ ≤ n := le_trans (le_max_right N₁ N₂) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn))
  have hn3 : N₃ ≤ n := le_trans (le_max_left N₃ N₄) (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn))
  have hn4 : N₄ ≤ n := le_trans (le_max_right N₃ N₄) (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn))
  have hn5 : C_M1 / (c * (ε₂ - ε₁) ^ 2) < (n : ℝ) := lt_of_lt_of_le hN₅ (by
    exact_mod_cast le_trans (le_max_left N₅ N₆) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn)))
  have hn6 : C_M2 / (c * ε₃ ^ 2) < (n : ℝ) := lt_of_lt_of_le hN₆ (by
    exact_mod_cast le_trans (le_max_right N₅ N₆) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn)))
  have hn7 : log2 (1 / (c / 4)) / (gap / 2) ≤ (n : ℝ) := le_of_lt (lt_of_lt_of_le hN₇ (by
    exact_mod_cast le_trans (le_max_left N₇ 1) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn))))
  set M_b1 := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁)))
  set M_b2 := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₂)))
  set M_c1 := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁')))
  set M_c2 := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₂')))
  have hMb1_pos : 0 < M_b1 := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
  have hMb2_pos : 0 < M_b2 := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
  have hMc1_pos : 0 < M_c1 := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
  have hMc2_pos : 0 < M_c2 := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
  have hH1f_nn := shannonEntropy_nonneg Q₁.fst
  have hH1s_nn := shannonEntropy_nonneg Q₁.snd
  have hH1_nn := shannonEntropy_nonneg Q₁
  have hH2f_nn := shannonEntropy_nonneg Q₂.fst
  have hH2s_nn := shannonEntropy_nonneg Q₂.snd
  have hH2_nn := shannonEntropy_nonneg Q₂
  have hH12f_nn := shannonEntropy_nonneg Q₁₂.fst
  have hH12s_nn := shannonEntropy_nonneg Q₁₂.snd
  have hH12_nn := shannonEntropy_nonneg Q₁₂
  have hH1f : shannonEntropy Q₁.fst ≤ Hmax := by dsimp only [Hmax]; linarith only [hH1s_nn, hH1_nn, hH2f_nn, hH2s_nn, hH2_nn, hH12f_nn, hH12s_nn, hH12_nn]
  have hH1s : shannonEntropy Q₁.snd ≤ Hmax := by dsimp only [Hmax]; linarith only [hH1f_nn, hH1_nn, hH2f_nn, hH2s_nn, hH2_nn, hH12f_nn, hH12s_nn, hH12_nn]
  have hH1 : shannonEntropy Q₁ ≤ Hmax := by dsimp only [Hmax]; linarith only [hH1f_nn, hH1s_nn, hH2f_nn, hH2s_nn, hH2_nn, hH12f_nn, hH12s_nn, hH12_nn]
  have hH2f : shannonEntropy Q₂.fst ≤ Hmax := by dsimp only [Hmax]; linarith only [hH1f_nn, hH1s_nn, hH1_nn, hH2s_nn, hH2_nn, hH12f_nn, hH12s_nn, hH12_nn]
  have hH2s : shannonEntropy Q₂.snd ≤ Hmax := by dsimp only [Hmax]; linarith only [hH1f_nn, hH1s_nn, hH1_nn, hH2f_nn, hH2_nn, hH12f_nn, hH12s_nn, hH12_nn]
  have hH2 : shannonEntropy Q₂ ≤ Hmax := by dsimp only [Hmax]; linarith only [hH1f_nn, hH1s_nn, hH1_nn, hH2f_nn, hH2s_nn, hH12f_nn, hH12s_nn, hH12_nn]
  have hH12f : shannonEntropy Q₁₂.fst ≤ Hmax := by dsimp only [Hmax]; linarith only [hH1f_nn, hH1s_nn, hH1_nn, hH2f_nn, hH2s_nn, hH2_nn, hH12s_nn, hH12_nn]
  have hH12s : shannonEntropy Q₁₂.snd ≤ Hmax := by dsimp only [Hmax]; linarith only [hH1f_nn, hH1s_nn, hH1_nn, hH2f_nn, hH2s_nn, hH2_nn, hH12f_nn, hH12_nn]
  have hH12 : shannonEntropy Q₁₂ ≤ Hmax := by dsimp only [Hmax]; linarith only [hH1f_nn, hH1s_nn, hH1_nn, hH2f_nn, hH2s_nn, hH2_nn, hH12f_nn, hH12s_nn]
  have hMc1_le : (M_c1 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R₁') := bt_max_one_floor_two_rpow_le n hR1'_nn
  have hMc2_le : (M_c2 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R₂') := bt_max_one_floor_two_rpow_le n hR2'_nn
  have hMb1_ge : (2 : ℝ) ^ ((n : ℝ) * R₁) / 2 ≤ (M_b1 : ℝ) := bt_half_two_rpow_le_max_one_floor n (le_of_lt hR₁_pos)
  have hMb2_ge : (2 : ℝ) ^ ((n : ℝ) * R₂) / 2 ≤ (M_b2 : ℝ) := bt_half_two_rpow_le_max_one_floor n (le_of_lt hR₂_pos)
  have hratio1 : (M_c1 : ℝ) / (M_b1 : ℝ) ≤ 2 * (2 : ℝ) ^ ((n : ℝ) * (R₁' - R₁)) := by
    have h1 : (M_c1 : ℝ) / (M_b1 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R₁') / ((2 : ℝ) ^ ((n : ℝ) * R₁) / 2) :=
      div_le_div₀ (by positivity) hMc1_le (by positivity) hMb1_ge
    have h2 : (2 : ℝ) ^ ((n : ℝ) * R₁') / ((2 : ℝ) ^ ((n : ℝ) * R₁) / 2) =
        2 * (2 : ℝ) ^ ((n : ℝ) * (R₁' - R₁)) := by
      rw [div_div_eq_mul_div, mul_comm, mul_div_assoc, ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
      congr 2; ring
    linarith only [h1, h2]
  have hratio2 : (M_c2 : ℝ) / (M_b2 : ℝ) ≤ 2 * (2 : ℝ) ^ ((n : ℝ) * (R₂' - R₂)) := by
    have h1 : (M_c2 : ℝ) / (M_b2 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R₂') / ((2 : ℝ) ^ ((n : ℝ) * R₂) / 2) :=
      div_le_div₀ (by positivity) hMc2_le (by positivity) hMb2_ge
    have h2 : (2 : ℝ) ^ ((n : ℝ) * R₂') / ((2 : ℝ) ^ ((n : ℝ) * R₂) / 2) =
        2 * (2 : ℝ) ^ ((n : ℝ) * (R₂' - R₂)) := by
      rw [div_div_eq_mul_div, mul_comm, mul_div_assoc, ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
      congr 2; ring
    linarith only [h1, h2]
  have hdecay4 : 4 * (2 : ℝ) ^ (-((n : ℝ) * (gap / 2))) ≤ c := by
    have h2 := bt_two_rpow_neg_le_of_ge (half_pos hgap) (by positivity : 0 < c / 4) hn7
    linarith only [h2]
  have hdecay2 : 2 * (2 : ℝ) ^ (-((n : ℝ) * (gap / 2))) ≤ c := by
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (-((n : ℝ) * (gap / 2))) := Real.rpow_pos_of_pos (by norm_num) _
    linarith only [hdecay4, hpos]
  have hmul16 : (ε₃ / 16) * Hmax = (ε₃ * Hmax) / 16 := by ring
  have hbin1_bd : ((M_c1 : ℝ) / (M_b1 : ℝ)) * (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Q₁₂ - 3 * ε_b))) ≤ c := by
    have hexp1 : (n : ℝ) * (R₁' - R₁) + -((n : ℝ) * (mutualInfo Q₁₂ - 3 * ε_b)) ≤ -((n : ℝ) * (gap / 2)) := by
      have hcoef : R₁' - R₁ - (mutualInfo Q₁₂ - 3 * ε_b) ≤ -(gap / 2) := by
        dsimp only [R₁', ε_c, ε_b, ε₁]; rw [hmul16]; linarith only [hgap1, hε₃_gap, hgap]
      have hmul := mul_le_mul_of_nonneg_left hcoef (le_of_lt hn_r)
      linarith only [hmul]
    calc ((M_c1 : ℝ) / (M_b1 : ℝ)) * (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Q₁₂ - 3 * ε_b)))
      _ ≤ (2 * (2 : ℝ) ^ ((n : ℝ) * (R₁' - R₁))) * (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Q₁₂ - 3 * ε_b))) :=
          mul_le_mul_of_nonneg_right hratio1 (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
      _ = 2 * (2 : ℝ) ^ ((n : ℝ) * (R₁' - R₁) + -((n : ℝ) * (mutualInfo Q₁₂ - 3 * ε_b))) := by
          rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ ≤ 2 * (2 : ℝ) ^ (-((n : ℝ) * (gap / 2))) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp1) (by norm_num)
      _ ≤ c := hdecay2
  have hbin2_bd : ((M_c2 : ℝ) / (M_b2 : ℝ)) * (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Q₁₂ - 3 * ε_b))) ≤ c := by
    have hexp2 : (n : ℝ) * (R₂' - R₂) + -((n : ℝ) * (mutualInfo Q₁₂ - 3 * ε_b)) ≤ -((n : ℝ) * (gap / 2)) := by
      have hcoef : R₂' - R₂ - (mutualInfo Q₁₂ - 3 * ε_b) ≤ -(gap / 2) := by
        dsimp only [R₂', ε_c, ε_b, ε₁]; rw [hmul16]; linarith only [hgap2, hε₃_gap, hgap]
      have hmul := mul_le_mul_of_nonneg_left hcoef (le_of_lt hn_r)
      linarith only [hmul]
    calc ((M_c2 : ℝ) / (M_b2 : ℝ)) * (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Q₁₂ - 3 * ε_b)))
      _ ≤ (2 * (2 : ℝ) ^ ((n : ℝ) * (R₂' - R₂))) * (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Q₁₂ - 3 * ε_b))) :=
          mul_le_mul_of_nonneg_right hratio2 (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
      _ = 2 * (2 : ℝ) ^ ((n : ℝ) * (R₂' - R₂) + -((n : ℝ) * (mutualInfo Q₁₂ - 3 * ε_b))) := by
          rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ ≤ 2 * (2 : ℝ) ^ (-((n : ℝ) * (gap / 2))) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp2) (by norm_num)
      _ ≤ c := hdecay2
  have hbin12_bd : (((M_c1 : ℝ) / (M_b1 : ℝ)) * ((M_c2 : ℝ) / (M_b2 : ℝ))) *
      (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Q₁₂ - 3 * ε_b))) ≤ c := by
    have hratio12 : ((M_c1 : ℝ) / (M_b1 : ℝ)) * ((M_c2 : ℝ) / (M_b2 : ℝ)) ≤
        4 * (2 : ℝ) ^ ((n : ℝ) * (R₁' - R₁ + (R₂' - R₂))) := by
      have hmul := mul_le_mul hratio1 hratio2 (by positivity) (by positivity)
      have heq : (2 * (2 : ℝ) ^ ((n : ℝ) * (R₁' - R₁))) * (2 * (2 : ℝ) ^ ((n : ℝ) * (R₂' - R₂))) =
          4 * (2 : ℝ) ^ ((n : ℝ) * (R₁' - R₁ + (R₂' - R₂))) := by
        have hadd : (2 : ℝ) ^ ((n : ℝ) * (R₁' - R₁)) * (2 : ℝ) ^ ((n : ℝ) * (R₂' - R₂)) =
            (2 : ℝ) ^ ((n : ℝ) * (R₁' - R₁ + (R₂' - R₂))) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; congr 1; ring
        linarith only [hadd]
      linarith only [hmul, heq]
    have hexp12 : (n : ℝ) * (R₁' - R₁ + (R₂' - R₂)) + -((n : ℝ) * (mutualInfo Q₁₂ - 3 * ε_b)) ≤
        -((n : ℝ) * (gap / 2)) := by
      have hcoef : R₁' - R₁ + (R₂' - R₂) - (mutualInfo Q₁₂ - 3 * ε_b) ≤ -(gap / 2) := by
        dsimp only [R₁', R₂', ε_c, ε_b, ε₁]; rw [hmul16]; linarith only [hgap12, hε₃_gap, hgap]
      have hmul := mul_le_mul_of_nonneg_left hcoef (le_of_lt hn_r)
      linarith only [hmul]
    calc (((M_c1 : ℝ) / (M_b1 : ℝ)) * ((M_c2 : ℝ) / (M_b2 : ℝ))) *
          (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Q₁₂ - 3 * ε_b)))
      _ ≤ (4 * (2 : ℝ) ^ ((n : ℝ) * (R₁' - R₁ + (R₂' - R₂)))) *
            (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Q₁₂ - 3 * ε_b))) :=
          mul_le_mul_of_nonneg_right hratio12 (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
      _ = 4 * (2 : ℝ) ^ ((n : ℝ) * (R₁' - R₁ + (R₂' - R₂)) + -((n : ℝ) * (mutualInfo Q₁₂ - 3 * ε_b))) := by
          rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ ≤ 4 * (2 : ℝ) ^ (-((n : ℝ) * (gap / 2))) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp12) (by norm_num)
      _ ≤ c := hdecay4
  have hmk1_bd : C_M1 / ((n : ℝ) * (ε₂ - ε₁) ^ 2) ≤ c := by
    have hdiff : 0 < ε₂ - ε₁ := by linarith only [hε₁_lt_ε₂]
    have hsq : 0 < (ε₂ - ε₁) ^ 2 := sq_pos_of_pos hdiff
    rw [div_le_iff₀ (mul_pos hn_r hsq)]
    have h1 := (div_lt_iff₀ (mul_pos hc hsq)).mp hn5
    linarith only [h1]
  have hmk2_bd : C_M2 / ((n : ℝ) * ε₃ ^ 2) ≤ c := by
    have hsq : 0 < ε₃ ^ 2 := sq_pos_of_pos hε₃
    rw [div_le_iff₀ (mul_pos hn_r hsq)]
    have h1 := (div_lt_iff₀ (mul_pos hc hsq)).mp hn6
    linarith only [h1]
  exact bt_achiev_fixed_n P d₁ d₂ Q g₁ g₂
    (M_b1 := M_b1) (M_b2 := M_b2) (M_c1 := M_c1) (M_c2 := M_c2)
    (ε₁ := ε₁) (ε₂ := ε₂) (ε₃ := ε₃) (ε_c := ε_c) (ε_b := ε_b) (δ := δ) (c := c) (dmax := dmax) (B := B)
    ⟨hmarg, hmk1, hmk2, ⟨hn_pos, hMb1_pos, hMb2_pos, hMc1_pos, hMc2_pos⟩,
     ⟨hδ, hc, hdmax0, le_add_of_nonneg_right zero_le_one, by dsimp [c]; field_simp [ne_of_gt hB]; ring⟩,
     ⟨hd1_le, hd2_le⟩, ⟨hε₁, hε₁_lt_ε₂, hε₃, hε₃_le1, hε_c, rfl, rfl⟩,
     ⟨hε₃_Ed₁, hε₃_Ed₂⟩,
     ⟨mul_le_mul_of_nonneg_left hH1f (le_of_lt hε₁),
      mul_le_mul_of_nonneg_left hH1s (le_of_lt hε₁),
      mul_le_mul_of_nonneg_left hH1 (le_of_lt hε₁),
      mul_le_mul_of_nonneg_left hH2f (le_of_lt hε₁),
      mul_le_mul_of_nonneg_left hH2s (le_of_lt hε₁),
      mul_le_mul_of_nonneg_left hH2 (le_of_lt hε₁),
      mul_le_mul_of_nonneg_left hH12f (le_of_lt hε₃),
      mul_le_mul_of_nonneg_left hH12s (le_of_lt hε₃),
      mul_le_mul_of_nonneg_left hH12 (le_of_lt hε₃)⟩,
     ⟨by linarith only [hN₁ n hn1], by linarith only [hN₂ n hn2], hN₃ n hn3, hN₄ n hn4⟩,
     ⟨hmk1_bd, hmk2_bd⟩, ⟨hbin1_bd, hbin2_bd, hbin12_bd⟩⟩

/-- **Operational Berger–Tung Inner Bound Achievability** (Berger 1978; Tung 1978;
    El Gamal & Kim Theorem 12.1):
    every rate pair `(R₁, R₂)` in `bergerTungInnerBound P d₁ d₂ D₁ D₂` is operationally
    achievable (`IsBergerTungAchievable P d₁ d₂ R₁ R₂ D₁ D₂`). -/
theorem bergerTung_inner_achievability
    (P : ProbDist (X₁ × X₂)) (d₁ : Distortion X₁ Xh₁) (d₂ : Distortion X₂ Xh₂)
    {R₁ R₂ D₁ D₂ : ℝ}
    (hr : (R₁, R₂) ∈ bergerTungInnerBound P d₁ d₂ D₁ D₂) :
    IsBergerTungAchievable P d₁ d₂ R₁ R₂ D₁ D₂ := by
  rcases hr with ⟨hR₁0, hR₂0, kU₁, kU₂, Q, g₁, g₂, hmarg, hmk1, hmk2, hd₁, hd₂, hR₁, hR₂, hR₁₂⟩
  refine ⟨hR₁0, hR₂0, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := bergerTung_inner_achievability_of_dist P d₁ d₂ Q g₁ g₂ hmarg hmk1 hmk2
    (R₁ := R₁ + ε) (R₂ := R₂ + ε) (δ := ε) (by linarith) (by linarith) (by linarith) hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨enc₁, enc₂, dec₁, dec₂, h1, h2⟩ := hN n hn
  exact ⟨enc₁, enc₂, dec₁, dec₂, by linarith, by linarith⟩

omit [Fintype X₁] [Fintype X₂] [Fintype Xh₁] [Fintype Xh₂] in
/-- Helper: widening message alphabet sizes `M₁ ≤ M₁'`, `M₂ ≤ M₂'` preserves block distortions. -/
private lemma bt_widen_block_code {n M₁ M₂ M₁' M₂' : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (h1 : M₁ ≤ M₁') (h2 : M₂ ≤ M₂')
    (enc₁ : (Fin n → X₁) → Fin M₁) (enc₂ : (Fin n → X₂) → Fin M₂)
    (dec₁ : Fin M₁ × Fin M₂ → Fin n → Xh₁) (dec₂ : Fin M₁ × Fin M₂ → Fin n → Xh₂) :
    ∃ (enc₁' : (Fin n → X₁) → Fin M₁') (enc₂' : (Fin n → X₂) → Fin M₂')
      (dec₁' : Fin M₁' × Fin M₂' → Fin n → Xh₁) (dec₂' : Fin M₁' × Fin M₂' → Fin n → Xh₂),
      (∀ x₁ x₂, dec₁' (enc₁' x₁, enc₂' x₂) = dec₁ (enc₁ x₁, enc₂ x₂)) ∧
      (∀ x₁ x₂, dec₂' (enc₁' x₁, enc₂' x₂) = dec₂ (enc₁ x₁, enc₂ x₂)) := by
  let enc₁' : (Fin n → X₁) → Fin M₁' := fun x => Fin.castLE h1 (enc₁ x)
  let enc₂' : (Fin n → X₂) → Fin M₂' := fun x => Fin.castLE h2 (enc₂ x)
  let proj₁ : Fin M₁' → Fin M₁ := fun m => if h : m.1 < M₁ then ⟨m.1, h⟩ else ⟨0, hM₁⟩
  let proj₂ : Fin M₂' → Fin M₂ := fun m => if h : m.1 < M₂ then ⟨m.1, h⟩ else ⟨0, hM₂⟩
  have hp1 : ∀ m : Fin M₁, proj₁ (Fin.castLE h1 m) = m := fun m => by
    dsimp [proj₁, Fin.castLE]; simp [m.2]
  have hp2 : ∀ m : Fin M₂, proj₂ (Fin.castLE h2 m) = m := fun m => by
    dsimp [proj₂, Fin.castLE]; simp [m.2]
  exact ⟨enc₁', enc₂', fun m => dec₁ (proj₁ m.1, proj₂ m.2), fun m => dec₂ (proj₁ m.1, proj₂ m.2),
    fun x₁ x₂ => by dsimp [enc₁', enc₂']; rw [hp1, hp2],
    fun x₁ x₂ => by dsimp [enc₁', enc₂']; rw [hp1, hp2]⟩

/-- Monotonicity of `IsBergerTungAchievable` in `(R₁, R₂, D₁, D₂)`. -/
theorem isBergerTungAchievable_mono
    {P : ProbDist (X₁ × X₂)} {d₁ : Distortion X₁ Xh₁} {d₂ : Distortion X₂ Xh₂}
    {R₁ R₂ D₁ D₂ R₁' R₂' D₁' D₂' : ℝ}
    (h : IsBergerTungAchievable P d₁ d₂ R₁ R₂ D₁ D₂)
    (hR₁ : R₁ ≤ R₁') (hR₂ : R₂ ≤ R₂') (hD₁ : D₁ ≤ D₁') (hD₂ : D₂ ≤ D₂') :
    IsBergerTungAchievable P d₁ d₂ R₁' R₂' D₁' D₂' := by
  rcases h with ⟨h01, h02, hach⟩
  refine ⟨le_trans h01 hR₁, le_trans h02 hR₂, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hach ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨enc₁, enc₂, dec₁, dec₂, hd₁, hd₂⟩ := hN n hn
  have hM₁_le : Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * (R₁ + ε)))) ≤
      Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * (R₁' + ε)))) :=
    max_le_max le_rfl (Nat.floor_mono
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg n))))
  have hM₂_le : Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * (R₂ + ε)))) ≤
      Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * (R₂' + ε)))) :=
    max_le_max le_rfl (Nat.floor_mono
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg n))))
  have hM₁_pos : 0 < Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * (R₁ + ε)))) :=
    lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
  have hM₂_pos : 0 < Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * (R₂ + ε)))) :=
    lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
  obtain ⟨enc₁', enc₂', dec₁', dec₂', heq1, heq2⟩ :=
    bt_widen_block_code hM₁_pos hM₂_pos hM₁_le hM₂_le enc₁ enc₂ dec₁ dec₂
  refine ⟨enc₁', enc₂', dec₁', dec₂', ?_, ?_⟩
  · dsimp only; simp_rw [heq1]; linarith
  · dsimp only; simp_rw [heq2]; linarith

/-- Helper: marginalization of an i.i.d. expectation onto a contiguous coordinate block
    `[off, off + len)` inside `Fin n`. -/
private lemma bt_iid_sum_block_slice {α : Type*} [Fintype α] (P : ProbDist α)
    {n off len : ℕ} (hbound : off + len ≤ n) (f : (Fin len → α) → ℝ) :
    ∑ x : Fin n → α, (∏ k : Fin n, P.pmf (x k)) *
        f (fun j : Fin len => x ⟨off + j.1, lt_of_lt_of_le (Nat.add_lt_add_left j.2 off) hbound⟩) =
      ∑ y : Fin len → α, (∏ j : Fin len, P.pmf (y j)) * f y := by
  let inBlk (k : Fin n) : Prop := off ≤ k.1 ∧ k.1 < off + len
  let eBlk : (Fin n → α) ≃ (Fin len → α) × ({ k : Fin n // ¬ inBlk k } → α) :=
    { toFun := fun x =>
        (fun j => x ⟨off + j.1, lt_of_lt_of_le (Nat.add_lt_add_left j.2 off) hbound⟩,
         fun k => x k.1)
      invFun := fun yr k =>
        if h : inBlk k then yr.1 ⟨k.1 - off, by rcases h with ⟨h1, h2⟩; omega⟩
        else yr.2 ⟨k, h⟩
      left_inv := fun x => by
        funext k; by_cases h : inBlk k
        · simp only [h, ↓reduceDIte]; congr 1; apply Fin.ext; dsimp; rcases h with ⟨h1, _⟩; omega
        · simp [h]
      right_inv := fun ⟨y, r⟩ => by
        refine Prod.ext (funext fun j => ?_) (funext fun ⟨k, hk⟩ => by simp [hk])
        have h : inBlk ⟨off + j.1, lt_of_lt_of_le (Nat.add_lt_add_left j.2 off) hbound⟩ :=
          ⟨Nat.le_add_right _ _, Nat.add_lt_add_left j.2 _⟩
        simp only [h, ↓reduceDIte]; congr 1; apply Fin.ext; dsimp; omega }
  rw [Fintype.sum_equiv eBlk _ (fun yr => (∏ k : Fin n, P.pmf (eBlk.symm yr k)) * f yr.1) (fun x => by
    have : eBlk.symm (eBlk x) = x := eBlk.symm_apply_apply x
    rw [this]; rfl)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hfac : ∀ r : { k : Fin n // ¬ inBlk k } → α,
      (∏ k : Fin n, P.pmf (eBlk.symm (y, r) k)) =
        (∏ j : Fin len, P.pmf (y j)) * ∏ k : { k : Fin n // ¬ inBlk k }, P.pmf (r k) := by
    intro r
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ inBlk]
    congr 1
    · refine Finset.prod_bij (fun k _ => ⟨k.1 - off, by
          have hk := (Finset.mem_filter.mp ‹_›).2; omega⟩) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro k₁ hk₁ k₂ hk₂ heq
        have h1 := (Finset.mem_filter.mp hk₁).2
        have h2 := (Finset.mem_filter.mp hk₂).2
        have hv : k₁.1 - off = k₂.1 - off := congrArg Fin.val heq
        exact Fin.ext (by omega)
      · intro j _
        refine ⟨⟨off + j.1, lt_of_lt_of_le (Nat.add_lt_add_left j.2 off) hbound⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.le_add_right _ _, Nat.add_lt_add_left j.2 _⟩,
          Fin.ext (by dsimp; omega)⟩
      · intro k hk
        have h := (Finset.mem_filter.mp hk).2
        simp [eBlk, h]
    · refine Finset.prod_bij (fun k hk => ⟨k, (Finset.mem_filter.mp hk).2⟩) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro k₁ _ k₂ _ heq; exact congrArg Subtype.val heq
      · intro ⟨k, hk⟩ _; exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩, rfl⟩
      · intro k hk; have h := (Finset.mem_filter.mp hk).2; simp [eBlk, h]
  simp_rw [hfac]
  have hrest1 : ∑ r : { k : Fin n // ¬ inBlk k } → α,
      ∏ k : { k : Fin n // ¬ inBlk k }, P.pmf (r k) = 1 := by
    rw [← Fintype.prod_sum]; exact Finset.prod_eq_one fun _ _ => P.sum_one
  have hpull : (∑ r : { k : Fin n // ¬ inBlk k } → α,
      ((∏ j : Fin len, P.pmf (y j)) * ∏ k, P.pmf (r k)) * f y) =
      (∑ r : { k : Fin n // ¬ inBlk k } → α, ∏ k, P.pmf (r k)) *
        ((∏ j : Fin len, P.pmf (y j)) * f y) := by
    rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun r _ => by ring
  rw [hpull, hrest1, one_mul]

open scoped Classical in
/-- **Time-Sharing Convexity of `IsBergerTungAchievable`**:
    any finite convex combination of operationally achievable Berger–Tung 4-tuples
    `(r₁ i, r₂ i, δ₁ i, δ₂ i)` is operationally achievable. -/
theorem isBergerTungAchievable_timeSharing
    (P : ProbDist (X₁ × X₂)) (d₁ : Distortion X₁ Xh₁) (d₂ : Distortion X₂ Xh₂)
    {m : ℕ} {w r₁ r₂ δ₁ δ₂ : Fin m → ℝ}
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i : Fin m, w i = 1)
    (hach : ∀ i, IsBergerTungAchievable P d₁ d₂ (r₁ i) (r₂ i) (δ₁ i) (δ₂ i)) :
    IsBergerTungAchievable P d₁ d₂
      (∑ i : Fin m, w i * r₁ i) (∑ i : Fin m, w i * r₂ i)
      (∑ i : Fin m, w i * δ₁ i) (∑ i : Fin m, w i * δ₂ i) := by
  have hR₁0 : 0 ≤ ∑ i : Fin m, w i * r₁ i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw0 i) (hach i).1
  have hR₂0 : 0 ≤ ∑ i : Fin m, w i * r₂ i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw0 i) (hach i).2.1
  -- Extract default reconstruction symbols `xh1_0, xh2_0` from any active index `i₀`.
  have hex_i0 : ∃ i₀ : Fin m, 0 < w i₀ := by
    by_contra h; push Not at h
    have h0 : ∑ i : Fin m, w i = 0 := Finset.sum_eq_zero fun i _ => le_antisymm (h i) (hw0 i)
    linarith
  obtain ⟨i₀, _⟩ := hex_i0
  have hne_xh : Nonempty Xh₁ ∧ Nonempty Xh₂ := by
    obtain ⟨N0, hN0⟩ := (hach i₀).2.2 1 one_pos
    let n0 := max N0 1
    obtain ⟨_, _, dec₁0, dec₂0, _, _⟩ := hN0 n0 (le_max_left N0 1)
    have hn0 : 0 < n0 := lt_of_lt_of_le Nat.zero_lt_one (le_max_right N0 1)
    have hM1 : 0 < Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n0 : ℝ) * (r₁ i₀ + 1)))) :=
      lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
    have hM2 : 0 < Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n0 : ℝ) * (r₂ i₀ + 1)))) :=
      lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
    exact ⟨⟨dec₁0 (⟨0, hM1⟩, ⟨0, hM2⟩) ⟨0, hn0⟩⟩, ⟨dec₂0 (⟨0, hM1⟩, ⟨0, hM2⟩) ⟨0, hn0⟩⟩⟩
  let xh1_0 : Xh₁ := Classical.choice hne_xh.1
  let xh2_0 : Xh₂ := Classical.choice hne_xh.2
  let dmax₁ : ℝ := ∑ p : X₁ × Xh₁, d₁.dist p.1 p.2
  let dmax₂ : ℝ := ∑ p : X₂ × Xh₂, d₂.dist p.1 p.2
  let dmax : ℝ := max dmax₁ dmax₂
  have hdmax0 : 0 ≤ dmax := le_trans (Finset.sum_nonneg fun p _ => d₁.nonneg p.1 p.2) (le_max_left _ _)
  have hd1_le : ∀ x xh, d₁.dist x xh ≤ dmax := fun x xh =>
    le_trans (Finset.single_le_sum (f := fun p : X₁ × Xh₁ => d₁.dist p.1 p.2)
      (fun p _ => d₁.nonneg p.1 p.2) (Finset.mem_univ (x, xh))) (le_max_left _ _)
  have hd2_le : ∀ x xh, d₂.dist x xh ≤ dmax := fun x xh =>
    le_trans (Finset.single_le_sum (f := fun p : X₂ × Xh₂ => d₂.dist p.1 p.2)
      (fun p _ => d₂.nonneg p.1 p.2) (Finset.mem_univ (x, xh))) (le_max_right _ _)
  refine ⟨hR₁0, hR₂0, fun ε hε => ?_⟩
  -- For each `i`, get blocklength threshold `N_i` at tolerance `ε / 4`.
  have hcode_i : ∀ i : Fin m, ∃ N : ℕ, ∀ k ≥ N,
      let M₁ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((k : ℝ) * (r₁ i + ε / 4))))
      let M₂ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((k : ℝ) * (r₂ i + ε / 4))))
      ∃ (enc₁ : (Fin k → X₁) → Fin M₁) (enc₂ : (Fin k → X₂) → Fin M₂)
        (dec₁ : Fin M₁ × Fin M₂ → Fin k → Xh₁) (dec₂ : Fin M₁ × Fin M₂ → Fin k → Xh₂),
        (∑ x : Fin k → X₁ × X₂, (∏ j : Fin k, P.pmf (x j)) *
          ((1 / (k : ℝ)) * ∑ j : Fin k, d₁.dist (x j).1 (dec₁ (enc₁ (fun l => (x l).1), enc₂ (fun l => (x l).2)) j))) ≤
          δ₁ i + ε / 4 ∧
        (∑ x : Fin k → X₁ × X₂, (∏ j : Fin k, P.pmf (x j)) *
          ((1 / (k : ℝ)) * ∑ j : Fin k, d₂.dist (x j).2 (dec₂ (enc₁ (fun l => (x l).1), enc₂ (fun l => (x l).2)) j))) ≤
          δ₂ i + ε / 4 :=
    fun i => (hach i).2.2 (ε / 4) (by linarith)
  let Ni : Fin m → ℕ := fun i => Classical.choose (hcode_i i)
  have hNi : ∀ i k, Ni i ≤ k → _ := fun i => Classical.choose_spec (hcode_i i)
  -- Active indices `S_pos = {i | 0 < w i}`.
  let S_pos : Finset (Fin m) := Finset.univ.filter fun i => 0 < w i
  -- Choose `N` large enough that:
  -- (a) for every `i ∈ S_pos`, `⌊w i * n⌋ ≥ max (Ni i) 1`;
  -- (b) `(m : ℝ) * (dmax + 1) / n ≤ ε / 2`;
  -- (c) `(2 : ℝ) ^ (n * (ε / 2)) ≥ 2` (so floor loss is absorbed into `ε / 2`!).
  have hex_N_each : ∀ i : Fin m, ∃ N : ℕ, ∀ n ≥ N, 0 < w i → max (Ni i) 1 ≤ Nat.floor (w i * (n : ℝ)) := by
    intro i
    by_cases hwi : 0 < w i
    · obtain ⟨N, hN⟩ := exists_nat_gt (((max (Ni i) 1 : ℕ) : ℝ) / w i)
      refine ⟨N, fun n hn _ => ?_⟩
      have h1 : ((max (Ni i) 1 : ℕ) : ℝ) ≤ w i * (n : ℝ) := by
        have hlt := lt_of_lt_of_le hN (Nat.cast_le.mpr hn)
        have := (div_lt_iff₀ hwi).mp hlt; linarith
      exact Nat.le_floor h1
    · exact ⟨0, fun _ _ h => absurd h hwi⟩
  let N_each : Fin m → ℕ := fun i => Classical.choose (hex_N_each i)
  have hN_each : ∀ i n, N_each i ≤ n → 0 < w i → max (Ni i) 1 ≤ Nat.floor (w i * (n : ℝ)) :=
    fun i => Classical.choose_spec (hex_N_each i)
  let N_blocks : ℕ := Finset.univ.sup N_each
  obtain ⟨N_dist, hN_dist⟩ := exists_nat_gt ((m : ℝ) * (dmax + 1) / (ε / 2))
  obtain ⟨N_rate, hN_rate⟩ := exists_nat_gt (1 / (ε / 2))
  refine ⟨max (max N_blocks N_dist) (max N_rate 1), fun n hn => ?_⟩
  dsimp only
  have hn_pos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right N_rate 1) (le_trans (le_max_right _ _) hn))
  have hn_r : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  have hn_blk : N_blocks ≤ n := le_trans (le_max_left N_blocks N_dist) (le_trans (le_max_left _ _) hn)
  have hn_dist : (m : ℝ) * (dmax + 1) / (ε / 2) < (n : ℝ) := lt_of_lt_of_le hN_dist (by
    exact_mod_cast le_trans (le_max_right N_blocks N_dist) (le_trans (le_max_left _ _) hn))
  have hn_rate : 1 / (ε / 2) < (n : ℝ) := lt_of_lt_of_le hN_rate (by
    exact_mod_cast le_trans (le_max_left N_rate 1) (le_trans (le_max_right _ _) hn))
  -- Block lengths `len i := Nat.floor (w i * n)` and cumulative offsets `off i`.
  let len : Fin m → ℕ := fun i => Nat.floor (w i * (n : ℝ))
  have hlen_le : ∀ i, (len i : ℝ) ≤ w i * (n : ℝ) := fun i =>
    Nat.floor_le (mul_nonneg (hw0 i) (Nat.cast_nonneg n))
  have hlen_sum_le : ∑ i : Fin m, len i ≤ n := by
    have hcast : ((∑ i : Fin m, len i : ℕ) : ℝ) ≤ (n : ℝ) := by
      rw [Nat.cast_sum]
      calc ∑ i : Fin m, (len i : ℝ)
        _ ≤ ∑ i : Fin m, w i * (n : ℝ) := Finset.sum_le_sum fun i _ => hlen_le i
        _ = (∑ i : Fin m, w i) * (n : ℝ) := (Finset.sum_mul ..).symm
        _ = (n : ℝ) := by rw [hw1, one_mul]
    exact_mod_cast hcast
  have hlen_sum_ge : (n : ℝ) - (m : ℝ) ≤ ∑ i : Fin m, (len i : ℝ) := by
    have hgt : ∀ i : Fin m, w i * (n : ℝ) - 1 < (len i : ℝ) := fun i => by
      have := Nat.lt_floor_add_one (w i * (n : ℝ)); linarith
    have hsum : ∑ i : Fin m, (w i * (n : ℝ) - 1) ≤ ∑ i : Fin m, (len i : ℝ) :=
      Finset.sum_le_sum fun i _ => le_of_lt (hgt i)
    have hlhs : ∑ i : Fin m, (w i * (n : ℝ) - 1) = (n : ℝ) - (m : ℝ) := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    linarith
  have hlen_ge_Ni : ∀ i : Fin m, 0 < w i → Ni i ≤ len i ∧ 0 < len i := fun i hwi => by
    have h1 := hN_each i n (le_trans (Finset.le_sup (f := N_each) (Finset.mem_univ i)) hn_blk) hwi
    exact ⟨le_trans (le_max_left _ _) h1, lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ _) h1)⟩
  have hlen_zero : ∀ i : Fin m, ¬ (0 < w i) → len i = 0 := fun i hwi => by
    have hw_eq : w i = 0 := le_antisymm (not_lt.mp hwi) (hw0 i)
    simp [len, hw_eq]
  -- Cumulative offsets `off i = ∑_{j < i} len j`.
  let off : Fin m → ℕ := fun i => ∑ j ∈ Finset.univ.filter (fun j : Fin m => j.1 < i.1), len j
  have hoff_add_le : ∀ i : Fin m, off i + len i ≤ n := by
    intro i
    have hsub : insert i (Finset.univ.filter (fun j : Fin m => j.1 < i.1)) ⊆ Finset.univ :=
      Finset.subset_univ _
    have hni : i ∉ Finset.univ.filter (fun j : Fin m => j.1 < i.1) := by simp
    have hsum := Finset.sum_le_sum_of_subset_of_nonneg (f := len) hsub (fun _ _ _ => Nat.zero_le _)
    rw [Finset.sum_insert hni] at hsum
    dsimp only [off]; omega
  -- Disjointness of blocks `[off i, off i + len i)`.
  have hblock_disj : ∀ {i₁ i₂ : Fin m} (j₁ : Fin (len i₁)) (j₂ : Fin (len i₂)),
      off i₁ + j₁.1 = off i₂ + j₂.1 → i₁ = i₂ := by
    intro i₁ i₂ j₁ j₂ heq
    by_contra hne
    have hlt_or : i₁.1 < i₂.1 ∨ i₂.1 < i₁.1 := Nat.lt_or_gt.mp (fun h => hne (Fin.ext h))
    have hmono : ∀ a b : Fin m, a.1 < b.1 → off a + len a ≤ off b := by
      intro a b hab
      have hsub : insert a (Finset.univ.filter (fun j : Fin m => j.1 < a.1)) ⊆
          Finset.univ.filter (fun j : Fin m => j.1 < b.1) := by
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj'
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_trans (Finset.mem_filter.mp hj').2 hab⟩
      have hna : a ∉ Finset.univ.filter (fun j : Fin m => j.1 < a.1) := by simp
      have hsum := Finset.sum_le_sum_of_subset_of_nonneg (f := len) hsub (fun _ _ _ => Nat.zero_le _)
      rw [Finset.sum_insert hna] at hsum; dsimp only [off]; omega
    rcases hlt_or with hlt | hgt
    · have := hmono i₁ i₂ hlt; omega
    · have := hmono i₂ i₁ hgt; omega
  -- Per-block code sizes and codes (trivial 1-message code when `len i = 0`).
  let M1_i : Fin m → ℕ := fun i =>
    if 0 < w i then Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((len i : ℝ) * (r₁ i + ε / 4)))) else 1
  let M2_i : Fin m → ℕ := fun i =>
    if 0 < w i then Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((len i : ℝ) * (r₂ i + ε / 4)))) else 1
  have hM1_i_pos : ∀ i, 0 < M1_i i := fun i => by
    dsimp [M1_i]; split_ifs
    · exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
    · exact one_pos
  have hM2_i_pos : ∀ i, 0 < M2_i i := fun i => by
    dsimp [M2_i]; split_ifs
    · exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
    · exact one_pos
  -- Extract per-block encoders and decoders for each `i`.
  have hblk_codes : ∀ i : Fin m,
      ∃ (e₁ : (Fin (len i) → X₁) → Fin (M1_i i)) (e₂ : (Fin (len i) → X₂) → Fin (M2_i i))
        (dc₁ : Fin (M1_i i) × Fin (M2_i i) → Fin (len i) → Xh₁)
        (dc₂ : Fin (M1_i i) × Fin (M2_i i) → Fin (len i) → Xh₂),
        (0 < w i →
          (∑ x : Fin (len i) → X₁ × X₂, (∏ j : Fin (len i), P.pmf (x j)) *
            ((1 / (len i : ℝ)) * ∑ j : Fin (len i),
              d₁.dist (x j).1 (dc₁ (e₁ (fun l => (x l).1), e₂ (fun l => (x l).2)) j))) ≤ δ₁ i + ε / 4 ∧
          (∑ x : Fin (len i) → X₁ × X₂, (∏ j : Fin (len i), P.pmf (x j)) *
            ((1 / (len i : ℝ)) * ∑ j : Fin (len i),
              d₂.dist (x j).2 (dc₂ (e₁ (fun l => (x l).1), e₂ (fun l => (x l).2)) j))) ≤ δ₂ i + ε / 4) := by
    intro i
    by_cases hwi : 0 < w i
    · obtain ⟨e₁, e₂, dc₁, dc₂, hd1, hd2⟩ := hNi i (len i) (hlen_ge_Ni i hwi).1
      refine ⟨?_, ?_, ?_, ?_, fun _ => ?_⟩
      · intro x; exact Fin.cast (by simp [M1_i, hwi]) (e₁ x)
      · intro x; exact Fin.cast (by simp [M2_i, hwi]) (e₂ x)
      · intro m; exact dc₁ (Fin.cast (by simp [M1_i, hwi]) m.1, Fin.cast (by simp [M2_i, hwi]) m.2)
      · intro m; exact dc₂ (Fin.cast (by simp [M1_i, hwi]) m.1, Fin.cast (by simp [M2_i, hwi]) m.2)
      · simpa using And.intro hd1 hd2
    · exact ⟨fun _ => ⟨0, hM1_i_pos i⟩, fun _ => ⟨0, hM2_i_pos i⟩,
        fun _ _ => xh1_0, fun _ _ => xh2_0, fun h => absurd h hwi⟩
  let e1_i := fun i => Classical.choose (hblk_codes i)
  let e2_i := fun i => Classical.choose (Classical.choose_spec (hblk_codes i))
  let dc1_i := fun i => Classical.choose (Classical.choose_spec (Classical.choose_spec (hblk_codes i)))
  let dc2_i := fun i => Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hblk_codes i))))
  have hdc_spec : ∀ i, 0 < w i →
      (∑ x : Fin (len i) → X₁ × X₂, (∏ j : Fin (len i), P.pmf (x j)) *
        ((1 / (len i : ℝ)) * ∑ j : Fin (len i),
          d₁.dist (x j).1 (dc1_i i (e1_i i (fun l => (x l).1), e2_i i (fun l => (x l).2)) j))) ≤ δ₁ i + ε / 4 ∧
      (∑ x : Fin (len i) → X₁ × X₂, (∏ j : Fin (len i), P.pmf (x j)) *
        ((1 / (len i : ℝ)) * ∑ j : Fin (len i),
          d₂.dist (x j).2 (dc2_i i (e1_i i (fun l => (x l).1), e2_i i (fun l => (x l).2)) j))) ≤ δ₂ i + ε / 4 :=
    fun i => Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hblk_codes i))))
  -- Message-product cardinality bounds: `∏_i M1_i i ≤ M₁` and `∏_i M2_i i ≤ M₂`.
  let M₁ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * ((∑ i, w i * r₁ i) + ε))))
  let M₂ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * ((∑ i, w i * r₂ i) + ε))))
  have hprod1_le : Fintype.card (∀ i : Fin m, Fin (M1_i i)) ≤ M₁ := by
    rw [Fintype.card_pi]; simp_rw [Fintype.card_fin]
    have hcast : ((∏ i : Fin m, M1_i i : ℕ) : ℝ) ≤ (M₁ : ℝ) := by
      rw [Nat.cast_prod]
      have hterm : ∀ i : Fin m, (M1_i i : ℝ) ≤ (2 : ℝ) ^ ((len i : ℝ) * (r₁ i + ε / 4)) := fun i => by
        dsimp [M1_i]
        by_cases hwi : 0 < w i
        · rw [ite_eq_left_iff.mpr (fun h => absurd hwi h)]
          exact bt_max_one_floor_two_rpow_le (len i) (by linarith [(hach i).1])
        · rw [ite_eq_right_iff.mpr (fun h => absurd h hwi), hlen_zero i hwi]; simp
      have hprod_rpow : (∏ i : Fin m, (M1_i i : ℝ)) ≤
          (2 : ℝ) ^ (∑ i : Fin m, (len i : ℝ) * (r₁ i + ε / 4)) := by
        calc ∏ i : Fin m, (M1_i i : ℝ)
          _ ≤ ∏ i : Fin m, (2 : ℝ) ^ ((len i : ℝ) * (r₁ i + ε / 4)) :=
              Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => hterm i)
          _ = (2 : ℝ) ^ (∑ i : Fin m, (len i : ℝ) * (r₁ i + ε / 4)) :=
              (Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 2) _ _).symm
      have hexp_le : (∑ i : Fin m, (len i : ℝ) * (r₁ i + ε / 4)) ≤
          (n : ℝ) * ((∑ i : Fin m, w i * r₁ i) + ε) - 1 := by
        have hsum_le : ∑ i : Fin m, (len i : ℝ) * (r₁ i + ε / 4) ≤
            (n : ℝ) * ((∑ i : Fin m, w i * r₁ i) + ε / 4) := by
          calc ∑ i : Fin m, (len i : ℝ) * (r₁ i + ε / 4)
            _ ≤ ∑ i : Fin m, (w i * (n : ℝ)) * (r₁ i + ε / 4) :=
                Finset.sum_le_sum fun i _ =>
                  mul_le_mul_of_nonneg_right (hlen_le i) (by linarith [(hach i).1])
            _ = (n : ℝ) * ((∑ i : Fin m, w i * r₁ i) + (ε / 4) * ∑ i : Fin m, w i) := by
                rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun i _ => by ring
            _ = (n : ℝ) * ((∑ i : Fin m, w i * r₁ i) + ε / 4) := by rw [hw1, mul_one]
        have h1_le : (1 : ℝ) < (n : ℝ) * (ε / 2) := (div_lt_iff₀ (by positivity : 0 < ε / 2)).mp hn_rate
        linarith
      have hhalf : (2 : ℝ) ^ ((n : ℝ) * ((∑ i : Fin m, w i * r₁ i) + ε) - 1) =
          (2 : ℝ) ^ ((n : ℝ) * ((∑ i : Fin m, w i * r₁ i) + ε)) / 2 := by
        rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
      have hM1_ge := bt_half_two_rpow_le_max_one_floor n (by linarith : 0 ≤ (∑ i : Fin m, w i * r₁ i) + ε)
      calc ∏ i : Fin m, (M1_i i : ℝ)
        _ ≤ (2 : ℝ) ^ (∑ i : Fin m, (len i : ℝ) * (r₁ i + ε / 4)) := hprod_rpow
        _ ≤ (2 : ℝ) ^ ((n : ℝ) * ((∑ i : Fin m, w i * r₁ i) + ε) - 1) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_le
        _ = (2 : ℝ) ^ ((n : ℝ) * ((∑ i : Fin m, w i * r₁ i) + ε)) / 2 := hhalf
        _ ≤ (M₁ : ℝ) := hM1_ge
    exact_mod_cast hcast
  have hprod2_le : Fintype.card (∀ i : Fin m, Fin (M2_i i)) ≤ M₂ := by
    rw [Fintype.card_pi]; simp_rw [Fintype.card_fin]
    have hcast : ((∏ i : Fin m, M2_i i : ℕ) : ℝ) ≤ (M₂ : ℝ) := by
      rw [Nat.cast_prod]
      have hterm : ∀ i : Fin m, (M2_i i : ℝ) ≤ (2 : ℝ) ^ ((len i : ℝ) * (r₂ i + ε / 4)) := fun i => by
        dsimp [M2_i]
        by_cases hwi : 0 < w i
        · rw [ite_eq_left_iff.mpr (fun h => absurd hwi h)]
          exact bt_max_one_floor_two_rpow_le (len i) (by linarith [(hach i).2.1])
        · rw [ite_eq_right_iff.mpr (fun h => absurd h hwi), hlen_zero i hwi]; simp
      have hprod_rpow : (∏ i : Fin m, (M2_i i : ℝ)) ≤
          (2 : ℝ) ^ (∑ i : Fin m, (len i : ℝ) * (r₂ i + ε / 4)) := by
        calc ∏ i : Fin m, (M2_i i : ℝ)
          _ ≤ ∏ i : Fin m, (2 : ℝ) ^ ((len i : ℝ) * (r₂ i + ε / 4)) :=
              Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => hterm i)
          _ = (2 : ℝ) ^ (∑ i : Fin m, (len i : ℝ) * (r₂ i + ε / 4)) :=
              (Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 2) _ _).symm
      have hexp_le : (∑ i : Fin m, (len i : ℝ) * (r₂ i + ε / 4)) ≤
          (n : ℝ) * ((∑ i : Fin m, w i * r₂ i) + ε) - 1 := by
        have hsum_le : ∑ i : Fin m, (len i : ℝ) * (r₂ i + ε / 4) ≤
            (n : ℝ) * ((∑ i : Fin m, w i * r₂ i) + ε / 4) := by
          calc ∑ i : Fin m, (len i : ℝ) * (r₂ i + ε / 4)
            _ ≤ ∑ i : Fin m, (w i * (n : ℝ)) * (r₂ i + ε / 4) :=
                Finset.sum_le_sum fun i _ =>
                  mul_le_mul_of_nonneg_right (hlen_le i) (by linarith [(hach i).2.1])
            _ = (n : ℝ) * ((∑ i : Fin m, w i * r₂ i) + (ε / 4) * ∑ i : Fin m, w i) := by
                rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun i _ => by ring
            _ = (n : ℝ) * ((∑ i : Fin m, w i * r₂ i) + ε / 4) := by rw [hw1, mul_one]
        have h1_le : (1 : ℝ) < (n : ℝ) * (ε / 2) := (div_lt_iff₀ (by positivity : 0 < ε / 2)).mp hn_rate
        linarith
      have hhalf : (2 : ℝ) ^ ((n : ℝ) * ((∑ i : Fin m, w i * r₂ i) + ε) - 1) =
          (2 : ℝ) ^ ((n : ℝ) * ((∑ i : Fin m, w i * r₂ i) + ε)) / 2 := by
        rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
      have hM2_ge := bt_half_two_rpow_le_max_one_floor n (by linarith : 0 ≤ (∑ i : Fin m, w i * r₂ i) + ε)
      calc ∏ i : Fin m, (M2_i i : ℝ)
        _ ≤ (2 : ℝ) ^ (∑ i : Fin m, (len i : ℝ) * (r₂ i + ε / 4)) := hprod_rpow
        _ ≤ (2 : ℝ) ^ ((n : ℝ) * ((∑ i : Fin m, w i * r₂ i) + ε) - 1) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_le
        _ = (2 : ℝ) ^ ((n : ℝ) * ((∑ i : Fin m, w i * r₂ i) + ε)) / 2 := hhalf
        _ ≤ (M₂ : ℝ) := hM2_ge
    exact_mod_cast hcast
  -- Pack/unpack product messages into `Fin M₁` and `Fin M₂`.
  let pack1 := Fintype.equivFin (∀ i : Fin m, Fin (M1_i i))
  let pack2 := Fintype.equivFin (∀ i : Fin m, Fin (M2_i i))
  let slice₁ (x : Fin n → X₁) (i : Fin m) : Fin (len i) → X₁ :=
    fun j => x ⟨off i + j.1, lt_of_lt_of_le (Nat.add_lt_add_left j.2 (off i)) (hoff_add_le i)⟩
  let slice₂ (x : Fin n → X₂) (i : Fin m) : Fin (len i) → X₂ :=
    fun j => x ⟨off i + j.1, lt_of_lt_of_le (Nat.add_lt_add_left j.2 (off i)) (hoff_add_le i)⟩
  let slice12 (x : Fin n → X₁ × X₂) (i : Fin m) : Fin (len i) → X₁ × X₂ :=
    fun j => x ⟨off i + j.1, lt_of_lt_of_le (Nat.add_lt_add_left j.2 (off i)) (hoff_add_le i)⟩
  let enc₁ : (Fin n → X₁) → Fin M₁ := fun x =>
    Fin.castLE hprod1_le (pack1 (fun i => e1_i i (slice₁ x i)))
  let enc₂ : (Fin n → X₂) → Fin M₂ := fun x =>
    Fin.castLE hprod2_le (pack2 (fun i => e2_i i (slice₂ x i)))
  let unpack1 : Fin M₁ → (∀ i : Fin m, Fin (M1_i i)) := fun m₁ =>
    if h : m₁.1 < Fintype.card (∀ i : Fin m, Fin (M1_i i)) then pack1.symm ⟨m₁.1, h⟩
    else fun i => ⟨0, hM1_i_pos i⟩
  let unpack2 : Fin M₂ → (∀ i : Fin m, Fin (M2_i i)) := fun m₂ =>
    if h : m₂.1 < Fintype.card (∀ i : Fin m, Fin (M2_i i)) then pack2.symm ⟨m₂.1, h⟩
    else fun i => ⟨0, hM2_i_pos i⟩
  have hunpack1 : ∀ x i, unpack1 (enc₁ x) i = e1_i i (slice₁ x i) := fun x i => by
    dsimp only [unpack1, enc₁, Fin.castLE]
    simp only [Fin.is_lt, ↓reduceDIte, Fin.eta, Equiv.symm_apply_apply]
  have hunpack2 : ∀ x i, unpack2 (enc₂ x) i = e2_i i (slice₂ x i) := fun x i => by
    dsimp only [unpack2, enc₂, Fin.castLE]
    simp only [Fin.is_lt, ↓reduceDIte, Fin.eta, Equiv.symm_apply_apply]
  -- Coordinate lookup: map `k : Fin n` to `(i, j)` when `k` falls in block `i`, else default.
  let dec₁ : Fin M₁ × Fin M₂ → Fin n → Xh₁ := fun msg k =>
    if h : ∃ i : Fin m, off i ≤ k.1 ∧ k.1 < off i + len i then
      dc1_i (Classical.choose h) (unpack1 msg.1 (Classical.choose h), unpack2 msg.2 (Classical.choose h))
        ⟨k.1 - off (Classical.choose h), by
          rcases Classical.choose_spec h with ⟨h1, h2⟩; omega⟩
    else xh1_0
  let dec₂ : Fin M₁ × Fin M₂ → Fin n → Xh₂ := fun msg k =>
    if h : ∃ i : Fin m, off i ≤ k.1 ∧ k.1 < off i + len i then
      dc2_i (Classical.choose h) (unpack1 msg.1 (Classical.choose h), unpack2 msg.2 (Classical.choose h))
        ⟨k.1 - off (Classical.choose h), by
          rcases Classical.choose_spec h with ⟨h1, h2⟩; omega⟩
    else xh2_0
  -- Verify `dec₁` and `dec₂` agree with `dc1_i i` and `dc2_i i` on block `i`.
  have hdec1_block : ∀ (x : Fin n → X₁ × X₂) (i : Fin m) (j : Fin (len i)),
      dec₁ (enc₁ (fun l => (x l).1), enc₂ (fun l => (x l).2))
        ⟨off i + j.1, lt_of_lt_of_le (Nat.add_lt_add_left j.2 (off i)) (hoff_add_le i)⟩ =
      dc1_i i (e1_i i (slice₁ (fun l => (x l).1) i), e2_i i (slice₂ (fun l => (x l).2) i)) j := by
    intro x i j
    have hex : ∃ i' : Fin m, off i' ≤ off i + j.1 ∧ off i + j.1 < off i' + len i' :=
      ⟨i, Nat.le_add_right _ _, Nat.add_lt_add_left j.2 _⟩
    dsimp only [dec₁]; simp only [hex, ↓reduceDIte]
    generalize_proofs hlt
    have hi' : off (Classical.choose hex) ≤ off i + j.1 ∧
        off i + j.1 < off (Classical.choose hex) + len (Classical.choose hex) :=
      Classical.choose_spec hex
    have hi_eq : Classical.choose hex = i :=
      hblock_disj ⟨(off i + j.1) - off (Classical.choose hex), by omega⟩ j (by dsimp; omega)
    revert hlt
    generalize Classical.choose hex = i' at hi_eq ⊢
    subst i'
    intro hlt
    exact congrArg₂ (dc1_i i)
      (Prod.ext (hunpack1 (fun l => (x l).1) i) (hunpack2 (fun l => (x l).2) i))
      (Fin.ext (by dsimp; omega))
  have hdec2_block : ∀ (x : Fin n → X₁ × X₂) (i : Fin m) (j : Fin (len i)),
      dec₂ (enc₁ (fun l => (x l).1), enc₂ (fun l => (x l).2))
        ⟨off i + j.1, lt_of_lt_of_le (Nat.add_lt_add_left j.2 (off i)) (hoff_add_le i)⟩ =
      dc2_i i (e1_i i (slice₁ (fun l => (x l).1) i), e2_i i (slice₂ (fun l => (x l).2) i)) j := by
    intro x i j
    have hex : ∃ i' : Fin m, off i' ≤ off i + j.1 ∧ off i + j.1 < off i' + len i' :=
      ⟨i, Nat.le_add_right _ _, Nat.add_lt_add_left j.2 _⟩
    dsimp only [dec₂]; simp only [hex, ↓reduceDIte]
    generalize_proofs hlt
    have hi' : off (Classical.choose hex) ≤ off i + j.1 ∧
        off i + j.1 < off (Classical.choose hex) + len (Classical.choose hex) :=
      Classical.choose_spec hex
    have hi_eq : Classical.choose hex = i :=
      hblock_disj ⟨(off i + j.1) - off (Classical.choose hex), by omega⟩ j (by dsimp; omega)
    revert hlt
    generalize Classical.choose hex = i' at hi_eq ⊢
    subst i'
    intro hlt
    exact congrArg₂ (dc2_i i)
      (Prod.ext (hunpack1 (fun l => (x l).1) i) (hunpack2 (fun l => (x l).2) i))
      (Fin.ext (by dsimp; omega))
  -- Marginalization of i.i.d. sum onto a block slice `slice12 x i`.
  have hslice_exp : ∀ (i : Fin m) (f : (Fin (len i) → X₁ × X₂) → ℝ),
      ∑ x : Fin n → X₁ × X₂, (∏ k : Fin n, P.pmf (x k)) * f (slice12 x i) =
        ∑ y : Fin (len i) → X₁ × X₂, (∏ j : Fin (len i), P.pmf (y j)) * f y :=
    fun i f => bt_iid_sum_block_slice P (hoff_add_le i) f
  -- Partition coordinates `k : Fin n` into the `m` disjoint blocks plus `≤ m` leftover coordinates.
  let blkCoords (i : Fin m) : Finset (Fin n) :=
    Finset.univ.filter fun k : Fin n => off i ≤ k.1 ∧ k.1 < off i + len i
  let covered : Finset (Fin n) := Finset.univ.biUnion blkCoords
  have hblk_card : ∀ i, (blkCoords i).card = len i := fun i => by
    rw [← Fintype.card_fin (len i), ← Finset.card_univ]
    refine Finset.card_bij (fun k hk => ⟨k.1 - off i, by have := (Finset.mem_filter.mp hk).2; omega⟩) ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro k₁ hk₁ k₂ hk₂ heq
      have h1 := (Finset.mem_filter.mp hk₁).2
      have h2 := (Finset.mem_filter.mp hk₂).2
      have hv : k₁.1 - off i = k₂.1 - off i := congrArg Fin.val heq
      exact Fin.ext (by omega)
    · intro j _
      exact ⟨⟨off i + j.1, lt_of_lt_of_le (Nat.add_lt_add_left j.2 (off i)) (hoff_add_le i)⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.le_add_right _ _, Nat.add_lt_add_left j.2 _⟩,
        Fin.ext (by dsimp; omega)⟩
  have hblk_disj' : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin m))) blkCoords := by
    intro i₁ _ i₂ _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    have h1 := (Finset.mem_filter.mp hk1).2
    have h2 := (Finset.mem_filter.mp hk2).2
    exact hne (hblock_disj ⟨k.1 - off i₁, by omega⟩ ⟨k.1 - off i₂, by omega⟩ (by dsimp; omega))
  have hcov_card : covered.card = ∑ i : Fin m, len i := by
    rw [Finset.card_biUnion hblk_disj']
    exact Finset.sum_congr rfl fun i _ => hblk_card i
  have hrem_card : ((Finset.univ \ covered).card : ℝ) ≤ (m : ℝ) := by
    have hsub : covered ⊆ Finset.univ := Finset.subset_univ _
    have h1 : (Finset.univ \ covered).card + covered.card = n := by
      have := Finset.card_sdiff_add_card_eq_card hsub; simpa using this
    have h2 : ((Finset.univ \ covered).card : ℝ) + (∑ i : Fin m, (len i : ℝ)) = (n : ℝ) := by
      have hcast : ((Finset.univ \ covered).card : ℝ) + (covered.card : ℝ) = (n : ℝ) := by
        exact_mod_cast h1
      rw [hcov_card, Nat.cast_sum] at hcast; exact hcast
    linarith
  have hrem_dist : (1 / (n : ℝ)) * (((Finset.univ \ covered).card : ℝ) * dmax) ≤ ε / 2 := by
    have h1 : (m : ℝ) * (dmax + 1) < (n : ℝ) * (ε / 2) := (div_lt_iff₀ (by positivity : 0 < ε / 2)).mp hn_dist
    have h2 : ((Finset.univ \ covered).card : ℝ) * dmax ≤ (m : ℝ) * (dmax + 1) := by
      have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      nlinarith
    rw [one_div_mul_eq_div, div_le_iff₀ hn_r]; linarith
  have hPn_sum : ∑ x : Fin n → X₁ × X₂, (∏ k : Fin n, P.pmf (x k)) = 1 :=
    (iidDist P n).sum_one
  refine ⟨enc₁, enc₂, dec₁, dec₂, ?_, ?_⟩
  · -- Average distortion 1 bound.
    have hpt1 : ∀ x : Fin n → X₁ × X₂,
        ((1 / (n : ℝ)) * ∑ k : Fin n,
          d₁.dist (x k).1 (dec₁ (enc₁ (fun l => (x l).1), enc₂ (fun l => (x l).2)) k)) ≤
        (1 / (n : ℝ)) * (∑ i : Fin m, ∑ j : Fin (len i),
          d₁.dist (slice12 x i j).1
            (dc1_i i (e1_i i (slice₁ (fun l => (x l).1) i), e2_i i (slice₂ (fun l => (x l).2) i)) j)) +
        (1 / (n : ℝ)) * (((Finset.univ \ covered).card : ℝ) * dmax) := by
      intro x
      have hsplit_k : (∑ k : Fin n, d₁.dist (x k).1 (dec₁ (enc₁ (fun l => (x l).1), enc₂ (fun l => (x l).2)) k)) =
          (∑ k ∈ covered, d₁.dist (x k).1 (dec₁ (enc₁ (fun l => (x l).1), enc₂ (fun l => (x l).2)) k)) +
          (∑ k ∈ Finset.univ \ covered, d₁.dist (x k).1 (dec₁ (enc₁ (fun l => (x l).1), enc₂ (fun l => (x l).2)) k)) := by
        rw [add_comm, Finset.sum_sdiff (Finset.subset_univ covered)]
      rw [hsplit_k, mul_add]
      have hcov_eq : (∑ k ∈ covered, d₁.dist (x k).1 (dec₁ (enc₁ (fun l => (x l).1), enc₂ (fun l => (x l).2)) k)) =
          ∑ i : Fin m, ∑ j : Fin (len i),
            d₁.dist (slice12 x i j).1
              (dc1_i i (e1_i i (slice₁ (fun l => (x l).1) i), e2_i i (slice₂ (fun l => (x l).2) i)) j) := by
        rw [Finset.sum_biUnion hblk_disj']
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_bij (fun k hk => ⟨k.1 - off i, by have := (Finset.mem_filter.mp hk).2; omega⟩)
          ?_ ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro k₁ hk₁ k₂ hk₂ heq
          have h1 := (Finset.mem_filter.mp hk₁).2
          have h2 := (Finset.mem_filter.mp hk₂).2
          have hv : k₁.1 - off i = k₂.1 - off i := congrArg Fin.val heq
          exact Fin.ext (by omega)
        · intro j _
          exact ⟨⟨off i + j.1, lt_of_lt_of_le (Nat.add_lt_add_left j.2 (off i)) (hoff_add_le i)⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.le_add_right _ _, Nat.add_lt_add_left j.2 _⟩,
            Fin.ext (by dsimp; omega)⟩
        · intro k hk
          have h := (Finset.mem_filter.mp hk).2
          let j : Fin (len i) := ⟨k.1 - off i, by omega⟩
          have hk_eq : k = ⟨off i + j.1, lt_of_lt_of_le (Nat.add_lt_add_left j.2 (off i)) (hoff_add_le i)⟩ :=
            Fin.ext (by dsimp [j]; omega)
          conv_lhs => rw [hk_eq]
          rw [hdec1_block x i j]
      have hrem_le : (∑ k ∈ Finset.univ \ covered,
            d₁.dist (x k).1 (dec₁ (enc₁ (fun l => (x l).1), enc₂ (fun l => (x l).2)) k)) ≤
          ((Finset.univ \ covered).card : ℝ) * dmax := by
        calc _ ≤ ∑ _k ∈ Finset.univ \ covered, dmax := Finset.sum_le_sum fun k _ => hd1_le _ _
          _ = ((Finset.univ \ covered).card : ℝ) * dmax := by rw [Finset.sum_const, nsmul_eq_mul]
      rw [hcov_eq]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hrem_le (by positivity))
    calc ∑ x : Fin n → X₁ × X₂, (∏ k : Fin n, P.pmf (x k)) *
          ((1 / (n : ℝ)) * ∑ k : Fin n,
            d₁.dist (x k).1 (dec₁ (enc₁ (fun l => (x l).1), enc₂ (fun l => (x l).2)) k))
      _ ≤ ∑ x : Fin n → X₁ × X₂, (∏ k : Fin n, P.pmf (x k)) *
            ((1 / (n : ℝ)) * (∑ i : Fin m, ∑ j : Fin (len i),
              d₁.dist (slice12 x i j).1
                (dc1_i i (e1_i i (slice₁ (fun l => (x l).1) i), e2_i i (slice₂ (fun l => (x l).2) i)) j)) +
             (1 / (n : ℝ)) * (((Finset.univ \ covered).card : ℝ) * dmax)) :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpt1 x)
            (Finset.prod_nonneg fun k _ => P.nonneg _)
      _ = (1 / (n : ℝ)) * (∑ i : Fin m, ∑ y : Fin (len i) → X₁ × X₂, (∏ j : Fin (len i), P.pmf (y j)) *
            ∑ j : Fin (len i), d₁.dist (y j).1 (dc1_i i (e1_i i (fun l => (y l).1), e2_i i (fun l => (y l).2)) j)) +
          (1 / (n : ℝ)) * (((Finset.univ \ covered).card : ℝ) * dmax) := by
          simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hPn_sum, one_mul]
          congr 1
          have hpush : ∀ x : Fin n → X₁ × X₂, (∏ k : Fin n, P.pmf (x k)) *
                ((1 / (n : ℝ)) * ∑ i : Fin m, ∑ j : Fin (len i),
                  d₁.dist (slice12 x i j).1
                    (dc1_i i (e1_i i (slice₁ (fun l => (x l).1) i), e2_i i (slice₂ (fun l => (x l).2) i)) j)) =
              ∑ i : Fin m, (1 / (n : ℝ)) * ((∏ k : Fin n, P.pmf (x k)) * ∑ j : Fin (len i),
                d₁.dist (slice12 x i j).1
                  (dc1_i i (e1_i i (slice₁ (fun l => (x l).1) i), e2_i i (slice₂ (fun l => (x l).2) i)) j)) := by
            intro x
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => by ring
          simp_rw [hpush]
          rw [Finset.sum_comm, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.mul_sum]
          refine congrArg ((1 / (n : ℝ)) * ·) ?_
          exact hslice_exp i (fun y => ∑ j : Fin (len i),
            d₁.dist (y j).1 (dc1_i i (e1_i i (fun l => (y l).1), e2_i i (fun l => (y l).2)) j))
      _ ≤ (1 / (n : ℝ)) * (∑ i : Fin m, (w i * (n : ℝ)) * (δ₁ i + ε / 4)) + ε / 2 := by
          refine add_le_add (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by positivity)) hrem_dist
          by_cases hwi : 0 < w i
          · have hli_pos : (0 : ℝ) < (len i : ℝ) := Nat.cast_pos.mpr (hlen_ge_Ni i hwi).2
            have hd := (hdc_spec i hwi).1
            have hmul : (∑ y : Fin (len i) → X₁ × X₂, (∏ j : Fin (len i), P.pmf (y j)) *
                ∑ j : Fin (len i), d₁.dist (y j).1 (dc1_i i (e1_i i (fun l => (y l).1), e2_i i (fun l => (y l).2)) j)) ≤
                (len i : ℝ) * (δ₁ i + ε / 4) := by
              have h1 := mul_le_mul_of_nonneg_left hd (le_of_lt hli_pos)
              have hlhs : (len i : ℝ) * (∑ y : Fin (len i) → X₁ × X₂, (∏ j : Fin (len i), P.pmf (y j)) *
                  ((1 / (len i : ℝ)) * ∑ j : Fin (len i), d₁.dist (y j).1
                    (dc1_i i (e1_i i (fun l => (y l).1), e2_i i (fun l => (y l).2)) j))) =
                  ∑ y : Fin (len i) → X₁ × X₂, (∏ j : Fin (len i), P.pmf (y j)) *
                    ∑ j : Fin (len i), d₁.dist (y j).1
                      (dc1_i i (e1_i i (fun l => (y l).1), e2_i i (fun l => (y l).2)) j) := by
                rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun y _ => by
                  field_simp [ne_of_gt hli_pos]
              linarith
            have hδ_nn : 0 ≤ δ₁ i + ε / 4 := by
              have h0 : 0 ≤ ∑ y : Fin (len i) → X₁ × X₂, (∏ j : Fin (len i), P.pmf (y j)) *
                  ((1 / (len i : ℝ)) * ∑ j : Fin (len i), d₁.dist (y j).1
                    (dc1_i i (e1_i i (fun l => (y l).1), e2_i i (fun l => (y l).2)) j)) :=
                Finset.sum_nonneg fun y _ => mul_nonneg (Finset.prod_nonneg fun _ _ => P.nonneg _)
                  (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => d₁.nonneg _ _))
              linarith
            exact le_trans hmul (mul_le_mul_of_nonneg_right (hlen_le i) hδ_nn)
          · have hw_eq : w i = 0 := le_antisymm (not_lt.mp hwi) (hw0 i)
            have hl0 : len i = 0 := hlen_zero i hwi
            have hsum0 : (∑ y : Fin (len i) → X₁ × X₂, (∏ j : Fin (len i), P.pmf (y j)) *
                ∑ j : Fin (len i), d₁.dist (y j).1
                  (dc1_i i (e1_i i (fun l => (y l).1), e2_i i (fun l => (y l).2)) j)) = 0 := by
              refine Finset.sum_eq_zero fun y _ => ?_
              have : IsEmpty (Fin (len i)) := by rw [hl0]; infer_instance
              simp
            rw [hsum0, hw_eq]; simp
      _ ≤ (∑ i : Fin m, w i * δ₁ i) + ε := by
          have hsimp : (1 / (n : ℝ)) * (∑ i : Fin m, (w i * (n : ℝ)) * (δ₁ i + ε / 4)) =
              (∑ i : Fin m, w i * δ₁ i) + ε / 4 := by
            rw [Finset.mul_sum]
            have hterm : ∀ i : Fin m, (1 / (n : ℝ)) * ((w i * (n : ℝ)) * (δ₁ i + ε / 4)) =
                w i * δ₁ i + (ε / 4) * w i := fun i => by field_simp [ne_of_gt hn_r]
            simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, hw1, mul_one]
          linarith
  · -- Average distortion 2 bound (symmetric).
    have hpt2 : ∀ x : Fin n → X₁ × X₂,
        ((1 / (n : ℝ)) * ∑ k : Fin n,
          d₂.dist (x k).2 (dec₂ (enc₁ (fun l => (x l).1), enc₂ (fun l => (x l).2)) k)) ≤
        (1 / (n : ℝ)) * (∑ i : Fin m, ∑ j : Fin (len i),
          d₂.dist (slice12 x i j).2
            (dc2_i i (e1_i i (slice₁ (fun l => (x l).1) i), e2_i i (slice₂ (fun l => (x l).2) i)) j)) +
        (1 / (n : ℝ)) * (((Finset.univ \ covered).card : ℝ) * dmax) := by
      intro x
      have hsplit_k : (∑ k : Fin n, d₂.dist (x k).2 (dec₂ (enc₁ (fun l => (x l).1), enc₂ (fun l => (x l).2)) k)) =
          (∑ k ∈ covered, d₂.dist (x k).2 (dec₂ (enc₁ (fun l => (x l).1), enc₂ (fun l => (x l).2)) k)) +
          (∑ k ∈ Finset.univ \ covered, d₂.dist (x k).2 (dec₂ (enc₁ (fun l => (x l).1), enc₂ (fun l => (x l).2)) k)) := by
        rw [add_comm, Finset.sum_sdiff (Finset.subset_univ covered)]
      rw [hsplit_k, mul_add]
      have hcov_eq : (∑ k ∈ covered, d₂.dist (x k).2 (dec₂ (enc₁ (fun l => (x l).1), enc₂ (fun l => (x l).2)) k)) =
          ∑ i : Fin m, ∑ j : Fin (len i),
            d₂.dist (slice12 x i j).2
              (dc2_i i (e1_i i (slice₁ (fun l => (x l).1) i), e2_i i (slice₂ (fun l => (x l).2) i)) j) := by
        rw [Finset.sum_biUnion hblk_disj']
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_bij (fun k hk => ⟨k.1 - off i, by have := (Finset.mem_filter.mp hk).2; omega⟩)
          ?_ ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro k₁ hk₁ k₂ hk₂ heq
          have h1 := (Finset.mem_filter.mp hk₁).2
          have h2 := (Finset.mem_filter.mp hk₂).2
          have hv : k₁.1 - off i = k₂.1 - off i := congrArg Fin.val heq
          exact Fin.ext (by omega)
        · intro j _
          exact ⟨⟨off i + j.1, lt_of_lt_of_le (Nat.add_lt_add_left j.2 (off i)) (hoff_add_le i)⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.le_add_right _ _, Nat.add_lt_add_left j.2 _⟩,
            Fin.ext (by dsimp; omega)⟩
        · intro k hk
          have h := (Finset.mem_filter.mp hk).2
          let j : Fin (len i) := ⟨k.1 - off i, by omega⟩
          have hk_eq : k = ⟨off i + j.1, lt_of_lt_of_le (Nat.add_lt_add_left j.2 (off i)) (hoff_add_le i)⟩ :=
            Fin.ext (by dsimp [j]; omega)
          conv_lhs => rw [hk_eq]
          rw [hdec2_block x i j]
      have hrem_le : (∑ k ∈ Finset.univ \ covered,
            d₂.dist (x k).2 (dec₂ (enc₁ (fun l => (x l).1), enc₂ (fun l => (x l).2)) k)) ≤
          ((Finset.univ \ covered).card : ℝ) * dmax := by
        calc _ ≤ ∑ _k ∈ Finset.univ \ covered, dmax := Finset.sum_le_sum fun k _ => hd2_le _ _
          _ = ((Finset.univ \ covered).card : ℝ) * dmax := by rw [Finset.sum_const, nsmul_eq_mul]
      rw [hcov_eq]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hrem_le (by positivity))
    calc ∑ x : Fin n → X₁ × X₂, (∏ k : Fin n, P.pmf (x k)) *
          ((1 / (n : ℝ)) * ∑ k : Fin n,
            d₂.dist (x k).2 (dec₂ (enc₁ (fun l => (x l).1), enc₂ (fun l => (x l).2)) k))
      _ ≤ ∑ x : Fin n → X₁ × X₂, (∏ k : Fin n, P.pmf (x k)) *
            ((1 / (n : ℝ)) * (∑ i : Fin m, ∑ j : Fin (len i),
              d₂.dist (slice12 x i j).2
                (dc2_i i (e1_i i (slice₁ (fun l => (x l).1) i), e2_i i (slice₂ (fun l => (x l).2) i)) j)) +
             (1 / (n : ℝ)) * (((Finset.univ \ covered).card : ℝ) * dmax)) :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpt2 x)
            (Finset.prod_nonneg fun k _ => P.nonneg _)
      _ = (1 / (n : ℝ)) * (∑ i : Fin m, ∑ y : Fin (len i) → X₁ × X₂, (∏ j : Fin (len i), P.pmf (y j)) *
            ∑ j : Fin (len i), d₂.dist (y j).2 (dc2_i i (e1_i i (fun l => (y l).1), e2_i i (fun l => (y l).2)) j)) +
          (1 / (n : ℝ)) * (((Finset.univ \ covered).card : ℝ) * dmax) := by
          simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hPn_sum, one_mul]
          congr 1
          have hpush : ∀ x : Fin n → X₁ × X₂, (∏ k : Fin n, P.pmf (x k)) *
                ((1 / (n : ℝ)) * ∑ i : Fin m, ∑ j : Fin (len i),
                  d₂.dist (slice12 x i j).2
                    (dc2_i i (e1_i i (slice₁ (fun l => (x l).1) i), e2_i i (slice₂ (fun l => (x l).2) i)) j)) =
              ∑ i : Fin m, (1 / (n : ℝ)) * ((∏ k : Fin n, P.pmf (x k)) * ∑ j : Fin (len i),
                d₂.dist (slice12 x i j).2
                  (dc2_i i (e1_i i (slice₁ (fun l => (x l).1) i), e2_i i (slice₂ (fun l => (x l).2) i)) j)) := by
            intro x
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => by ring
          simp_rw [hpush]
          rw [Finset.sum_comm, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.mul_sum]
          refine congrArg ((1 / (n : ℝ)) * ·) ?_
          exact hslice_exp i (fun y => ∑ j : Fin (len i),
            d₂.dist (y j).2 (dc2_i i (e1_i i (fun l => (y l).1), e2_i i (fun l => (y l).2)) j))
      _ ≤ (1 / (n : ℝ)) * (∑ i : Fin m, (w i * (n : ℝ)) * (δ₂ i + ε / 4)) + ε / 2 := by
          refine add_le_add (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by positivity)) hrem_dist
          by_cases hwi : 0 < w i
          · have hli_pos : (0 : ℝ) < (len i : ℝ) := Nat.cast_pos.mpr (hlen_ge_Ni i hwi).2
            have hd := (hdc_spec i hwi).2
            have hmul : (∑ y : Fin (len i) → X₁ × X₂, (∏ j : Fin (len i), P.pmf (y j)) *
                ∑ j : Fin (len i), d₂.dist (y j).2 (dc2_i i (e1_i i (fun l => (y l).1), e2_i i (fun l => (y l).2)) j)) ≤
                (len i : ℝ) * (δ₂ i + ε / 4) := by
              have h1 := mul_le_mul_of_nonneg_left hd (le_of_lt hli_pos)
              have hlhs : (len i : ℝ) * (∑ y : Fin (len i) → X₁ × X₂, (∏ j : Fin (len i), P.pmf (y j)) *
                  ((1 / (len i : ℝ)) * ∑ j : Fin (len i), d₂.dist (y j).2
                    (dc2_i i (e1_i i (fun l => (y l).1), e2_i i (fun l => (y l).2)) j))) =
                  ∑ y : Fin (len i) → X₁ × X₂, (∏ j : Fin (len i), P.pmf (y j)) *
                    ∑ j : Fin (len i), d₂.dist (y j).2
                      (dc2_i i (e1_i i (fun l => (y l).1), e2_i i (fun l => (y l).2)) j) := by
                rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun y _ => by
                  field_simp [ne_of_gt hli_pos]
              linarith
            have hδ_nn : 0 ≤ δ₂ i + ε / 4 := by
              have h0 : 0 ≤ ∑ y : Fin (len i) → X₁ × X₂, (∏ j : Fin (len i), P.pmf (y j)) *
                  ((1 / (len i : ℝ)) * ∑ j : Fin (len i), d₂.dist (y j).2
                    (dc2_i i (e1_i i (fun l => (y l).1), e2_i i (fun l => (y l).2)) j)) :=
                Finset.sum_nonneg fun y _ => mul_nonneg (Finset.prod_nonneg fun _ _ => P.nonneg _)
                  (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => d₂.nonneg _ _))
              linarith
            exact le_trans hmul (mul_le_mul_of_nonneg_right (hlen_le i) hδ_nn)
          · have hw_eq : w i = 0 := le_antisymm (not_lt.mp hwi) (hw0 i)
            have hl0 : len i = 0 := hlen_zero i hwi
            have hsum0 : (∑ y : Fin (len i) → X₁ × X₂, (∏ j : Fin (len i), P.pmf (y j)) *
                ∑ j : Fin (len i), d₂.dist (y j).2
                  (dc2_i i (e1_i i (fun l => (y l).1), e2_i i (fun l => (y l).2)) j)) = 0 := by
              refine Finset.sum_eq_zero fun y _ => ?_
              have : IsEmpty (Fin (len i)) := by rw [hl0]; infer_instance
              simp
            rw [hsum0, hw_eq]; simp
      _ ≤ (∑ i : Fin m, w i * δ₂ i) + ε := by
          have hsimp : (1 / (n : ℝ)) * (∑ i : Fin m, (w i * (n : ℝ)) * (δ₂ i + ε / 4)) =
              (∑ i : Fin m, w i * δ₂ i) + ε / 4 := by
            rw [Finset.mul_sum]
            have hterm : ∀ i : Fin m, (1 / (n : ℝ)) * ((w i * (n : ℝ)) * (δ₂ i + ε / 4)) =
                w i * δ₂ i + (ε / 4) * w i := fun i => by field_simp [ne_of_gt hn_r]
            simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, hw1, mul_one]
          linarith

/-- **Closure Achievability of the Berger–Tung Inner Bound**:
    every 4-tuple `(R₁, R₂, D₁, D₂)` (`R₁, R₂ ≥ 0`) in the closed convex hull
    (time-sharing closure) of `bergerTungInnerBound` satisfies `IsBergerTungAchievable`. -/
theorem bergerTung_inner_closure_achievability
    (P : ProbDist (X₁ × X₂)) (d₁ : Distortion X₁ Xh₁) (d₂ : Distortion X₂ Xh₂)
    {R₁ R₂ D₁ D₂ : ℝ} (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂)
    (hclos : ∀ ε > 0, ∃ (m : ℕ) (w r₁ r₂ δ₁ δ₂ : Fin m → ℝ),
      (∀ i, 0 ≤ w i) ∧ (∑ i : Fin m, w i = 1) ∧
      (∀ i, (r₁ i, r₂ i) ∈ bergerTungInnerBound P d₁ d₂ (δ₁ i) (δ₂ i)) ∧
      (∑ i : Fin m, w i * r₁ i) ≤ R₁ + ε ∧
      (∑ i : Fin m, w i * r₂ i) ≤ R₂ + ε ∧
      (∑ i : Fin m, w i * δ₁ i) ≤ D₁ + ε ∧
      (∑ i : Fin m, w i * δ₂ i) ≤ D₂ + ε) :
    IsBergerTungAchievable P d₁ d₂ R₁ R₂ D₁ D₂ := by
  refine ⟨hR₁, hR₂, fun ε hε => ?_⟩
  obtain ⟨m, w, r₁, r₂, δ₁, δ₂, hw0, hw1, hmem, hr1, hr2, hd1, hd2⟩ := hclos (ε / 2) (half_pos hε)
  have hts := isBergerTungAchievable_timeSharing P d₁ d₂ hw0 hw1
    (fun i => bergerTung_inner_achievability P d₁ d₂ (hmem i))
  have hmono := isBergerTungAchievable_mono hts hr1 hr2 hd1 hd2
  obtain ⟨N, hN⟩ := hmono.2.2 (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have hN' := hN n hn
  have hR1_eq : R₁ + ε / 2 + ε / 2 = R₁ + ε := by ring
  have hR2_eq : R₂ + ε / 2 + ε / 2 = R₂ + ε := by ring
  rw [hR1_eq, hR2_eq] at hN'
  obtain ⟨enc₁, enc₂, dec₁, dec₂, h1, h2⟩ := hN'
  exact ⟨enc₁, enc₂, dec₁, dec₂, by linarith, by linarith⟩

end BergerTungAchievability

end InfoTheory.Bridge

