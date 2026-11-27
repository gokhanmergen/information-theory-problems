import InfoTheory.Bridge.ChannelCoding

/-!
# Rate–Distortion Theory & Covering Lemma (Cover & Thomas Ch. 10; El Gamal–Kim Lemma 3.3)

Purely additive, kernel-verified formalization of discrete memoryless rate–distortion theory
built on top of `InfoTheory.Core.SourceCoding` (`Distortion`, `rateDistortion`) and
`InfoTheory.Bridge.ChannelCoding`:

1. **Convexity of Mutual Information & Basic Properties of `rateDistortion P d D`**:
   - `mixtureDist`, `mutualInfo_mixture_le`, `mutualInfo_convex_channel`
   - `rateDistortion_nonneg`, `rateDistortion_le_mutualInfo`, `rateDistortion_antitone`
   - `rateDistortion_le_shannonEntropy_of_feasible`, `rateDistortion_le_shannonEntropy`,
     `rateDistortion_zero_le_shannonEntropy`, `rateDistortion_eq_zero_of_const`
   - `rateDistortion_convex` (convexity of `D ↦ R(D)` via zero-calculus conditional-MI time-sharing)

2. **Rate–Distortion Converse (Cover & Thomas §10.4, Theorem 10.2.1 converse)**:
   - `condEntropy_pi_le_sum` (`H(X_1, …, X_n | Y) ≤ ∑_i H(X_i | Y)`)
   - `condEntropy_le_map_right` (`H(X | Y) ≤ H(X | g(Y))`)
   - `iid_sum_mutualInfo_le` (`∑_i I(X_i; X̂_i) ≤ I(X^n; X̂^n)` for i.i.d. `X^n`)
   - `rateDistortion_converse`: for any `(n, M)` block code (`n ≥ 1, M ≥ 1`) with expected
     per-symbol distortion `≤ D`, `rateDistortion P d D ≤ log₂ M / n`

3. **Covering Lemma (El Gamal–Kim Lemma 3.3; Cover & Thomas Lemmas 10.5.3 & 10.6.1)**:
   - `codebookDist` (i.i.d. random codebook of `M` length-`n` codewords)
   - `one_sub_mul_pow_le_add_exp` (`(1 - x y)^M ≤ 1 - x + exp(-M y)` for `x, y ∈ [0, 1]`)
   - `covering_lemma_subset` (finite-blocklength exponential covering bound for any `S ⊆ A_ε^(n)`)
   - `covering_lemma` (El Gamal–Kim Lemma 3.3 for `S = jointTypicalSet P n ε`)
   - `covering_lemma_tendsto_zero` (asymptotic covering when `R > I(X; X̂) + 3ε`)

4. **Distortion Typicality & Rate–Distortion Achievability (Cover & Thomas §10.5, Theorem 10.2.1)**:
   - `expectedDist`, `blockDist`, `distVariance`, `distortionTypicalSet`
   - `jointIidDist_prob_not_distTypical_le` (explicit `O(1 / (n ε²))` Chebyshev–union tail bound)
   - `rateDistortion_achievability_of_dist` (single test-channel achievability via random coding)
   - `rateDistortion_achievability` (full Shannon Rate–Distortion Theorem achievability)

5. **Operational Rate–Distortion Theorem (Cover & Thomas Theorem 10.2.1)**:
   - `IsRateDistortionAchievable`, `operationalRateDistortion`
   - `rateDistortion_rightContinuous` (right-continuity of `D ↦ R(D)` at every feasible `D` via
     compactness of the feasible joint-distribution simplex)
   - `rateDistortion_operational_converse` and `rateDistortion_operational_achievability`
   - `shannon_rate_distortion_theorem` (`operationalRateDistortion P d D = rateDistortion P d D`)

All theorems leave `Core/`, `Problems/`, `Known/`, `STATEMENT_LOCK.json`, and existing
`Bridge/` modules untouched.
-/

open scoped BigOperators
open InfoTheory InfoTheory.Bridge

namespace InfoTheory.Bridge

/-! ### 1. Mixture Convexity of Mutual Information & Basic Properties of `rateDistortion` -/

section RateDistortionBasics

variable {α β γ ι : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype ι]

/-- Single-letter expected distortion `E_Q[d(X, X̂)]`. -/
def expectedDist (Q : ProbDist (α × β)) (d : Distortion α β) : ℝ :=
  ∑ xy : α × β, Q.pmf xy * d.dist xy.1 xy.2

/-- Empirical per-symbol block distortion `(1 / n) ∑_{i=1}^n d(x_i, x̂_i)`. -/
noncomputable def blockDist (d : Distortion α β) {n : ℕ} (x : Fin n → α) (xh : Fin n → β) : ℝ :=
  (1 / (n : ℝ)) * ∑ i : Fin n, d.dist (x i) (xh i)

/-- Convex mixture distribution `∑_t w(t) Q_t` over a finite index type `ι`. -/
def mixtureDist (w : ProbDist ι) (Q : ι → ProbDist α) : ProbDist α where
  pmf := fun a => ∑ t : ι, w.pmf t * (Q t).pmf a
  nonneg := fun a => Finset.sum_nonneg fun t _ => mul_nonneg (w.nonneg t) ((Q t).nonneg a)
  sum_one := by
    rw [Finset.sum_comm]
    have h : ∀ t : ι, ∑ a : α, w.pmf t * (Q t).pmf a = w.pmf t := fun t => by
      rw [← Finset.mul_sum, (Q t).sum_one, mul_one]
    simp_rw [h]
    exact w.sum_one

private lemma mixtureDist_fst (w : ProbDist ι) (Q : ι → ProbDist (α × β))
    (P : ProbDist α) (hQ : ∀ t, (Q t).fst = P) :
    (mixtureDist w Q).fst = P := by
  unfold ProbDist.fst mixtureDist
  congr
  funext a
  dsimp only
  rw [Finset.sum_comm]
  have h : ∀ t : ι, ∑ b : β, w.pmf t * (Q t).pmf (a, b) = w.pmf t * P.pmf a := fun t => by
    rw [← Finset.mul_sum]
    change w.pmf t * (Q t).fst.pmf a = w.pmf t * P.pmf a
    rw [hQ t]
  simp_rw [h, ← Finset.sum_mul, w.sum_one, one_mul]

private lemma expectedDist_mixtureDist (w : ProbDist ι) (Q : ι → ProbDist (α × β))
    (d : Distortion α β) :
    expectedDist (mixtureDist w Q) d = ∑ t : ι, w.pmf t * expectedDist (Q t) d := by
  unfold expectedDist mixtureDist
  dsimp only
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun xy _ => by ring

/-- Helper: entropy of a conditioned mixture distribution `(t, x) ↦ w(t) R_t(x)` equals
    `H(w) + ∑_t w(t) H(R_t)`. -/
private lemma shannonEntropy_condMixture (w : ProbDist ι) (R : ι → ProbDist α) :
    let M : ProbDist (ι × α) :=
      { pmf := fun ta => w.pmf ta.1 * (R ta.1).pmf ta.2
        nonneg := fun ta => mul_nonneg (w.nonneg ta.1) ((R ta.1).nonneg ta.2)
        sum_one := by
          rw [Fintype.sum_prod_type]
          simp_rw [← Finset.mul_sum, (R _).sum_one, mul_one]
          exact w.sum_one }
    shannonEntropy M = shannonEntropy w + ∑ t : ι, w.pmf t * shannonEntropy (R t) := by
  dsimp only
  unfold shannonEntropy
  rw [Fintype.sum_prod_type]
  have hterm : ∀ t : ι, ∑ a : α, negPLogP (w.pmf t * (R t).pmf a) =
      negPLogP (w.pmf t) + w.pmf t * ∑ a : α, negPLogP ((R t).pmf a) := fun t => by
    simp_rw [negPLogP_mul (w.nonneg t) ((R t).nonneg _), Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul, (R t).sum_one, one_mul]
    ring
  simp_rw [hterm, Finset.sum_add_distrib]

/-- **Convexity of Mutual Information in the Conditional Law (General Mixture Form)**
    (Cover & Thomas, Theorem 2.7.4):
    if every `Q_t` shares the same first marginal `P`, then the mutual information of the
    mixture `∑_t w(t) Q_t` is bounded above by the average mutual information:
    `I(X; X̂) ≤ ∑_t w(t) I_t(X; X̂)`.

    Proved without calculus via strong subadditivity `I(X; T | X̂) ≥ 0`. -/
theorem mutualInfo_mixture_le (w : ProbDist ι) (Q : ι → ProbDist (α × β))
    (P : ProbDist α) (hQ : ∀ t, (Q t).fst = P) :
    mutualInfo (mixtureDist w Q) ≤ ∑ t : ι, w.pmf t * mutualInfo (Q t) := by
  classical
  -- Construct joint triple `(X, T, X̂)` with pmf `w(t) * (Q t)(x, x̂)`.
  let T : ProbDist (α × ι × β) :=
    { pmf := fun z => w.pmf z.2.1 * (Q z.2.1).pmf (z.1, z.2.2)
      nonneg := fun z => mul_nonneg (w.nonneg z.2.1) ((Q z.2.1).nonneg (z.1, z.2.2))
      sum_one := by
        rw [Fintype.sum_prod_type]
        simp_rw [Fintype.sum_prod_type]
        rw [Finset.sum_comm]
        have h : ∀ t : ι, ∑ a : α, ∑ b : β, w.pmf t * (Q t).pmf (a, b) = w.pmf t := fun t => by
          simp_rw [← Finset.mul_sum]
          rw [← Fintype.sum_prod_type, (Q t).sum_one, mul_one]
        simp_rw [h]
        exact w.sum_one }
  -- Identify the four marginals appearing in `condMutualInfo T = I(X; T | X̂) ≥ 0`.
  have hT_xz : T.map (fun z => (z.1, z.2.2)) = mixtureDist w Q := by
    unfold ProbDist.map mixtureDist
    congr; funext ⟨a, b⟩; dsimp only
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single a]
    · rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Finset.sum_eq_single b]
      · simp [T]
      · intro b' _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro a' _ hne
      rw [Fintype.sum_prod_type]
      exact Finset.sum_eq_zero fun t _ =>
        Finset.sum_eq_zero fun b' _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  let M_tb : ProbDist (ι × β) :=
    { pmf := fun tb => w.pmf tb.1 * (Q tb.1).snd.pmf tb.2
      nonneg := fun tb => mul_nonneg (w.nonneg tb.1) ((Q tb.1).snd.nonneg tb.2)
      sum_one := by
        rw [Fintype.sum_prod_type]
        simp_rw [← Finset.mul_sum, (Q _).snd.sum_one, mul_one]
        exact w.sum_one }
  have hT_yz : T.map (fun z => (z.2.1, z.2.2)) = M_tb := by
    unfold ProbDist.map M_tb ProbDist.snd
    congr; funext ⟨t, b⟩; dsimp only
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single t]
    · rw [Finset.sum_eq_single b]
      · simp [T]
      · intro b' _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro t' _ hne
      exact Finset.sum_eq_zero fun b' _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hT_z : T.map (fun z => z.2.2) = (mixtureDist w Q).snd := by
    have h1 : T.map (fun z => z.2.2) = (T.map (fun z => (z.1, z.2.2))).map Prod.snd := by
      rw [map_comp_eq]; rfl
    rw [h1, hT_xz]
    unfold ProbDist.map ProbDist.snd
    congr; funext b
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single b]
    · simp
    · intro b' _ hne; simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  let M_tab : ProbDist (ι × (α × β)) :=
    { pmf := fun z => w.pmf z.1 * (Q z.1).pmf z.2
      nonneg := fun z => mul_nonneg (w.nonneg z.1) ((Q z.1).nonneg z.2)
      sum_one := by
        rw [Fintype.sum_prod_type]
        simp_rw [← Finset.mul_sum, (Q _).sum_one, mul_one]
        exact w.sum_one }
  let eT : (α × ι × β) ≃ (ι × (α × β)) :=
    { toFun := fun z => (z.2.1, (z.1, z.2.2))
      invFun := fun z => (z.2.1, z.1, z.2.2)
      left_inv := fun ⟨_, _, _⟩ => rfl
      right_inv := fun ⟨_, _, _⟩ => rfl }
  have hT_map : T.map eT = M_tab := by
    unfold ProbDist.map M_tab
    congr; funext ⟨t, a, b⟩; dsimp only
    rw [Finset.sum_eq_single (eT.symm (t, a, b))]
    · simp [eT, T]
    · intro z _ hne
      have : eT z ≠ (t, a, b) := fun h => hne (eT.symm_apply_eq.mpr h.symm).symm
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hHT : shannonEntropy T = shannonEntropy w + ∑ t : ι, w.pmf t * shannonEntropy (Q t) := by
    rw [← shannonEntropy_map_equiv eT T, hT_map]
    exact shannonEntropy_condMixture w Q
  have hHTyz : shannonEntropy M_tb =
      shannonEntropy w + ∑ t : ι, w.pmf t * shannonEntropy (Q t).snd :=
    shannonEntropy_condMixture w (fun t => (Q t).snd)
  have hcmi : 0 ≤ condMutualInfo T := condMutualInfo_nonneg T
  unfold condMutualInfo at hcmi
  dsimp only at hcmi
  rw [hT_xz, hT_yz, hT_z, hHT, hHTyz] at hcmi
  -- `hcmi` gives: `H(Q_mix) - H(Q_mix.snd) + ∑_t w(t) H((Q t).snd) - ∑_t w(t) H(Q t) ≥ 0`.
  have hfst_mix : (mixtureDist w Q).fst = P := mixtureDist_fst w Q P hQ
  have hHP : shannonEntropy P = ∑ t : ι, w.pmf t * shannonEntropy P := by
    rw [← Finset.sum_mul, w.sum_one, one_mul]
  have hsum_mi : ∑ t : ι, w.pmf t * mutualInfo (Q t) =
      shannonEntropy P + (∑ t : ι, w.pmf t * shannonEntropy (Q t).snd) -
        ∑ t : ι, w.pmf t * shannonEntropy (Q t) := by
    have hterm : ∀ t : ι, w.pmf t * mutualInfo (Q t) =
        w.pmf t * shannonEntropy P + w.pmf t * shannonEntropy (Q t).snd -
          w.pmf t * shannonEntropy (Q t) := fun t => by
      unfold mutualInfo
      rw [hQ t]
      ring
    simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [← hHP]
  rw [hsum_mi]
  unfold mutualInfo
  rw [hfst_mix]
  linarith

/-- **Two-Point Convexity of Mutual Information in the Test Channel** (Cover & Thomas, Thm. 2.7.4):
    for `0 ≤ λ ≤ 1` and joint distributions `Q₁, Q₂` with common first marginal `P`,
    `I(λ Q₁ + (1 - λ) Q₂) ≤ λ I(Q₁) + (1 - λ) I(Q₂)`. -/
theorem mutualInfo_convex_channel {P : ProbDist α} {Q₁ Q₂ : ProbDist (α × β)}
    (hQ₁ : Q₁.fst = P) (hQ₂ : Q₂.fst = P) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    let w := ProbDist.bernoulli lam h0 h1
    let Q := fun b : Bool => if b then Q₁ else Q₂
    mutualInfo (mixtureDist w Q) ≤ lam * mutualInfo Q₁ + (1 - lam) * mutualInfo Q₂ := by
  dsimp only
  have h := mutualInfo_mixture_le (ProbDist.bernoulli lam h0 h1) (fun b => if b then Q₁ else Q₂)
    P (fun b => by cases b <;> assumption)
  simpa [ProbDist.bernoulli] using h

/-- **Non-negativity of the Rate–Distortion Function**: `R(D) ≥ 0`. -/
theorem rateDistortion_nonneg (P : ProbDist α) (d : Distortion α β) (D : ℝ) :
    0 ≤ rateDistortion P d D := by
  unfold rateDistortion
  refine Real.sInf_nonneg ?_
  rintro r ⟨Q, _, _, rfl⟩
  exact mutualInfo_nonneg Q

/-- Any feasible test channel `Q` (`Q.fst = P`, `E_Q[d] ≤ D`) upper-bounds `rateDistortion P d D`. -/
theorem rateDistortion_le_mutualInfo {P : ProbDist α} {d : Distortion α β} {D : ℝ}
    {Q : ProbDist (α × β)} (hfst : Q.fst = P) (hdist : expectedDist Q d ≤ D) :
    rateDistortion P d D ≤ mutualInfo Q := by
  unfold rateDistortion
  refine csInf_le ⟨0, ?_⟩ ⟨Q, hfst, hdist, rfl⟩
  rintro r ⟨Q', _, _, rfl⟩
  exact mutualInfo_nonneg Q'

/-- **Monotonicity (Antitonicity) of `R(D)`** (Cover & Thomas, §10.2):
    whenever `D₁` is feasible and `D₁ ≤ D₂`, `R(D₂) ≤ R(D₁)`. -/
theorem rateDistortion_antitone {P : ProbDist α} {d : Distortion α β} {D₁ D₂ : ℝ}
    (hfeas : ∃ Q : ProbDist (α × β), Q.fst = P ∧ expectedDist Q d ≤ D₁) (hD : D₁ ≤ D₂) :
    rateDistortion P d D₂ ≤ rateDistortion P d D₁ := by
  unfold rateDistortion
  refine csInf_le_csInf ⟨0, ?_⟩ ?_ ?_
  · rintro r ⟨Q', _, _, rfl⟩; exact mutualInfo_nonneg Q'
  · rcases hfeas with ⟨Q, hfst, hdist⟩
    exact ⟨mutualInfo Q, Q, hfst, hdist, rfl⟩
  · rintro r ⟨Q, hfst, hdist, rfl⟩
    exact ⟨Q, hfst, le_trans hdist hD, rfl⟩

/-- Whenever `D` is feasible, `R(D) ≤ H(P)`. -/
theorem rateDistortion_le_shannonEntropy_of_feasible {P : ProbDist α} {d : Distortion α β} {D : ℝ}
    (hfeas : ∃ Q : ProbDist (α × β), Q.fst = P ∧ expectedDist Q d ≤ D) :
    rateDistortion P d D ≤ shannonEntropy P := by
  rcases hfeas with ⟨Q, hfst, hdist⟩
  have h1 : rateDistortion P d D ≤ mutualInfo Q := rateDistortion_le_mutualInfo hfst hdist
  have hce : 0 ≤ condEntropy Q := condEntropy_nonneg Q
  unfold mutualInfo at h1
  unfold condEntropy at hce
  rw [hfst] at h1
  linarith

/-- **Upper Bound `R(D) ≤ H(P)` under Pointwise Achievable Distortion** (Cover & Thomas, §10.2):
    if every source symbol `x` admits a reproduction `x̂` with `d(x, x̂) ≤ D`,
    then `rateDistortion P d D ≤ shannonEntropy P`. -/
theorem rateDistortion_le_shannonEntropy (P : ProbDist α) (d : Distortion α β) {D : ℝ}
    (h : ∀ x : α, ∃ xh : β, d.dist x xh ≤ D) :
    rateDistortion P d D ≤ shannonEntropy P := by
  classical
  let f : α → β := fun x => Classical.choose (h x)
  have hf : ∀ x : α, d.dist x (f x) ≤ D := fun x => Classical.choose_spec (h x)
  let Q : ProbDist (α × β) := P.map (fun x => (x, f x))
  have hfst : Q.fst = P := by
    unfold Q ProbDist.fst ProbDist.map
    congr; funext x; dsimp only
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single x]
    · rw [Finset.sum_eq_single (f x)]
      · simp
      · intro b _ hne; simp [hne.symm]
      · intro h'; exact absurd (Finset.mem_univ _) h'
    · intro x' _ hne
      exact Finset.sum_eq_zero fun b _ => by simp [hne]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  have hdist : expectedDist Q d ≤ D := by
    unfold expectedDist Q
    rw [← sum_pmf_mul_comp P (fun x => (x, f x)) (fun xy => d.dist xy.1 xy.2)]
    calc ∑ x : α, P.pmf x * d.dist x (f x)
      _ ≤ ∑ x : α, P.pmf x * D :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hf x) (P.nonneg x)
      _ = D := by rw [← Finset.sum_mul, P.sum_one, one_mul]
  exact rateDistortion_le_shannonEntropy_of_feasible ⟨Q, hfst, hdist⟩

/-- Special case `D = 0` when `d(x, x) = 0`: `R(0) ≤ H(P)`. -/
theorem rateDistortion_zero_le_shannonEntropy (P : ProbDist α) (d : Distortion α α)
    (hdiag : ∀ x : α, d.dist x x = 0) :
    rateDistortion P d 0 ≤ shannonEntropy P :=
  rateDistortion_le_shannonEntropy P d fun x => ⟨x, le_of_eq (hdiag x)⟩

/-- **Zero Rate Above `D_max`** (Cover & Thomas, §10.2):
    if a single constant reproduction `x̂₀` achieves expected distortion `≤ D`, then `R(D) = 0`. -/
theorem rateDistortion_eq_zero_of_const (P : ProbDist α) (d : Distortion α β) {D : ℝ}
    (hconst : ∃ xh₀ : β, ∑ x : α, P.pmf x * d.dist x xh₀ ≤ D) :
    rateDistortion P d D = 0 := by
  classical
  rcases hconst with ⟨xh₀, hxh₀⟩
  let δ₀ : ProbDist β :=
    { pmf := fun b => if b = xh₀ then 1 else 0
      nonneg := fun b => by split_ifs <;> norm_num
      sum_one := by simp }
  let Q : ProbDist (α × β) := P.prod δ₀
  have hfst : Q.fst = P := by
    unfold Q ProbDist.fst ProbDist.prod
    congr; funext a; simp [← Finset.mul_sum, δ₀.sum_one]
  have hsnd : Q.snd = δ₀ := by
    unfold Q ProbDist.snd ProbDist.prod
    congr; funext b; dsimp only
    rw [← Finset.sum_mul, P.sum_one, one_mul]
  have hmi : mutualInfo Q = 0 := by
    rw [mutualInfo_eq_zero_iff_indep, hfst, hsnd]
  have hdist : expectedDist Q d ≤ D := by
    unfold expectedDist Q ProbDist.prod
    rw [Fintype.sum_prod_type]
    have hinner : ∀ x : α, ∑ b : β, (P.pmf x * δ₀.pmf b) * d.dist x b = P.pmf x * d.dist x xh₀ := by
      intro x
      rw [Finset.sum_eq_single xh₀]
      · simp [δ₀]
      · intro b _ hne; simp [δ₀, hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    simp_rw [hinner]
    exact hxh₀
  exact le_antisymm (hmi ▸ rateDistortion_le_mutualInfo hfst hdist) (rateDistortion_nonneg P d D)

/-- **Convexity of the Rate–Distortion Function** (Cover & Thomas, Lemma 10.4.1):
    for any `0 ≤ λ ≤ 1` and feasible distortions `D₁, D₂`,
    `R(λ D₁ + (1 - λ) D₂) ≤ λ R(D₁) + (1 - λ) R(D₂)`. -/
theorem rateDistortion_convex {P : ProbDist α} {d : Distortion α β} {D₁ D₂ lam : ℝ}
    (hfeas₁ : ∃ Q : ProbDist (α × β), Q.fst = P ∧ expectedDist Q d ≤ D₁)
    (hfeas₂ : ∃ Q : ProbDist (α × β), Q.fst = P ∧ expectedDist Q d ≤ D₂)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    rateDistortion P d (lam * D₁ + (1 - lam) * D₂) ≤
      lam * rateDistortion P d D₁ + (1 - lam) * rateDistortion P d D₂ := by
  have hbdd : ∀ D : ℝ, BddBelow { r : ℝ | ∃ Q : ProbDist (α × β),
      Q.fst = P ∧ expectedDist Q d ≤ D ∧ r = mutualInfo Q } := fun D =>
    ⟨0, by rintro r ⟨Q, _, _, rfl⟩; exact mutualInfo_nonneg Q⟩
  have hne₁ : { r : ℝ | ∃ Q : ProbDist (α × β),
      Q.fst = P ∧ expectedDist Q d ≤ D₁ ∧ r = mutualInfo Q }.Nonempty := by
    rcases hfeas₁ with ⟨Q, hf, hd⟩; exact ⟨mutualInfo Q, Q, hf, hd, rfl⟩
  have hne₂ : { r : ℝ | ∃ Q : ProbDist (α × β),
      Q.fst = P ∧ expectedDist Q d ≤ D₂ ∧ r = mutualInfo Q }.Nonempty := by
    rcases hfeas₂ with ⟨Q, hf, hd⟩; exact ⟨mutualInfo Q, Q, hf, hd, rfl⟩
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hlt₁ : rateDistortion P d D₁ < rateDistortion P d D₁ + ε := by linarith
  have hlt₂ : rateDistortion P d D₂ < rateDistortion P d D₂ + ε := by linarith
  obtain ⟨r₁, ⟨Q₁, hQ₁_fst, hQ₁_dist, rfl⟩, hr₁⟩ :=
    (csInf_lt_iff (hbdd D₁) hne₁).mp hlt₁
  obtain ⟨r₂, ⟨Q₂, hQ₂_fst, hQ₂_dist, rfl⟩, hr₂⟩ :=
    (csInf_lt_iff (hbdd D₂) hne₂).mp hlt₂
  let w := ProbDist.bernoulli lam h0 h1
  let Qfun : Bool → ProbDist (α × β) := fun b => if b then Q₁ else Q₂
  let Qmix := mixtureDist w Qfun
  have hmix_fst : Qmix.fst = P := mixtureDist_fst w Qfun P (fun b => by cases b <;> assumption)
  have hmix_dist : expectedDist Qmix d ≤ lam * D₁ + (1 - lam) * D₂ := by
    have heq : expectedDist Qmix d = lam * expectedDist Q₁ d + (1 - lam) * expectedDist Q₂ d := by
      rw [show Qmix = mixtureDist w Qfun from rfl, expectedDist_mixtureDist]
      simp [w, Qfun, ProbDist.bernoulli]
    have hmul₁ : lam * expectedDist Q₁ d ≤ lam * D₁ := mul_le_mul_of_nonneg_left hQ₁_dist h0
    have hmul₂ : (1 - lam) * expectedDist Q₂ d ≤ (1 - lam) * D₂ :=
      mul_le_mul_of_nonneg_left hQ₂_dist (by linarith)
    linarith
  have hle_mix : rateDistortion P d (lam * D₁ + (1 - lam) * D₂) ≤ mutualInfo Qmix :=
    rateDistortion_le_mutualInfo hmix_fst hmix_dist
  have hconv := mutualInfo_convex_channel hQ₁_fst hQ₂_fst h0 h1
  dsimp only at hconv
  have h1' : lam * mutualInfo Q₁ ≤ lam * (rateDistortion P d D₁ + ε) :=
    mul_le_mul_of_nonneg_left (le_of_lt hr₁) h0
  have h2' : (1 - lam) * mutualInfo Q₂ ≤ (1 - lam) * (rateDistortion P d D₂ + ε) :=
    mul_le_mul_of_nonneg_left (le_of_lt hr₂) (by linarith)
  linarith

end RateDistortionBasics

/-! ### 2. Rate–Distortion Converse (Cover & Thomas §10.4, Theorem 10.2.1 Converse) -/

section RateDistortionConverse

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- **Subadditivity of Conditional Entropy**: `H(X_1, …, X_n | Y) ≤ ∑_i H(X_i | Y)`. -/
theorem condEntropy_pi_le_sum (n : ℕ) (P : ProbDist ((Fin n → α) × β)) :
    condEntropy P ≤ ∑ i : Fin n, condEntropy (P.map (fun xy => (xy.1 i, xy.2))) := by
  induction n with
  | zero =>
    have hcard : Fintype.card (Fin 0 → α) = 1 := Fintype.card_unique
    have hle := condEntropy_le_log2_card P
    rw [hcard] at hle
    simp only [Nat.cast_one, log2, Real.log_one, zero_div] at hle
    simpa using hle
  | succ n ih =>
    classical
    let e : ((Fin (n + 1) → α) × β) ≃ (α × (Fin n → α) × β) :=
      { toFun := fun xy => (xy.1 0, fun i => xy.1 i.succ, xy.2)
        invFun := fun z => (Fin.cons z.1 z.2.1, z.2.2)
        left_inv := fun ⟨x, y⟩ => by
          ext i
          · refine Fin.cases ?_ ?_ i <;> simp
          · rfl
        right_inv := fun ⟨a, xs, y⟩ => by
          refine Prod.ext (by simp) (Prod.ext ?_ rfl)
          funext i; simp }
    let Q : ProbDist (α × (Fin n → α) × β) := P.map e
    have hHQ : shannonEntropy Q = shannonEntropy P := shannonEntropy_map_equiv e P
    have hQ_xz : Q.map (fun t => (t.1, t.2.2)) = P.map (fun xy => (xy.1 0, xy.2)) := by
      rw [map_comp_eq]; rfl
    have hQ_yz : Q.map (fun t => (t.2.1, t.2.2)) =
        P.map (fun xy => (fun i : Fin n => xy.1 i.succ, xy.2)) := by
      rw [map_comp_eq]; rfl
    have hQ_z : Q.map (fun t => t.2.2) = P.snd := by
      rw [map_comp_eq]
      unfold ProbDist.map ProbDist.snd
      congr; funext b
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_eq_single b]
      · simp [e]
      · intro b' _ hne; simp [e, hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hQ_xz_snd : (P.map (fun xy => (xy.1 0, xy.2))).snd = P.snd := by
      unfold ProbDist.snd ProbDist.map
      congr; funext b; dsimp only
      rw [Finset.sum_comm, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_eq_single b]
      · rw [Finset.sum_eq_single (x 0)]
        · simp
        · intro a _ hne; simp [hne.symm]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro b' _ hne
        exact Finset.sum_eq_zero fun a _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hQ_yz_snd : (P.map (fun xy => (fun i : Fin n => xy.1 i.succ, xy.2))).snd = P.snd := by
      unfold ProbDist.snd ProbDist.map
      congr; funext b; dsimp only
      rw [Finset.sum_comm, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_eq_single b]
      · rw [Finset.sum_eq_single (fun i : Fin n => x i.succ)]
        · simp
        · intro xs _ hne; simp [hne.symm]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro b' _ hne
        exact Finset.sum_eq_zero fun xs _ => by simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    -- Strong subadditivity `I(X_0; X_{1..n} | Y) ≥ 0` gives `H(X^{n+1} | Y) ≤ H(X_0 | Y) + H(X_{1..n} | Y)`.
    have hcmi : 0 ≤ condMutualInfo Q := condMutualInfo_nonneg Q
    unfold condMutualInfo at hcmi
    dsimp only at hcmi
    rw [hQ_xz, hQ_yz, hQ_z, hHQ] at hcmi
    have hstep : condEntropy P ≤
        condEntropy (P.map (fun xy => (xy.1 0, xy.2))) +
          condEntropy (P.map (fun xy => (fun i : Fin n => xy.1 i.succ, xy.2))) := by
      unfold condEntropy
      rw [hQ_xz_snd, hQ_yz_snd]
      linarith
    have hih := ih (P.map (fun xy => (fun i : Fin n => xy.1 i.succ, xy.2)))
    have hcomp : ∀ i : Fin n,
        (P.map (fun xy => (fun j : Fin n => xy.1 j.succ, xy.2))).map (fun xy => (xy.1 i, xy.2)) =
          P.map (fun xy => (xy.1 i.succ, xy.2)) := fun i => by
      rw [map_comp_eq]; rfl
    simp_rw [hcomp] at hih
    rw [Fin.sum_univ_succ]
    linarith

/-- **Conditioning on More Reduces Entropy** (Data Processing for Conditional Entropy):
    for any joint distribution `P` on `α × β` and deterministic function `g : β → γ`,
    `H(X | Y) ≤ H(X | g(Y))`. -/
theorem condEntropy_le_map_right (P : ProbDist (α × β)) (g : β → γ) :
    condEntropy P ≤ condEntropy (P.map (Prod.map id g)) := by
  classical
  have hdpi := mutualInfo_map_right_le P g
  have hfst : (P.map (Prod.map id g)).fst = P.fst := by
    unfold ProbDist.fst ProbDist.map
    congr; funext a; dsimp only
    rw [Finset.sum_comm, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single a]
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_eq_single (g b)]
      · simp
      · intro c _ hne; simp [hne.symm]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro a' _ hne
      exact Finset.sum_eq_zero fun b _ =>
        Finset.sum_eq_zero fun c _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  unfold mutualInfo at hdpi
  unfold condEntropy
  rw [hfst] at hdpi
  linarith

private lemma iidDist_map_coord (P : ProbDist α) {n : ℕ} (i : Fin n) :
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

/-- **Superadditivity of Mutual Information for an i.i.d. Source** (Cover & Thomas, §10.4):
    for any joint distribution `J` on `(Fin n → α) × (Fin n → β)` whose first marginal
    is i.i.d. (`J.fst = iidDist P n`),
    `∑_i I(X_i; X̂_i) ≤ I(X^n; X̂^n)`. -/
theorem iid_sum_mutualInfo_le (P : ProbDist α) (n : ℕ)
    (J : ProbDist ((Fin n → α) × (Fin n → β))) (hfst : J.fst = iidDist P n) :
    ∑ i : Fin n, mutualInfo (J.map (fun xy => (xy.1 i, xy.2 i))) ≤ mutualInfo J := by
  have hH_fst : shannonEntropy J.fst = ∑ _i : Fin n, shannonEntropy P := by
    rw [hfst]
    change shannonEntropy (piProdDist (fun _ : Fin n => P)) = _
    exact shannonEntropy_piProdDist n (fun _ => P)
  have hcoord_fst : ∀ i : Fin n, (J.map (fun xy => (xy.1 i, xy.2 i))).fst = P := by
    intro i
    have h1 : (J.map (fun xy => (xy.1 i, xy.2 i))).fst = J.fst.map (fun x => x i) := by
      classical
      unfold ProbDist.fst ProbDist.map
      congr; funext a; dsimp only
      rw [Finset.sum_comm, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hxi : x i = a
      · simp only [hxi, ↓reduceIte]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_eq_single (y i)]
        · simp
        · intro b _ hne; simp [hne.symm]
        · intro h; exact absurd (Finset.mem_univ _) h
      · simp only [hxi, ↓reduceIte]
        exact Finset.sum_eq_zero fun y _ =>
          Finset.sum_eq_zero fun b _ => by simp [hxi]
    rw [h1, hfst, iidDist_map_coord]
  have hce_sum : condEntropy J ≤ ∑ i : Fin n, condEntropy (J.map (fun xy => (xy.1 i, xy.2 i))) := by
    refine le_trans (condEntropy_pi_le_sum n J) (Finset.sum_le_sum fun i _ => ?_)
    have h2 := condEntropy_le_map_right (J.map (fun xy => (xy.1 i, xy.2))) (fun y : Fin n → β => y i)
    have hcomp : (J.map (fun xy => (xy.1 i, xy.2))).map (Prod.map id (fun y : Fin n → β => y i)) =
        J.map (fun xy => (xy.1 i, xy.2 i)) := by
      rw [map_comp_eq]; rfl
    rw [hcomp] at h2
    exact h2
  have hmi_eq : ∀ Q : ProbDist (α × β), mutualInfo Q = shannonEntropy Q.fst - condEntropy Q := by
    intro Q; unfold mutualInfo condEntropy; ring
  have hmi_J : mutualInfo J = shannonEntropy J.fst - condEntropy J := by
    unfold mutualInfo condEntropy; ring
  simp_rw [hmi_eq, hcoord_fst, Finset.sum_sub_distrib]
  rw [hmi_J, hH_fst]
  linarith

/-- **Rate–Distortion Converse** (Cover & Thomas, §10.4, Theorem 10.2.1 converse):
    for any blocklength `n ≥ 1`, codebook size `M ≥ 1`, encoder `enc : (Fin n → α) → Fin M`,
    and decoder `dec : Fin M → (Fin n → β)` achieving expected per-symbol distortion `≤ D`
    on an i.i.d. source `P`,
    `rateDistortion P d D ≤ log₂ M / n`. -/
theorem rateDistortion_converse (P : ProbDist α) (d : Distortion α β) {n M : ℕ}
    (hn : 0 < n) (hM : 0 < M)
    (enc : (Fin n → α) → Fin M) (dec : Fin M → (Fin n → β)) {D : ℝ}
    (hdist : ∑ x : Fin n → α, (iidDist P n).pmf x * blockDist d x (dec (enc x)) ≤ D) :
    rateDistortion P d D ≤ log2 (M : ℝ) / (n : ℝ) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  let f : (Fin n → α) → (Fin n → β) := fun x => dec (enc x)
  let J : ProbDist ((Fin n → α) × (Fin n → β)) := (iidDist P n).map (fun x => (x, f x))
  have hJ_fst : J.fst = iidDist P n := by
    classical
    unfold J ProbDist.fst ProbDist.map
    congr; funext x; dsimp only
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single x]
    · rw [Finset.sum_eq_single (f x)]
      · simp [iidDist]
      · intro y _ hne; simp [hne.symm]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro x' _ hne
      exact Finset.sum_eq_zero fun y _ => by simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hJ_snd : J.snd = ((iidDist P n).map enc).map dec := by
    classical
    rw [map_comp_eq]
    unfold J ProbDist.snd ProbDist.map
    congr; funext y; dsimp only
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_eq_single x]
    · simp [f]
    · intro x' _ hne; simp [hne.symm]
    · intro h; exact absurd (Finset.mem_univ _) h
  -- Step 1: `I(X^n; X̂^n) ≤ H(X̂^n) ≤ H(enc(X^n)) ≤ log₂ M`.
  have hmi_le_logM : mutualInfo J ≤ log2 (M : ℝ) := by
    have hce_swap : 0 ≤ condEntropy (J.map Prod.swap) := condEntropy_nonneg (J.map Prod.swap)
    unfold condEntropy at hce_swap
    rw [shannonEntropy_swap, snd_map_swap] at hce_swap
    have hmi_le_snd : mutualInfo J ≤ shannonEntropy J.snd := by
      unfold mutualInfo; linarith
    have hsnd_le : shannonEntropy J.snd ≤ shannonEntropy ((iidDist P n).map enc) := by
      rw [hJ_snd]
      exact shannonEntropy_map_le dec ((iidDist P n).map enc)
    have hcard_le : shannonEntropy ((iidDist P n).map enc) ≤ log2 (M : ℝ) := by
      have h := shannonEntropy_le_log2_card ((iidDist P n).map enc)
      simpa using h
    linarith
  -- Step 2: `∑_i I(X_i; X̂_i) ≤ I(X^n; X̂^n)` by i.i.d. superadditivity.
  let Qi : Fin n → ProbDist (α × β) := fun i => J.map (fun xy => (xy.1 i, xy.2 i))
  have hsum_le : ∑ i : Fin n, mutualInfo (Qi i) ≤ mutualInfo J :=
    iid_sum_mutualInfo_le P n J hJ_fst
  -- Step 3: Time-sharing mixture `Q_mix = (1/n) ∑_i Q_i` is feasible with `I(Q_mix) ≤ (1/n) ∑_i I(Q_i)`.
  have hQi_fst : ∀ i : Fin n, (Qi i).fst = P := by
    intro i
    have h1 : (Qi i).fst = J.fst.map (fun x => x i) := by
      classical
      unfold Qi ProbDist.fst ProbDist.map
      congr; funext a; dsimp only
      rw [Finset.sum_comm, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hxi : x i = a
      · simp only [hxi, ↓reduceIte]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_eq_single (y i)]
        · simp
        · intro b _ hne; simp [hne.symm]
        · intro h; exact absurd (Finset.mem_univ _) h
      · simp only [hxi, ↓reduceIte]
        exact Finset.sum_eq_zero fun y _ =>
          Finset.sum_eq_zero fun b _ => by simp [hxi]
    rw [h1, hJ_fst, iidDist_map_coord]
  let Qmix : ProbDist (α × β) := mixtureDist (ProbDist.uniform (α := Fin n)) Qi
  have hmix_fst : Qmix.fst = P := mixtureDist_fst ProbDist.uniform Qi P hQi_fst
  have hQi_dist : ∀ i : Fin n, expectedDist (Qi i) d =
      ∑ x : Fin n → α, (iidDist P n).pmf x * d.dist (x i) (f x i) := by
    intro i
    unfold expectedDist Qi J
    rw [map_comp_eq]
    have hcomp : ((fun xy : (Fin n → α) × (Fin n → β) => (xy.1 i, xy.2 i)) ∘
        fun x => (x, f x)) = fun x => (x i, f x i) := rfl
    rw [hcomp]
    exact (sum_pmf_mul_comp (iidDist P n) (fun x => (x i, f x i))
      (fun ab => d.dist ab.1 ab.2)).symm
  have hmix_dist : expectedDist Qmix d ≤ D := by
    rw [expectedDist_mixtureDist]
    simp_rw [hQi_dist, ProbDist.uniform, Fintype.card_fin]
    have hrew : (∑ i : Fin n, (1 / (n : ℝ)) *
        ∑ x : Fin n → α, (iidDist P n).pmf x * d.dist (x i) (f x i)) =
        ∑ x : Fin n → α, (iidDist P n).pmf x * blockDist d x (f x) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      unfold blockDist
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [hrew]
    exact hdist
  have hR_le_mix : rateDistortion P d D ≤ mutualInfo Qmix :=
    rateDistortion_le_mutualInfo hmix_fst hmix_dist
  have hmix_le : mutualInfo Qmix ≤ (1 / (n : ℝ)) * ∑ i : Fin n, mutualInfo (Qi i) := by
    have h := mutualInfo_mixture_le (ProbDist.uniform (α := Fin n)) Qi P hQi_fst
    simpa [Qmix, ProbDist.uniform, Finset.mul_sum] using h
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hinv_nonneg : 0 ≤ (1 : ℝ) / (n : ℝ) := by positivity
  calc rateDistortion P d D
    _ ≤ mutualInfo Qmix := hR_le_mix
    _ ≤ (1 / (n : ℝ)) * ∑ i : Fin n, mutualInfo (Qi i) := hmix_le
    _ ≤ (1 / (n : ℝ)) * mutualInfo J := mul_le_mul_of_nonneg_left hsum_le hinv_nonneg
    _ ≤ (1 / (n : ℝ)) * log2 (M : ℝ) := mul_le_mul_of_nonneg_left hmi_le_logM hinv_nonneg
    _ = log2 (M : ℝ) / (n : ℝ) := by ring

end RateDistortionConverse

/-! ### 3. Covering Lemma (El Gamal–Kim Lemma 3.3; Cover & Thomas Lemmas 10.5.3 & 10.6.1) -/

section CoveringLemma

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Random codebook distribution: `M` codewords drawn i.i.d. from `iidDist Q n`. -/
def codebookDist (Q : ProbDist β) (n M : ℕ) : ProbDist (Fin M → Fin n → β) :=
  iidDist (iidDist Q n) M

/-- Auxiliary convexity inequality `(1 - x y)^M ≤ 1 - x + x (1 - y)^M` for `x, y ∈ [0, 1]`. -/
private lemma one_sub_mul_pow_le_linear {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (M : ℕ) :
    (1 - x * y) ^ M ≤ 1 - x + x * (1 - y) ^ M := by
  induction M with
  | zero => simp
  | succ M ih =>
    have h1my0 : 0 ≤ 1 - y := by linarith
    have h1my1 : 1 - y ≤ 1 := by linarith
    have hpow1 : (1 - y) ^ M ≤ 1 := pow_le_one₀ h1my0 h1my1
    have h1mxy0 : 0 ≤ 1 - x * y := by nlinarith
    have hstep1 : (1 - x * y) ^ (M + 1) ≤ (1 - x + x * (1 - y) ^ M) * (1 - x * y) := by
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_right ih h1mxy0
    have hdiff : (1 - x + x * (1 - y) ^ (M + 1)) - (1 - x + x * (1 - y) ^ M) * (1 - x * y) =
        x * (1 - x) * y * (1 - (1 - y) ^ M) := by
      rw [pow_succ]; ring
    have hnonneg : 0 ≤ x * (1 - x) * y * (1 - (1 - y) ^ M) :=
      mul_nonneg (mul_nonneg (mul_nonneg hx0 (by linarith)) hy0) (by linarith)
    linarith

/-- **Cover & Thomas Lemma 10.5.3**: for `x, y ∈ [0, 1]` and `M : ℕ`,
    `(1 - x y)^M ≤ 1 - x + exp(-M y)`. -/
theorem one_sub_mul_pow_le_add_exp {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (M : ℕ) :
    (1 - x * y) ^ M ≤ 1 - x + Real.exp (-((M : ℝ) * y)) := by
  have h1 := one_sub_mul_pow_le_linear hx0 hx1 hy0 hy1 M
  have h1my0 : 0 ≤ 1 - y := by linarith
  have hpow0 : 0 ≤ (1 - y) ^ M := pow_nonneg h1my0 M
  have h2 : x * (1 - y) ^ M ≤ (1 - y) ^ M := by nlinarith
  have hexp1 : 1 - y ≤ Real.exp (-y) := by
    have := Real.add_one_le_exp (-y); linarith
  have hexpM : (1 - y) ^ M ≤ Real.exp (-((M : ℝ) * y)) := by
    calc (1 - y) ^ M
      _ ≤ (Real.exp (-y)) ^ M := pow_le_pow_left₀ h1my0 hexp1 M
      _ = Real.exp ((M : ℝ) * (-y)) := (Real.exp_nat_mul (-y) M).symm
      _ = Real.exp (-((M : ℝ) * y)) := by ring_nf
  linarith

open Classical in
/-- **General Finite-Blocklength Covering Bound** for any subset `S ⊆ jointTypicalSet P n ε`:
    drawing `M` codewords i.i.d. from `P_Y^n`, the expected `P_X^n`-probability that no
    codeword `C m` satisfies `(x, C m) ∈ S` is bounded by
    `(1 - P^n(S)) + exp(-M · 2^(-n (I(X; Y) + 3ε)))`. -/
theorem covering_lemma_subset (P : ProbDist (α × β)) (n M : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (S : Finset ((Fin n → α) × (Fin n → β))) (hS : S ⊆ jointTypicalSet P n ε) :
    ∑ C : Fin M → Fin n → β, (codebookDist P.snd n M).pmf C *
      (∑ x : Fin n → α, (iidDist P.fst n).pmf x *
        (if ∀ m : Fin M, (x, C m) ∉ S then (1 : ℝ) else 0)) ≤
      (1 - ∑ xy ∈ S, (jointIidDist P n).pmf xy) +
        Real.exp (-((M : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo P + 3 * ε))))) := by
  let a : ℝ := (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo P + 3 * ε)))
  have ha0 : 0 ≤ a := le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  have ha1 : a ≤ 1 := by
    have hmi0 : 0 ≤ mutualInfo P := mutualInfo_nonneg P
    have hexp : -((n : ℝ) * (mutualInfo P + 3 * ε)) ≤ 0 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    simpa [a] using Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 2) hexp
  -- Swap sums over `C` and `x`.
  have hswap :
      (∑ C : Fin M → Fin n → β, (codebookDist P.snd n M).pmf C *
        (∑ x : Fin n → α, (iidDist P.fst n).pmf x *
          (if ∀ m : Fin M, (x, C m) ∉ S then (1 : ℝ) else 0))) =
      ∑ x : Fin n → α, (iidDist P.fst n).pmf x *
        (∑ C : Fin M → Fin n → β, (codebookDist P.snd n M).pmf C *
          (if ∀ m : Fin M, (x, C m) ∉ S then (1 : ℝ) else 0)) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    refine Finset.sum_congr rfl fun C _ => by ring
  rw [hswap]
  -- Evaluate the inner sum over `C` as `(1 - q(x))^M` by independence across `m : Fin M`.
  let q : (Fin n → α) → ℝ := fun x =>
    ∑ y : Fin n → β, if (x, y) ∈ S then (iidDist P.snd n).pmf y else 0
  have hinner : ∀ x : Fin n → α,
      (∑ C : Fin M → Fin n → β, (codebookDist P.snd n M).pmf C *
        (if ∀ m : Fin M, (x, C m) ∉ S then (1 : ℝ) else 0)) = (1 - q x) ^ M := by
    intro x
    have hind : ∀ C : Fin M → Fin n → β,
        (if ∀ m : Fin M, (x, C m) ∉ S then (1 : ℝ) else 0) =
          ∏ m : Fin M, (if (x, C m) ∉ S then (1 : ℝ) else 0) := by
      intro C
      by_cases h : ∀ m : Fin M, (x, C m) ∉ S
      · simp [h]
      · rw [ite_eq_right_iff.mpr (fun h' => absurd h' h)]
        push Not at h
        rcases h with ⟨m₀, hm₀⟩
        exact (Finset.prod_eq_zero (Finset.mem_univ m₀) (by simp [hm₀])).symm
    have hfac : ∀ C : Fin M → Fin n → β,
        (codebookDist P.snd n M).pmf C * (if ∀ m : Fin M, (x, C m) ∉ S then (1 : ℝ) else 0) =
          ∏ m : Fin M, ((iidDist P.snd n).pmf (C m) *
            (if (x, C m) ∉ S then (1 : ℝ) else 0)) := fun C => by
      rw [hind C]
      unfold codebookDist iidDist
      dsimp only
      rw [← Finset.prod_mul_distrib]
    simp_rw [hfac]
    rw [← Fintype.prod_sum (fun (_m : Fin M) (y : Fin n → β) =>
      (iidDist P.snd n).pmf y * (if (x, y) ∉ S then (1 : ℝ) else 0))]
    have h1mq : (∑ y : Fin n → β, (iidDist P.snd n).pmf y *
        (if (x, y) ∉ S then (1 : ℝ) else 0)) = 1 - q x := by
      have hsplit : ∑ y : Fin n → β, (iidDist P.snd n).pmf y =
          q x + ∑ y : Fin n → β, (iidDist P.snd n).pmf y *
            (if (x, y) ∉ S then (1 : ℝ) else 0) := by
        unfold q
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun y _ => by by_cases h : (x, y) ∈ S <;> simp [h]
      rw [(iidDist P.snd n).sum_one] at hsplit
      linarith
    simp_rw [h1mq, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp_rw [hinner]
  -- Key typicality comparison: for every `(x, y) ∈ S`,
  -- `P_X^n(x) * P_Y^n(y) ≥ a * P_{XY}^n(x, y)`.
  have htyp_mul : ∀ (x : Fin n → α) (y : Fin n → β), (x, y) ∈ S →
      a * (jointIidDist P n).pmf (x, y) ≤ (iidDist P.fst n).pmf x * (iidDist P.snd n).pmf y := by
    intro x y hxy
    have hmem := mem_jointTypicalSet.mp (hS hxy)
    have hx := hmem.1
    have hy := hmem.2.1
    have hjoint := hmem.2.2
    simp only [weakTypicalSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy hjoint
    have hjoint_le : (jointIidDist P n).pmf (x, y) ≤
        (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P - ε))) := hjoint.2
    have hpow_eq : a * (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P - ε))) =
        (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.fst + ε))) *
          (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.snd + ε))) := by
      dsimp only [a]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      unfold mutualInfo
      ring
    calc a * (jointIidDist P n).pmf (x, y)
      _ ≤ a * (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P - ε))) :=
          mul_le_mul_of_nonneg_left hjoint_le ha0
      _ = (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.fst + ε))) *
            (2 : ℝ) ^ (-((n : ℝ) * (shannonEntropy P.snd + ε))) := hpow_eq
      _ ≤ (iidDist P.fst n).pmf x * (iidDist P.snd n).pmf y :=
          mul_le_mul hx.1 hy.1 (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
            ((iidDist P.fst n).nonneg x)
  -- Per-`x` bound via Cover & Thomas Lemma 10.5.3.
  have hper_x : ∀ x : Fin n → α,
      (iidDist P.fst n).pmf x * (1 - q x) ^ M ≤
        (iidDist P.fst n).pmf x -
          (∑ y : Fin n → β, if (x, y) ∈ S then (jointIidDist P n).pmf (x, y) else 0) +
          (iidDist P.fst n).pmf x * Real.exp (-((M : ℝ) * a)) := by
    intro x
    let jx : ℝ := ∑ y : Fin n → β, if (x, y) ∈ S then (jointIidDist P n).pmf (x, y) else 0
    have hjx_nonneg : 0 ≤ jx :=
      Finset.sum_nonneg fun y _ => by split_ifs; exact (jointIidDist P n).nonneg _; exact le_rfl
    have hjx_le : jx ≤ (iidDist P.fst n).pmf x := by
      calc jx
        _ ≤ ∑ y : Fin n → β, (jointIidDist P n).pmf (x, y) :=
            Finset.sum_le_sum fun y _ => by
              split_ifs; exact le_rfl; exact (jointIidDist P n).nonneg _
        _ = (jointIidDist P n).fst.pmf x := rfl
        _ = (iidDist P.fst n).pmf x := by rw [jointIidDist_fst]
    by_cases hpx : (iidDist P.fst n).pmf x ≤ 0
    · have hpx0 : (iidDist P.fst n).pmf x = 0 := le_antisymm hpx ((iidDist P.fst n).nonneg x)
      have hjx0 : jx = 0 := le_antisymm (hpx0 ▸ hjx_le) hjx_nonneg
      simp only [hpx0, zero_mul, zero_sub]
      change 0 ≤ -jx + 0
      linarith
    · have hpx_pos : 0 < (iidDist P.fst n).pmf x := lt_of_not_ge hpx
      let b : ℝ := jx / (iidDist P.fst n).pmf x
      have hb0 : 0 ≤ b := div_nonneg hjx_nonneg (le_of_lt hpx_pos)
      have hb1 : b ≤ 1 := (div_le_one hpx_pos).mpr hjx_le
      have hqx_ge : a * b ≤ q x := by
        rw [mul_div_assoc', div_le_iff₀ hpx_pos]
        unfold q jx
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_le_sum fun y _ => ?_
        by_cases hxy : (x, y) ∈ S
        · simp only [hxy, ↓reduceIte]
          linarith [htyp_mul x y hxy]
        · simp [hxy]
      have hqx_le1 : q x ≤ 1 := by
        calc q x
          _ ≤ ∑ y : Fin n → β, (iidDist P.snd n).pmf y :=
              Finset.sum_le_sum fun y _ => by
                split_ifs; exact le_rfl; exact (iidDist P.snd n).nonneg _
          _ = 1 := (iidDist P.snd n).sum_one
      have hpow : (1 - q x) ^ M ≤ (1 - b * a) ^ M := by
        refine pow_le_pow_left₀ (by linarith) (by linarith) M
      have h1053 := one_sub_mul_pow_le_add_exp hb0 hb1 ha0 ha1 M
      have hcomb : (1 - q x) ^ M ≤ 1 - b + Real.exp (-((M : ℝ) * a)) := le_trans hpow h1053
      have hmul := mul_le_mul_of_nonneg_left hcomb (le_of_lt hpx_pos)
      have hpb : (iidDist P.fst n).pmf x * b = jx := mul_div_cancel₀ jx (ne_of_gt hpx_pos)
      linarith
  -- Sum over `x : Fin n → α`.
  calc ∑ x : Fin n → α, (iidDist P.fst n).pmf x * (1 - q x) ^ M
    _ ≤ ∑ x : Fin n → α, ((iidDist P.fst n).pmf x -
          (∑ y : Fin n → β, if (x, y) ∈ S then (jointIidDist P n).pmf (x, y) else 0) +
          (iidDist P.fst n).pmf x * Real.exp (-((M : ℝ) * a))) :=
        Finset.sum_le_sum fun x _ => hper_x x
    _ = (∑ x : Fin n → α, (iidDist P.fst n).pmf x) -
          (∑ x : Fin n → α, ∑ y : Fin n → β,
            if (x, y) ∈ S then (jointIidDist P n).pmf (x, y) else 0) +
          (∑ x : Fin n → α, (iidDist P.fst n).pmf x) * Real.exp (-((M : ℝ) * a)) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul]
    _ = (1 - ∑ xy ∈ S, (jointIidDist P n).pmf xy) + Real.exp (-((M : ℝ) * a)) := by
        have hSsum : (∑ x : Fin n → α, ∑ y : Fin n → β,
            if (x, y) ∈ S then (jointIidDist P n).pmf (x, y) else 0) =
            ∑ xy ∈ S, (jointIidDist P n).pmf xy := by
          rw [← Fintype.sum_prod_type (fun xy : (Fin n → α) × (Fin n → β) =>
            if xy ∈ S then (jointIidDist P n).pmf xy else 0)]
          rw [← Finset.sum_filter]
          congr 1; ext xy; simp
        rw [(iidDist P.fst n).sum_one, one_mul, hSsum]

open Classical in
/-- **Covering Lemma** (El Gamal–Kim Lemma 3.3; Cover & Thomas Lemma 10.6.1):
    for any joint distribution `P` on `α × β`, `n M : ℕ`, and `ε ≥ 0`, drawing `M` codewords
    i.i.d. from `P_Y^n`, the expected probability that `X^n ~ P_X^n` has no jointly typical
    codeword in the codebook satisfies
    `E_C [P_X^n(∀ m, (X^n, C m) ∉ A_ε^(n))] ≤ (1 - P^n(A_ε^(n))) + exp(-M · 2^(-n(I(X;Y) + 3ε)))`. -/
theorem covering_lemma (P : ProbDist (α × β)) (n M : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    ∑ C : Fin M → Fin n → β, (codebookDist P.snd n M).pmf C *
      (∑ x : Fin n → α, (iidDist P.fst n).pmf x *
        (if ∀ m : Fin M, (x, C m) ∉ jointTypicalSet P n ε then (1 : ℝ) else 0)) ≤
      (1 - ∑ xy ∈ jointTypicalSet P n ε, (jointIidDist P n).pmf xy) +
        Real.exp (-((M : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo P + 3 * ε))))) :=
  covering_lemma_subset P n M hε (jointTypicalSet P n ε) (Finset.Subset.refl _)

/-- Helper: exponential decay `exp(-M · 2^(-n (I + 3ε))) ≤ c` for `M = max 1 ⌊2^(n R)⌋`
    when `I + 3ε < R` and `n` is sufficiently large. -/
private lemma covering_exp_le {I R ε c : ℝ} (hI : 0 ≤ I) (hε : 0 ≤ ε)
    (hR : I + 3 * ε < R) (hc : 0 < c) :
    ∃ N : ℕ, ∀ n ≥ N,
      let M := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
      Real.exp (-((M : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I + 3 * ε))))) ≤ c := by
  have hR_pos : 0 < R := by linarith
  let η : ℝ := R - (I + 3 * ε)
  have hη : 0 < η := by dsimp [η]; linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (1 / R)
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (2 / (c * η * Real.log 2))
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  dsimp only
  set M := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
  have hn1 : 1 / R < (n : ℝ) := lt_of_lt_of_le hN₁ (by exact_mod_cast le_trans (le_max_left N₁ N₂) hn)
  have hn2 : 2 / (c * η * Real.log 2) < (n : ℝ) :=
    lt_of_lt_of_le hN₂ (by exact_mod_cast le_trans (le_max_right N₁ N₂) hn)
  have hnR : 1 ≤ (n : ℝ) * R := by
    have := (div_lt_iff₀ hR_pos).mp hn1; linarith
  have h2R : (2 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R) := by
    calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * R) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hnR
  have hM_ge : (1 / 2 : ℝ) * (2 : ℝ) ^ ((n : ℝ) * R) ≤ (M : ℝ) := by
    have hfl : (2 : ℝ) ^ ((n : ℝ) * R) - 1 < (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)) : ℝ) :=
      Nat.sub_one_lt_floor _
    have hleM : (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)) : ℝ) ≤ (M : ℝ) := by
      exact_mod_cast Nat.le_max_right 1 _
    linarith
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (-((n : ℝ) * (I + 3 * ε))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hprod_ge : (1 / 2 : ℝ) * (2 : ℝ) ^ ((n : ℝ) * η) ≤
      (M : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I + 3 * ε))) := by
    calc (1 / 2 : ℝ) * (2 : ℝ) ^ ((n : ℝ) * η)
      _ = ((1 / 2 : ℝ) * (2 : ℝ) ^ ((n : ℝ) * R)) * (2 : ℝ) ^ (-((n : ℝ) * (I + 3 * ε))) := by
          rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 2; dsimp [η]; ring
      _ ≤ (M : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I + 3 * ε))) :=
          mul_le_mul_of_nonneg_right hM_ge (le_of_lt hpow_pos)
  have h2η : (n : ℝ) * η * Real.log 2 ≤ (2 : ℝ) ^ ((n : ℝ) * η) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h := Real.add_one_le_exp (Real.log 2 * ((n : ℝ) * η))
    linarith
  have hlin : 1 / c ≤ (1 / 2 : ℝ) * ((n : ℝ) * η * Real.log 2) := by
    have h1 := (div_lt_iff₀ (by positivity : 0 < c * η * Real.log 2)).mp hn2
    rw [div_le_iff₀ hc]
    linarith
  have ht_ge : 1 / c ≤ (M : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I + 3 * ε))) := by linarith
  have hexp_ge : 1 / c ≤ Real.exp ((M : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I + 3 * ε)))) := by
    have h := Real.add_one_le_exp ((M : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I + 3 * ε))))
    linarith
  rw [Real.exp_neg]
  have hpos_inv : (0 : ℝ) < 1 / c := by positivity
  calc (Real.exp ((M : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (I + 3 * ε)))))⁻¹
    _ ≤ (1 / c)⁻¹ := inv_anti₀ hpos_inv hexp_ge
    _ = c := by rw [one_div, inv_inv]

open Classical in
/-- **Asymptotic Covering Lemma** (El Gamal–Kim Lemma 3.3):
    for any `P : ProbDist (α × β)`, `ε > 0`, `R > I(X; Y) + 3ε`, and `δ > 0`,
    for all sufficiently large `n` and `M = max 1 ⌊2^(n R)⌋`, the expected uncovered
    probability under an i.i.d. random codebook from `P_Y^n` is at most `δ`. -/
theorem covering_lemma_tendsto_zero (P : ProbDist (α × β)) {R ε δ : ℝ}
    (hε : 0 < ε) (hR : mutualInfo P + 3 * ε < R) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N,
      let M := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
      ∑ C : Fin M → Fin n → β, (codebookDist P.snd n M).pmf C *
        (∑ x : Fin n → α, (iidDist P.fst n).pmf x *
          (if ∀ m : Fin M, (x, C m) ∉ jointTypicalSet P n ε then (1 : ℝ) else 0)) ≤ δ := by
  obtain ⟨N₁, hN₁⟩ := joint_aep_prob_tendsto_one P hε (half_pos hδ)
  obtain ⟨N₂, hN₂⟩ := covering_exp_le (mutualInfo_nonneg P) (le_of_lt hε) hR (half_pos hδ)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  dsimp only
  have hcov := covering_lemma P n (Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))) (le_of_lt hε)
  have h1 := hN₁ n (le_trans (le_max_left N₁ N₂) hn)
  have h2 := hN₂ n (le_trans (le_max_right N₁ N₂) hn)
  linarith

end CoveringLemma

/-! ### 4. Distortion Typicality & Rate–Distortion Achievability (Cover & Thomas §10.5, Thm. 10.2.1) -/

section RateDistortionAchievability

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Variance of the single-letter distortion `d(X, X̂)` under `Q`. -/
def distVariance (Q : ProbDist (α × β)) (d : Distortion α β) : ℝ :=
  ∑ xy : α × β, Q.pmf xy * (d.dist xy.1 xy.2 - expectedDist Q d) ^ 2

private lemma distVariance_nonneg (Q : ProbDist (α × β)) (d : Distortion α β) :
    0 ≤ distVariance Q d :=
  Finset.sum_nonneg fun xy _ => mul_nonneg (Q.nonneg xy) (sq_nonneg _)

/-- **Distortion-Typical Set** (Cover & Thomas, §10.5, Eq. 10.65):
    jointly weakly typical pairs `(x, x̂)` whose empirical average distortion lies within `ε`
    of `E_Q[d(X, X̂)]`. -/
noncomputable def distortionTypicalSet (Q : ProbDist (α × β)) (d : Distortion α β)
    (n : ℕ) (ε : ℝ) : Finset ((Fin n → α) × (Fin n → β)) := by
  classical
  exact (jointTypicalSet Q n ε).filter fun xy =>
    |blockDist d xy.1 xy.2 - expectedDist Q d| ≤ ε

/-- **Explicit Chebyshev–Union Tail Bound for Distortion Typicality** (Cover & Thomas, Lemma 10.5.1):
    for any `n ≥ 1` and `ε > 0`,
    `1 - Q^n(A_{d, ε}^(n)) ≤ (V(Q_X) + V(Q_X̂) + V(Q) + Var_Q(d)) / (n ε²)`. -/
theorem jointIidDist_prob_not_distTypical_le (Q : ProbDist (α × β)) (d : Distortion α β)
    {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    1 - ∑ xy ∈ distortionTypicalSet Q d n ε, (jointIidDist Q n).pmf xy ≤
      (varentropy Q.fst + varentropy Q.snd + varentropy Q + distVariance Q d) /
        ((n : ℝ) * ε ^ 2) := by
  classical
  let p := (jointIidDist Q n).pmf
  have hcomp_eq : 1 - ∑ xy ∈ distortionTypicalSet Q d n ε, p xy =
      ∑ xy : (Fin n → α) × (Fin n → β),
        if xy ∉ distortionTypicalSet Q d n ε then p xy else 0 := by
    have hsplit : ∑ xy : (Fin n → α) × (Fin n → β), p xy =
        (∑ xy : (Fin n → α) × (Fin n → β),
          if xy ∈ distortionTypicalSet Q d n ε then p xy else 0) +
        (∑ xy : (Fin n → α) × (Fin n → β),
          if xy ∉ distortionTypicalSet Q d n ε then p xy else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun xy _ => by
        by_cases h : xy ∈ distortionTypicalSet Q d n ε <;> simp [h]
    rw [(jointIidDist Q n).sum_one] at hsplit
    have hmem : (∑ xy : (Fin n → α) × (Fin n → β),
        if xy ∈ distortionTypicalSet Q d n ε then p xy else 0) =
        ∑ xy ∈ distortionTypicalSet Q d n ε, p xy := by
      rw [← Finset.sum_filter]; congr 1; ext xy; simp
    linarith
  have hunion : ∀ xy : (Fin n → α) × (Fin n → β),
      (if xy ∉ distortionTypicalSet Q d n ε then p xy else 0) ≤
        (if xy ∉ jointTypicalSet Q n ε then p xy else 0) +
        (if ¬ (|blockDist d xy.1 xy.2 - expectedDist Q d| ≤ ε) then p xy else 0) := by
    intro xy
    have hp0 : 0 ≤ p xy := (jointIidDist Q n).nonneg xy
    by_cases h1 : xy ∈ jointTypicalSet Q n ε
    · by_cases h2 : |blockDist d xy.1 xy.2 - expectedDist Q d| ≤ ε
      · have hmem : xy ∈ distortionTypicalSet Q d n ε := by
          simp [distortionTypicalSet, h1, h2]
        simp [hmem, h1, h2]
      · simp [distortionTypicalSet, h1, h2]
    · simp only [distortionTypicalSet, Finset.mem_filter, h1, false_and, not_false_eq_true,
        ↓reduceIte]
      split_ifs <;> linarith
  have hsum_union :
      (∑ xy : (Fin n → α) × (Fin n → β),
        if xy ∉ distortionTypicalSet Q d n ε then p xy else 0) ≤
      (∑ xy : (Fin n → α) × (Fin n → β), if xy ∉ jointTypicalSet Q n ε then p xy else 0) +
      (∑ xy : (Fin n → α) × (Fin n → β),
        if ¬ (|blockDist d xy.1 xy.2 - expectedDist Q d| ≤ ε) then p xy else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun xy _ => hunion xy
  -- Bound the first sum by `jointIidDist_prob_not_typical_le`.
  have hfirst : (∑ xy : (Fin n → α) × (Fin n → β),
      if xy ∉ jointTypicalSet Q n ε then p xy else 0) =
      1 - ∑ xy ∈ jointTypicalSet Q n ε, p xy := by
    have hsplit : ∑ xy : (Fin n → α) × (Fin n → β), p xy =
        (∑ xy : (Fin n → α) × (Fin n → β), if xy ∈ jointTypicalSet Q n ε then p xy else 0) +
        (∑ xy : (Fin n → α) × (Fin n → β), if xy ∉ jointTypicalSet Q n ε then p xy else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun xy _ => by
        by_cases h : xy ∈ jointTypicalSet Q n ε <;> simp [h]
    rw [(jointIidDist Q n).sum_one] at hsplit
    have hmem : (∑ xy : (Fin n → α) × (Fin n → β),
        if xy ∈ jointTypicalSet Q n ε then p xy else 0) =
        ∑ xy ∈ jointTypicalSet Q n ε, p xy := by
      rw [← Finset.sum_filter]; congr 1; ext xy; simp
    linarith
  have htail1 := jointIidDist_prob_not_typical_le Q hn hε
  -- Bound the distortion-deviation sum by Chebyshev's inequality.
  let Z : α × β → ℝ := fun xy => d.dist xy.1 xy.2 - expectedDist Q d
  have hEZ : ∑ xy : α × β, Q.pmf xy * Z xy = 0 := by
    simp_rw [Z, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, Q.sum_one, one_mul]
    change expectedDist Q d - expectedDist Q d = 0
    ring
  have hVar : ∑ z : Fin n → α × β, (iidDist Q n).pmf z * (∑ i : Fin n, Z (z i)) ^ 2 =
      (n : ℝ) * distVariance Q d := by
    have hsq : ∀ z : Fin n → α × β,
        (iidDist Q n).pmf z * (∑ i : Fin n, Z (z i)) ^ 2 =
          ∑ i : Fin n, ∑ j : Fin n, (iidDist Q n).pmf z * (Z (z i) * Z (z j)) := by
      intro z
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
    simp_rw [hsq]
    rw [Finset.sum_comm]
    trans (∑ i : Fin n, ∑ j : Fin n,
        ∑ z : Fin n → α × β, (iidDist Q n).pmf z * (Z (z i) * Z (z j)))
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
    · trans (∑ i : Fin n, distVariance Q d)
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_eq_single i]
        · have h := iidDist_sum_coord Q (fun xy => Z xy * Z xy) i
          simpa [← sq, distVariance, Z] using h
        · intro j _ hji
          rw [iidDist_sum_two_coords Q Z Z hji.symm, hEZ, mul_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
      · simp
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hcheb_term : ∀ xy : (Fin n → α) × (Fin n → β),
      ((n : ℝ) * ε) ^ 2 *
        (if ¬ (|blockDist d xy.1 xy.2 - expectedDist Q d| ≤ ε) then p xy else 0) ≤
      p xy * (∑ i : Fin n, Z (xy.1 i, xy.2 i)) ^ 2 := by
    intro xy
    have hp0 : 0 ≤ p xy := (jointIidDist Q n).nonneg xy
    by_cases hle : |blockDist d xy.1 xy.2 - expectedDist Q d| ≤ ε
    · simp only [hle, not_true_eq_false, ↓reduceIte, mul_zero]
      exact mul_nonneg hp0 (sq_nonneg _)
    · simp only [hle, not_false_eq_true, ↓reduceIte]
      have hgt : ε < |blockDist d xy.1 xy.2 - expectedDist Q d| := lt_of_not_ge hle
      have hsumZ : ∑ i : Fin n, Z (xy.1 i, xy.2 i) =
          (n : ℝ) * (blockDist d xy.1 xy.2 - expectedDist Q d) := by
        unfold blockDist Z
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, mul_sub, ← mul_assoc, mul_one_div_cancel (ne_of_gt hn_pos), one_mul]
      have habs : (n : ℝ) * ε < |∑ i : Fin n, Z (xy.1 i, xy.2 i)| := by
        rw [hsumZ, abs_mul, abs_of_pos hn_pos]
        exact mul_lt_mul_of_pos_left hgt hn_pos
      have hsq : ((n : ℝ) * ε) ^ 2 ≤ (∑ i : Fin n, Z (xy.1 i, xy.2 i)) ^ 2 := by
        rw [← sq_abs (∑ i : Fin n, Z (xy.1 i, xy.2 i))]
        have hne0 : 0 ≤ (n : ℝ) * ε := by positivity
        nlinarith
      nlinarith
  have hsum_cheb :
      ((n : ℝ) * ε) ^ 2 *
        (∑ xy : (Fin n → α) × (Fin n → β),
          if ¬ (|blockDist d xy.1 xy.2 - expectedDist Q d| ≤ ε) then p xy else 0) ≤
      (n : ℝ) * distVariance Q d := by
    rw [Finset.mul_sum]
    calc ∑ xy : (Fin n → α) × (Fin n → β),
          ((n : ℝ) * ε) ^ 2 *
            (if ¬ (|blockDist d xy.1 xy.2 - expectedDist Q d| ≤ ε) then p xy else 0)
      _ ≤ ∑ xy : (Fin n → α) × (Fin n → β),
            p xy * (∑ i : Fin n, Z (xy.1 i, xy.2 i)) ^ 2 :=
          Finset.sum_le_sum fun xy _ => hcheb_term xy
      _ = ∑ z : Fin n → α × β, (iidDist Q n).pmf z * (∑ i : Fin n, Z (z i)) ^ 2 :=
          Fintype.sum_equiv (zipEquiv α β n) _ _ (fun _ => rfl)
      _ = (n : ℝ) * distVariance Q d := hVar
  have htail2 :
      (∑ xy : (Fin n → α) × (Fin n → β),
        if ¬ (|blockDist d xy.1 xy.2 - expectedDist Q d| ≤ ε) then p xy else 0) ≤
      distVariance Q d / ((n : ℝ) * ε ^ 2) := by
    have hden_pos : (0 : ℝ) < (n : ℝ) * ε ^ 2 := by positivity
    rw [le_div_iff₀ hden_pos]
    have hrew : ((n : ℝ) * ε) ^ 2 = (n : ℝ) * ((n : ℝ) * ε ^ 2) := by ring
    rw [hrew, mul_assoc, mul_comm ((n : ℝ) * ε ^ 2)] at hsum_cheb
    exact le_of_mul_le_mul_left hsum_cheb hn_pos
  have hadd : (varentropy Q.fst + varentropy Q.snd + varentropy Q) / ((n : ℝ) * ε ^ 2) +
      distVariance Q d / ((n : ℝ) * ε ^ 2) =
      (varentropy Q.fst + varentropy Q.snd + varentropy Q + distVariance Q d) /
        ((n : ℝ) * ε ^ 2) := by ring
  rw [hcomp_eq]
  rw [hfirst] at hsum_union
  linarith

/-- Finite probabilistic method: if `E_W[f] ≤ B`, then there exists `c` with `f c ≤ B`. -/
private lemma exists_le_of_expectation_le {Ω : Type*} [Fintype Ω] (W : ProbDist Ω)
    (f : Ω → ℝ) {B : ℝ} (h : ∑ ω : Ω, W.pmf ω * f ω ≤ B) :
    ∃ ω : Ω, f ω ≤ B := by
  by_contra hall
  push Not at hall
  have hex_pos : ∃ ω₀ : Ω, 0 < W.pmf ω₀ := by
    by_contra hnone
    push Not at hnone
    have hzero : ∑ ω : Ω, W.pmf ω = 0 :=
      Finset.sum_eq_zero fun ω _ => le_antisymm (hnone ω) (W.nonneg ω)
    linarith [W.sum_one]
  rcases hex_pos with ⟨ω₀, hω₀⟩
  have hlt : B < ∑ ω : Ω, W.pmf ω * f ω := by
    have hB : B = ∑ ω : Ω, W.pmf ω * B := by rw [← Finset.sum_mul, W.sum_one, one_mul]
    rw [hB]
    refine Finset.sum_lt_sum (fun ω _ => mul_le_mul_of_nonneg_left (le_of_lt (hall ω)) (W.nonneg ω))
      ⟨ω₀, Finset.mem_univ ω₀, mul_lt_mul_of_pos_left (hall ω₀) hω₀⟩
  linarith

/-- **Single Test-Channel Rate–Distortion Achievability** (Cover & Thomas, §10.5):
    for any joint distribution `Q` on `α × β` with `Q.fst = P`, any rate `R > I(X; X̂)`,
    and any `δ > 0`, for all sufficiently large `n` there exists a block code of size
    `M = max 1 ⌊2^(n R)⌋` achieving expected per-symbol distortion `≤ E_Q[d] + δ`. -/
theorem rateDistortion_achievability_of_dist (P : ProbDist α) (d : Distortion α β)
    (Q : ProbDist (α × β)) (hfst : Q.fst = P) {R δ : ℝ}
    (hR : mutualInfo Q < R) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N,
      let M := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
      ∃ (enc : (Fin n → α) → Fin M) (dec : Fin M → (Fin n → β)),
        ∑ x : Fin n → α, (iidDist P n).pmf x * blockDist d x (dec (enc x)) ≤
          expectedDist Q d + δ := by
  classical
  let gap : ℝ := R - mutualInfo Q
  have hgap : 0 < gap := by dsimp [gap]; linarith
  let ε : ℝ := min (δ / 2) (gap / 4)
  have hε : 0 < ε := lt_min (by linarith) (by linarith)
  have hε_le_δ : ε ≤ δ / 2 := min_le_left _ _
  have hε_le_gap : ε ≤ gap / 4 := min_le_right _ _
  have hR_eps : mutualInfo Q + 3 * ε < R := by dsimp [gap] at hε_le_gap; linarith
  -- Finite uniform upper bound on `d`.
  let dmax : ℝ := ∑ xy : α × β, d.dist xy.1 xy.2
  have hdmax0 : 0 ≤ dmax := Finset.sum_nonneg fun xy _ => d.nonneg xy.1 xy.2
  have hd_le : ∀ x y, d.dist x y ≤ dmax := fun x y =>
    Finset.single_le_sum (fun xy _ => d.nonneg xy.1 xy.2) (Finset.mem_univ (x, y))
  let B : ℝ := dmax + 1
  have hB : 0 < B := by dsimp [B]; linarith
  let c : ℝ := δ / (4 * B)
  have hc : 0 < c := by positivity
  -- Choose `N` so both the distortion-typicality tail and the covering exponential are `≤ c`.
  let V : ℝ := varentropy Q.fst + varentropy Q.snd + varentropy Q + distVariance Q d
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (V / (c * ε ^ 2))
  obtain ⟨N₂, hN₂⟩ := covering_exp_le (mutualInfo_nonneg Q) (le_of_lt hε) hR_eps hc
  refine ⟨max (max N₁ N₂) 1, fun n hn => ?_⟩
  dsimp only
  have hn_pos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right _ 1) hn)
  have hn1 : V / (c * ε ^ 2) < (n : ℝ) :=
    lt_of_lt_of_le hN₁ (by exact_mod_cast le_trans (le_trans (le_max_left N₁ N₂) (le_max_left _ 1)) hn)
  have hn2 : N₂ ≤ n := le_trans (le_trans (le_max_right N₁ N₂) (le_max_left _ 1)) hn
  set M := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
  have hM_pos : 0 < M := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
  let S := distortionTypicalSet Q d n ε
  -- For any codebook `C`, define the distortion-typicality encoder `enc_C`.
  let encOf : (Fin M → Fin n → β) → (Fin n → α) → Fin M := fun C x =>
    if h : ∃ m : Fin M, (x, C m) ∈ S then Classical.choose h else ⟨0, hM_pos⟩
  let codeDist : (Fin M → Fin n → β) → ℝ := fun C =>
    ∑ x : Fin n → α, (iidDist P n).pmf x * blockDist d x (C (encOf C x))
  have hblock_le : ∀ (x : Fin n → α) (y : Fin n → β), blockDist d x y ≤ dmax := fun x y => by
    unfold blockDist
    have hn_r : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
    calc (1 / (n : ℝ)) * ∑ i : Fin n, d.dist (x i) (y i)
      _ ≤ (1 / (n : ℝ)) * ∑ _i : Fin n, dmax :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hd_le (x i) (y i)) (by positivity)
      _ = dmax := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← mul_assoc, one_div_mul_cancel (ne_of_gt hn_r), one_mul]
  have hED_nonneg : 0 ≤ expectedDist Q d :=
    Finset.sum_nonneg fun xy _ => mul_nonneg (Q.nonneg xy) (d.nonneg xy.1 xy.2)
  -- Per-codebook distortion bound in terms of the uncovered probability.
  have hcode_bound : ∀ C : Fin M → Fin n → β,
      codeDist C ≤ (expectedDist Q d + ε) +
        dmax * (∑ x : Fin n → α, (iidDist Q.fst n).pmf x *
          (if ∀ m : Fin M, (x, C m) ∉ S then (1 : ℝ) else 0)) := by
    intro C
    unfold codeDist
    rw [← hfst]
    have hpt : ∀ x : Fin n → α,
        (iidDist Q.fst n).pmf x * blockDist d x (C (encOf C x)) ≤
          (iidDist Q.fst n).pmf x * (expectedDist Q d + ε) +
          dmax * ((iidDist Q.fst n).pmf x *
            (if ∀ m : Fin M, (x, C m) ∉ S then (1 : ℝ) else 0)) := by
      intro x
      have hpx : 0 ≤ (iidDist Q.fst n).pmf x := (iidDist Q.fst n).nonneg x
      by_cases hex : ∃ m : Fin M, (x, C m) ∈ S
      · have hnotall : ¬ (∀ m : Fin M, (x, C m) ∉ S) := by
          push Not; exact hex
        have hmem : (x, C (encOf C x)) ∈ S := by
          simp only [encOf, hex, ↓reduceDIte]
          exact Classical.choose_spec hex
        have habs : |blockDist d x (C (encOf C x)) - expectedDist Q d| ≤ ε := by
          simp only [S, distortionTypicalSet, Finset.mem_filter] at hmem
          exact hmem.2
        have hbd : blockDist d x (C (encOf C x)) ≤ expectedDist Q d + ε := by
          linarith [(abs_le.mp habs).2]
        simp only [hnotall, ↓reduceIte, mul_zero, add_zero]
        exact mul_le_mul_of_nonneg_left hbd hpx
      · have hall : ∀ m : Fin M, (x, C m) ∉ S := fun m hm => hex ⟨m, hm⟩
        have hite : (if ∀ m : Fin M, (x, C m) ∉ S then (1 : ℝ) else 0) = 1 :=
          ite_eq_left_iff.mpr (fun h => absurd hall h)
        rw [hite, mul_one]
        have hbd := hblock_le x (C (encOf C x))
        have h1 : (iidDist Q.fst n).pmf x * blockDist d x (C (encOf C x)) ≤
            (iidDist Q.fst n).pmf x * dmax := mul_le_mul_of_nonneg_left hbd hpx
        have h2 : 0 ≤ (iidDist Q.fst n).pmf x * (expectedDist Q d + ε) :=
          mul_nonneg hpx (by linarith)
        linarith
    calc ∑ x : Fin n → α, (iidDist Q.fst n).pmf x * blockDist d x (C (encOf C x))
      _ ≤ ∑ x : Fin n → α, ((iidDist Q.fst n).pmf x * (expectedDist Q d + ε) +
            dmax * ((iidDist Q.fst n).pmf x *
              (if ∀ m : Fin M, (x, C m) ∉ S then (1 : ℝ) else 0))) :=
          Finset.sum_le_sum fun x _ => hpt x
      _ = (expectedDist Q d + ε) +
            dmax * (∑ x : Fin n → α, (iidDist Q.fst n).pmf x *
              (if ∀ m : Fin M, (x, C m) ∉ S then (1 : ℝ) else 0)) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, (iidDist Q.fst n).sum_one, one_mul,
            ← Finset.mul_sum]
  -- Average over `C ~ codebookDist Q.snd n M` and apply `covering_lemma_subset`.
  have hS_sub : S ⊆ jointTypicalSet Q n ε := Finset.filter_subset _ _
  have hcov := covering_lemma_subset Q n M (le_of_lt hε) S hS_sub
  have htail_le : 1 - ∑ xy ∈ S, (jointIidDist Q n).pmf xy ≤ c := by
    have ht := jointIidDist_prob_not_distTypical_le Q d hn_pos hε
    have hn_r : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
    have hV_le : V / ((n : ℝ) * ε ^ 2) ≤ c := by
      rw [div_le_iff₀ (by positivity)]
      have h1 := (div_lt_iff₀ (by positivity : 0 < c * ε ^ 2)).mp hn1
      linarith
    exact le_trans ht hV_le
  have hexp_le : Real.exp (-((M : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Q + 3 * ε))))) ≤ c :=
    hN₂ n hn2
  have havg_le : ∑ C : Fin M → Fin n → β, (codebookDist Q.snd n M).pmf C * codeDist C ≤
      expectedDist Q d + δ := by
    calc ∑ C : Fin M → Fin n → β, (codebookDist Q.snd n M).pmf C * codeDist C
      _ ≤ ∑ C : Fin M → Fin n → β, (codebookDist Q.snd n M).pmf C *
            ((expectedDist Q d + ε) +
              dmax * (∑ x : Fin n → α, (iidDist Q.fst n).pmf x *
                (if ∀ m : Fin M, (x, C m) ∉ S then (1 : ℝ) else 0))) :=
          Finset.sum_le_sum fun C _ =>
            mul_le_mul_of_nonneg_left (hcode_bound C) ((codebookDist Q.snd n M).nonneg C)
      _ = (expectedDist Q d + ε) +
            dmax * (∑ C : Fin M → Fin n → β, (codebookDist Q.snd n M).pmf C *
              (∑ x : Fin n → α, (iidDist Q.fst n).pmf x *
                (if ∀ m : Fin M, (x, C m) ∉ S then (1 : ℝ) else 0))) := by
          simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
            (codebookDist Q.snd n M).sum_one, one_mul]
          congr 1
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun C _ => by ring
      _ ≤ (expectedDist Q d + ε) +
            dmax * ((1 - ∑ xy ∈ S, (jointIidDist Q n).pmf xy) +
              Real.exp (-((M : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (mutualInfo Q + 3 * ε)))))) := by
          gcongr
      _ ≤ (expectedDist Q d + ε) + dmax * (c + c) := by
          gcongr
      _ ≤ (expectedDist Q d + ε) + B * (2 * c) := by
          have hdB : dmax ≤ B := by dsimp [B]; linarith
          have h2c : 0 ≤ 2 * c := by positivity
          nlinarith
      _ ≤ expectedDist Q d + δ := by
          have hBc : B * (2 * c) = δ / 2 := by
            dsimp [c]
            field_simp [ne_of_gt hB]
            ring
          linarith
  -- Extract a deterministic codebook `C` via the probabilistic method.
  obtain ⟨C, hC⟩ := exists_le_of_expectation_le (codebookDist Q.snd n M) codeDist havg_le
  exact ⟨encOf C, C, hC⟩

/-- **Shannon Rate–Distortion Achievability** (Cover & Thomas, Theorem 10.2.1):
    for any source `P : ProbDist α`, distortion measure `d : Distortion α β`, feasible
    distortion level `D`, rate `R > rateDistortion P d D`, and `δ > 0`, for all sufficiently
    large `n` there exists a block code `(enc, dec)` of size `M = max 1 ⌊2^(n R)⌋` with
    expected per-symbol distortion `≤ D + δ`. -/
theorem rateDistortion_achievability (P : ProbDist α) (d : Distortion α β) {D R δ : ℝ}
    (hfeas : ∃ Q : ProbDist (α × β), Q.fst = P ∧ expectedDist Q d ≤ D)
    (hR : rateDistortion P d D < R) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N,
      let M := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
      ∃ (enc : (Fin n → α) → Fin M) (dec : Fin M → (Fin n → β)),
        ∑ x : Fin n → α, (iidDist P n).pmf x * blockDist d x (dec (enc x)) ≤ D + δ := by
  have hbdd : BddBelow { r : ℝ | ∃ Q : ProbDist (α × β),
      Q.fst = P ∧ expectedDist Q d ≤ D ∧ r = mutualInfo Q } :=
    ⟨0, by rintro r ⟨Q, _, _, rfl⟩; exact mutualInfo_nonneg Q⟩
  have hne : { r : ℝ | ∃ Q : ProbDist (α × β),
      Q.fst = P ∧ expectedDist Q d ≤ D ∧ r = mutualInfo Q }.Nonempty := by
    rcases hfeas with ⟨Q, hf, hd⟩; exact ⟨mutualInfo Q, Q, hf, hd, rfl⟩
  obtain ⟨r, ⟨Q, hQ_fst, hQ_dist, rfl⟩, hQ_mi⟩ := (csInf_lt_iff hbdd hne).mp hR
  obtain ⟨N, hN⟩ := rateDistortion_achievability_of_dist P d Q hQ_fst hQ_mi hδ
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨enc, dec, hcode⟩ := hN n hn
  exact ⟨enc, dec, le_trans hcode (by linarith)⟩

end RateDistortionAchievability

/-! ### 5. Operational Rate–Distortion Theorem (Cover & Thomas, Theorem 10.2.1) -/

section OperationalRateDistortion

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Operational achievability of rate `R` at distortion level `D` for an i.i.d. source `P`
    and distortion measure `d`: `R ≥ 0` and for every `δ > 0`, for all sufficiently large
    blocklengths `n ≥ N` (`N > 0`), there exists a block code of size
    `M = max 1 ⌊2^(n R)⌋` with expected per-symbol distortion at most `D + δ`. -/
def IsRateDistortionAchievable (P : ProbDist α) (d : Distortion α β) (D R : ℝ) : Prop :=
  0 ≤ R ∧ ∀ δ > 0, ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N,
    let M := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
    ∃ (enc : (Fin n → α) → Fin M) (dec : Fin M → (Fin n → β)),
      ∑ x : Fin n → α, (iidDist P n).pmf x * blockDist d x (dec (enc x)) ≤ D + δ

/-- Operational rate–distortion function: infimum of all operationally achievable rates
    at distortion level `D`. -/
noncomputable def operationalRateDistortion (P : ProbDist α) (d : Distortion α β) (D : ℝ) : ℝ :=
  sInf { R : ℝ | IsRateDistortionAchievable P d D R }

/-- The simplex of joint pmfs on `α × β` with first marginal `P`. -/
private def rdSimplex (P : ProbDist α) (β : Type*) [Fintype β] : Set (α × β → ℝ) :=
  { f | (∀ z, 0 ≤ f z) ∧ (∑ z : α × β, f z = 1) ∧ (∀ a : α, ∑ b : β, f (a, b) = P.pmf a) }

private lemma continuous_sum_finset {ι X : Type*} [TopologicalSpace X]
    (s : Finset ι) (f : ι → X → ℝ) (hf : ∀ i ∈ s, Continuous (f i)) :
    Continuous (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using continuous_const
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private lemma isCompact_rdSimplex (P : ProbDist α) : IsCompact (rdSimplex P β) := by
  have h1 : IsClosed { f : α × β → ℝ | ∀ z, 0 ≤ f z } := by
    have heq : { f : α × β → ℝ | ∀ z, 0 ≤ f z } = ⋂ z : α × β, { f : α × β → ℝ | 0 ≤ f z } := by
      ext f; simp
    rw [heq]
    exact isClosed_iInter fun z => isClosed_le continuous_const (continuous_apply z)
  have h2 : IsClosed { f : α × β → ℝ | ∑ z : α × β, f z = 1 } :=
    isClosed_eq (continuous_sum_finset Finset.univ _ fun z _ => continuous_apply z) continuous_const
  have h3 : IsClosed { f : α × β → ℝ | ∀ a : α, ∑ b : β, f (a, b) = P.pmf a } := by
    have heq : { f : α × β → ℝ | ∀ a : α, ∑ b : β, f (a, b) = P.pmf a } =
        ⋂ a : α, { f : α × β → ℝ | ∑ b : β, f (a, b) = P.pmf a } := by
      ext f; simp
    rw [heq]
    exact isClosed_iInter fun a =>
      isClosed_eq (continuous_sum_finset Finset.univ _ fun b _ => continuous_apply (a, b))
        continuous_const
  have hclosed : IsClosed (rdSimplex P β) := h1.inter (h2.inter h3)
  have hsub : rdSimplex P β ⊆ Set.pi Set.univ (fun _ : α × β => Set.Icc (0 : ℝ) 1) := by
    intro f ⟨h0, hsum, _⟩ z _
    refine ⟨h0 z, ?_⟩
    calc f z ≤ ∑ w : α × β, f w :=
          Finset.single_le_sum (fun w _ => h0 w) (Finset.mem_univ z)
      _ = 1 := hsum
  exact (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset hclosed hsub

private def rdDistFn (d : Distortion α β) (f : α × β → ℝ) : ℝ :=
  ∑ z : α × β, f z * d.dist z.1 z.2

private lemma continuous_rdDistFn (d : Distortion α β) : Continuous (rdDistFn d) :=
  continuous_sum_finset Finset.univ _ fun z _ => (continuous_apply z).mul continuous_const

private noncomputable def rdMiFn (P : ProbDist α) (f : α × β → ℝ) : ℝ :=
  shannonEntropy P +
    (∑ b : β, Real.negMulLog (∑ a : α, f (a, b))) / Real.log 2 -
    (∑ z : α × β, Real.negMulLog (f z)) / Real.log 2

private lemma continuous_rdMiFn (P : ProbDist α) : Continuous (rdMiFn P (β := β)) := by
  have h1 : Continuous (fun f : α × β → ℝ =>
      (∑ b : β, Real.negMulLog (∑ a : α, f (a, b))) / Real.log 2) :=
    (continuous_sum_finset Finset.univ _ fun b _ =>
      Real.continuous_negMulLog.comp
        (continuous_sum_finset Finset.univ _ fun a _ => continuous_apply (a, b))).div_const _
  have h2 : Continuous (fun f : α × β → ℝ =>
      (∑ z : α × β, Real.negMulLog (f z)) / Real.log 2) :=
    (continuous_sum_finset Finset.univ _ fun z _ =>
      Real.continuous_negMulLog.comp (continuous_apply z)).div_const _
  exact (continuous_const.add h1).sub h2

private lemma rdMiFn_eq_mutualInfo {P : ProbDist α} {Q : ProbDist (α × β)} (hfst : Q.fst = P) :
    rdMiFn P Q.pmf = mutualInfo Q := by
  unfold rdMiFn mutualInfo
  rw [hfst, InfoTheory.Known.shannonEntropy_eq_sum_negMulLog Q.snd,
    InfoTheory.Known.shannonEntropy_eq_sum_negMulLog Q]
  rfl

private lemma pmf_mem_rdSimplex {P : ProbDist α} {Q : ProbDist (α × β)} (hfst : Q.fst = P) :
    Q.pmf ∈ rdSimplex P β :=
  ⟨Q.nonneg, Q.sum_one, fun a => by
    change Q.fst.pmf a = P.pmf a
    rw [hfst]⟩

private def probDistOfRdSimplex {P : ProbDist α} {f : α × β → ℝ} (hf : f ∈ rdSimplex P β) :
    ProbDist (α × β) where
  pmf := f
  nonneg := hf.1
  sum_one := hf.2.1

private lemma probDistOfRdSimplex_fst {P : ProbDist α} {f : α × β → ℝ} (hf : f ∈ rdSimplex P β) :
    (probDistOfRdSimplex hf).fst = P := by
  unfold ProbDist.fst probDistOfRdSimplex
  congr
  funext a
  exact hf.2.2 a

/-- **Right-Continuity of the Rate–Distortion Function** (Cover & Thomas, §10.2):
    at any feasible distortion `D` (including the boundary `D = D_min`),
    for every `ε > 0` there exists `δ > 0` with `R(D) - ε ≤ R(D + δ)`. -/
theorem rateDistortion_rightContinuous (P : ProbDist α) (d : Distortion α β) {D : ℝ}
    (hfeas : ∃ Q : ProbDist (α × β), Q.fst = P ∧ expectedDist Q d ≤ D) :
    ∀ ε > 0, ∃ δ > 0, rateDistortion P d D - ε ≤ rateDistortion P d (D + δ) := by
  intro ε hε
  by_contra h
  push Not at h
  have hbdd : ∀ D' : ℝ, BddBelow { r : ℝ | ∃ Q : ProbDist (α × β),
      Q.fst = P ∧ expectedDist Q d ≤ D' ∧ r = mutualInfo Q } := fun _ =>
    ⟨0, by rintro r ⟨Q, _, _, rfl⟩; exact mutualInfo_nonneg Q⟩
  have hstep : ∀ k : ℕ, ∃ Q : ProbDist (α × β),
      Q.fst = P ∧ expectedDist Q d ≤ D + 1 / ((k : ℝ) + 1) ∧
        mutualInfo Q < rateDistortion P d D - ε := by
    intro k
    have hδ : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have hlt := h (1 / ((k : ℝ) + 1)) hδ
    have hne : { r : ℝ | ∃ Q : ProbDist (α × β),
        Q.fst = P ∧ expectedDist Q d ≤ D + 1 / ((k : ℝ) + 1) ∧ r = mutualInfo Q }.Nonempty := by
      rcases hfeas with ⟨Q₀, hfst₀, hdist₀⟩
      exact ⟨mutualInfo Q₀, Q₀, hfst₀, by linarith, rfl⟩
    obtain ⟨r, ⟨Q, hQ_fst, hQ_dist, rfl⟩, hQ_mi⟩ := (csInf_lt_iff (hbdd _) hne).mp hlt
    exact ⟨Q, hQ_fst, hQ_dist, hQ_mi⟩
  choose Q hQ_fst hQ_dist hQ_mi using hstep
  let seq : ℕ → (α × β → ℝ) := fun k => (Q k).pmf
  have hmem : ∀ k : ℕ, seq k ∈ rdSimplex P β := fun k => pmf_mem_rdSimplex (hQ_fst k)
  obtain ⟨fstar, hfstar, φ, hφ, htend⟩ := (isCompact_rdSimplex P).tendsto_subseq hmem
  let Qstar : ProbDist (α × β) := probDistOfRdSimplex hfstar
  have hQstar_fst : Qstar.fst = P := probDistOfRdSimplex_fst hfstar
  have hdist_tend : Filter.Tendsto (fun k => rdDistFn d (seq (φ k))) Filter.atTop
      (nhds (rdDistFn d fstar)) :=
    (continuous_rdDistFn d).continuousAt.tendsto.comp htend
  have hrhs_tend : Filter.Tendsto (fun k => D + 1 / ((φ k : ℝ) + 1)) Filter.atTop
      (nhds (D + 0)) :=
    tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop)
  have hQstar_dist : expectedDist Qstar d ≤ D := by
    have hle : rdDistFn d fstar ≤ D + 0 :=
      le_of_tendsto_of_tendsto hdist_tend hrhs_tend (Filter.Eventually.of_forall fun k => hQ_dist (φ k))
    simpa [Qstar, probDistOfRdSimplex, rdDistFn, expectedDist] using hle
  have hmi_tend : Filter.Tendsto (fun k => rdMiFn P (seq (φ k))) Filter.atTop
      (nhds (rdMiFn P fstar)) :=
    (continuous_rdMiFn P).continuousAt.tendsto.comp htend
  have hQstar_mi : mutualInfo Qstar ≤ rateDistortion P d D - ε := by
    have hle : rdMiFn P fstar ≤ rateDistortion P d D - ε :=
      le_of_tendsto hmi_tend (Filter.Eventually.of_forall fun k => by
        dsimp only [seq]
        rw [rdMiFn_eq_mutualInfo (hQ_fst (φ k))]
        exact le_of_lt (hQ_mi (φ k)))
    have hpmf : Qstar.pmf = fstar := rfl
    have heq : rdMiFn P fstar = mutualInfo Qstar := by
      rw [← hpmf]
      exact rdMiFn_eq_mutualInfo hQstar_fst
    linarith
  have hR_le : rateDistortion P d D ≤ mutualInfo Qstar :=
    rateDistortion_le_mutualInfo hQstar_fst hQstar_dist
  linarith

/-- Time-sharing single-letter feasibility witness extracted from a block code. -/
private lemma exists_feasible_of_code (P : ProbDist α) (d : Distortion α β) {n M : ℕ}
    (hn : 0 < n) (enc : (Fin n → α) → Fin M) (dec : Fin M → (Fin n → β)) {D' : ℝ}
    (hdist : ∑ x : Fin n → α, (iidDist P n).pmf x * blockDist d x (dec (enc x)) ≤ D') :
    ∃ Q : ProbDist (α × β), Q.fst = P ∧ expectedDist Q d ≤ D' := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let f : (Fin n → α) → (Fin n → β) := fun x => dec (enc x)
  let Qi : Fin n → ProbDist (α × β) := fun i => (iidDist P n).map (fun x => (x i, f x i))
  have hQi_fst : ∀ i : Fin n, (Qi i).fst = P := by
    intro i
    have h1 : (Qi i).fst = (iidDist P n).map (fun x => x i) := by
      classical
      unfold Qi ProbDist.fst ProbDist.map
      congr; funext a; dsimp only
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hxi : x i = a
      · simp only [hxi, ↓reduceIte]
        rw [Finset.sum_eq_single (f x i)]
        · simp
        · intro b _ hne; simp [hne.symm]
        · intro h; exact absurd (Finset.mem_univ _) h
      · simp only [hxi, ↓reduceIte]
        exact Finset.sum_eq_zero fun b _ => by simp [hxi]
    rw [h1, iidDist_map_coord]
  let Qmix : ProbDist (α × β) := mixtureDist (ProbDist.uniform (α := Fin n)) Qi
  have hmix_fst : Qmix.fst = P := mixtureDist_fst ProbDist.uniform Qi P hQi_fst
  have hQi_dist : ∀ i : Fin n, expectedDist (Qi i) d =
      ∑ x : Fin n → α, (iidDist P n).pmf x * d.dist (x i) (f x i) := fun i =>
    (sum_pmf_mul_comp (iidDist P n) (fun x => (x i, f x i)) (fun ab => d.dist ab.1 ab.2)).symm
  have hmix_dist : expectedDist Qmix d ≤ D' := by
    rw [expectedDist_mixtureDist]
    simp_rw [hQi_dist, ProbDist.uniform, Fintype.card_fin]
    have hrew : (∑ i : Fin n, (1 / (n : ℝ)) *
        ∑ x : Fin n → α, (iidDist P n).pmf x * d.dist (x i) (f x i)) =
        ∑ x : Fin n → α, (iidDist P n).pmf x * blockDist d x (f x) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      unfold blockDist
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [hrew]
    exact hdist
  exact ⟨Qmix, hmix_fst, hmix_dist⟩

/-- Operational achievability at distortion `D` implies `D` is single-letter feasible. -/
private lemma feasible_of_isRateDistortionAchievable {P : ProbDist α} {d : Distortion α β}
    {D R : ℝ} (hach : IsRateDistortionAchievable P d D R) :
    ∃ Q : ProbDist (α × β), Q.fst = P ∧ expectedDist Q d ≤ D := by
  have hstep : ∀ k : ℕ, ∃ Q : ProbDist (α × β),
      Q.fst = P ∧ expectedDist Q d ≤ D + 1 / ((k : ℝ) + 1) := by
    intro k
    obtain ⟨N, hN_pos, hN⟩ := hach.2 (1 / ((k : ℝ) + 1)) (by positivity)
    obtain ⟨enc, dec, hcode⟩ := hN N le_rfl
    exact exists_feasible_of_code P d hN_pos enc dec hcode
  choose Q hQ_fst hQ_dist using hstep
  let seq : ℕ → (α × β → ℝ) := fun k => (Q k).pmf
  have hmem : ∀ k : ℕ, seq k ∈ rdSimplex P β := fun k => pmf_mem_rdSimplex (hQ_fst k)
  obtain ⟨fstar, hfstar, φ, hφ, htend⟩ := (isCompact_rdSimplex P).tendsto_subseq hmem
  let Qstar : ProbDist (α × β) := probDistOfRdSimplex hfstar
  have hdist_tend : Filter.Tendsto (fun k => rdDistFn d (seq (φ k))) Filter.atTop
      (nhds (rdDistFn d fstar)) :=
    (continuous_rdDistFn d).continuousAt.tendsto.comp htend
  have hrhs_tend : Filter.Tendsto (fun k => D + 1 / ((φ k : ℝ) + 1)) Filter.atTop
      (nhds (D + 0)) :=
    tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop)
  have hQstar_dist : expectedDist Qstar d ≤ D := by
    have hle : rdDistFn d fstar ≤ D + 0 :=
      le_of_tendsto_of_tendsto hdist_tend hrhs_tend (Filter.Eventually.of_forall fun k => hQ_dist (φ k))
    simpa [Qstar, probDistOfRdSimplex, rdDistFn, expectedDist] using hle
  exact ⟨Qstar, probDistOfRdSimplex_fst hfstar, hQstar_dist⟩

/-- **Operational Rate–Distortion Converse**: every operationally achievable rate `R`
    at distortion level `D` satisfies `rateDistortion P d D ≤ R`. -/
theorem rateDistortion_operational_converse (P : ProbDist α) (d : Distortion α β) {D R : ℝ}
    (hach : IsRateDistortionAchievable P d D R) :
    rateDistortion P d D ≤ R := by
  have hfeas : ∃ Q : ProbDist (α × β), Q.fst = P ∧ expectedDist Q d ≤ D :=
    feasible_of_isRateDistortionAchievable hach
  have hR_nonneg : 0 ≤ R := hach.1
  have hle_plus : ∀ δ > 0, rateDistortion P d (D + δ) ≤ R := by
    intro δ hδ
    obtain ⟨N, hN_pos, hN⟩ := hach.2 δ hδ
    let M := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((N : ℝ) * R)))
    obtain ⟨enc, dec, hcode⟩ := hN N le_rfl
    have hM_pos : 0 < M := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
    have hconv : rateDistortion P d (D + δ) ≤ log2 (M : ℝ) / (N : ℝ) :=
      rateDistortion_converse P d hN_pos hM_pos enc dec hcode
    have hpow_ge_one : (1 : ℝ) ≤ (2 : ℝ) ^ ((N : ℝ) * R) :=
      Real.one_le_rpow (by norm_num) (mul_nonneg (Nat.cast_nonneg N) hR_nonneg)
    have hM_le_pow : (M : ℝ) ≤ (2 : ℝ) ^ ((N : ℝ) * R) := by
      have hfloor_ge : 1 ≤ Nat.floor ((2 : ℝ) ^ ((N : ℝ) * R)) :=
        Nat.le_floor (by exact_mod_cast hpow_ge_one)
      have hM_eq : M = Nat.floor ((2 : ℝ) ^ ((N : ℝ) * R)) := Nat.max_eq_right hfloor_ge
      rw [hM_eq]
      exact Nat.floor_le (le_trans zero_le_one hpow_ge_one)
    have hM_pos_r : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM_pos
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogM_le : log2 (M : ℝ) ≤ (N : ℝ) * R := by
      unfold log2
      rw [div_le_iff₀ hlog2_pos]
      calc Real.log (M : ℝ)
        _ ≤ Real.log ((2 : ℝ) ^ ((N : ℝ) * R)) := Real.log_le_log hM_pos_r hM_le_pow
        _ = ((N : ℝ) * R) * Real.log 2 := Real.log_rpow (by norm_num : (0 : ℝ) < 2) _
    have hN_pos_r : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN_pos
    have hdiv_le : log2 (M : ℝ) / (N : ℝ) ≤ R := by
      rw [div_le_iff₀ hN_pos_r]
      linarith
    exact le_trans hconv hdiv_le
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨δ, hδ, hrc⟩ := rateDistortion_rightContinuous P d hfeas ε hε
  have hR_ge := hle_plus δ hδ
  linarith

/-- **Operational Rate–Distortion Achievability**: for any feasible distortion `D`,
    every rate `R > rateDistortion P d D` is operationally achievable. -/
theorem rateDistortion_operational_achievability (P : ProbDist α) (d : Distortion α β) {D R : ℝ}
    (hfeas : ∃ Q : ProbDist (α × β), Q.fst = P ∧ expectedDist Q d ≤ D)
    (hR : rateDistortion P d D < R) :
    IsRateDistortionAchievable P d D R := by
  refine ⟨le_of_lt (lt_of_le_of_lt (rateDistortion_nonneg P d D) hR), fun δ hδ => ?_⟩
  obtain ⟨N, hN⟩ := rateDistortion_achievability P d hfeas hR hδ
  exact ⟨max N 1, lt_of_lt_of_le Nat.zero_lt_one (le_max_right N 1),
    fun n hn => hN n (le_trans (le_max_left N 1) hn)⟩

/-- **Shannon's Rate–Distortion Theorem** (Cover & Thomas, Theorem 10.2.1):
    for any discrete memoryless source `P : ProbDist α`, distortion measure `d : Distortion α β`,
    and feasible distortion level `D`, the operational rate–distortion function equals the
    information-theoretic rate–distortion function:
    `operationalRateDistortion P d D = rateDistortion P d D`. -/
theorem shannon_rate_distortion_theorem (P : ProbDist α) (d : Distortion α β) {D : ℝ}
    (hfeas : ∃ Q : ProbDist (α × β), Q.fst = P ∧ expectedDist Q d ≤ D) :
    operationalRateDistortion P d D = rateDistortion P d D := by
  unfold operationalRateDistortion
  have hbdd : BddBelow { R : ℝ | IsRateDistortionAchievable P d D R } :=
    ⟨0, fun _ hR => hR.1⟩
  have hne : { R : ℝ | IsRateDistortionAchievable P d D R }.Nonempty :=
    ⟨rateDistortion P d D + 1,
      rateDistortion_operational_achievability P d hfeas (by linarith)⟩
  refine le_antisymm ?_ ?_
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    exact csInf_le hbdd (rateDistortion_operational_achievability P d hfeas (by linarith))
  · exact le_csInf hne fun R hR => rateDistortion_operational_converse P d hR

end OperationalRateDistortion

end InfoTheory.Bridge
