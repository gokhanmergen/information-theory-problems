import InfoTheory.Known.Entropy
import InfoTheory.Known.Channels
import InfoTheory.Bridge

/-!
# Binary symmetric Markov source: block law and the Shannon lower bound

Salvaged from the dropped draft entry `binary-markov-source-rate-distortion` (expert review,
2026-11-26: R(D) of this source is already known to be computable via Jalali–Weissman 2007
convergent bounds, so the draft's open-problem framing was not kept). The proved facts are kept as
known results:

* the stationary binary symmetric Markov source (switching probability `q`) as a block law
  `bsmsBlock`, with uniform first marginal and `H(Xⁿ⁺¹) = 1 + n·h(q)` (`entropy_bsmsBlock`);
* its rate–distortion function `bsmsRateDistortion` (inf over blocks of `R_n(D)/n`, Core
  `rateDistortion`, block-averaged Hamming distortion), which is genuine (`rdSet_bddBelow`),
  lies in `[0, 1]`, and vanishes for `D ≥ 1/2`;
* **the Shannon lower bound** `R(D) ≥ h(q) − h(D)` for `0 ≤ D ≤ 1/2` (`shannon_lower_bound`;
  Gray 1970/71, Berger 1971 §4.3), tight below Gray's critical distortion `D_c(q)`
  (`criticalDistortion`, with `0 < D_c < 1/2`).
-/

open scoped BigOperators

namespace InfoTheory.Known.MarkovSource

open InfoTheory InfoTheory.Bridge

/-!
# Rate–distortion function of the binary symmetric Markov source beyond Gray's critical
# distortion

**Source.** The binary symmetric Markov source `BSMS(q)` is the stationary binary Markov chain
with `P(X_1 = 0) = 1/2` and `P(X_{t+1} ≠ X_t | X_t) = q`. Its block law is
`P(x^n) = (1/2) ∏_{t=1}^{n-1} (q if x_{t+1} ≠ x_t else 1 - q)`. Since the chain is
reversible, the block law can be built by *prepending* symbols:
`P(x_0, x_1, …, x_n) = P(x_1, …, x_n) · (q if x_0 ≠ x_1 else 1 - q)`, which is how
`bsmsPmf` is defined below.

**Distortion.** Per-letter Hamming distortion, averaged over the block:
`d_n(x^n, x̂^n) = (1/n) #{i : x_i ≠ x̂_i}`.

**Rate–distortion function.** `R_n(D) = min { I(X^n; X̂^n) : E d_n(X^n, X̂^n) ≤ D }` is the
`n`-block rate–distortion function (Core `rateDistortion` applied to the block source; it is
*not* normalised). For a stationary source the sequence `n ↦ R_n(D)` is subadditive
(`R_{n+m}(D) ≤ R_n(D) + R_m(D)`: concatenate optimal test channels and use stationarity), so by
Fekete's lemma the operational rate–distortion function
`R(D) = lim_n R_n(D)/n = inf_{n ≥ 1} R_n(D)/n` (Gallager 1968, Ch. 9; Berger 1971, Ch. 6;
Gray 1990). We define `R(D)` as this infimum: a genuine infimum over a nonempty
set bounded below by `0` (for `D ≥ 0`), not a supremum over blocklengths.

**Known.** For `0 < q < 1/2`, Gray (1970/1971) showed `R(D) = h(q) - h(D)` (the Shannon lower
bound) for `0 ≤ D ≤ D_c(q) = (1 - √(1 - (q/(1-q))²))/2`; `D_c` is the exact critical
distortion (Avram–Berger 1985). For `D_c < D < 1/2` the value of `R(D)` is unknown; only
upper and lower bounds are available (Berger 1977; Jalali–Weissman 2007, whose bounds
`r_k R_k(D) ≤ R(D) ≤ r_k R_k(D) + H(X_1^k | X_0)/(k+1)` determine `R(D)` numerically to any
precision but give no closed form).
-/

/-- Block probability of the binary symmetric Markov source with switching probability `q`. -/
noncomputable def bsmsPmf (q : ℝ) : (n : ℕ) → (Fin n → Bool) → ℝ
  | 0, _ => 1
  | 1, _ => 1 / 2
  | n + 2, x => bsmsPmf q (n + 1) (Fin.tail x) * (if x 0 = x 1 then 1 - q else q)

lemma bsmsPmf_nonneg {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    ∀ (n : ℕ) (x : Fin n → Bool), 0 ≤ bsmsPmf q n x
  | 0, _ => by simp [bsmsPmf]
  | 1, _ => by simp [bsmsPmf]
  | n + 2, x => by
      simp only [bsmsPmf]
      refine mul_nonneg (bsmsPmf_nonneg h0 h1 (n + 1) _) ?_
      split_ifs <;> linarith

lemma sum_fin_succ_pi {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) :
    ∑ y : Fin (n + 1) → Bool, f y = ∑ b : Bool, ∑ t : Fin n → Bool, f (Fin.cons b t) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => Bool) _ _ (fun _ => rfl)).symm

lemma bsmsPmf_sum (q : ℝ) : ∀ n : ℕ, ∑ x : Fin n → Bool, bsmsPmf q n x = 1
  | 0 => by simp [bsmsPmf]
  | 1 => by simp [bsmsPmf]
  | n + 2 => by
      rw [sum_fin_succ_pi, Finset.sum_comm]
      simp only [bsmsPmf, Fin.tail_cons, Fin.cons_zero, Fin.cons_one]
      simp_rw [← Finset.mul_sum]
      have h : ∀ t : Fin (n + 1) → Bool,
          (∑ b : Bool, if b = t 0 then 1 - q else q) = 1 := by
        intro t; cases t 0 <;> simp
      simp_rw [h, mul_one]
      exact bsmsPmf_sum q (n + 1)

/-- The `n`-block law of `BSMS(q)` as a `ProbDist` on `{0,1}^n`. -/
noncomputable def bsmsBlock (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (n : ℕ) :
    ProbDist (Fin n → Bool) where
  pmf := bsmsPmf q n
  nonneg := bsmsPmf_nonneg h0 h1 n
  sum_one := bsmsPmf_sum q n

/-- Block-averaged Hamming distortion `d_n(x, x̂) = (1/n) #{i : x_i ≠ x̂_i}`. -/
noncomputable def hammingAvg (n : ℕ) : Distortion (Fin n → Bool) (Fin n → Bool) where
  dist := fun x y => ((Finset.univ.filter fun i => x i ≠ y i).card : ℝ) / (n : ℝ)
  nonneg := fun _ _ => by positivity

/-- Rate–distortion function (bits/symbol) of `BSMS(q)` under Hamming distortion,
    `R(D) = inf_{n ≥ 1} R_n(D)/n` (`= lim_n R_n(D)/n` by subadditivity). -/
noncomputable def bsmsRateDistortion (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (D : ℝ) : ℝ :=
  sInf { r : ℝ | ∃ n : ℕ, 0 < n ∧
    r = rateDistortion (bsmsBlock q h0 h1 n) (hammingAvg n) D / (n : ℝ) }

/-- Gray's critical distortion `D_c(q) = (1 - √(1 - (q/(1-q))²))/2` (for `0 < q < 1/2`). -/
noncomputable def criticalDistortion (q : ℝ) : ℝ :=
  (1 - Real.sqrt (1 - (q / (1 - q)) ^ 2)) / 2

variable {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1)

/-! ### Sanity checks on the source -/

theorem bsmsBlock_one_pmf (x : Fin 1 → Bool) : (bsmsBlock q h0 h1 1).pmf x = 1 / 2 := rfl

theorem bsmsBlock_two_pmf (x : Fin 2 → Bool) :
    (bsmsBlock q h0 h1 2).pmf x = 1 / 2 * (if x 0 = x 1 then 1 - q else q) := rfl

/-- Entropy of one transition row: `∑_b -T(b|a) log T(b|a) = h(q)`. -/
lemma row_entropy (a : Bool) :
    ∑ b : Bool, negPLogP (if b = a then 1 - q else q) = binaryEntropy q := by
  cases a <;> simp [binaryEntropy, add_comm]

lemma row_sum (a : Bool) : ∑ b : Bool, (if b = a then 1 - q else q) = 1 := by
  cases a <;> simp

/-- `H(X^{n+1}) = 1 + n·h(q)`. -/
theorem entropy_bsmsBlock : ∀ n : ℕ,
    shannonEntropy (bsmsBlock q h0 h1 (n + 1)) = 1 + n * binaryEntropy q
  | 0 => by
      simp only [shannonEntropy, bsmsBlock, bsmsPmf, Finset.sum_const, Finset.card_univ,
        Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, CharP.cast_eq_zero, zero_mul,
        add_zero]
      have : negPLogP (1 / 2 : ℝ) = 1 / 2 := by
        have hb := Known.binaryEntropy_half
        rw [binaryEntropy, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at hb
        linarith
      rw [this]; norm_num
  | n + 1 => by
      have ih := entropy_bsmsBlock n
      simp only [shannonEntropy, bsmsBlock] at ih ⊢
      rw [sum_fin_succ_pi, Finset.sum_comm]
      simp only [bsmsPmf, Fin.tail_cons, Fin.cons_zero, Fin.cons_one]
      have hstep : ∀ t : Fin (n + 1) → Bool,
          ∑ b : Bool, negPLogP (bsmsPmf q (n + 1) t * (if b = t 0 then 1 - q else q)) =
            negPLogP (bsmsPmf q (n + 1) t) + bsmsPmf q (n + 1) t * binaryEntropy q := by
        intro t
        have hP := bsmsPmf_nonneg h0 h1 (n + 1) t
        have hT : ∀ b : Bool, 0 ≤ (if b = t 0 then 1 - q else q) := fun b => by
          split_ifs <;> linarith
        simp_rw [negPLogP_mul hP (hT _), Finset.sum_add_distrib, ← Finset.mul_sum,
          ← Finset.sum_mul, row_entropy, row_sum, one_mul]
        ring
      simp_rw [hstep, Finset.sum_add_distrib, ← Finset.sum_mul, bsmsPmf_sum, ih]
      push_cast; ring

/-! ### The infimum defining `R(D)` is genuine -/

/-- The set whose infimum is `R(D)`. -/
def rdSet (D : ℝ) : Set ℝ :=
  { r : ℝ | ∃ n : ℕ, 0 < n ∧
    r = rateDistortion (bsmsBlock q h0 h1 n) (hammingAvg n) D / (n : ℝ) }

lemma bsmsRateDistortion_eq (D : ℝ) : bsmsRateDistortion q h0 h1 D = sInf (rdSet h0 h1 D) := rfl

theorem rdSet_nonempty (D : ℝ) : (rdSet h0 h1 D).Nonempty := ⟨_, 1, one_pos, rfl⟩

lemma rdSet_nonneg {D r : ℝ} (hr : r ∈ rdSet h0 h1 D) : 0 ≤ r := by
  obtain ⟨n, _, rfl⟩ := hr
  exact div_nonneg (rateDistortion_nonneg _ _ _) (Nat.cast_nonneg n)

theorem rdSet_bddBelow (D : ℝ) : BddBelow (rdSet h0 h1 D) :=
  ⟨0, fun _ hr => rdSet_nonneg h0 h1 hr⟩

theorem rateDistortion_le_block (D : ℝ) {n : ℕ} (hn : 0 < n) :
    bsmsRateDistortion q h0 h1 D ≤
      rateDistortion (bsmsBlock q h0 h1 n) (hammingAvg n) D / (n : ℝ) :=
  csInf_le (rdSet_bddBelow h0 h1 D) ⟨n, hn, rfl⟩

theorem rateDistortion_nonneg' (D : ℝ) : 0 ≤ bsmsRateDistortion q h0 h1 D :=
  le_csInf (rdSet_nonempty h0 h1 D) (fun _ hr => rdSet_nonneg h0 h1 hr)

/-- `R(D) ≤ R_1(D) ≤ H(X_1) = 1` for `D ≥ 0`. -/
theorem rateDistortion_le_one {D : ℝ} (hD : 0 ≤ D) : bsmsRateDistortion q h0 h1 D ≤ 1 := by
  refine (rateDistortion_le_block h0 h1 D one_pos).trans ?_
  rw [Nat.cast_one, div_one]
  refine (rateDistortion_le_shannonEntropy _ _ (fun x => ⟨x, ?_⟩)).trans ?_
  · simp [hammingAvg, hD]
  · have h := entropy_bsmsBlock h0 h1 0
    simp only [CharP.cast_eq_zero, zero_mul, add_zero] at h
    exact h.le

/-- `R(D) = 0` for `D ≥ 1/2` (reproduce the constant `0`; distortion `1/2`). -/
theorem rateDistortion_eq_zero_of_half_le {D : ℝ} (hD : 1 / 2 ≤ D) :
    bsmsRateDistortion q h0 h1 D = 0 := by
  refine le_antisymm ?_ (rateDistortion_nonneg' h0 h1 D)
  refine (rateDistortion_le_block h0 h1 D one_pos).trans (le_of_eq ?_)
  rw [rateDistortion_eq_zero_of_const]
  · simp
  · refine ⟨fun _ => false, ?_⟩
    refine (le_of_eq (sum_fin_succ_pi (n := 0) (fun x : Fin 1 → Bool =>
      (bsmsBlock q h0 h1 1).pmf x * (hammingAvg 1).dist x fun _ => false))).trans ?_
    have hcard : ∀ b : Bool, ∀ t : Fin 0 → Bool,
        ((Finset.univ.filter fun i : Fin 1 => (Fin.cons b t : Fin 1 → Bool) i ≠ false).card : ℝ)
          = if b then 1 else 0 := by
      intro b t
      rw [Finset.univ_unique, Finset.filter_singleton]
      cases b <;> simp
    simp only [bsmsBlock, bsmsPmf, hammingAvg, hcard]
    simp
    linarith

/-! ### The Shannon lower bound `R(D) ≥ h(q) - h(D)` -/

section SLB

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Expectations under a push-forward. -/
lemma sum_map_mul (f : α → β) (P : ProbDist α) (g : β → ℝ) :
    ∑ b : β, (P.map f).pmf b * g b = ∑ a : α, P.pmf a * g (f a) := by
  classical
  simp only [ProbDist.map]
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_ite_eq]
  simp

/-- The diagonal coupling `X̂ = X` has first marginal `P`. -/
lemma map_diag_fst (P : ProbDist α) : (P.map (fun x => (x, x))).fst = P := by
  classical
  unfold ProbDist.fst ProbDist.map
  congr; funext x; dsimp only
  rw [Finset.sum_comm, Finset.sum_eq_single x]
  · rw [Finset.sum_eq_single x]
    · simp
    · intro b _ hne; simp [hne.symm]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · intro x' _ hne
    exact Finset.sum_eq_zero fun b _ => by simp [hne]
  · intro h'; exact absurd (Finset.mem_univ _) h'

end SLB

/-- The diagonal coupling has zero block Hamming distortion. -/
lemma map_diag_dist (n : ℕ) (P : ProbDist (Fin n → Bool)) :
    ∑ xy, (P.map (fun x => (x, x))).pmf xy * (hammingAvg n).dist xy.1 xy.2 = 0 := by
  rw [sum_map_mul]
  simp [hammingAvg]

lemma binaryEntropy_le_of_le {p D : ℝ} (hp0 : 0 ≤ p) (hpD : p ≤ D) (hD : D ≤ 1 / 2) :
    binaryEntropy p ≤ binaryEntropy D := by
  have hD0 : 0 ≤ D := hp0.trans hpD
  rw [Known.binaryEntropy_eq_binEntropy hp0 (by linarith),
    Known.binaryEntropy_eq_binEntropy hD0 (by linarith)]
  refine div_le_div_of_nonneg_right ?_ (Real.log_pos one_lt_two).le
  exact Real.binEntropy_strictMonoOn.monotoneOn ⟨hp0, by norm_num; linarith⟩
    ⟨hD0, by norm_num; linarith⟩ hpD

/-- Jensen for binary entropy: `∑_i h(p_i) ≤ n · h((1/n) ∑_i p_i)`. -/
lemma sum_binaryEntropy_le {n : ℕ} (hn : 0 < n) (p : Fin n → ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∀ i, p i ≤ 1) :
    ∑ i, binaryEntropy (p i) ≤ n * binaryEntropy ((1 / n) * ∑ i, p i) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hJ := Real.strictConcave_binEntropy.concaveOn.le_map_sum (t := Finset.univ)
    (w := fun _ => (1 / n : ℝ)) (p := p) (fun _ _ => by positivity)
    (by simp; field_simp) (fun i _ => ⟨hp0 i, hp1 i⟩)
  simp only [smul_eq_mul, ← Finset.mul_sum] at hJ
  have havg0 : 0 ≤ (1 / n : ℝ) * ∑ i, p i :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => hp0 i)
  have havg1 : (1 / n : ℝ) * ∑ i, p i ≤ 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_one hnR]
    calc ∑ i, p i ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => hp1 i
      _ = n := by simp
  rw [Known.binaryEntropy_eq_binEntropy havg0 havg1]
  simp_rw [Known.binaryEntropy_eq_binEntropy (hp0 _) (hp1 _)]
  rw [← Finset.sum_div, mul_div_assoc']
  refine div_le_div_of_nonneg_right ?_ (Real.log_pos one_lt_two).le
  have := mul_le_mul_of_nonneg_left hJ hnR.le
  rw [← mul_assoc, mul_one_div_cancel hnR.ne', one_mul] at this
  exact this

/-- Blockwise Shannon lower bound: any test channel with expected block Hamming distortion
    `≤ D ≤ 1/2` has `I(X^n; X̂^n) ≥ 1 + (n-1) h(q) - n h(D)`. -/
theorem mutualInfo_ge_block {n : ℕ} (hn : 0 < n) {D : ℝ} (_hD0 : 0 ≤ D) (hD : D ≤ 1 / 2)
    (Q : ProbDist ((Fin n → Bool) × (Fin n → Bool))) (hfst : Q.fst = bsmsBlock q h0 h1 n)
    (hdist : ∑ xy, Q.pmf xy * (hammingAvg n).dist xy.1 xy.2 ≤ D) :
    1 + ((n : ℝ) - 1) * binaryEntropy q - n * binaryEntropy D ≤ mutualInfo Q := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  -- per-coordinate joint laws of `(X_i, X̂_i)`
  let Pi : Fin n → ProbDist (Bool × Bool) := fun i =>
    (Q.map (fun xy => (xy.1 i, xy.2))).map (Prod.map id (fun xh => xh i))
  let pe : Fin n → ℝ := fun i => estErrorProb (Pi i) id
  have hpe0 : ∀ i, 0 ≤ pe i := fun i => estErrorProb_nonneg _ _
  have hpe1 : ∀ i, pe i ≤ 1 := fun i => estErrorProb_le_one _ _
  -- H(X^n | X̂^n) ≤ ∑ h(pe_i)
  have hcond : condEntropy Q ≤ ∑ i, binaryEntropy (pe i) := by
    refine (condEntropy_pi_le_sum n Q).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (condEntropy_le_map_right _ (fun xh : Fin n → Bool => xh i)).trans ?_
    have hF := fano_inequality (Pi i) id (by simp)
    have hl : log2 ((Fintype.card Bool : ℝ) - 1) = 0 := by
      simp [log2]; norm_num
    rw [hl, mul_zero, add_zero] at hF
    exact hF
  -- ∑ pe_i = n · E d_n
  have hsum_pe : ∑ i, pe i = n * ∑ xy, Q.pmf xy * (hammingAvg n).dist xy.1 xy.2 := by
    have hpe : ∀ i, pe i = ∑ xy, Q.pmf xy * (if xy.1 i ≠ xy.2 i then 1 else 0) := by
      intro i
      have h1 : pe i = ∑ ab : Bool × Bool, (Pi i).pmf ab * (if ab.2 ≠ ab.1 then 1 else 0) := by
        simp only [pe, estErrorProb, id, mul_ite, mul_one, mul_zero]
        refine Finset.sum_congr rfl fun ab _ => ?_
        by_cases h : ab.2 = ab.1 <;> simp [h]
      rw [h1, sum_map_mul, sum_map_mul]
      refine Finset.sum_congr rfl fun xy _ => ?_
      simp only [Prod.map, id]
      congr 1
      by_cases h : xy.1 i = xy.2 i <;> simp [h, eq_comm]
    simp_rw [hpe]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun xy _ => ?_
    rw [← Finset.mul_sum]
    simp only [hammingAvg]
    rw [Finset.card_filter]
    push_cast
    field_simp
  have havg : (1 / n : ℝ) * ∑ i, pe i ≤ D := by
    rw [hsum_pe, ← mul_assoc, one_div_mul_cancel hnR.ne', one_mul]; exact hdist
  have hJ := sum_binaryEntropy_le hn pe hpe0 hpe1
  have hmono := binaryEntropy_le_of_le
    (mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => hpe0 i)) havg hD
  -- H(X^n)
  have hH : shannonEntropy Q.fst = 1 + ((n : ℝ) - 1) * binaryEntropy q := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [hfst, entropy_bsmsBlock]; push_cast; ring
  have hI : mutualInfo Q = shannonEntropy Q.fst - condEntropy Q := by
    unfold mutualInfo condEntropy; ring
  rw [hI, hH]
  nlinarith [mul_le_mul_of_nonneg_left hmono hnR.le]

/-- **Shannon lower bound** for the binary symmetric Markov source:
    `R(D) ≥ h(q) - h(D)` for `0 ≤ D ≤ 1/2` (Gray 1970, 1971). -/
theorem shannon_lower_bound {D : ℝ} (hD0 : 0 ≤ D) (hD : D ≤ 1 / 2) :
    binaryEntropy q - binaryEntropy D ≤ bsmsRateDistortion q h0 h1 D := by
  refine le_csInf (rdSet_nonempty h0 h1 D) ?_
  rintro r ⟨n, hn, rfl⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [le_div_iff₀ hnR]
  unfold rateDistortion
  refine le_csInf ⟨_, (bsmsBlock q h0 h1 n).map (fun x => (x, x)), map_diag_fst _,
    (map_diag_dist n _).le.trans hD0, rfl⟩ ?_
  · rintro r ⟨Q, hfst, hdist, rfl⟩
    have := mutualInfo_ge_block h0 h1 hn hD0 hD Q hfst hdist
    have hq1 : binaryEntropy q ≤ 1 := Known.binaryEntropy_le_one h0 h1
    nlinarith

/-! ### The interval `(D_c, 1/2)` is nonempty -/

theorem criticalDistortion_pos {q : ℝ} (hq0 : 0 < q) (hq : q < 1 / 2) :
    0 < criticalDistortion q := by
  unfold criticalDistortion
  have hr0 : 0 < q / (1 - q) := div_pos hq0 (by linarith)
  have hr1 : q / (1 - q) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have hs : Real.sqrt (1 - (q / (1 - q)) ^ 2) < 1 := by
    rw [Real.sqrt_lt' one_pos]; nlinarith
  linarith

theorem criticalDistortion_lt_half {q : ℝ} (hq0 : 0 < q) (hq : q < 1 / 2) :
    criticalDistortion q < 1 / 2 := by
  unfold criticalDistortion
  have hr0 : 0 < q / (1 - q) := div_pos hq0 (by linarith)
  have hr1 : q / (1 - q) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have hs : 0 < Real.sqrt (1 - (q / (1 - q)) ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  linarith

end InfoTheory.Known.MarkovSource
