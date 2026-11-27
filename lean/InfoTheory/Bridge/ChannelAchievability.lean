import InfoTheory.Bridge.ChannelCoding

/-!
# Shannon's Channel Coding Theorem (Cover & Thomas, Theorem 7.7.1)

Purely additive, kernel-verified formalization of Shannon's Channel Coding Theorem for
Discrete Memoryless Channels (DMCs) via random coding and joint typicality decoding,
built entirely with finite sums on top of `InfoTheory.Bridge.ChannelCoding`:

1. **Joint-Typicality Decoder & Random-Codebook Ensemble (Cover & Thomas §7.7)**:
   - `jointTypicalDec` (unique joint-typicality decoder)
   - `codebookProb`, `codebookProb_nonneg`, `codebookProb_sum_one` (i.i.d. random codebook law)

2. **Random-Coding Average Error Bound (Cover & Thomas §7.7)**:
   - `dmc_random_coding_expected_error_le` (exact finite-sum ensemble error bound
     `E[P_e] ≤ (1 - P^n(A_ε^(n))) + (M - 1) · (P_X^n × P_Y^n)(A_ε^(n))`)
   - `dmc_random_coding_bound` (existence of a deterministic `(n, M)` codebook attaining the bound
     `P_e ≤ (1 - P^n(A_ε^(n))) + (M - 1) · 2^(-n (I(X; Y) - 3ε))`)
   - `dmc_achievable_lt_mutualInfo` (vanishing average error for every rate `0 ≤ R < I(X; Y)`)

3. **Shannon's Channel Coding Theorem (Achievability + Converse)**:
   - `IsDmcAchievableRate`, `dmcOperationalCapacity`, `isDmcAchievableRate_zero`
   - `shannon_channel_coding_achievability` (`0 ≤ R < C(W) → IsDmcAchievableRate W R`)
   - `shannon_channel_coding_converse` (`IsDmcAchievableRate W R → R ≤ C(W)`,
     via `dmcAvgError_rate_converse`)
   - `shannon_channel_coding_theorem` (`dmcOperationalCapacity W = W.capacity`)

All theorems leave `Core/`, `Problems/`, `Bridge/ChannelCoding.lean`, `Bridge/CoverThomas.lean`,
`Bridge/Mathlib.lean`, `STATEMENT_LOCK.json`, and `Known/` untouched.
-/

open scoped BigOperators
open InfoTheory InfoTheory.Bridge

namespace InfoTheory.Bridge

/-! ### 1. Joint-Typicality Decoder and Random-Codebook Ensemble -/

section RandomCoding

variable {α β : Type*} [Fintype α] [Fintype β]

/-- **Joint-Typicality Decoder** (Cover & Thomas, §7.7):
    given a codebook `enc : Fin M → Fin n → α` (`0 < M`) and channel output `y : Fin n → β`,
    outputs the unique message `m : Fin M` such that `(enc m, y) ∈ A_ε^(n)(P)` if one exists,
    and otherwise declares an error by outputting `⟨0, hM⟩`. -/
noncomputable def jointTypicalDec (P : ProbDist (α × β)) (n M : ℕ) (hM : 0 < M) (ε : ℝ)
    (enc : Fin M → Fin n → α) (y : Fin n → β) : Fin M := by
  classical
  exact if h : ∃! m : Fin M, (enc m, y) ∈ jointTypicalSet P n ε then
    Classical.choose h
  else
    ⟨0, hM⟩

private lemma jointTypicalDec_eq_of_unique (P : ProbDist (α × β)) (n M : ℕ) (hM : 0 < M) (ε : ℝ)
    (enc : Fin M → Fin n → α) (y : Fin n → β) (m : Fin M)
    (hm : (enc m, y) ∈ jointTypicalSet P n ε)
    (huniq : ∀ m' : Fin M, m' ≠ m → (enc m', y) ∉ jointTypicalSet P n ε) :
    jointTypicalDec P n M hM ε enc y = m := by
  classical
  have hex : ∃! k : Fin M, (enc k, y) ∈ jointTypicalSet P n ε := by
    refine ⟨m, hm, ?_⟩
    intro k hk
    by_contra hne
    exact huniq k hne hk
  simp only [jointTypicalDec, hex, ↓reduceDIte]
  have hspec := Classical.choose_spec hex
  by_contra hne
  exact huniq (Classical.choose hex) hne hspec.1

private lemma jointTypicalDec_err_indicator_le [DecidableEq α] [DecidableEq β]
    (P : ProbDist (α × β)) (n M : ℕ) (hM : 0 < M) (ε : ℝ)
    (enc : Fin M → Fin n → α) (y : Fin n → β) (m : Fin M) :
    (if jointTypicalDec P n M hM ε enc y ≠ m then (1 : ℝ) else 0) ≤
      (if (enc m, y) ∉ jointTypicalSet P n ε then (1 : ℝ) else 0) +
      ∑ m' ∈ Finset.univ.erase m,
        (if (enc m', y) ∈ jointTypicalSet P n ε then (1 : ℝ) else 0) := by
  have hsum_nonneg :
      (0 : ℝ) ≤ ∑ m' ∈ Finset.univ.erase m,
        (if (enc m', y) ∈ jointTypicalSet P n ε then (1 : ℝ) else 0) :=
    Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  split_ifs with herr hm
  · have hex : ∃ m' : Fin M, m' ≠ m ∧ (enc m', y) ∈ jointTypicalSet P n ε := by
      by_contra hnone
      push Not at hnone
      exact herr (jointTypicalDec_eq_of_unique P n M hM ε enc y m hm hnone)
    obtain ⟨m', hm'_ne, hm'_mem⟩ := hex
    have hmem_erase : m' ∈ Finset.univ.erase m := Finset.mem_erase.mpr ⟨hm'_ne, Finset.mem_univ m'⟩
    have hle : (1 : ℝ) ≤ ∑ k ∈ Finset.univ.erase m,
        (if (enc k, y) ∈ jointTypicalSet P n ε then (1 : ℝ) else 0) := by
      calc (1 : ℝ)
        _ = (if (enc m', y) ∈ jointTypicalSet P n ε then (1 : ℝ) else 0) := by
            simp only [hm'_mem, ↓reduceIte]
        _ ≤ ∑ k ∈ Finset.univ.erase m,
              (if (enc k, y) ∈ jointTypicalSet P n ε then (1 : ℝ) else 0) :=
            Finset.single_le_sum
              (f := fun k => if (enc k, y) ∈ jointTypicalSet P n ε then (1 : ℝ) else 0)
              (fun _ _ => by split_ifs <;> norm_num) hmem_erase
    linarith
  · linarith
  · linarith
  · linarith

/-- The i.i.d. random-codebook probability mass function on codebooks `Fin M → Fin n → α`,
    where each codeword `enc m` is drawn independently from `(iidDist Px n)`. -/
def codebookProb (Px : ProbDist α) (n M : ℕ) (enc : Fin M → Fin n → α) : ℝ :=
  ∏ m : Fin M, (iidDist Px n).pmf (enc m)

lemma codebookProb_nonneg (Px : ProbDist α) (n M : ℕ) (enc : Fin M → Fin n → α) :
    0 ≤ codebookProb Px n M enc :=
  Finset.prod_nonneg fun m _ => (iidDist Px n).nonneg (enc m)

lemma codebookProb_sum_one (Px : ProbDist α) (n M : ℕ) :
    ∑ enc : Fin M → Fin n → α, codebookProb Px n M enc = 1 := by
  unfold codebookProb
  rw [← Fintype.prod_sum]
  exact Finset.prod_eq_one fun _ _ => (iidDist Px n).sum_one

private lemma sum_pi_prod_mul_single {γ : Type*} [Fintype γ] (Q : ProbDist γ)
    (M : ℕ) (m : Fin M) (f : γ → ℝ) :
    ∑ enc : Fin M → γ, (∏ k : Fin M, Q.pmf (enc k)) * f (enc m) =
      ∑ x : γ, Q.pmf x * f x := by
  let F : Fin M → γ → ℝ := fun k x => if k = m then Q.pmf x * f x else Q.pmf x
  have hfun : ∀ enc : Fin M → γ,
      (∏ k : Fin M, Q.pmf (enc k)) * f (enc m) = ∏ k : Fin M, F k (enc k) := by
    intro enc
    rw [← Finset.mul_prod_erase Finset.univ (fun k => Q.pmf (enc k)) (Finset.mem_univ m),
        ← Finset.mul_prod_erase Finset.univ (fun k => F k (enc k)) (Finset.mem_univ m)]
    have hrest : ∏ k ∈ Finset.univ.erase m, F k (enc k) =
        ∏ k ∈ Finset.univ.erase m, Q.pmf (enc k) :=
      Finset.prod_congr rfl fun k hk => by simp [F, (Finset.mem_erase.mp hk).1]
    rw [hrest]
    simp only [F, ↓reduceIte]
    ring
  simp_rw [hfun, ← Fintype.prod_sum F]
  rw [← Finset.mul_prod_erase Finset.univ (fun k => ∑ x : γ, F k x) (Finset.mem_univ m)]
  have hm : ∑ x : γ, F m x = ∑ x : γ, Q.pmf x * f x := by simp [F]
  have hrest : ∏ k ∈ Finset.univ.erase m, ∑ x : γ, F k x = 1 :=
    Finset.prod_eq_one fun k hk => by
      have hne : k ≠ m := (Finset.mem_erase.mp hk).1
      simp only [F, hne, ↓reduceIte]
      exact Q.sum_one
  rw [hm, hrest, mul_one]

private lemma sum_pi_prod_mul_pair {γ : Type*} [Fintype γ] (Q : ProbDist γ)
    (M : ℕ) (m m' : Fin M) (hm' : m' ≠ m) (f g : γ → ℝ) :
    ∑ enc : Fin M → γ, (∏ k : Fin M, Q.pmf (enc k)) * (f (enc m) * g (enc m')) =
      (∑ x : γ, Q.pmf x * f x) * (∑ x' : γ, Q.pmf x' * g x') := by
  let F : Fin M → γ → ℝ := fun k x =>
    if k = m then Q.pmf x * f x
    else if k = m' then Q.pmf x * g x
    else Q.pmf x
  have hm'_mem : m' ∈ Finset.univ.erase m := Finset.mem_erase.mpr ⟨hm', Finset.mem_univ m'⟩
  have hfun : ∀ enc : Fin M → γ,
      (∏ k : Fin M, Q.pmf (enc k)) * (f (enc m) * g (enc m')) = ∏ k : Fin M, F k (enc k) := by
    intro enc
    rw [← Finset.mul_prod_erase Finset.univ (fun k => Q.pmf (enc k)) (Finset.mem_univ m),
        ← Finset.mul_prod_erase (Finset.univ.erase m) (fun k => Q.pmf (enc k)) hm'_mem,
        ← Finset.mul_prod_erase Finset.univ (fun k => F k (enc k)) (Finset.mem_univ m),
        ← Finset.mul_prod_erase (Finset.univ.erase m) (fun k => F k (enc k)) hm'_mem]
    have hrest : ∏ k ∈ (Finset.univ.erase m).erase m', F k (enc k) =
        ∏ k ∈ (Finset.univ.erase m).erase m', Q.pmf (enc k) :=
      Finset.prod_congr rfl fun k hk => by
        have hk1 : k ≠ m' := (Finset.mem_erase.mp hk).1
        have hk2 : k ≠ m := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
        simp [F, hk1, hk2]
    rw [hrest]
    simp only [F, hm', ↓reduceIte]
    ring
  simp_rw [hfun, ← Fintype.prod_sum F]
  rw [← Finset.mul_prod_erase Finset.univ (fun k => ∑ x : γ, F k x) (Finset.mem_univ m),
      ← Finset.mul_prod_erase (Finset.univ.erase m) (fun k => ∑ x : γ, F k x) hm'_mem]
  have hm_sum : ∑ x : γ, F m x = ∑ x : γ, Q.pmf x * f x := by simp [F]
  have hm'_sum : ∑ x : γ, F m' x = ∑ x : γ, Q.pmf x * g x := by simp [F, hm']
  have hrest : ∏ k ∈ (Finset.univ.erase m).erase m', ∑ x : γ, F k x = 1 :=
    Finset.prod_eq_one fun k hk => by
      have hk1 : k ≠ m' := (Finset.mem_erase.mp hk).1
      have hk2 : k ≠ m := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
      simp only [F, hk2, hk1, ↓reduceIte]
      exact Q.sum_one
  rw [hm_sum, hm'_sum, hrest, mul_one]

private lemma jointIidDist_dmc_joint_pmf (W : DMC α β) (Px : ProbDist α) (n : ℕ)
    (x : Fin n → α) (y : Fin n → β) :
    (iidDist Px n).pmf x * (W.power n).trans x y = (jointIidDist (W.joint Px) n).pmf (x, y) := by
  unfold iidDist DMC.power jointIidDist DMC.joint
  dsimp only
  rw [← Finset.prod_mul_distrib]

private lemma exists_le_of_weighted_sum_le {ι : Type*} [Fintype ι]
    (w f : ι → ℝ) (B : ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i : ι, w i = 1)
    (hle : ∑ i : ι, w i * f i ≤ B) :
    ∃ i : ι, f i ≤ B := by
  by_contra hall
  push Not at hall
  have hpos : ∃ i₀ : ι, 0 < w i₀ := by
    by_contra hno
    push Not at hno
    have hzero : ∑ i : ι, w i = 0 :=
      Finset.sum_eq_zero fun i _ => le_antisymm (hno i) (hw0 i)
    linarith
  obtain ⟨i₀, hi₀⟩ := hpos
  have hlt : ∑ i : ι, w i * B < ∑ i : ι, w i * f i :=
    Finset.sum_lt_sum
      (fun i _ => mul_le_mul_of_nonneg_left (le_of_lt (hall i)) (hw0 i))
      ⟨i₀, Finset.mem_univ i₀, mul_lt_mul_of_pos_left (hall i₀) hi₀⟩
  have hB : ∑ i : ι, w i * B = B := by
    rw [← Finset.sum_mul, hw1, one_mul]
  linarith

private lemma dmc_random_coding_first_term [DecidableEq α] [DecidableEq β]
    (W : DMC α β) (Px : ProbDist α) (n M : ℕ) (ε : ℝ) (m : Fin M) :
    let P := W.joint Px
    let A := jointTypicalSet P n ε
    (∑ y : Fin n → β, ∑ enc : Fin M → Fin n → α,
        codebookProb Px n M enc *
          ((W.power n).trans (enc m) y * (if (enc m, y) ∉ A then (1 : ℝ) else 0))) =
      1 - ∑ xy ∈ A, (jointIidDist P n).pmf xy := by
  dsimp only
  let P := W.joint Px
  let A := jointTypicalSet P n ε
  have hinner : ∀ y : Fin n → β,
      (∑ enc : Fin M → Fin n → α,
        codebookProb Px n M enc *
          ((W.power n).trans (enc m) y * (if (enc m, y) ∉ A then (1 : ℝ) else 0))) =
      ∑ x : Fin n → α, if (x, y) ∉ A then (jointIidDist P n).pmf (x, y) else 0 := by
    intro y
    unfold codebookProb
    rw [sum_pi_prod_mul_single (iidDist Px n) M m
      (fun x => (W.power n).trans x y * (if (x, y) ∉ A then (1 : ℝ) else 0))]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← mul_assoc, jointIidDist_dmc_joint_pmf W Px n x y]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun y _ => hinner y]
  have hprod := Fintype.sum_prod_type_right
    (fun xy : (Fin n → α) × (Fin n → β) => if xy ∉ A then (jointIidDist P n).pmf xy else 0)
  rw [← hprod]
  have hsplit : ∑ xy : (Fin n → α) × (Fin n → β), (jointIidDist P n).pmf xy =
      (∑ xy : (Fin n → α) × (Fin n → β), if xy ∈ A then (jointIidDist P n).pmf xy else 0) +
      (∑ xy : (Fin n → α) × (Fin n → β), if xy ∉ A then (jointIidDist P n).pmf xy else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun xy _ => by by_cases h : xy ∈ A <;> simp [h]
  rw [(jointIidDist P n).sum_one] at hsplit
  have hmem : (∑ xy : (Fin n → α) × (Fin n → β),
        if xy ∈ A then (jointIidDist P n).pmf xy else 0) =
      ∑ xy ∈ A, (jointIidDist P n).pmf xy := by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  change (∑ xy : (Fin n → α) × (Fin n → β), if xy ∉ A then (jointIidDist P n).pmf xy else 0) =
    1 - ∑ xy ∈ A, (jointIidDist P n).pmf xy
  linarith

private lemma dmc_random_coding_second_term [DecidableEq α] [DecidableEq β]
    (W : DMC α β) (Px : ProbDist α) (n M : ℕ) (ε : ℝ) (m m' : Fin M) (hne : m' ≠ m) :
    let P := W.joint Px
    let A := jointTypicalSet P n ε
    (∑ y : Fin n → β, ∑ enc : Fin M → Fin n → α,
        codebookProb Px n M enc *
          ((W.power n).trans (enc m) y * (if (enc m', y) ∈ A then (1 : ℝ) else 0))) =
      ∑ xy ∈ A, ((iidDist P.fst n).prod (iidDist P.snd n)).pmf xy := by
  dsimp only
  let P := W.joint Px
  let A := jointTypicalSet P n ε
  have hinner : ∀ y : Fin n → β,
      (∑ enc : Fin M → Fin n → α,
        codebookProb Px n M enc *
          ((W.power n).trans (enc m) y * (if (enc m', y) ∈ A then (1 : ℝ) else 0))) =
      ∑ x' : Fin n → α,
        if (x', y) ∈ A then ((iidDist P.fst n).prod (iidDist P.snd n)).pmf (x', y) else 0 := by
    intro y
    unfold codebookProb
    rw [sum_pi_prod_mul_pair (iidDist Px n) M m m' hne
      (fun x => (W.power n).trans x y)
      (fun x' => if (x', y) ∈ A then (1 : ℝ) else 0)]
    have hy_marg : ∑ x : Fin n → α, (iidDist Px n).pmf x * (W.power n).trans x y =
        (iidDist P.snd n).pmf y := by
      simp_rw [jointIidDist_dmc_joint_pmf W Px n _ y]
      change (jointIidDist P n).snd.pmf y = (iidDist P.snd n).pmf y
      rw [jointIidDist_snd]
    rw [hy_marg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x' _ => ?_
    have hfst : P.fst = Px := dmc_joint_fst W Px
    unfold ProbDist.prod
    dsimp only
    rw [hfst]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun y _ => hinner y]
  have hprod := Fintype.sum_prod_type_right
    (fun xy : (Fin n → α) × (Fin n → β) =>
      if xy ∈ A then ((iidDist P.fst n).prod (iidDist P.snd n)).pmf xy else 0)
  rw [← hprod, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-! ### 2. Random-Coding Average Error Bound (Cover & Thomas §7.7) -/

/-- **Random-Coding Expected Average Error Bound** (Cover & Thomas, §7.7):
    averaging `dmcAvgError` of the joint-typicality decoder over the i.i.d. random codebook
    ensemble `codebookProb Px n M` yields
    `E[P_e] ≤ (1 - P^n(A_ε^(n))) + (M - 1) · (P_X^n × P_Y^n)(A_ε^(n))`,
    where `P = W.joint Px`. -/
theorem dmc_random_coding_expected_error_le [DecidableEq β]
    (W : DMC α β) (Px : ProbDist α) (n M : ℕ) (hM : 0 < M) (ε : ℝ) :
    let P := W.joint Px
    ∑ enc : Fin M → Fin n → α,
      codebookProb Px n M enc * dmcAvgError W n M enc (jointTypicalDec P n M hM ε enc) ≤
        (1 - ∑ xy ∈ jointTypicalSet P n ε, (jointIidDist P n).pmf xy) +
        ((M - 1 : ℕ) : ℝ) *
          (∑ xy ∈ jointTypicalSet P n ε, ((iidDist P.fst n).prod (iidDist P.snd n)).pmf xy) := by
  classical
  dsimp only
  let P := W.joint Px
  let A := jointTypicalSet P n ε
  have hMne : M ≠ 0 := Nat.ne_of_gt hM
  have hMpos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  have hterm_m : ∀ m : Fin M,
      ∑ enc : Fin M → Fin n → α,
        codebookProb Px n M enc *
          (∑ y : Fin n → β,
            if jointTypicalDec P n M hM ε enc y ≠ m then (W.power n).trans (enc m) y else 0) ≤
        (1 - ∑ xy ∈ A, (jointIidDist P n).pmf xy) +
        ((M - 1 : ℕ) : ℝ) *
          (∑ xy ∈ A, ((iidDist P.fst n).prod (iidDist P.snd n)).pmf xy) := by
    intro m
    have hstep1 :
        ∑ enc : Fin M → Fin n → α,
          codebookProb Px n M enc *
            (∑ y : Fin n → β,
              if jointTypicalDec P n M hM ε enc y ≠ m then (W.power n).trans (enc m) y else 0) ≤
        (∑ y : Fin n → β, ∑ enc : Fin M → Fin n → α,
            codebookProb Px n M enc *
              ((W.power n).trans (enc m) y * (if (enc m, y) ∉ A then (1 : ℝ) else 0))) +
        ∑ m' ∈ Finset.univ.erase m,
          ∑ y : Fin n → β, ∑ enc : Fin M → Fin n → α,
            codebookProb Px n M enc *
              ((W.power n).trans (enc m) y * (if (enc m', y) ∈ A then (1 : ℝ) else 0)) := by
      have hpoint : ∀ enc : Fin M → Fin n → α,
          codebookProb Px n M enc *
            (∑ y : Fin n → β,
              if jointTypicalDec P n M hM ε enc y ≠ m then (W.power n).trans (enc m) y else 0) ≤
          (∑ y : Fin n → β,
            codebookProb Px n M enc *
              ((W.power n).trans (enc m) y * (if (enc m, y) ∉ A then (1 : ℝ) else 0))) +
          ∑ m' ∈ Finset.univ.erase m,
            ∑ y : Fin n → β,
              codebookProb Px n M enc *
                ((W.power n).trans (enc m) y * (if (enc m', y) ∈ A then (1 : ℝ) else 0)) := by
        intro enc
        rw [Finset.mul_sum]
        have hswap :
            (∑ m' ∈ Finset.univ.erase m, ∑ y : Fin n → β,
                codebookProb Px n M enc *
                  ((W.power n).trans (enc m) y * (if (enc m', y) ∈ A then (1 : ℝ) else 0))) =
            ∑ y : Fin n → β, ∑ m' ∈ Finset.univ.erase m,
                codebookProb Px n M enc *
                  ((W.power n).trans (enc m) y * (if (enc m', y) ∈ A then (1 : ℝ) else 0)) :=
          Finset.sum_comm
        rw [hswap, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun y _ => ?_
        have hind := jointTypicalDec_err_indicator_le P n M hM ε enc y m
        have hcoeff : 0 ≤ codebookProb Px n M enc * (W.power n).trans (enc m) y :=
          mul_nonneg (codebookProb_nonneg Px n M enc) ((W.power n).nonneg (enc m) y)
        have hmul := mul_le_mul_of_nonneg_left hind hcoeff
        have hlhs : codebookProb Px n M enc *
              (if jointTypicalDec P n M hM ε enc y ≠ m then (W.power n).trans (enc m) y else 0) =
            (codebookProb Px n M enc * (W.power n).trans (enc m) y) *
              (if jointTypicalDec P n M hM ε enc y ≠ m then (1 : ℝ) else 0) := by
          split_ifs <;> ring
        have hrhs : (codebookProb Px n M enc * (W.power n).trans (enc m) y) *
              ((if (enc m, y) ∉ A then (1 : ℝ) else 0) +
                ∑ m' ∈ Finset.univ.erase m, (if (enc m', y) ∈ A then (1 : ℝ) else 0)) =
            codebookProb Px n M enc *
              ((W.power n).trans (enc m) y * (if (enc m, y) ∉ A then (1 : ℝ) else 0)) +
            ∑ m' ∈ Finset.univ.erase m,
              codebookProb Px n M enc *
                ((W.power n).trans (enc m) y * (if (enc m', y) ∈ A then (1 : ℝ) else 0)) := by
          rw [mul_add, Finset.mul_sum]
          congr 1
          · ring
          · refine Finset.sum_congr rfl fun m' _ => by ring
        rw [hlhs, ← hrhs]
        exact hmul
      calc ∑ enc : Fin M → Fin n → α,
            codebookProb Px n M enc *
              (∑ y : Fin n → β,
                if jointTypicalDec P n M hM ε enc y ≠ m then (W.power n).trans (enc m) y else 0)
        _ ≤ ∑ enc : Fin M → Fin n → α,
              ((∑ y : Fin n → β,
                  codebookProb Px n M enc *
                    ((W.power n).trans (enc m) y * (if (enc m, y) ∉ A then (1 : ℝ) else 0))) +
                ∑ m' ∈ Finset.univ.erase m,
                  ∑ y : Fin n → β,
                    codebookProb Px n M enc *
                      ((W.power n).trans (enc m) y * (if (enc m', y) ∈ A then (1 : ℝ) else 0))) :=
            Finset.sum_le_sum fun enc _ => hpoint enc
        _ = (∑ enc : Fin M → Fin n → α, ∑ y : Fin n → β,
              codebookProb Px n M enc *
                ((W.power n).trans (enc m) y * (if (enc m, y) ∉ A then (1 : ℝ) else 0))) +
            ∑ enc : Fin M → Fin n → α, ∑ m' ∈ Finset.univ.erase m, ∑ y : Fin n → β,
              codebookProb Px n M enc *
                ((W.power n).trans (enc m) y * (if (enc m', y) ∈ A then (1 : ℝ) else 0)) :=
            Finset.sum_add_distrib
        _ = (∑ y : Fin n → β, ∑ enc : Fin M → Fin n → α,
              codebookProb Px n M enc *
                ((W.power n).trans (enc m) y * (if (enc m, y) ∉ A then (1 : ℝ) else 0))) +
            ∑ m' ∈ Finset.univ.erase m, ∑ y : Fin n → β, ∑ enc : Fin M → Fin n → α,
              codebookProb Px n M enc *
                ((W.power n).trans (enc m) y * (if (enc m', y) ∈ A then (1 : ℝ) else 0)) := by
            congr 1
            · exact Finset.sum_comm
            · rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun m' _ => Finset.sum_comm
    have hfirst := dmc_random_coding_first_term W Px n M ε m
    have hsecond_each : ∀ m' ∈ Finset.univ.erase m,
        (∑ y : Fin n → β, ∑ enc : Fin M → Fin n → α,
            codebookProb Px n M enc *
              ((W.power n).trans (enc m) y * (if (enc m', y) ∈ A then (1 : ℝ) else 0))) =
        ∑ xy ∈ A, ((iidDist P.fst n).prod (iidDist P.snd n)).pmf xy :=
      fun m' hm' => dmc_random_coding_second_term W Px n M ε m m' (Finset.mem_erase.mp hm').1
    have hsecond :
        (∑ m' ∈ Finset.univ.erase m,
          ∑ y : Fin n → β, ∑ enc : Fin M → Fin n → α,
            codebookProb Px n M enc *
              ((W.power n).trans (enc m) y * (if (enc m', y) ∈ A then (1 : ℝ) else 0))) =
        ((M - 1 : ℕ) : ℝ) *
          (∑ xy ∈ A, ((iidDist P.fst n).prod (iidDist P.snd n)).pmf xy) := by
      rw [Finset.sum_congr rfl hsecond_each, Finset.sum_const,
          Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
    dsimp only at hfirst
    rw [hfirst, hsecond] at hstep1
    exact hstep1
  -- Average over `m : Fin M`
  have havg :
      ∑ enc : Fin M → Fin n → α,
        codebookProb Px n M enc * dmcAvgError W n M enc (jointTypicalDec P n M hM ε enc) =
      ((1 : ℝ) / (M : ℝ)) *
        ∑ m : Fin M, ∑ enc : Fin M → Fin n → α,
          codebookProb Px n M enc *
            (∑ y : Fin n → β,
              if jointTypicalDec P n M hM ε enc y ≠ m then (W.power n).trans (enc m) y else 0) := by
    unfold dmcAvgError
    simp only [hMne, ↓reduceIte]
    have h1 : ∀ enc : Fin M → Fin n → α,
        codebookProb Px n M enc *
          (((1 : ℝ) / (M : ℝ)) *
            ∑ m : Fin M, ∑ y : Fin n → β,
              if jointTypicalDec P n M hM ε enc y ≠ m then (W.power n).trans (enc m) y else 0) =
        ((1 : ℝ) / (M : ℝ)) *
          ∑ m : Fin M, codebookProb Px n M enc *
            (∑ y : Fin n → β,
              if jointTypicalDec P n M hM ε enc y ≠ m then (W.power n).trans (enc m) y else 0) := by
      intro enc
      rw [← mul_assoc, mul_comm (codebookProb Px n M enc), mul_assoc, Finset.mul_sum]
    simp_rw [h1]
    rw [← Finset.mul_sum]
    congr 1
    exact Finset.sum_comm
  rw [havg]
  let B := (1 - ∑ xy ∈ A, (jointIidDist P n).pmf xy) +
    ((M - 1 : ℕ) : ℝ) *
      (∑ xy ∈ A, ((iidDist P.fst n).prod (iidDist P.snd n)).pmf xy)
  calc ((1 : ℝ) / (M : ℝ)) *
        ∑ m : Fin M, ∑ enc : Fin M → Fin n → α,
          codebookProb Px n M enc *
            (∑ y : Fin n → β,
              if jointTypicalDec P n M hM ε enc y ≠ m then (W.power n).trans (enc m) y else 0)
    _ ≤ ((1 : ℝ) / (M : ℝ)) * ∑ _m : Fin M, B :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ => hterm_m m) (by positivity)
    _ = ((1 : ℝ) / (M : ℝ)) * ((M : ℝ) * B) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = B := by field_simp [ne_of_gt hMpos]

/-- **Random-Coding Existence Bound** (Cover & Thomas, §7.7):
    for any DMC `W`, input distribution `Px`, blocklength `n`, message count `M > 0`, and `ε : ℝ`,
    there exists a deterministic `(n, M)` block code `(enc, dec)` satisfying
    `dmcAvgError W n M enc dec ≤ (1 - P^n(A_ε^(n))) + (M - 1) · 2^(-n (I(X; Y) - 3ε))`. -/
theorem dmc_random_coding_bound [DecidableEq β]
    (W : DMC α β) (Px : ProbDist α) (n M : ℕ) (hM : 0 < M) (ε : ℝ) :
    ∃ (enc : Fin M → Fin n → α) (dec : (Fin n → β) → Fin M),
      dmcAvgError W n M enc dec ≤
        (1 - ∑ xy ∈ jointTypicalSet (W.joint Px) n ε, (jointIidDist (W.joint Px) n).pmf xy) +
        ((M - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W.mutualInfo Px - 3 * ε))) := by
  let P := W.joint Px
  let B := (1 - ∑ xy ∈ jointTypicalSet P n ε, (jointIidDist P n).pmf xy) +
    ((M - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W.mutualInfo Px - 3 * ε)))
  have hexp := dmc_random_coding_expected_error_le W Px n M hM ε
  have hindep := jointTypicalSet_indep_prob_le P n ε
  have hle : ∑ enc : Fin M → Fin n → α,
      codebookProb Px n M enc * dmcAvgError W n M enc (jointTypicalDec P n M hM ε enc) ≤ B := by
    have hmul : ((M - 1 : ℕ) : ℝ) *
        (∑ xy ∈ jointTypicalSet P n ε, ((iidDist P.fst n).prod (iidDist P.snd n)).pmf xy) ≤
        ((M - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W.mutualInfo Px - 3 * ε))) :=
      mul_le_mul_of_nonneg_left hindep (Nat.cast_nonneg _)
    dsimp only at hexp
    linarith
  obtain ⟨enc, henc⟩ := exists_le_of_weighted_sum_le
    (codebookProb Px n M)
    (fun enc => dmcAvgError W n M enc (jointTypicalDec P n M hM ε enc))
    B
    (codebookProb_nonneg Px n M)
    (codebookProb_sum_one Px n M)
    hle
  exact ⟨enc, jointTypicalDec P n M hM ε enc, henc⟩

/-- **Achievability Below Single-Letter Mutual Information** (Cover & Thomas, Theorem 7.7.1):
    for any input distribution `Px`, rate `0 ≤ R < I(X; Y)`, and target error `δ > 0`,
    for all sufficiently large blocklengths `n` there exists an `(n, max 1 ⌊2^(n R)⌋)` block code
    with average error probability at most `δ`. -/
theorem dmc_achievable_lt_mutualInfo [DecidableEq β]
    (W : DMC α β) (Px : ProbDist α) {R : ℝ} (_hR0 : 0 ≤ R) (hR : R < W.mutualInfo Px)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N,
      let M := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
      ∃ (enc : Fin M → Fin n → α) (dec : (Fin n → β) → Fin M),
        dmcAvgError W n M enc dec ≤ δ := by
  let ε : ℝ := (W.mutualInfo Px - R) / 4
  have hε : 0 < ε := by dsimp only [ε]; linarith
  have hδ2 : 0 < δ / 2 := by linarith
  obtain ⟨N₁, hN₁⟩ := joint_aep_prob_tendsto_one (W.joint Px) hε hδ2
  obtain ⟨N₂, hN₂⟩ := exists_nat_ge (log2 (2 / δ) / ε)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  dsimp only
  let M := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
  have hM : 0 < M := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
  obtain ⟨enc, dec, hbound⟩ := dmc_random_coding_bound W Px n M hM ε
  refine ⟨enc, dec, ?_⟩
  have hterm1 :
      1 - ∑ xy ∈ jointTypicalSet (W.joint Px) n ε, (jointIidDist (W.joint Px) n).pmf xy ≤
        δ / 2 := by
    have hprob := hN₁ n (le_trans (le_max_left N₁ N₂) hn)
    linarith
  have hMsub : ((M - 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R) := by
    by_cases h1 : M ≤ 1
    · have hzero : M - 1 = 0 := Nat.sub_eq_zero_of_le h1
      rw [hzero, Nat.cast_zero]
      exact le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
    · push Not at h1
      have hMeq : M = Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)) := by
        dsimp only [M]
        rw [max_eq_right]
        by_contra hlt
        push Not at hlt
        have hM1 : max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R))) = 1 :=
          max_eq_left (Nat.le_of_lt_succ (Nat.lt_succ_of_lt hlt))
        change M = 1 at hM1
        omega
      have hle_M : ((M - 1 : ℕ) : ℝ) ≤ (M : ℝ) := Nat.cast_le.mpr (Nat.sub_le M 1)
      have hfloor_le : (M : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R) := by
        rw [hMeq]
        exact Nat.floor_le (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
      linarith
  have hterm2 :
      ((M - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W.mutualInfo Px - 3 * ε))) ≤ δ / 2 := by
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (-((n : ℝ) * (W.mutualInfo Px - 3 * ε))) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hprod :
        (2 : ℝ) ^ ((n : ℝ) * R) * (2 : ℝ) ^ (-((n : ℝ) * (W.mutualInfo Px - 3 * ε))) =
          (2 : ℝ) ^ (-((n : ℝ) * ε)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      dsimp only [ε]
      ring
    have hn2 : log2 (2 / δ) / ε ≤ (n : ℝ) :=
      le_trans hN₂ (by exact_mod_cast le_trans (le_max_right N₁ N₂) hn)
    have hlog_le : Real.log (2 / δ) ≤ (n : ℝ) * ε * Real.log 2 := by
      have h1 : log2 (2 / δ) ≤ (n : ℝ) * ε := (div_le_iff₀ hε).mp hn2
      unfold log2 at h1
      exact (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp h1
    have hexp_le : 2 / δ ≤ (2 : ℝ) ^ ((n : ℝ) * ε) := by
      have h2δ : 0 < 2 / δ := by positivity
      calc 2 / δ
        _ = Real.exp (Real.log (2 / δ)) := (Real.exp_log h2δ).symm
        _ ≤ Real.exp ((n : ℝ) * ε * Real.log 2) := Real.exp_le_exp.mpr hlog_le
        _ = Real.exp (Real.log 2 * ((n : ℝ) * ε)) := by ring_nf
        _ = (2 : ℝ) ^ ((n : ℝ) * ε) := (Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) _).symm
    have hneg_le : (2 : ℝ) ^ (-((n : ℝ) * ε)) ≤ δ / 2 := by
      have hpos1 : (0 : ℝ) < (2 : ℝ) ^ (-((n : ℝ) * ε)) :=
        Real.rpow_pos_of_pos (by norm_num) _
      have hmul1 : (2 : ℝ) ^ (-((n : ℝ) * ε)) * (2 : ℝ) ^ ((n : ℝ) * ε) = 1 := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), neg_add_cancel, Real.rpow_zero]
      have hmul2 : (2 / δ) * (2 : ℝ) ^ (-((n : ℝ) * ε)) ≤ 1 := by
        calc (2 / δ) * (2 : ℝ) ^ (-((n : ℝ) * ε))
          _ ≤ (2 : ℝ) ^ ((n : ℝ) * ε) * (2 : ℝ) ^ (-((n : ℝ) * ε)) :=
              mul_le_mul_of_nonneg_right hexp_le (le_of_lt hpos1)
          _ = 1 := by rw [mul_comm, hmul1]
      have hmul3 := mul_le_mul_of_nonneg_left hmul2 (le_of_lt hδ2)
      have hsimp : δ / 2 * (2 / δ * (2 : ℝ) ^ (-((n : ℝ) * ε))) =
          (2 : ℝ) ^ (-((n : ℝ) * ε)) := by
        field_simp [ne_of_gt hδ]
      linarith
    calc ((M - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (-((n : ℝ) * (W.mutualInfo Px - 3 * ε)))
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * R) * (2 : ℝ) ^ (-((n : ℝ) * (W.mutualInfo Px - 3 * ε))) :=
          mul_le_mul_of_nonneg_right hMsub (le_of_lt hpow_pos)
      _ = (2 : ℝ) ^ (-((n : ℝ) * ε)) := hprod
      _ ≤ δ / 2 := hneg_le
  linarith

end RandomCoding

/-! ### 3. Shannon's Channel Coding Theorem (Full Achievability + Converse) -/

section ChannelCodingTheorem

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Operational achievability of rate `R` (in bits per channel use) over a DMC `W`
    (Cover & Thomas, §7.5; matching `IsBCAchievable` and `IsRelayAchievable`). -/
def IsDmcAchievableRate (W : DMC α β) (R : ℝ) : Prop :=
  0 ≤ R ∧
  ∀ δ > 0, ∃ N : ℕ, ∀ n ≥ N,
    let M := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
    ∃ (enc : Fin M → Fin n → α) (dec : (Fin n → β) → Fin M),
      letI : DecidableEq β := Classical.decEq β
      dmcAvgError W n M enc dec ≤ δ

/-- Operational channel capacity of a DMC `W`: supremum of all operationally achievable rates. -/
noncomputable def dmcOperationalCapacity (W : DMC α β) : ℝ :=
  sSup { R : ℝ | IsDmcAchievableRate W R }

private lemma log2_two_rpow (x : ℝ) : log2 ((2 : ℝ) ^ x) = x := by
  unfold log2
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  exact mul_div_cancel_right₀ x (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))

/-- Rate `0` is operationally achievable over any DMC on a nonempty input alphabet. -/
theorem isDmcAchievableRate_zero [Nonempty α] (W : DMC α β) :
    IsDmcAchievableRate W 0 := by
  classical
  refine ⟨le_rfl, fun δ hδ => ⟨0, fun n _ => ?_⟩⟩
  dsimp only
  let M := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * 0)))
  have hM1 : M = 1 := by
    dsimp only [M]
    norm_num
  have hMpos : 0 < M := by omega
  let a₀ : α := Classical.arbitrary α
  refine ⟨fun _ _ => a₀, fun _ => ⟨0, hMpos⟩, ?_⟩
  have herr : dmcAvgError W n M (fun _ _ => a₀) (fun _ => ⟨0, hMpos⟩) = 0 := by
    unfold dmcAvgError
    have hMne : M ≠ 0 := by omega
    simp only [hMne, ↓reduceIte]
    have hzero : ∀ m : Fin M, (⟨0, hMpos⟩ : Fin M) = m := fun m => by
      ext; dsimp only; omega
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun m _ => Finset.sum_eq_zero fun _ _ => ?_)
    simp [hzero m]
  linarith

/-- **Shannon's Channel Coding Theorem — Achievability** (Cover & Thomas, Theorem 7.7.1):
    every rate `0 ≤ R < C(W)` is operationally achievable over `W`. -/
theorem shannon_channel_coding_achievability (W : DMC α β) (R : ℝ)
    (hR0 : 0 ≤ R) (hR : R < W.capacity) :
    IsDmcAchievableRate W R := by
  classical
  have hSne : { r : ℝ | ∃ P : ProbDist α, r = W.mutualInfo P }.Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    rw [DMC.capacity, hempty, Real.sSup_empty] at hR
    linarith
  obtain ⟨r, ⟨Px, rfl⟩, hr⟩ := exists_lt_of_lt_csSup hSne hR
  refine ⟨hR0, fun δ hδ => ?_⟩
  exact dmc_achievable_lt_mutualInfo W Px hR0 hr hδ

/-- **Shannon's Channel Coding Theorem — Converse** (Cover & Thomas, Theorem 7.7.1 & §7.9):
    every operationally achievable rate satisfies `R ≤ C(W)`. -/
theorem shannon_channel_coding_converse (W : DMC α β) (R : ℝ)
    (hR : IsDmcAchievableRate W R) :
    R ≤ W.capacity := by
  classical
  by_contra hlt
  push Not at hlt
  -- From achievability of `R`, the input alphabet `α` must be nonempty
  have hα : Nonempty α := by
    obtain ⟨N, hN⟩ := hR.2 1 zero_lt_one
    obtain ⟨enc, _, _⟩ := hN (max N 1) (le_max_left N 1)
    have hMpos : 0 < max 1 (Nat.floor ((2 : ℝ) ^ (((max N 1 : ℕ) : ℝ) * R))) :=
      lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
    have hn_pos : 0 < max N 1 := lt_of_lt_of_le Nat.zero_lt_one (le_max_right N 1)
    exact ⟨enc ⟨0, hMpos⟩ ⟨0, hn_pos⟩⟩
  have hcap0 : 0 ≤ W.capacity := by
    have hmi : 0 ≤ mutualInfo (W.joint (ProbDist.uniform (α := α))) := mutualInfo_nonneg _
    exact le_trans hmi (dmc_mutualInfo_le_capacity W ProbDist.uniform)
  let Δ : ℝ := R - W.capacity
  have hΔ : 0 < Δ := by dsimp only [Δ]; linarith
  have hRpos : 0 < R := by linarith
  let δ : ℝ := min (1 / 2) (Δ / (4 * R))
  have hδ_pos : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ_half : δ ≤ 1 / 2 := min_le_left _ _
  have hδR : δ * R ≤ Δ / 4 := by
    have h1 : δ ≤ Δ / (4 * R) := min_le_right _ _
    have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt hRpos)
    have h3 : Δ / (4 * R) * R = Δ / 4 := by field_simp [ne_of_gt hRpos]
    linarith
  obtain ⟨N₁, hN₁⟩ := hR.2 δ hδ_pos
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (max (1 / R) (4 / Δ))
  let n : ℕ := max (max N₁ N₂) 1
  have hn_pos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ 1)
  have hn_r : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
  have hn_ge_N₁ : N₁ ≤ n := le_trans (le_max_left N₁ N₂) (le_max_left _ 1)
  have hn_gt_max : max (1 / R) (4 / Δ) < (n : ℝ) :=
    lt_of_lt_of_le hN₂ (by exact_mod_cast le_trans (le_max_right N₁ N₂) (le_max_left _ 1))
  have hn_gt_1R : 1 / R < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn_gt_max
  have hn_gt_4Δ : 4 / Δ < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn_gt_max
  have hnR_gt1 : 1 < (n : ℝ) * R := by
    have h := (div_lt_iff₀ hRpos).mp hn_gt_1R
    linarith
  have h2n_lt : 2 / (n : ℝ) < Δ / 2 := by
    rw [div_lt_iff₀ hn_r]
    have h := (div_lt_iff₀ hΔ).mp hn_gt_4Δ
    linarith
  obtain ⟨enc, dec, herr⟩ := hN₁ n hn_ge_N₁
  let M : ℕ := max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)))
  have h2pow_ge2 : (2 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * R) := by
    calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
      _ ≤ (2 : ℝ) ^ ((n : ℝ) * R) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_of_lt hnR_gt1)
  have hM_ge2 : 2 ≤ M :=
    le_trans (Nat.le_floor (by exact_mod_cast h2pow_ge2)) (le_max_right 1 _)
  have hM_gt_pow : (2 : ℝ) ^ ((n : ℝ) * R - 1) ≤ (M : ℝ) := by
    have hhalf : (2 : ℝ) ^ ((n : ℝ) * R - 1) = (2 : ℝ) ^ ((n : ℝ) * R) / 2 := by
      rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
    have hsub1 : (2 : ℝ) ^ ((n : ℝ) * R) / 2 ≤ (2 : ℝ) ^ ((n : ℝ) * R) - 1 := by linarith
    have hfloor : (2 : ℝ) ^ ((n : ℝ) * R) - 1 < (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)) : ℝ) := by
      linarith [Nat.lt_floor_add_one ((2 : ℝ) ^ ((n : ℝ) * R))]
    have hleM : (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R)) : ℝ) ≤ (M : ℝ) :=
      Nat.cast_le.mpr (le_max_right 1 _)
    linarith
  have hlogM_ge : (n : ℝ) * R - 1 ≤ log2 (M : ℝ) := by
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ ((n : ℝ) * R - 1) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hlog_mono : log2 ((2 : ℝ) ^ ((n : ℝ) * R - 1)) ≤ log2 (M : ℝ) := by
      unfold log2
      exact div_le_div_of_nonneg_right (Real.log_le_log hpow_pos hM_gt_pow)
        (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
    rw [log2_two_rpow] at hlog_mono
    exact hlog_mono
  have hrate_ge : R - 1 / (n : ℝ) ≤ log2 (M : ℝ) / (n : ℝ) := by
    have hdiv := div_le_div_of_nonneg_right hlogM_ge (le_of_lt hn_r)
    have hsimp : ((n : ℝ) * R - 1) / (n : ℝ) = R - 1 / (n : ℝ) := by
      rw [sub_div, mul_div_cancel_left₀ _ (ne_of_gt hn_r)]
    linarith
  have hrate_nonneg : 0 ≤ R - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) < R := (div_lt_iff₀ hn_r).mpr (by linarith)
    linarith
  have hconv := dmcAvgError_rate_converse W n M hn_pos hM_ge2 enc dec
  have herr_le : dmcAvgError W n M enc dec ≤ δ := herr
  have hprod_le : (1 - δ) * (R - 1 / (n : ℝ)) ≤
      (1 - dmcAvgError W n M enc dec) * (log2 (M : ℝ) / (n : ℝ)) :=
    mul_le_mul (by linarith) hrate_ge hrate_nonneg (by linarith)
  have hcomb : (1 - δ) * (R - 1 / (n : ℝ)) ≤ W.capacity + 1 / (n : ℝ) :=
    le_trans hprod_le hconv
  have hδn : 0 ≤ δ * (1 / (n : ℝ)) := by positivity
  have hexpand : (1 - δ) * (R - 1 / (n : ℝ)) = R - 1 / (n : ℝ) - δ * R + δ * (1 / (n : ℝ)) := by
    ring
  have h2div : 1 / (n : ℝ) + 1 / (n : ℝ) = 2 / (n : ℝ) := by ring
  have hfinal : Δ ≤ δ * R + 2 / (n : ℝ) := by
    dsimp only [Δ]
    linarith
  linarith

/-- **Shannon's Channel Coding Theorem** (Cover & Thomas, Theorem 7.7.1):
    the operational capacity of any Discrete Memoryless Channel `W` equals its
    single-letter Shannon capacity `C(W) = sup_{P_X} I(X; Y)`. -/
theorem shannon_channel_coding_theorem (W : DMC α β) :
    dmcOperationalCapacity W = W.capacity := by
  by_cases hα : Nonempty α
  · have hSne : { R : ℝ | IsDmcAchievableRate W R }.Nonempty :=
      ⟨0, isDmcAchievableRate_zero W⟩
    have hSbdd : BddAbove { R : ℝ | IsDmcAchievableRate W R } :=
      ⟨W.capacity, fun R hR => shannon_channel_coding_converse W R hR⟩
    have hle : dmcOperationalCapacity W ≤ W.capacity :=
      csSup_le hSne (fun R hR => shannon_channel_coding_converse W R hR)
    have hge : W.capacity ≤ dmcOperationalCapacity W := by
      by_contra hlt
      push Not at hlt
      have hop0 : 0 ≤ dmcOperationalCapacity W :=
        le_csSup hSbdd (isDmcAchievableRate_zero W)
      let R : ℝ := (dmcOperationalCapacity W + W.capacity) / 2
      have hR0 : 0 ≤ R := by dsimp only [R]; linarith
      have hRlt : R < W.capacity := by dsimp only [R]; linarith
      have hgt : dmcOperationalCapacity W < R := by dsimp only [R]; linarith
      have hach : IsDmcAchievableRate W R :=
        shannon_channel_coding_achievability W R hR0 hRlt
      have hRle : R ≤ dmcOperationalCapacity W := le_csSup hSbdd hach
      linarith
    exact le_antisymm hle hge
  · have hcap_empty : { r : ℝ | ∃ P : ProbDist α, r = W.mutualInfo P } = ∅ := by
      ext r
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨P, _⟩
      have h0 : ∑ a : α, P.pmf a = 0 := Finset.sum_eq_zero fun a _ => (hα ⟨a⟩).elim
      linarith [P.sum_one]
    have hop_empty : { R : ℝ | IsDmcAchievableRate W R } = ∅ := by
      ext R
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hR
      obtain ⟨N, hN⟩ := hR.2 1 zero_lt_one
      obtain ⟨enc, _, _⟩ := hN (max N 1) (le_max_left N 1)
      have hMpos : 0 < max 1 (Nat.floor ((2 : ℝ) ^ (((max N 1 : ℕ) : ℝ) * R))) :=
        lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
      have hn_pos : 0 < max N 1 := lt_of_lt_of_le Nat.zero_lt_one (le_max_right N 1)
      exact hα ⟨enc ⟨0, hMpos⟩ ⟨0, hn_pos⟩⟩
    rw [dmcOperationalCapacity, DMC.capacity, hop_empty, hcap_empty]

end ChannelCodingTheorem

end InfoTheory.Bridge
