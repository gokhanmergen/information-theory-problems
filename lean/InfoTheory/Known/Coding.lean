import InfoTheory.Core
import InfoTheory.Bridge.Mathlib
import Mathlib.InformationTheory.Hamming
import Mathlib.RingTheory.Polynomial.Basic

open scoped BigOperators
open Finset

namespace InfoTheory.Known

-- Canonical versions live in `InfoTheory.Bridge` (proved via Mathlib's `klDiv`/`hammingDist`).
open InfoTheory.Bridge (hammingDistVec_eq_hammingDist hammingDistVec_comm hammingDistVec_eq_zero hammingDistVec_triangle)

/-- `d(x, x) = 0`. -/
@[simp] theorem hammingDistVec_self {α : Type*} [DecidableEq α] {n : ℕ} (x : Fin n → α) :
    hammingDistVec x x = 0 := hammingDist_self x

/-- `0 < d(x, y) ↔ x ≠ y`. -/
theorem hammingDistVec_pos {α : Type*} [DecidableEq α] {n : ℕ} {x y : Fin n → α} :
    0 < hammingDistVec x y ↔ x ≠ y := hammingDist_pos

/-- `d(x, y) ≤ n`. -/
theorem hammingDistVec_le_length {α : Type*} [DecidableEq α] {n : ℕ} (x y : Fin n → α) :
    hammingDistVec x y ≤ n := by
  rw [hammingDistVec_eq_hammingDist]
  simpa using (hammingDist_le_card_fintype (x := x) (y := y))

/-! ### `maxCodeSize` API -/

/-- The set whose supremum defines `maxCodeSize`. -/
private def codeSizes (q n d : ℕ) : Set ℕ :=
  { M : ℕ | ∃ C : Finset (Fin n → Fin q), IsCode q n d C ∧ C.card = M }

private theorem codeSizes_nonempty (q n d : ℕ) : (codeSizes q n d).Nonempty :=
  ⟨0, ∅, by simp [IsCode], rfl⟩

private theorem codeSizes_bdd (q n d : ℕ) : ∀ M ∈ codeSizes q n d, M ≤ q ^ n := by
  rintro M ⟨C, -, rfl⟩
  simpa using C.card_le_univ

/-- `A_q(n,d)` is defined by a bounded set: every code has at most `q^n` words. -/
theorem bddAbove_codeSizes (q n d : ℕ) :
    BddAbove { M : ℕ | ∃ C : Finset (Fin n → Fin q), IsCode q n d C ∧ C.card = M } :=
  ⟨q ^ n, codeSizes_bdd q n d⟩

/-- `A_q(n,d)` is attained by some code. -/
theorem exists_code_card_eq_maxCodeSize (q n d : ℕ) :
    ∃ C : Finset (Fin n → Fin q), IsCode q n d C ∧ C.card = maxCodeSize q n d :=
  Nat.sSup_mem (codeSizes_nonempty q n d) (bddAbove_codeSizes q n d)

/-- Any code has at most `A_q(n,d)` codewords. -/
theorem isCode_card_le_maxCodeSize {q n d : ℕ} {C : Finset (Fin n → Fin q)}
    (hC : IsCode q n d C) : C.card ≤ maxCodeSize q n d :=
  le_csSup (bddAbove_codeSizes q n d) ⟨C, hC, rfl⟩

/-- Trivial upper bound `A_q(n,d) ≤ q^n`. -/
theorem maxCodeSize_le_pow (q n d : ℕ) : maxCodeSize q n d ≤ q ^ n := by
  obtain ⟨C, hC, h⟩ := exists_code_card_eq_maxCodeSize q n d
  rw [← h]; exact codeSizes_bdd q n d _ ⟨C, hC, rfl⟩

/-- Characterisation: `M ≤ A_q(n,d)` iff there is a code of size `M` (codes are closed under
subsets). -/
theorem le_maxCodeSize_iff {q n d M : ℕ} :
    M ≤ maxCodeSize q n d ↔ ∃ C : Finset (Fin n → Fin q), IsCode q n d C ∧ C.card = M := by
  constructor
  · intro hM
    obtain ⟨C, hC, h⟩ := exists_code_card_eq_maxCodeSize q n d
    obtain ⟨D, hDC, hD⟩ := Finset.exists_subset_card_eq (h ▸ hM : M ≤ C.card)
    exact ⟨D, fun x hx y hy hxy => hC x (hDC hx) y (hDC hy) hxy, hD⟩
  · rintro ⟨C, hC, rfl⟩; exact isCode_card_le_maxCodeSize hC

/-- Codes are monotone in `d`: a code of distance `d` is a code of every distance `d' ≤ d`. -/
theorem isCode_mono {q n d d' : ℕ} {C : Finset (Fin n → Fin q)} (hC : IsCode q n d C)
    (h : d' ≤ d) : IsCode q n d' C :=
  fun x hx y hy hxy => h.trans (hC x hx y hy hxy)

/-- `A_q(n,d)` is antitone in `d`. -/
theorem maxCodeSize_antitone {q n d d' : ℕ} (h : d' ≤ d) :
    maxCodeSize q n d ≤ maxCodeSize q n d' := by
  obtain ⟨C, hC, hc⟩ := exists_code_card_eq_maxCodeSize q n d
  rw [← hc]; exact isCode_card_le_maxCodeSize (isCode_mono hC h)

/-- The whole space is a code of minimum distance `1`. -/
theorem isCode_univ_one (q n : ℕ) : IsCode q n 1 (Finset.univ : Finset (Fin n → Fin q)) :=
  fun _ _ _ _ hxy => Nat.one_le_iff_ne_zero.mpr ((hammingDistVec_eq_zero _ _).not.mpr hxy)

/-- `A_q(n,d) = q^n` for `d ≤ 1` (in particular for `d = 0`). -/
theorem maxCodeSize_of_le_one {q n d : ℕ} (hd : d ≤ 1) : maxCodeSize q n d = q ^ n := by
  refine le_antisymm (maxCodeSize_le_pow q n d) ?_
  have := isCode_card_le_maxCodeSize (isCode_mono (isCode_univ_one q n) hd)
  simpa using this

/-- `A_q(n,0) = q^n`. -/
theorem maxCodeSize_zero (q n : ℕ) : maxCodeSize q n 0 = q ^ n :=
  maxCodeSize_of_le_one (Nat.zero_le 1)

/-! ### Singleton bound -/

/-- Number of indices `i : Fin n` with `m ≤ i`. -/
theorem card_filter_le_val (n m : ℕ) :
    (Finset.univ.filter (fun i : Fin n => m ≤ i.val)).card = n - m := by
  rw [← Finset.card_map Fin.valEmbedding]
  have : (Finset.univ.filter (fun i : Fin n => m ≤ i.val)).map Fin.valEmbedding =
      Finset.Ico m n := by
    ext j; simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨hi, i.isLt⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨j, h2⟩, h1, rfl⟩
  rw [this, Nat.card_Ico]

/-- **Singleton bound** (Singleton 1964; MacWilliams–Sloane Ch. 1 Thm 11):
`A_q(n,d) ≤ q^(n-d+1)` for `1 ≤ d ≤ n`. Proof: deleting the last `d-1` coordinates is
injective on a code of minimum distance `d`. -/
theorem singleton_bound {q n d : ℕ} (hd : 1 ≤ d) (hdn : d ≤ n) :
    maxCodeSize q n d ≤ q ^ (n - d + 1) := by
  obtain ⟨C, hC, hc⟩ := exists_code_card_eq_maxCodeSize q n d
  set m := n - d + 1 with hm
  have hmn : m ≤ n := by omega
  let π : (Fin n → Fin q) → (Fin m → Fin q) := fun x i => x (Fin.castLE hmn i)
  have hinj : Set.InjOn π C := by
    intro x hx y hy hxy
    by_contra hne
    have h1 := hC x hx y hy hne
    have h2 : hammingDistVec x y ≤ n - m := by
      rw [← card_filter_le_val n m]
      apply Finset.card_le_card
      intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro hi
      by_contra hlt
      push Not at hlt
      exact hi (congrFun hxy ⟨i.val, hlt⟩)
    omega
  rw [← hc, ← Finset.card_image_of_injOn hinj]
  simpa using (C.image π).card_le_univ

/-! ### Repetition code -/

/-- The `q`-ary repetition code of length `n`. -/
def repetitionCode (q n : ℕ) : Finset (Fin n → Fin q) :=
  Finset.univ.image (fun a : Fin q => fun _ : Fin n => a)

/-- The repetition code has minimum distance `n`. -/
theorem isCode_repetitionCode (q n : ℕ) : IsCode q n n (repetitionCode q n) := by
  intro x hx y hy hxy
  simp only [repetitionCode, Finset.mem_image, Finset.mem_univ, true_and] at hx hy
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  have hab : a ≠ b := fun h => hxy (h ▸ rfl)
  unfold hammingDistVec
  simp [hab]

/-- For `n ≥ 1` the repetition code has `q` codewords. -/
theorem card_repetitionCode {q n : ℕ} (hn : 1 ≤ n) : (repetitionCode q n).card = q := by
  unfold repetitionCode
  rw [Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
  intro a b h
  exact congrFun h ⟨0, hn⟩

/-- **Repetition code lower bound**: `q ≤ A_q(n,n)` for `n ≥ 1`. -/
theorem le_maxCodeSize_self {q n : ℕ} (hn : 1 ≤ n) : q ≤ maxCodeSize q n n := by
  have := isCode_card_le_maxCodeSize (isCode_repetitionCode q n)
  rwa [card_repetitionCode hn] at this

/-- `A_q(n,n) = q` for `n ≥ 1` (repetition code + Singleton bound). -/
theorem maxCodeSize_self {q n : ℕ} (hn : 1 ≤ n) : maxCodeSize q n n = q := by
  refine le_antisymm ?_ (le_maxCodeSize_self hn)
  simpa using singleton_bound (q := q) hn le_rfl

/-! ### Hamming spheres and balls -/

/-- Hamming sphere of radius `i` around `x`. -/
def hammingSphere {q n : ℕ} (x : Fin n → Fin q) (i : ℕ) : Finset (Fin n → Fin q) :=
  Finset.univ.filter (fun y => hammingDistVec x y = i)

/-- Hamming ball of radius `r` around `x`. -/
def hammingBall {q n : ℕ} (x : Fin n → Fin q) (r : ℕ) : Finset (Fin n → Fin q) :=
  Finset.univ.filter (fun y => hammingDistVec x y ≤ r)

/-- **Sphere size**: `|S(x,i)| = (n choose i) (q-1)^i` (MacWilliams–Sloane Ch. 1 §5). -/
theorem card_hammingSphere {q n : ℕ} (x : Fin n → Fin q) (i : ℕ) :
    (hammingSphere x i).card = n.choose i * (q - 1) ^ i := by
  classical
  let D : (Fin n → Fin q) → Finset (Fin n) := fun y => Finset.univ.filter (fun j => x j ≠ y j)
  have hmaps : ((hammingSphere x i : Finset (Fin n → Fin q)) : Set (Fin n → Fin q)).MapsTo D
      (Finset.powersetCard i (Finset.univ : Finset (Fin n))) := by
    intro y hy
    simp only [hammingSphere, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
      true_and] at hy
    rw [Finset.mem_coe, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hy⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ S ∈ Finset.powersetCard i (Finset.univ : Finset (Fin n)),
      ((hammingSphere x i).filter (fun y => D y = S)).card = (q - 1) ^ i := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    have heq : (hammingSphere x i).filter (fun y => D y = S) =
        Fintype.piFinset (fun j => if j ∈ S then Finset.univ.erase (x j) else {x j}) := by
      ext y
      simp only [hammingSphere, Finset.mem_filter, Finset.mem_univ, true_and,
        Fintype.mem_piFinset]
      constructor
      · rintro ⟨-, hD⟩ j
        have hj : j ∈ S ↔ x j ≠ y j := by rw [← hD]; simp [D]
        split_ifs with h
        · simp only [Finset.mem_erase, Finset.mem_univ, and_true]
          exact fun e => (hj.mp h) e.symm
        · simp only [Finset.mem_singleton]
          by_contra e
          exact h (hj.mpr (Ne.symm e))
      · intro hy
        have hD : D y = S := by
          ext j
          simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
          have := hy j
          split_ifs at this with h
          · simp only [Finset.mem_erase, Finset.mem_univ, and_true] at this
            exact ⟨fun _ => h, fun _ e => this e.symm⟩
          · simp only [Finset.mem_singleton] at this
            exact ⟨fun e => absurd this.symm e, fun e => absurd e h⟩
        refine ⟨?_, hD⟩
        show (D y).card = i
        rw [hD, hS.2]
    rw [heq, Fintype.card_piFinset]
    have hc : ∀ j, (if j ∈ S then Finset.univ.erase (x j) else ({x j} : Finset (Fin q))).card =
        if j ∈ S then q - 1 else 1 := by
      intro j
      split_ifs
      · rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      · rfl
    simp_rw [hc]
    rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const, hS.2]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

/-- **Ball size**: `|B(x,r)| = ∑_{i ≤ r} (n choose i)(q-1)^i`, independent of the centre. -/
theorem card_hammingBall {q n : ℕ} (x : Fin n → Fin q) (r : ℕ) :
    (hammingBall x r).card = ∑ i ∈ Finset.range (r + 1), n.choose i * (q - 1) ^ i := by
  classical
  have hmaps : ((hammingBall x r : Finset (Fin n → Fin q)) : Set (Fin n → Fin q)).MapsTo
      (hammingDistVec x) (Finset.range (r + 1)) := by
    intro y hy
    simp only [hammingBall, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
      true_and] at hy
    rw [Finset.mem_coe, Finset.mem_range]; omega
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← card_hammingSphere x i]
  congr 1
  ext y
  simp only [hammingBall, hammingSphere, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_range] at hi ⊢
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨by omega, h⟩

/-- Membership in a Hamming ball. -/
@[simp] theorem mem_hammingBall {q n : ℕ} {x y : Fin n → Fin q} {r : ℕ} :
    y ∈ hammingBall x r ↔ hammingDistVec x y ≤ r := by
  simp [hammingBall]

/-! ### Sphere-packing (Hamming) bound -/

/-- **Hamming (sphere-packing) bound** (Hamming 1950; MacWilliams–Sloane Ch. 1 Thm 6):
`A_q(n, 2t+1) · ∑_{i ≤ t} (n choose i)(q-1)^i ≤ q^n`. -/
theorem hamming_bound (q n t : ℕ) :
    maxCodeSize q n (2 * t + 1) * ∑ i ∈ Finset.range (t + 1), n.choose i * (q - 1) ^ i
      ≤ q ^ n := by
  classical
  obtain ⟨C, hC, hc⟩ := exists_code_card_eq_maxCodeSize q n (2 * t + 1)
  have hdisj : (C : Set (Fin n → Fin q)).PairwiseDisjoint (fun c => hammingBall c t) := by
    intro c hc' c' hc'' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro y hy hy'
    rw [mem_hammingBall] at hy hy'
    have h1 := hC c hc' c' hc'' hne
    have h2 := hammingDistVec_triangle c y c'
    rw [hammingDistVec_comm y c'] at h2
    omega
  have h := Finset.card_le_univ (C.biUnion fun c => hammingBall c t)
  rw [Finset.card_biUnion hdisj] at h
  simp_rw [card_hammingBall, Finset.sum_const, smul_eq_mul, Fintype.card_fun,
    Fintype.card_fin] at h
  rwa [hc] at h

/-! ### Gilbert–Varshamov bound (finite form) -/

/-- **Gilbert–Varshamov bound** (Gilbert 1952, Varshamov 1957; MacWilliams–Sloane Ch. 1 Thm 12):
for `d ≥ 1`, `q^n ≤ A_q(n,d) · ∑_{i ≤ d-1} (n choose i)(q-1)^i`. Proof: balls of radius `d-1`
around a code of maximum size cover the whole space. -/
theorem gilbert_varshamov_bound {q n d : ℕ} (hd : 1 ≤ d) :
    q ^ n ≤ maxCodeSize q n d * ∑ i ∈ Finset.range d, n.choose i * (q - 1) ^ i := by
  classical
  obtain ⟨C, hC, hc⟩ := exists_code_card_eq_maxCodeSize q n d
  have hcover : (Finset.univ : Finset (Fin n → Fin q)) ⊆ C.biUnion fun c => hammingBall c (d - 1) := by
    intro y _
    rw [Finset.mem_biUnion]
    by_contra hno
    push Not at hno
    have hyC : y ∉ C := by
      intro hy
      have := hno y hy
      rw [mem_hammingBall, hammingDistVec_self] at this
      omega
    have hC' : IsCode q n d (insert y C) := by
      intro a ha b hb hab
      rw [Finset.mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact absurd rfl hab
      · have := hno b hb; rw [mem_hammingBall, hammingDistVec_comm] at this; omega
      · have := hno a ha; rw [mem_hammingBall] at this; omega
      · exact hC a ha b hb hab
    have := isCode_card_le_maxCodeSize hC'
    rw [Finset.card_insert_of_notMem hyC, hc] at this
    omega
  have h := (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  simp_rw [card_hammingBall, Finset.sum_const, smul_eq_mul, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, Nat.sub_add_cancel hd] at h
  rwa [hc] at h

/-! ### Reed–Solomon codes are MDS -/

/-- Evaluation map of polynomials of degree `< k` at the points `α i` (Reed–Solomon encoder). -/
noncomputable def reedSolomonEval (F : Type*) [Field F] {n : ℕ} (α : Fin n → F) (k : ℕ) :
    Polynomial.degreeLT F k →ₗ[F] (Fin n → F) where
  toFun p i := p.1.eval (α i)
  map_add' p p' := by ext i; simp
  map_smul' c p := by ext i; simp

/-- A nonzero polynomial of degree `< k` vanishes at fewer than `k` of the distinct points
`α i`. -/
private theorem card_zeros_lt {F : Type*} [Field F] [DecidableEq F] {n : ℕ} {α : Fin n → F}
    (hα : Function.Injective α) {k : ℕ} (p : Polynomial F) (hp : p ∈ Polynomial.degreeLT F k)
    (hp0 : p ≠ 0) :
    (Finset.univ.filter (fun i : Fin n => p.eval (α i) = 0)).card < k := by
  classical
  set Z := Finset.univ.filter (fun i : Fin n => p.eval (α i) = 0)
  by_contra hle
  push Not at hle
  have hdeg : p.natDegree < k := by
    rw [Polynomial.mem_degreeLT] at hp
    exact (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hp
  apply hp0
  refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p
    (f := fun i : Z => α i.1) (hα.comp Subtype.val_injective) ?_ ?_
  · intro i
    have := i.2
    simp only [Z, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this
  · rw [Fintype.card_coe]; omega

/-- **Reed–Solomon codes are MDS** (Reed–Solomon 1960; MacWilliams–Sloane Ch. 10 §3, Ch. 11):
for `k ≤ n ≤ |F|` there is an `[n, k, n-k+1]` linear code over `F`. This validates the
definition `IsLinearMDSCode` used by the MDS-conjecture statement. -/
theorem reedSolomon_isLinearMDSCode (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    {n k : ℕ} (hkn : k ≤ n) (hnF : n ≤ Fintype.card F) : IsLinearMDSCode F n k := by
  classical
  obtain ⟨α⟩ := Function.Embedding.nonempty_of_card_le (α := Fin n) (β := F)
    (by simpa using hnF)
  let L := reedSolomonEval F α k
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    by_contra hne
    have hp0 : p.1 ≠ 0 := fun h => hne (Subtype.ext h)
    have h1 := card_zeros_lt α.injective p.1 p.2 hp0
    have hall : (Finset.univ.filter (fun i : Fin n => p.1.eval (α i) = 0)) = Finset.univ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact congrFun hp i
    rw [hall, Finset.card_univ, Fintype.card_fin] at h1
    omega
  refine ⟨LinearMap.range L, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hinj, LinearEquiv.finrank_eq (Polynomial.degreeLTEquiv F k),
      Module.finrank_fin_fun]
  · rintro v ⟨p, rfl⟩ hv
    have hp0 : p.1 ≠ 0 := by
      intro h; apply hv
      have : p = 0 := Subtype.ext h
      rw [this, map_zero]
    have h1 := card_zeros_lt α.injective p.1 p.2 hp0
    have h2 := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (fun i : Fin n => p.1.eval (α i) = 0)
    rw [Finset.card_univ, Fintype.card_fin] at h2
    have h3 : (Finset.univ.filter (fun i : Fin n => L p i ≠ 0)) =
        Finset.univ.filter (fun i : Fin n => ¬ p.1.eval (α i) = 0) := rfl
    rw [h3]
    omega

/-- The degenerate case `k = 0` of `IsLinearMDSCode` holds for every `n` (zero code). -/
theorem isLinearMDSCode_zero (F : Type*) [Field F] [Fintype F] [DecidableEq F] (n : ℕ) :
    IsLinearMDSCode F n 0 :=
  ⟨⊥, by simp, fun v hv hv0 => absurd ((Submodule.mem_bot F).mp hv) hv0⟩

/-! ### Asymptotic Gilbert–Varshamov bound -/

/-- `A_q(n,d) ≥ 1` whenever the alphabet is nonempty (a single word is a code). -/
theorem one_le_maxCodeSize {q : ℕ} (hq : 1 ≤ q) (n d : ℕ) : 1 ≤ maxCodeSize q n d := by
  have hC : IsCode q n d {fun _ => ⟨0, hq⟩} := by
    intro x hx y hy hxy
    rw [Finset.mem_singleton] at hx hy
    exact absurd (hx.trans hy.symm) hxy
  simpa using isCode_card_le_maxCodeSize hC

/-- Entropy bound on the binary Hamming-ball volume (MacWilliams–Sloane Ch. 10 Lemma 7,
natural-log form): for `0 < δ ≤ 1/2` and `m ≤ δ n`,
`(∑_{i ≤ m} (n choose i)) · e^{n(δ ln δ + (1-δ) ln (1-δ))} ≤ 1`. -/
theorem sum_choose_mul_exp_le_one {δ : ℝ} (h0 : 0 < δ) (h1 : δ ≤ 1 / 2) (n m : ℕ)
    (hm : (m : ℝ) ≤ δ * n) :
    (∑ i ∈ Finset.range (m + 1), (n.choose i : ℝ)) *
      Real.exp (n * (δ * Real.log δ + (1 - δ) * Real.log (1 - δ))) ≤ 1 := by
  have hδ1 : 0 < 1 - δ := by linarith
  have hmn : m ≤ n := by
    have : (m : ℝ) ≤ n := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    exact_mod_cast this
  set E := Real.exp (n * (δ * Real.log δ + (1 - δ) * Real.log (1 - δ)))
  have key : ∀ i ∈ Finset.range (m + 1), E ≤ δ ^ i * (1 - δ) ^ (n - i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hin : i ≤ n := by omega
    have hpos : 0 < δ ^ i * (1 - δ) ^ (n - i) := by positivity
    rw [← Real.exp_log hpos, Real.exp_le_exp, Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Nat.cast_sub hin]
    have hi' : (i : ℝ) ≤ m := by exact_mod_cast (by omega : i ≤ m)
    have ha : (i : ℝ) - δ * n ≤ 0 := by linarith
    have hb : Real.log δ - Real.log (1 - δ) ≤ 0 := by
      have := Real.log_le_log h0 (by linarith : δ ≤ 1 - δ)
      linarith
    nlinarith [mul_nonneg_of_nonpos_of_nonpos ha hb]
  calc (∑ i ∈ Finset.range (m + 1), (n.choose i : ℝ)) * E
      = ∑ i ∈ Finset.range (m + 1), (n.choose i : ℝ) * E := Finset.sum_mul _ _ _
    _ ≤ ∑ i ∈ Finset.range (m + 1), δ ^ i * (1 - δ) ^ (n - i) * (n.choose i : ℝ) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [mul_comm (δ ^ i * (1 - δ) ^ (n - i))]
        exact mul_le_mul_of_nonneg_left (key i hi) (Nat.cast_nonneg _)
    _ ≤ ∑ i ∈ Finset.range (n + 1), δ ^ i * (1 - δ) ^ (n - i) * (n.choose i : ℝ) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr (by omega)) fun i _ _ => by positivity
    _ = (δ + (1 - δ)) ^ n := (add_pow δ (1 - δ) n).symm
    _ = 1 := by ring

/-- `binaryEntropy` in natural-log form on `(0,1)`. -/
theorem binaryEntropy_mul_log_two {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) :
    binaryEntropy δ * Real.log 2 = -(δ * Real.log δ + (1 - δ) * Real.log (1 - δ)) := by
  have hl : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  unfold binaryEntropy negPLogP log2
  have h0' : ¬ δ ≤ 0 := not_le.mpr h0
  have h1' : ¬ 1 - δ ≤ 0 := not_le.mpr (by linarith)
  simp only [h0', h1', ↓reduceIte]
  field_simp
  ring

/-- **Asymptotic Gilbert–Varshamov bound** (MacWilliams–Sloane Ch. 17 Thm 30):
for `0 < δ < 1/2`, `1 - h(δ) ≤ R_2(δ)`. In fact `(1/n) log₂ A_2(n, ⌈δn⌉) ≥ 1 - h(δ)` for every
`n ≥ 1`. -/
theorem gilbertVarshamov_le_asymptoticCodeRate {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1 / 2) :
    gilbertVarshamov δ ≤ asymptoticCodeRate 2 δ := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- per-blocklength bound
  have hn : ∀ n : ℕ, 1 ≤ n → gilbertVarshamov δ ≤
      (Real.log (maxCodeSize 2 n (Nat.ceil (δ * (n : ℝ))) : ℝ) / Real.log 2) / (n : ℝ) := by
    intro n hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    set d := Nat.ceil (δ * (n : ℝ)) with hd
    set A := maxCodeSize 2 n d
    have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by positivity)).ne'
    have hgv := gilbert_varshamov_bound (q := 2) (n := n) hd1
    simp only [Nat.add_one_sub_one, one_pow, mul_one] at hgv
    set m := d - 1
    have hdm : d = m + 1 := by omega
    have hr : Finset.range d = Finset.range (m + 1) := by rw [hdm]
    rw [hr] at hgv
    have hm : (m : ℝ) ≤ δ * n := by
      have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ δ * n)
      rw [← hd] at this
      have : (m : ℝ) = (d : ℝ) - 1 := by rw [hdm]; push_cast; ring
      linarith
    have hvol := sum_choose_mul_exp_le_one h0 h1.le n m hm
    set L := δ * Real.log δ + (1 - δ) * Real.log (1 - δ)
    set V := ∑ i ∈ Finset.range (m + 1), (n.choose i : ℝ)
    have hgvR : (2 : ℝ) ^ n ≤ (A : ℝ) * V := by
      have := (Nat.cast_le (α := ℝ)).mpr hgv
      push_cast at this
      exact this
    have hA : 0 < (A : ℝ) := by
      have := one_le_maxCodeSize (q := 2) (by norm_num) n d
      exact_mod_cast this
    have hE : 0 < Real.exp (n * L) := Real.exp_pos _
    have hkey : (2 : ℝ) ^ n * Real.exp (n * L) ≤ A := by
      calc (2 : ℝ) ^ n * Real.exp (n * L) ≤ (A : ℝ) * V * Real.exp (n * L) :=
            mul_le_mul_of_nonneg_right hgvR hE.le
        _ = A * (V * Real.exp (n * L)) := by ring
        _ ≤ A * 1 := mul_le_mul_of_nonneg_left hvol hA.le
        _ = A := mul_one _
    have hlog := Real.log_le_log (by positivity) hkey
    rw [Real.log_mul (by positivity) hE.ne', Real.log_pow, Real.log_exp] at hlog
    have hH := binaryEntropy_mul_log_two h0 (by linarith)
    rw [le_div_iff₀ hnpos, le_div_iff₀ hl2]
    unfold gilbertVarshamov
    have : (1 - binaryEntropy δ) * n * Real.log 2 = n * Real.log 2 + n * L := by
      have : (1 - binaryEntropy δ) * n * Real.log 2 =
          n * Real.log 2 - n * (binaryEntropy δ * Real.log 2) := by ring
      rw [this, hH]; ring
    rw [this]
    exact hlog
  unfold asymptoticCodeRate
  apply le_csInf
  · refine ⟨max 1 (gilbertVarshamov δ) + 1, 0, fun n _ => ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp; positivity
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast hpos
      have hA := maxCodeSize_le_pow 2 n (Nat.ceil (δ * (n : ℝ)))
      have hA1 := one_le_maxCodeSize (q := 2) (by norm_num) n (Nat.ceil (δ * (n : ℝ)))
      have h1' : Real.log (maxCodeSize 2 n (Nat.ceil (δ * (n : ℝ))) : ℝ) ≤ n * Real.log 2 := by
        rw [← Real.log_pow]
        exact Real.log_le_log (by exact_mod_cast hA1) (by exact_mod_cast hA)
      have : (Real.log (maxCodeSize 2 n (Nat.ceil (δ * (n : ℝ))) : ℝ) / Real.log 2) / (n : ℝ)
          ≤ 1 := by
        rw [div_le_one hnpos, div_le_iff₀ hl2]; linarith
      have := le_max_left 1 (gilbertVarshamov δ)
      linarith
  · rintro r ⟨N, hN⟩
    exact (hn (max N 1) (le_max_right _ _)).trans (hN _ (le_max_left _ _))

/-- The normalised binary rate term `(1/n) log₂ A_2(n,d)` lies in `[0, 1]`. -/
theorem binary_rate_term_mem_Icc (n d : ℕ) :
    0 ≤ (Real.log (maxCodeSize 2 n d : ℝ) / Real.log 2) / (n : ℝ) ∧
      (Real.log (maxCodeSize 2 n d : ℝ) / Real.log 2) / (n : ℝ) ≤ 1 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hA := maxCodeSize_le_pow 2 n d
  have hA1 := one_le_maxCodeSize (q := 2) (by norm_num) n d
  have h0 : 0 ≤ Real.log (maxCodeSize 2 n d : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hA1)
  refine ⟨by positivity, ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast hpos
    have h1' : Real.log (maxCodeSize 2 n d : ℝ) ≤ n * Real.log 2 := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by exact_mod_cast hA1) (by exact_mod_cast hA)
    rw [div_le_one hnpos, div_le_iff₀ hl2]; linarith

/-- Sanity check on `asymptoticCodeRate`: the set in its `sInf` is bounded below (by `0`),
so for `q = 2` it is a genuine `limsup`, and `R_2(δ) ∈ [0, 1]` for every `δ`. -/
theorem asymptoticCodeRate_two_mem_Icc (δ : ℝ) :
    0 ≤ asymptoticCodeRate 2 δ ∧ asymptoticCodeRate 2 δ ≤ 1 := by
  unfold asymptoticCodeRate
  have hne : (1 : ℝ) ∈ { r : ℝ | ∃ N : ℕ, ∀ n ≥ N,
      (Real.log (maxCodeSize 2 n (Nat.ceil (δ * (n : ℝ))) : ℝ) / Real.log (2 : ℕ)) / (n : ℝ)
        ≤ r } :=
    ⟨0, fun n _ => by exact_mod_cast (binary_rate_term_mem_Icc n _).2⟩
  have hlb : ∀ r ∈ { r : ℝ | ∃ N : ℕ, ∀ n ≥ N,
      (Real.log (maxCodeSize 2 n (Nat.ceil (δ * (n : ℝ))) : ℝ) / Real.log (2 : ℕ)) / (n : ℝ)
        ≤ r }, 0 ≤ r := by
    rintro r ⟨N, hN⟩
    have := hN N le_rfl
    have h0 := (binary_rate_term_mem_Icc N (Nat.ceil (δ * (N : ℝ)))).1
    push_cast at this
    linarith
  exact ⟨le_csInf ⟨1, hne⟩ hlb, csInf_le ⟨0, hlb⟩ hne⟩

end InfoTheory.Known
