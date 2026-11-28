import InfoTheory.Problems.SecretSharingOptimalInfoRatio
import InfoTheory.Known

/-!
# Certificate for `InfoTheory.Problems.SecretSharingOptimalInfoRatio`

The frozen statement asks whether the optimal information ratio
`optimalSecretSharingRatio Γ` (an `sInf` over perfect schemes with finite share alphabets)
grows super-linearly in the number `n` of participants for some family of access structures.

## Certified (about exactly these objects)
* `exists_essential` — every access structure has an *essential* participant `i` and an
  unqualified set `B ∌ i` with `B ∪ {i}` qualified (a minimal qualified set exists).
* `one_le_of_mem` — **share-size lower bound** (Karnin–Greene–Hellman 1983; Capocelli et al.
  1993): every admissible ratio `r` in the defining set satisfies `1 ≤ r`, i.e. in every
  perfect scheme some share is at least as large as the secret, `H(S_i) ≥ H(S_0)`. Proved from
  the Shannon inequalities (`subsetEntropyVec_mono`, `subsetEntropyVec_submod`). Hence
  `optimalSecretSharingRatio Γ ≥ 1` whenever a scheme exists, so the `sInf` is not the junk
  value `0` on realizable structures (`one_le_optimalSecretSharingRatio`).
* `optimalSecretSharingRatio_oneOfN` — **regression**: for the `1`-out-of-`(n+1)` threshold
  structure (every nonempty set qualified) the optimal ratio is exactly `1` (give every
  participant a copy of a uniform secret bit; Shamir 1979 / Blakley 1979 ideal schemes).

## Not certified
* The Csirmaz (1997) `Ω(n / log n)` lower bound and the Csirmaz polymatroid barrier `≤ n`.
* Existence of a scheme for *every* access structure (Ito–Saito–Nishizeki 1987), and the
  `2^{0.585 n + o(n)}` upper bounds.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.SecretSharingOptimalInfoRatio

open InfoTheory InfoTheory.Known InfoTheory.Problems.SecretSharingOptimalInfoRatio

/-- The embedding `Fin n ↪ Fin (n + 1)`, `i ↦ i + 1`, used in `optimalSecretSharingRatio`. -/
def succE (n : ℕ) : Fin n ↪ Fin (n + 1) := ⟨Fin.succ, Fin.succ_injective n⟩

/-- Every access structure has an essential participant: some `i ∉ B` with `B` unqualified
    and `insert i B` qualified. -/
theorem exists_essential {n : ℕ} (Γ : AccessStructure n) :
    ∃ (i : Fin n) (B : Finset (Fin n)), i ∉ B ∧ ¬ Γ.qualified B ∧ Γ.qualified (insert i B) := by
  classical
  have key : ∀ A : Finset (Fin n), Γ.qualified A →
      ∃ (i : Fin n) (B : Finset (Fin n)), i ∉ B ∧ ¬ Γ.qualified B ∧
        Γ.qualified (insert i B) := by
    intro A
    induction A using Finset.induction_on with
    | empty => intro h; exact absurd h Γ.empty_unqualified
    | insert a A ha ih =>
      intro hq
      by_cases hA : Γ.qualified A
      · exact ih hA
      · exact ⟨a, A, ha, hA, hq⟩
  exact key _ Γ.nonempty_qualified

/-- **Share-size lower bound** (Karnin–Greene–Hellman 1983): in any perfect scheme for `Γ`,
    some participant's share entropy is at least the secret entropy, so any `r` bounding all
    ratios `H(S_i)/H(S_0)` satisfies `1 ≤ r`. -/
theorem one_le_of_scheme {n k : ℕ} (Γ : AccessStructure n) (P : ProbDist (Fin (n + 1) → Fin k))
    (r : ℝ) (h0 : 0 < subsetEntropyVec P {0})
    (hcond : ∀ A : Finset (Fin n),
      (Γ.qualified A → subsetEntropyVec P (insert 0 (A.map (succE n))) -
          subsetEntropyVec P (A.map (succE n)) = 0) ∧
      (¬ Γ.qualified A → subsetEntropyVec P (insert 0 (A.map (succE n))) -
          subsetEntropyVec P (A.map (succE n)) = subsetEntropyVec P {0}))
    (hr : ∀ i : Fin n, subsetEntropyVec P {i.succ} / subsetEntropyVec P {0} ≤ r) : 1 ≤ r := by
  classical
  obtain ⟨i, B, hiB, hB, hq⟩ := exists_essential Γ
  set H := subsetEntropyVec P with hH
  set B' := B.map (succE n) with hB'
  have hs : i.succ ∉ B' := by
    intro h
    rw [hB', Finset.mem_map] at h
    obtain ⟨j, hj, hji⟩ := h
    exact hiB ((Fin.succ_injective n hji) ▸ hj)
  have hmapins : (insert i B).map (succE n) = insert i.succ B' := by
    rw [Finset.map_insert]; rfl
  have c1 := (hcond (insert i B)).1 hq
  rw [hmapins] at c1
  have c2 := (hcond B).2 hB
  have hmono : H (insert 0 B') ≤ H (insert 0 (insert i.succ B')) :=
    subsetEntropyVec_mono P (Finset.insert_subset_insert _ (Finset.subset_insert _ _))
  have hsub := subsetEntropyVec_submod P {i.succ} B'
  have hu : ({i.succ} : Finset (Fin (n + 1))) ∪ B' = insert i.succ B' := by
    rw [Finset.insert_eq]
  have hi : ({i.succ} : Finset (Fin (n + 1))) ∩ B' = ∅ := by
    rw [Finset.singleton_inter_of_notMem hs]
  rw [hu, hi, subsetEntropyVec_empty] at hsub
  have hkey : H {0} ≤ H {i.succ} := by
    have : H {0} = H (insert 0 B') - H B' := c2.symm
    linarith
  have h1 : 1 ≤ H {i.succ} / H {0} := by
    rw [le_div_iff₀ h0]; linarith
  exact h1.trans (hr i)

/-- Every element of the set defining `optimalSecretSharingRatio Γ` is at least `1`. -/
theorem one_le_of_mem {n : ℕ} (Γ : AccessStructure n) {r : ℝ}
    (hr : r ∈ { r : ℝ | ∃ (k : ℕ) (P : ProbDist (Fin (n + 1) → Fin k)),
      let H (S : Finset (Fin (n + 1))) : ℝ := subsetEntropyVec P S
      0 < H {0} ∧
      (∀ A : Finset (Fin n),
        let A' : Finset (Fin (n + 1)) := A.map ⟨Fin.succ, Fin.succ_injective n⟩
        (Γ.qualified A → H (insert 0 A') - H A' = 0) ∧
        (¬ Γ.qualified A → H (insert 0 A') - H A' = H {0})) ∧
      ∀ i : Fin n, H {i.succ} / H {0} ≤ r }) : 1 ≤ r := by
  obtain ⟨k, P, h0, hc, hi⟩ := hr
  exact one_le_of_scheme Γ P r h0 hc hi

/-- If `Γ` admits at least one perfect scheme, then `optimalSecretSharingRatio Γ ≥ 1`. -/
theorem one_le_optimalSecretSharingRatio {n : ℕ} (Γ : AccessStructure n)
    (hne : ∃ r, r ∈ { r : ℝ | ∃ (k : ℕ) (P : ProbDist (Fin (n + 1) → Fin k)),
      let H (S : Finset (Fin (n + 1))) : ℝ := subsetEntropyVec P S
      0 < H {0} ∧
      (∀ A : Finset (Fin n),
        let A' : Finset (Fin (n + 1)) := A.map ⟨Fin.succ, Fin.succ_injective n⟩
        (Γ.qualified A → H (insert 0 A') - H A' = 0) ∧
        (¬ Γ.qualified A → H (insert 0 A') - H A' = H {0})) ∧
      ∀ i : Fin n, H {i.succ} / H {0} ≤ r }) :
    1 ≤ optimalSecretSharingRatio Γ :=
  le_csInf hne fun _ hr => one_le_of_mem Γ hr

/-! ### Regression: the `1`-out-of-`(n+1)` threshold structure has ratio exactly `1` -/

/-- The `1`-out-of-`(n+1)` threshold access structure: every nonempty set is qualified. -/
def oneOfN (n : ℕ) : AccessStructure (n + 1) where
  qualified A := A.Nonempty
  monotone _ _ hAB hA := hA.mono hAB
  nonempty_qualified := Finset.univ_nonempty
  empty_unqualified := Finset.not_nonempty_empty

/-- Pushforward composition `(P.map f).map g = P.map (g ∘ f)` (same proof as
    `InfoTheory.Bridge.map_comp_eq`; restated to avoid importing all of `Bridge`). -/
theorem map_comp_eq' {α β δ : Type*} [Fintype α] [Fintype β] [Fintype δ] (P : ProbDist α)
    (f : α → β) (g : β → δ) : (P.map f).map g = P.map (g ∘ f) := by
  classical
  unfold ProbDist.map
  congr
  funext d
  simp only [Function.comp_apply]
  trans (∑ b : β, ∑ a : α, if g b = d ∧ f a = b then P.pmf a else 0)
  · refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hgb : g b = d
    · simp [hgb]
    · simp [hgb]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single (f a)]
    · simp
    · intro b _ hne; simp [hne.symm]
    · intro h; exact absurd (Finset.mem_univ _) h

/-- The replication scheme: a uniform secret bit, copied to every participant. -/
noncomputable def replScheme (m : ℕ) : ProbDist (Fin m → Fin 2) :=
  (ProbDist.uniform : ProbDist (Fin 2)).map (fun b _ => b)

theorem replScheme_entropy_nonempty (m : ℕ) {S : Finset (Fin m)} (hS : S.Nonempty) :
    subsetEntropyVec (replScheme m) S = 1 := by
  obtain ⟨j, hj⟩ := hS
  show shannonEntropy ((replScheme m).map (fun x (i : S) => x i.1)) = 1
  rw [replScheme, map_comp_eq', InfoTheory.Known.Operational.shannonEntropy_map_of_injective,
    shannonEntropy_uniform]
  · simp only [Fintype.card_fin, log2]; norm_num
  · intro b b' h
    exact congrFun h ⟨j, hj⟩

theorem replScheme_entropy (m : ℕ) (S : Finset (Fin m)) :
    subsetEntropyVec (replScheme m) S = if S.Nonempty then 1 else 0 := by
  split_ifs with h
  · exact replScheme_entropy_nonempty m h
  · rw [Finset.not_nonempty_iff_eq_empty.1 h]; exact subsetEntropyVec_empty _

/-- **Regression:** `σ(1-out-of-(n+1)) = 1`. -/
theorem optimalSecretSharingRatio_oneOfN (n : ℕ) :
    optimalSecretSharingRatio (oneOfN n) = 1 := by
  have hmem : (1 : ℝ) ∈ { r : ℝ | ∃ (k : ℕ) (P : ProbDist (Fin (n + 1 + 1) → Fin k)),
      let H (S : Finset (Fin (n + 1 + 1))) : ℝ := subsetEntropyVec P S
      0 < H {0} ∧
      (∀ A : Finset (Fin (n + 1)),
        let A' : Finset (Fin (n + 1 + 1)) := A.map ⟨Fin.succ, Fin.succ_injective (n + 1)⟩
        ((oneOfN n).qualified A → H (insert 0 A') - H A' = 0) ∧
        (¬ (oneOfN n).qualified A → H (insert 0 A') - H A' = H {0})) ∧
      ∀ i : Fin (n + 1), H {i.succ} / H {0} ≤ r } := by
    refine ⟨2, replScheme (n + 2), ?_, ?_, ?_⟩
    · simp only [replScheme_entropy, Finset.singleton_nonempty, ite_true]; norm_num
    · intro A
      simp only [replScheme_entropy, Finset.insert_nonempty, ite_true, oneOfN,
        Finset.map_nonempty, Finset.singleton_nonempty]
      constructor
      · intro h; simp [h]
      · intro h; simp [h]
    · intro i
      simp [replScheme_entropy]
  refine le_antisymm ?_ (one_le_optimalSecretSharingRatio _ ⟨1, hmem⟩)
  exact csInf_le ⟨1, fun _ hr => one_le_of_mem _ hr⟩ hmem

end InfoTheory.Known.Certificates.SecretSharingOptimalInfoRatio
