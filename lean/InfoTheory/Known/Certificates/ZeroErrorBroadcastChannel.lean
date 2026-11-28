import InfoTheory.Problems.ZeroErrorBroadcastChannel
import InfoTheory.Known

/-!
# Certificate for `InfoTheory.Problems.ZeroErrorBroadcastChannel`

The frozen statement asks whether the pentagon has a free lunch:
`∃ ρ > 0, InPentagonRegion ρ (log₂ 5 / 2)`. Here `InPentagonRegion` is the closed zero-error
capacity region `C(K̄₅, C₅)` of the broadcast channel with a noiseless receiver and a `C₅`
receiver (Hu–Shayevitz 2017, Problems 1(ii) and 2).

Certified here, about the exact objects in `Statement`:
* `isPentagonBroadcastCode_shannon`: Shannon's code `{(i, 2i)}` is a zero-error
  `(n, M₁, M₂) = (2, 1, 5)` code (checked by `decide`);
* `isPentagonBroadcastCode_noiseless`: the trivial `(1, 5, 1)` code serving only the
  noiseless receiver;
* `inPentagonRegion_zero_half_log5`: `(0, ½ log₂ 5) ∈ C(K̄₅, C₅)`. The `Statement`'s condition
  holds at `ρ = 0`, so the question is exactly whether `ρ*(C₅) > 0`;
* `inPentagonRegion_log5_zero`: `(log₂ 5, 0) ∈ C(K̄₅, C₅)` (the other corner);
* `card_le_indepNumber_of_code`: every code has `M₂ ≤ α(C₅^{⊠n})`, so the `C₅` receiver alone
  sees the single-user zero-error problem;
* `card_le_sqrt5_pow_of_code` and `log2_card_snd_le`: `M₂ ≤ √5ⁿ`, i.e. `log₂ M₂ ≤ n · ½ log₂ 5`
  (via `Θ(C₅) = √5`, Lovász 1979);
* `inPentagonRegion_snd_le`: every `(R₁, R₂)` in the region has `R₂ ≤ ½ log₂ 5`. The
  receiver-2 target in `Statement` is the largest possible rate, `C₀(C₅) = log₂ Θ(C₅)`;
* `card_mul_card_le_of_code`: `M₁ M₂ ≤ 5ⁿ`;
* `le_half_log5_of_inPentagonRegion`: any free-lunch witness has `ρ ≤ ½ log₂ 5`.

Not certified: the time-sharing lower bound `C_ρ(C₅) ≥ ½(log₂ 5 - ρ)`, and the
Hu–Shayevitz Theorem 4 upper bound. Neither decides `ρ*(C₅) > 0`.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.ZeroErrorBroadcastChannel

open InfoTheory InfoTheory.Known InfoTheory.Problems.ZeroErrorBroadcastChannel

/-! ## `log₂` helpers -/

private lemma log2_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : log2 x ≤ log2 y :=
  div_le_div_of_nonneg_right (Real.log_le_log hx hxy) (Real.log_pos one_lt_two).le

private lemma log2_npow (x : ℝ) (n : ℕ) : log2 (x ^ n) = n * log2 x := by
  unfold log2; rw [Real.log_pow]; ring

private lemma log2_sqrt5 : log2 (Real.sqrt 5) = log2 5 / 2 := by
  unfold log2; rw [Real.log_sqrt (by norm_num)]; ring

private lemma log2_one : log2 1 = 0 := by simp [log2]

private lemma log2_mul {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    log2 (x * y) = log2 x + log2 y := by
  unfold log2; rw [Real.log_mul hx.ne' hy.ne']; ring

/-! ## Explicit codes -/

/-- Distinguishability in `C₅^{⊠n}` is decidable (for kernel `decide` on explicit codes). -/
instance decDistinguishable (n : ℕ) (x y : Fin n → ZMod 5) :
    Decidable (Distinguishable n x y) := by
  unfold Distinguishable; infer_instance

/-- Shannon's pentagon code `w ↦ (w, 2w)`, carrying no message for the noiseless receiver. -/
def shannonEnc : Fin 1 → Fin 5 → (Fin 2 → ZMod 5) := fun _ w => ![((w : ℕ) : ZMod 5), 2 * ((w : ℕ) : ZMod 5)]

/-- Shannon's code is a zero-error `(2, 1, 5)` broadcast code. -/
theorem isPentagonBroadcastCode_shannon : IsPentagonBroadcastCode 2 1 5 shannonEnc := by
  unfold IsPentagonBroadcastCode
  decide

/-- The trivial code sending `w₁` uncoded to the noiseless receiver. -/
def noiselessEnc : Fin 5 → Fin 1 → (Fin 1 → ZMod 5) := fun w _ _ => ((w : ℕ) : ZMod 5)

/-- The uncoded `(1, 5, 1)` code. -/
theorem isPentagonBroadcastCode_noiseless : IsPentagonBroadcastCode 1 5 1 noiselessEnc := by
  unfold IsPentagonBroadcastCode
  decide

/-- `(0, ½ log₂ 5)` lies in the zero-error region: the `Statement`'s condition holds at `ρ = 0`. -/
theorem inPentagonRegion_zero_half_log5 : InPentagonRegion 0 (log2 5 / 2) := by
  intro δ hδ
  refine ⟨2, 1, 5, shannonEnc, two_pos, one_pos, by norm_num,
    isPentagonBroadcastCode_shannon, ?_, ?_⟩
  · simp only [Nat.cast_one, log2_one]; push_cast; nlinarith
  · push_cast; nlinarith

/-- `(log₂ 5, 0)` lies in the zero-error region (uncoded transmission to receiver 1). -/
theorem inPentagonRegion_log5_zero : InPentagonRegion (log2 5) 0 := by
  intro δ hδ
  refine ⟨1, 5, 1, noiselessEnc, one_pos, by norm_num, one_pos,
    isPentagonBroadcastCode_noiseless, ?_, ?_⟩
  · push_cast; nlinarith
  · simp only [Nat.cast_one, log2_one]; nlinarith

/-! ## Converse facts -/

/-- The words carrying distinct receiver-2 messages (for a fixed `w₁`) form an independent set
in `C₅^{⊠n}`, so `M₂ ≤ α(C₅^{⊠n})`. -/
theorem card_le_indepNumber_of_code {n M₁ M₂ : ℕ} {enc : Fin M₁ → Fin M₂ → (Fin n → ZMod 5)}
    (h : IsPentagonBroadcastCode n M₁ M₂ enc) (hM₁ : 0 < M₁) :
    M₂ ≤ indepNumber (strongPower (cycleGraph 5) n) := by
  classical
  let w₀ : Fin M₁ := ⟨0, hM₁⟩
  let f : Fin M₂ → (Fin n → ZMod 5) := fun w₂ => enc w₀ w₂
  have hf : Function.Injective f := by
    intro a b hab
    by_contra hne
    exact (h.2 w₀ w₀ a b hne).1 hab
  have hcard : (Finset.univ.image f).card = M₂ := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  rw [← hcard]
  apply card_le_indepNumber
  intro u hu v hv
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hu hv
  obtain ⟨a, rfl⟩ := hu
  obtain ⟨b, rfl⟩ := hv
  by_cases hab : a = b
  · subst hab; exact (strongPower (cycleGraph 5) n).irrefl
  · exact (h.2 w₀ w₀ a b hab).2

/-- `M₂ ≤ √5ⁿ` for every zero-error code (Lovász's `Θ(C₅) = √5`). -/
theorem card_le_sqrt5_pow_of_code {n M₁ M₂ : ℕ} {enc : Fin M₁ → Fin M₂ → (Fin n → ZMod 5)}
    (h : IsPentagonBroadcastCode n M₁ M₂ enc) (hM₁ : 0 < M₁) (hn : 0 < n) :
    (M₂ : ℝ) ≤ Real.sqrt 5 ^ n := by
  have h1 : (M₂ : ℝ) ≤ indepNumber (strongPower (cycleGraph 5) n) := by
    exact_mod_cast card_le_indepNumber_of_code h hM₁
  have h2 := indepNumber_strongPower_rpow_le_shannonCapacity (cycleGraph 5) hn
  rw [shannonCapacity_cycle5, one_div] at h2
  have h3 : (indepNumber (strongPower (cycleGraph 5) n) : ℝ) ≤ Real.sqrt 5 ^ n := by
    have hx : (0 : ℝ) ≤ indepNumber (strongPower (cycleGraph 5) n) := Nat.cast_nonneg _
    calc (indepNumber (strongPower (cycleGraph 5) n) : ℝ)
        = ((indepNumber (strongPower (cycleGraph 5) n) : ℝ) ^ ((n : ℝ)⁻¹)) ^ n :=
          (Real.rpow_inv_natCast_pow hx hn.ne').symm
      _ ≤ Real.sqrt 5 ^ n := pow_le_pow_left₀ (Real.rpow_nonneg hx _) h2 n
  exact h1.trans h3

/-- `log₂ M₂ ≤ n · ½ log₂ 5` for every zero-error code. -/
theorem log2_card_snd_le {n M₁ M₂ : ℕ} {enc : Fin M₁ → Fin M₂ → (Fin n → ZMod 5)}
    (h : IsPentagonBroadcastCode n M₁ M₂ enc) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hn : 0 < n) :
    log2 (M₂ : ℝ) ≤ n * (log2 5 / 2) := by
  have := log2_mono (by exact_mod_cast hM₂) (card_le_sqrt5_pow_of_code h hM₁ hn)
  rwa [log2_npow, log2_sqrt5] at this

/-- Every rate pair in the region has `R₂ ≤ ½ log₂ 5 = log₂ Θ(C₅)`. -/
theorem inPentagonRegion_snd_le {R₁ R₂ : ℝ} (h : InPentagonRegion R₁ R₂) :
    R₂ ≤ log2 5 / 2 := by
  refine le_of_forall_pos_lt_add fun δ hδ => ?_
  obtain ⟨n, M₁, M₂, enc, hn, hM₁, hM₂, hc, -, h2⟩ := h (δ / 2) (by positivity)
  have hle := log2_card_snd_le hc hM₁ hM₂ hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have : (R₂ - δ / 2) * n ≤ (log2 5 / 2) * n := by linarith
  have := le_of_mul_le_mul_right this hnr
  linarith

/-- `M₁ M₂ ≤ 5ⁿ`: the encoder is injective on message pairs. -/
theorem card_mul_card_le_of_code {n M₁ M₂ : ℕ} {enc : Fin M₁ → Fin M₂ → (Fin n → ZMod 5)}
    (h : IsPentagonBroadcastCode n M₁ M₂ enc) : M₁ * M₂ ≤ 5 ^ n := by
  have hinj : Function.Injective (fun p : Fin M₁ × Fin M₂ => enc p.1 p.2) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    have hb : b = b' := by
      by_contra hne
      exact (h.2 a a' b b' hne).1 hab
    subst hb
    rw [h.1 a a' b b hab]
  have := Fintype.card_le_of_injective _ hinj
  simpa [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, ZMod.card] using this

/-- Any free-lunch witness satisfies `ρ ≤ ½ log₂ 5`. -/
theorem le_half_log5_of_inPentagonRegion {ρ : ℝ} (h : InPentagonRegion ρ (log2 5 / 2)) :
    ρ ≤ log2 5 / 2 := by
  by_contra hlt
  rw [not_le] at hlt
  set L := log2 5 / 2 with hL
  obtain ⟨n, M₁, M₂, enc, hn, hM₁, hM₂, hc, h1, h2⟩ := h ((ρ - L) / 3) (by linarith)
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hM₁r : (0 : ℝ) < M₁ := by exact_mod_cast hM₁
  have hM₂r : (0 : ℝ) < M₂ := by exact_mod_cast hM₂
  have hprod : (M₁ : ℝ) * M₂ ≤ (5 : ℝ) ^ n := by exact_mod_cast card_mul_card_le_of_code hc
  have hlog := log2_mono (mul_pos hM₁r hM₂r) hprod
  rw [log2_mul hM₁r hM₂r, log2_npow] at hlog
  have h5 : log2 5 = 2 * L := by rw [hL]; ring
  rw [h5] at hlog
  have : (ρ + L - 2 * ((ρ - L) / 3)) * n ≤ (2 * L) * n := by nlinarith
  have := le_of_mul_le_mul_right this hnr
  linarith

end InfoTheory.Known.Certificates.ZeroErrorBroadcastChannel
