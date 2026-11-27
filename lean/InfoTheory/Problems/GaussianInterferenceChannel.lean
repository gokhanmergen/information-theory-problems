import InfoTheory.Core

open scoped BigOperators Classical
open MeasureTheory

/-!
# Exact capacity region of the two-user Gaussian interference channel

Channel: `Y₁ = X₁ + a X₂ + Z₁`, `Y₂ = b X₁ + X₂ + Z₂`, `Zᵢ ~ N(0, 1)` independent, average
power constraints `P₁, P₂`; receiver `i` decodes only message `i`.

**Statement-fix (2026-11-27).**  The previous frozen statement compared the capacity region
with the *convex hull* of single-phase Gaussian Han–Kobayashi (HK) polytopes under power
control (plain time-sharing).  That set is strictly smaller than Gaussian HK with a coded
time-sharing variable `Q`, which is achievable: at `a = b = 1/2`, `P₁ = P₂ = 100` coded
time-sharing reaches sum rate `3.9229`, whereas the convex hull stays `≤ 3.8356`
(`attempts/gaussian-interference-channel/2026-11-26-claude-opus-5-5-coded-time-sharing-catalog-error.md`).
So the old statement was false as written.  The region below is the HK region *with a
time-sharing variable* `Q` (finite support, `ℙ(Q = i) = w i`), Gaussian superposition inputs
`Xⱼ = Uⱼ + Vⱼ` in each phase, and power control across phases
(`𝔼_Q[Pⱼc(Q) + Pⱼp(Q)] ≤ Pⱼ`): each of the seven right-hand sides of the compact HK region
(Chong–Motani–Garg 2008; Kobayashi–Han 2007; El Gamal–Kim Thm 6.4) is averaged over `Q`
separately.  This is `ℛ_{HK-GS}` of Costa–Gohari–Nair–Ng (ISIT 2023, Def. 2), extended from
the Z-channel to the two-sided channel.  The question "does Gaussian HK with time-sharing and
power control achieve capacity?" is posed in that paper ("it is still unknown whether the HK
achievable region (restricted to Gaussian inputs and allowing for power control) represents the
capacity region") and is open even for the Z-channel.

**Known facts** (it is known that `HK-GS ⊆ capacity region`, with equality in the cases below):
* the region contains `(0, 0)` and the old convex-hull region (certified);
* every point satisfies `Rⱼ ≤ ½ log₂(1 + Pⱼ)` (certified), so it is bounded;
* `a = b = 0` (two separate AWGN links): the region is exactly
  `[0, ½ log₂(1 + P₁)] × [0, ½ log₂(1 + P₂)]` (certified), which is the capacity region;
* strong interference `a² ≥ 1, b² ≥ 1` (Sato 1981; Han–Kobayashi 1981): equality;
* sum capacity is attained in the noisy-interference, mixed and Z regimes
  (Shang–Kramer–Chen, Motahari–Khandani, Annapureddy–Veeravalli 2009), and the region is within
  one bit of capacity everywhere (Etkin–Tse–Wang 2008);
* the achievability `HK-GS ⊆ capacity` (Han–Kobayashi 1981 with `Q`, Gaussian inputs) is
  classical but not formalized here.
-/

namespace InfoTheory.Problems.GaussianInterferenceChannel

/-- Single-letter Gaussian Han–Kobayashi rate polytope for one fixed power split
    `P₁ = P₁c + P₁p`, `P₂ = P₂c + P₂p` (common/private), without time-sharing: the seven
    compact HK inequalities (Chong–Motani–Garg 2008; El Gamal–Kim Thm 6.4) evaluated at
    independent Gaussian `Uⱼ ~ N(0, Pⱼc)`, `Vⱼ ~ N(0, Pⱼp)`.  This is the `m = 1` case of
    `InGaussianHKRegion`. -/
def InGaussianHKBasic (a b P₁ P₂ R₁ R₂ : ℝ) : Prop :=
  0 ≤ R₁ ∧ 0 ≤ R₂ ∧
  ∃ (P₁c P₁p P₂c P₂p : ℝ),
    0 ≤ P₁c ∧ 0 ≤ P₁p ∧ P₁c + P₁p ≤ P₁ ∧
    0 ≤ P₂c ∧ 0 ≤ P₂p ∧ P₂c + P₂p ≤ P₂ ∧
    let cap (s : ℝ) : ℝ := (1 / 2 : ℝ) * log2 (1 + s)
    let N₁ := 1 + a ^ 2 * P₂p
    let N₂ := 1 + b ^ 2 * P₁p
    R₁ ≤ cap ((P₁c + P₁p) / N₁) ∧
    R₂ ≤ cap ((P₂c + P₂p) / N₂) ∧
    R₁ + R₂ ≤ cap ((P₁c + P₁p + a ^ 2 * P₂c) / N₁) + cap (P₂p / N₂) ∧
    R₁ + R₂ ≤ cap (P₁p / N₁) + cap ((P₂c + P₂p + b ^ 2 * P₁c) / N₂) ∧
    R₁ + R₂ ≤ cap ((P₁p + a ^ 2 * P₂c) / N₁) + cap ((P₂p + b ^ 2 * P₁c) / N₂) ∧
    2 * R₁ + R₂ ≤ cap ((P₁c + P₁p + a ^ 2 * P₂c) / N₁) + cap (P₁p / N₁) +
                  cap ((P₂p + b ^ 2 * P₁c) / N₂) ∧
    R₁ + 2 * R₂ ≤ cap ((P₂c + P₂p + b ^ 2 * P₁c) / N₂) + cap (P₂p / N₂) +
                  cap ((P₁p + a ^ 2 * P₂c) / N₁)

/-- Gaussian Han–Kobayashi region **with a coded time-sharing variable `Q`** and power
    control (`ℛ_{HK-GS}`, Costa–Gohari–Nair–Ng 2023, Def. 2, for the two-sided channel).
    `Q` takes values in `Fin m` with `ℙ(Q = i) = w i`; in phase `i` user `j` sends
    `Xⱼ = Uⱼ + Vⱼ` with independent Gaussian common/private parts of powers `Pⱼc i`, `Pⱼp i`,
    subject to the *average* power constraints `∑ᵢ w i (Pⱼc i + Pⱼp i) ≤ Pⱼ`.  Each of the seven
    compact HK right-hand sides is averaged over `Q` **separately** (`E f = ∑ᵢ w i f i`); this is
    what distinguishes coded time-sharing from the convex hull of single-phase polytopes. -/
def InGaussianHKRegion (a b P₁ P₂ R₁ R₂ : ℝ) : Prop :=
  0 ≤ R₁ ∧ 0 ≤ R₂ ∧
  ∃ (m : ℕ) (w P₁c P₁p P₂c P₂p : Fin m → ℝ),
    (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
    (∀ i, 0 ≤ P₁c i ∧ 0 ≤ P₁p i ∧ 0 ≤ P₂c i ∧ 0 ≤ P₂p i) ∧
    (∑ i, w i * (P₁c i + P₁p i) ≤ P₁) ∧ (∑ i, w i * (P₂c i + P₂p i) ≤ P₂) ∧
    let cap (s : ℝ) : ℝ := (1 / 2 : ℝ) * log2 (1 + s)
    let E (f : Fin m → ℝ) : ℝ := ∑ i, w i * f i
    let N₁ := fun i => 1 + a ^ 2 * P₂p i
    let N₂ := fun i => 1 + b ^ 2 * P₁p i
    R₁ ≤ E (fun i => cap ((P₁c i + P₁p i) / N₁ i)) ∧
    R₂ ≤ E (fun i => cap ((P₂c i + P₂p i) / N₂ i)) ∧
    R₁ + R₂ ≤ E (fun i => cap ((P₁c i + P₁p i + a ^ 2 * P₂c i) / N₁ i) +
                          cap (P₂p i / N₂ i)) ∧
    R₁ + R₂ ≤ E (fun i => cap (P₁p i / N₁ i) +
                          cap ((P₂c i + P₂p i + b ^ 2 * P₁c i) / N₂ i)) ∧
    R₁ + R₂ ≤ E (fun i => cap ((P₁p i + a ^ 2 * P₂c i) / N₁ i) +
                          cap ((P₂p i + b ^ 2 * P₁c i) / N₂ i)) ∧
    2 * R₁ + R₂ ≤ E (fun i => cap ((P₁c i + P₁p i + a ^ 2 * P₂c i) / N₁ i) +
                              cap (P₁p i / N₁ i) +
                              cap ((P₂p i + b ^ 2 * P₁c i) / N₂ i)) ∧
    R₁ + 2 * R₂ ≤ E (fun i => cap ((P₂c i + P₂p i + b ^ 2 * P₁c i) / N₂ i) +
                              cap (P₂p i / N₂ i) +
                              cap ((P₁p i + a ^ 2 * P₂c i) / N₁ i))

/-- Operational Gaussian IC achievability with measurable decoders, per-codeword power
    constraints `∑ᵢ xᵢ² ≤ n Pⱼ`, and average error over both messages evaluated via Lebesgue
    `lintegral` against the i.i.d. `N(0, 1)` noise densities (a value in `[0, 1]`, so `toReal`
    is not a junk value). -/
def InGaussianICAchievable (a b P₁ P₂ R₁ R₂ : ℝ) : Prop :=
  0 ≤ R₁ ∧ 0 ≤ R₂ ∧
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    let M₁ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₁)))
    let M₂ := Nat.max 1 (Nat.floor ((2 : ℝ) ^ ((n : ℝ) * R₂)))
    ∃ (enc₁ : Fin M₁ → Fin n → ℝ) (enc₂ : Fin M₂ → Fin n → ℝ)
      (dec₁ : (Fin n → ℝ) → Fin M₁) (dec₂ : (Fin n → ℝ) → Fin M₂),
      Measurable dec₁ ∧ Measurable dec₂ ∧
      (∀ m₁, (∑ i : Fin n, (enc₁ m₁ i) ^ 2) ≤ (n : ℝ) * P₁) ∧
      (∀ m₂, (∑ i : Fin n, (enc₂ m₂ i) ^ 2) ≤ (n : ℝ) * P₂) ∧
      let errProb (m₁ : Fin M₁) (m₂ : Fin M₂) : ℝ :=
        (∫⁻ z₁ : Fin n → ℝ, ∫⁻ z₂ : Fin n → ℝ,
          let g₁ := ∏ i : Fin n, gaussianPdf1D 1 (z₁ i)
          let g₂ := ∏ i : Fin n, gaussianPdf1D 1 (z₂ i)
          let y₁ := fun i => enc₁ m₁ i + a * enc₂ m₂ i + z₁ i
          let y₂ := fun i => b * enc₁ m₁ i + enc₂ m₂ i + z₂ i
          if dec₁ y₁ ≠ m₁ ∨ dec₂ y₂ ≠ m₂ then ENNReal.ofReal (g₁ * g₂) else 0).toReal
      ((1 : ℝ) / ((M₁ * M₂ : ℕ) : ℝ)) * ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, errProb m₁ m₂ ≤ ε

/-- Exact Capacity Region of the Two-User Gaussian Interference Channel (Ahlswede; Carleial 1974;
    Han–Kobayashi 1981; Costa–Gohari–Nair–Ng 2023): does the closure of the Gaussian
    Han–Kobayashi region with coded time-sharing and power control equal the closed capacity
    region for all nonnegative coupling coefficients `(a, b)` (standard form) and positive
    powers `(P₁, P₂)`? Cross gains are restricted to `a, b ≥ 0`, as in the literature: the
    Gaussian HK region depends only on `a², b²`, while sign changes of the inputs/outputs only
    map `(a, b) ↦ (-a, -b)`, so no published result covers the sign of `ab`. -/
def Statement : Prop :=
  ∀ (a b P₁ P₂ : ℝ), 0 ≤ a → 0 ≤ b → 0 < P₁ → 0 < P₂ →
    closure { p : ℝ × ℝ | InGaussianICAchievable a b P₁ P₂ p.1 p.2 } =
      closure { p : ℝ × ℝ | InGaussianHKRegion a b P₁ P₂ p.1 p.2 }

def problem : OpenProblem where
  id := "gaussian-interference-channel"
  title := "Exact Capacity Region of the Two-User Gaussian Interference Channel"
  category := .networkInfoTheory
  status := .partiallySolved
  posedBy := "Ahlswede; Carleial"
  posedYear := 1974
  statement := Statement

end InfoTheory.Problems.GaussianInterferenceChannel
