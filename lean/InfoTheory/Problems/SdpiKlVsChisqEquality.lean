import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.SdpiKlVsChisqEquality

/-- Input-dependent KL strong data processing constant `s_KL(Q, W)`.
    While the channel-level supremum satisfies `sdpiKL W = sdpiChiSq W` for all DMCs,
    the input-dependent constant `sdpiKLAt Q W` can strictly exceed `sdpiChiSqAt Q W`. -/
noncomputable def sdpiKLAt {α β : Type*} [Fintype α] [Fintype β]
    (Q : ProbDist α) (W : DMC α β) : ℝ :=
  sSup { r : ℝ | ∃ (P : ProbDist α),
    AbsCont P Q ∧ klDivergence P Q > 0 ∧
    r = klDivergence (W.joint P).snd (W.joint Q).snd / klDivergence P Q }

/-- Input-dependent `χ²` contraction constant `s_{χ²}(Q, W) = ρ_m²(X; Y)`. -/
noncomputable def sdpiChiSqAt {α β : Type*} [Fintype α] [Fintype β]
    (Q : ProbDist α) (W : DMC α β) : ℝ :=
  sSup { r : ℝ | ∃ (P : ProbDist α),
    AbsCont P Q ∧ chiSqDivergence P Q > 0 ∧
    r = chiSqDivergence (W.joint P).snd (W.joint Q).snd / chiSqDivergence P Q }

/-- Nair (2014) exact KL characterization of the hypercontractivity ribbon `R(P_XY)` for
    `1 ≤ p ≤ q`: `(1/p) D(Q_X ‖ P_X) + (1 - 1/q) D(Q_Y ‖ P_Y) ≤ D(Q_{XY} ‖ P_{XY})`. -/
def inNairRibbon {X Y : Type*} [Fintype X] [Fintype Y]
    (P : ProbDist (X × Y)) (p q : ℝ) : Prop :=
  1 ≤ p ∧ p ≤ q ∧
  ∀ (Q : ProbDist (X × Y)),
    AbsCont Q P →
    (1 / p) * klDivergence Q.fst P.fst + (1 - 1 / q) * klDivergence Q.snd P.snd ≤
      klDivergence Q P

/-- Two-sided KL/χ² SDPI equality and hypercontractivity extremality:
    for every full-support finite bipartite source `(X, Y) ~ QX × W = QY × Wrev`, does
    two-sided equality `s_KL(QX, W) = s_{χ²}(QX, W)` and `s_KL(QY, Wrev) = s_{χ²}(QY, Wrev)`
    imply that the entire hypercontractivity ribbon coincides with the Bonami–Beckner
    hyperbola `(p - 1) / (q - 1) ≥ s_{χ²}(QX, W)`? -/
def Statement : Prop :=
  ∀ (kX kY : ℕ) (QX : ProbDist (Fin kX)) (QY : ProbDist (Fin kY))
    (W : DMC (Fin kX) (Fin kY)) (Wrev : DMC (Fin kY) (Fin kX)),
    0 < kX → 0 < kY →
    (∀ (x : Fin kX), 0 < QX.pmf x) →
    (∀ (y : Fin kY), 0 < QY.pmf y) →
    (∀ (x : Fin kX) (y : Fin kY), QX.pmf x * W.trans x y = QY.pmf y * Wrev.trans y x) →
    sdpiKLAt QX W = sdpiChiSqAt QX W →
    sdpiKLAt QY Wrev = sdpiChiSqAt QY Wrev →
    ∀ (p q : ℝ), 1 < p → p ≤ q →
      sdpiChiSqAt QX W ≤ (p - 1) / (q - 1) →
      inNairRibbon (W.joint QX) p q

def problem : OpenProblem where
  id := "sdpi-kl-vs-chisq-equality"
  title := "Equality Conditions Between KL and Chi-Squared Strong Data Processing Constants"
  category := .statisticalInfoTheory
  status := .open
  posedBy := "Rudolf Ahlswede and Péter Gács; Venkat Anantharam, Amin Gohari, Sudeep Kamath, and Chandra Nair"
  posedYear := 1976
  statement := Statement

end InfoTheory.Problems.SdpiKlVsChisqEquality
