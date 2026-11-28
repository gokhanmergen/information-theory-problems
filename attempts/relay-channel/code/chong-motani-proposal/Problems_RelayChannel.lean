import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.RelayChannel

/-- Joint law of the hybrid partial-decode-forward / compress-forward scheme of Cover–El Gamal
    (1979, Thm 7) and Chong–Motani (2011, Thm 2), in the form of El Gamal–Gohari–Nair
    ("Achievable rates for the relay channel with orthogonal receiver components", eq. (7)):
    on tuples `(s, u, x, x_r, y, y_r, v)`,
    `p(s, u) · p(x | s, u) · p(x_r | s) · W(y, y_r | x, x_r) · p(v | s, u, x_r, y_r)`.
    `S` is the cooperative part known to both source and relay (called `W` by El Gamal–Gohari–Nair;
    renamed here to avoid a clash with the channel `W`), `U` is the part the relay decodes, and
    `V` is the relay's compression of `Y_r`. Given `(S, U)`, the inputs `X` and `X_r` are
    conditionally independent: the source cannot know the relay's compression index. -/
noncomputable def chongMotaniJoint {X Xr Y Yr : Type*}
    [Fintype X] [Fintype Xr] [Fintype Y] [Fintype Yr] {kS kU kV : ℕ}
    (W : RelayChannel X Xr Y Yr) (P : ProbDist (Fin kS × Fin kU))
    (pX : DMC (Fin kS × Fin kU) X) (pXr : DMC (Fin kS) Xr)
    (pV : DMC (Fin kS × Fin kU × Xr × Yr) (Fin kV)) :
    ProbDist (Fin kS × Fin kU × X × Xr × Y × Yr × Fin kV) where
  pmf := fun ⟨s, u, x, xr, y, yr, v⟩ =>
    P.pmf (s, u) * pX.trans (s, u) x * pXr.trans s xr * W.trans (x, xr) (y, yr) *
      pV.trans (s, u, xr, yr) v
  nonneg := fun ⟨s, u, x, xr, y, yr, v⟩ =>
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (P.nonneg _) (pX.nonneg _ _))
      (pXr.nonneg _ _)) (W.nonneg _ _)) (pV.nonneg _ _)
  sum_one := by
    simp only [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, pV.sum_one, mul_one]
    have hW : ∀ x xr, ∑ y : Y, ∑ yr : Yr, W.trans (x, xr) (y, yr) = 1 := fun x xr => by
      rw [← Fintype.sum_prod_type]; exact W.sum_one (x, xr)
    simp_rw [← Finset.mul_sum, hW, mul_one]
    simp_rw [← Finset.mul_sum, pXr.sum_one, mul_one]
    simp_rw [← Finset.mul_sum, pX.sum_one, mul_one]
    simpa [Fintype.sum_prod_type] using P.sum_one

/-- **Best known single-letter lower bound** on the capacity of a DM relay channel `W`:
    the Chong–Motani (IEEE Trans. IT 57(3), 2011, Thm 2) partial-decode-forward +
    compress-forward rate, in the equivalent El Gamal–Gohari–Nair form (their eq. (7), Remark 1):
    the supremum of `min {c₁, c₂, c₃}` over all finite auxiliary alphabets and all laws
    `p(s, u) p(x | s, u) p(x_r | s) W(y, y_r | x, x_r) p(v | s, u, x_r, y_r)`, where
    * `c₁ = I(X, X_r; Y) - I(Y_r; V | S, U, X, X_r, Y)`,
    * `c₂ = I(X; V, Y | S, U, X_r) + I(U; Y_r | S, X_r)`,
    * `c₃ = I(X; Y | S, U, X_r) + I(U; Y_r | S, X_r) + I(X_r; Y | S, U)
            - I(Y_r; V | S, U, X, X_r, Y)`.
    It contains Cover–El Gamal (1979) Theorem 7 (the same expression with `I(X_r; Y | S)` in
    place of `I(X_r; Y | S, U)` in `c₃`; Chong–Motani 2011, Lemma 2 and Remark 6), and hence
    direct transmission, decode-forward, partial decode-forward, compress-forward, and all of
    these with coded time-sharing. On relay channels with orthogonal receiver components it
    equals Theorem 7 (El Gamal–Gohari–Nair, Thm 3). Every point is `≤ log₂ |Y|` (since
    `c₁ ≤ I(X, X_r; Y)`) and any point with `V` constant is `≥ 0`, so for nonempty alphabets the
    `sSup` is over a nonempty set that is bounded above, and its value lies in `[0, log₂ |Y|]`. -/
noncomputable def chongMotaniRate {X Xr Y Yr : Type*}
    [Fintype X] [Fintype Xr] [Fintype Y] [Fintype Yr]
    (W : RelayChannel X Xr Y Yr) : ℝ :=
  sSup { r : ℝ | ∃ (kS kU kV : ℕ) (P : ProbDist (Fin kS × Fin kU))
      (pX : DMC (Fin kS × Fin kU) X) (pXr : DMC (Fin kS) Xr)
      (pV : DMC (Fin kS × Fin kU × Xr × Yr) (Fin kV)),
    let J := chongMotaniJoint W P pX pXr pV
    -- `I(Y_r; V | S, U, X, X_r, Y)`
    let pen := condMutualInfo (J.map fun ⟨s, u, x, xr, y, yr, v⟩ => (yr, v, (s, u, x, xr, y)))
    -- `I(X, X_r; Y) - I(Y_r; V | S, U, X, X_r, Y)`
    let c₁ := mutualInfo (J.map fun ⟨_, _, x, xr, y, _, _⟩ => ((x, xr), y)) - pen
    -- `I(X; V, Y | S, U, X_r) + I(U; Y_r | S, X_r)`
    let c₂ := condMutualInfo (J.map fun ⟨s, u, x, xr, y, _, v⟩ => (x, (v, y), (s, u, xr))) +
      condMutualInfo (J.map fun ⟨s, u, _, xr, _, yr, _⟩ => (u, yr, (s, xr)))
    -- `I(X; Y | S, U, X_r) + I(U; Y_r | S, X_r) + I(X_r; Y | S, U) - I(Y_r; V | S, U, X, X_r, Y)`
    let c₃ := condMutualInfo (J.map fun ⟨s, u, x, xr, y, _, _⟩ => (x, y, (s, u, xr))) +
      condMutualInfo (J.map fun ⟨s, u, _, xr, _, yr, _⟩ => (u, yr, (s, xr))) +
      condMutualInfo (J.map fun ⟨s, u, _, xr, y, _, _⟩ => (xr, y, (s, u))) - pen
    r = min c₁ (min c₂ c₃) }

/-- Capacity of the General Relay Channel (van der Meulen 1971; Cover–El Gamal 1979):
    is the best known single-letter lower bound tight? That is, does the Chong–Motani (2011)
    hybrid partial-decode-forward / compress-forward rate `chongMotaniRate W` (which contains
    Cover–El Gamal Theorem 7) equal the operational capacity `relayCapacity W` of every
    finite-alphabet discrete memoryless relay channel?

    The direction `chongMotaniRate W ≤ relayCapacity W` is the published achievability theorem
    (not formalized here); the open content is the converse. No finite DM relay channel is known
    on which any coding scheme provably beats this rate, and no general converse is known.
    The statement is open; it is plausible that the answer is negative.

    Statement fix (2026-11-27): the previous right-hand side `coverElGamalTheorem7Rate` was a
    mis-transcription of Theorem 7 (no `S`, an arbitrary law `p(u, x, x_r)`, and the third
    constraint dropped). It exceeded the capacity on an explicit 4×2→6×2 channel, so the old
    statement was false (`problems/relay-channel.md`, notes on the formalization). -/
def Statement : Prop :=
  ∀ (kX kXr kY kYr : ℕ) (W : RelayChannel (Fin kX) (Fin kXr) (Fin kY) (Fin kYr)),
    relayCapacity W = chongMotaniRate W

def problem : OpenProblem where
  id := "relay-channel"
  title := "Capacity of the Relay Channel"
  category := .networkInfoTheory
  status := .open
  posedBy := "van der Meulen"
  posedYear := 1971
  statement := Statement

end InfoTheory.Problems.RelayChannel
