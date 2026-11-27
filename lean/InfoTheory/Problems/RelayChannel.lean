import InfoTheory.Core

/-!
# Capacity of the Relay Channel (van der Meulen 1971; Cover–El Gamal 1979)

Does Cover–El Gamal's Theorem 7 (the combination of partial decode-and-forward with
compress-and-forward, CEG79) achieve the operational capacity `relayCapacity W` of every
finite-alphabet discrete memoryless relay channel `W`?

The right-hand side `coverElGamalTheorem7Rate W` is Theorem 7 in its three-constraint form,
as stated by Chong–Motani (IEEE TIT 57(3), 2011, Lemma 2) and by El Gamal–Gohari–Nair
("Achievable rates for the relay channel with orthogonal receiver components", Theorem 1):
`R` is achievable if
* `R ≤ I(X, X_r; Y | Q) - I(Y_r; V | U, X, X_r, Y, Q)`,
* `R ≤ I(X; V, Y | U, X_r, Q) + I(U; Y_r | W, X_r, Q)`,
* `R ≤ I(X; V, Y | U, X_r, Q) + I(U; Y_r | W, X_r, Q) + I(X_r; Y | W, Q) - I(Y_r; V | U, X_r, Y, Q)`,

for some `p(q) p(w|q) p(u|w,q) p(x|u,q) p(x_r|w,q) p(y, y_r | x, x_r) p(v|u,x_r,y_r,q)`.
The auxiliaries range over all finite alphabets `Fin k`.

**Statement-fix (2026-11-27).** The previous `coverElGamalTheorem7Rate` kept only the first
two constraints (without `Q`, `W`) and allowed an arbitrary joint law `P(u, x, x_r)`. That
credits compress-forward with coherent source/relay inputs, which no code can realise when the
relay's input carries compression indices. On a 4×2→6×2 channel (relay observes the
destination's noise; destination sees `X₁ ⊕ Z` and the adder `X₂ + X_r`) the capacity is `3/2`
while the old functional equals `log₂ 3`, so the old statement was false
(`attempts/relay-channel/2026-11-26-claude-opus-5-5-thm7-transcription-catalog-error.md`).
The statement now uses the faithful three-constraint form, with the conditional independence
`X ⊥ X_r | (W, Q)` built into the joint law `thm7Joint`. On that channel the faithful rate is
`3/2 = C`.

Known facts: Theorem 7 is achievable (CEG79), so `coverElGamalTheorem7Rate W ≤ relayCapacity W`
(not formalized here); `relayCapacity W ≤ relayCutsetBound W`
(`Bridge.relayCapacity_le_cutsetBound`). Equality holds on all classical capacity classes
(degraded and reversely degraded: CEG79; semideterministic: El Gamal–Aref 1982; orthogonal
sender components: El Gamal–Zahedi 2005; Cover–Kim deterministic primitive class). The cutset
bound is not tight in general (Zhang 1988; El Gamal–Gohari–Nair 2022), and Chong–Motani's
Theorem 2 (with `I(X_r; Y | U, W, Q)` in the third constraint) is at least as large as
Theorem 7; whether it is ever strictly larger is open. Both sides of the equation lie in
`[0, log₂ |Y|]` (`Known.Certificates.RelayChannel`).
-/

open scoped BigOperators

namespace InfoTheory.Problems.RelayChannel

/-- Joint law of Cover–El Gamal Theorem 7 on tuples `t = (q, w, u, x, x_r, y, y_r, v)`:
    `p(q) p(w|q) p(u|w,q) p(x|u,q) p(x_r|w,q) W(y, y_r | x, x_r) p(v|u,x_r,y_r,q)`.
    Coordinates: `t.1 = q`, `t.2.1 = w`, `t.2.2.1 = u`, `t.2.2.2.1 = x`, `t.2.2.2.2.1 = x_r`,
    `t.2.2.2.2.2.1 = y`, `t.2.2.2.2.2.2.1 = y_r`, `t.2.2.2.2.2.2.2 = v`. -/
noncomputable def thm7Joint {X Xr Y Yr Q Wc U V : Type*}
    [Fintype X] [Fintype Xr] [Fintype Y] [Fintype Yr]
    [Fintype Q] [Fintype Wc] [Fintype U] [Fintype V]
    (W : RelayChannel X Xr Y Yr) (pQ : ProbDist Q) (pW : DMC Q Wc) (pU : DMC (Wc × Q) U)
    (pX : DMC (U × Q) X) (pXr : DMC (Wc × Q) Xr) (pV : DMC (U × Xr × Yr × Q) V) :
    ProbDist (Q × Wc × U × X × Xr × Y × Yr × V) where
  pmf t :=
    pQ.pmf t.1 * pW.trans t.1 t.2.1 * pU.trans (t.2.1, t.1) t.2.2.1 *
      pX.trans (t.2.2.1, t.1) t.2.2.2.1 * pXr.trans (t.2.1, t.1) t.2.2.2.2.1 *
      W.trans (t.2.2.2.1, t.2.2.2.2.1) (t.2.2.2.2.2.1, t.2.2.2.2.2.2.1) *
      pV.trans (t.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2.2.1, t.1) t.2.2.2.2.2.2.2
  nonneg t := by
    have := pQ.nonneg t.1
    have := pW.nonneg t.1 t.2.1
    have := pU.nonneg (t.2.1, t.1) t.2.2.1
    have := pX.nonneg (t.2.2.1, t.1) t.2.2.2.1
    have := pXr.nonneg (t.2.1, t.1) t.2.2.2.2.1
    have := W.nonneg (t.2.2.2.1, t.2.2.2.2.1) (t.2.2.2.2.2.1, t.2.2.2.2.2.2.1)
    have := pV.nonneg (t.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2.2.1, t.1) t.2.2.2.2.2.2.2
    positivity
  sum_one := by
    have hW : ∀ x xr, ∑ y : Y, ∑ yr : Yr, W.trans (x, xr) (y, yr) = 1 := fun x xr => by
      rw [← Fintype.sum_prod_type]; exact W.sum_one (x, xr)
    simp only [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, pV.sum_one, mul_one]
    simp only [← Finset.sum_mul, ← Finset.mul_sum, hW, mul_one]
    simp only [← Finset.mul_sum, pXr.sum_one, mul_one, pX.sum_one, pU.sum_one, pW.sum_one]
    exact pQ.sum_one

/-- The Theorem 7 rate `min(c₁, c₂, c₃)` of a joint law on `(q, w, u, x, x_r, y, y_r, v)`:
    * `c₁ = I(X, X_r; Y | Q) - I(Y_r; V | U, X, X_r, Y, Q)`,
    * `c₂ = I(X; V, Y | U, X_r, Q) + I(U; Y_r | W, X_r, Q)`,
    * `c₃ = c₂ + I(X_r; Y | W, Q) - I(Y_r; V | U, X_r, Y, Q)`.
    (`condMutualInfo` of a law on `α × β × γ` is `I(α; β | γ)`.) -/
noncomputable def thm7MinRate {X Xr Y Yr Q Wc U V : Type*}
    [Fintype X] [Fintype Xr] [Fintype Y] [Fintype Yr]
    [Fintype Q] [Fintype Wc] [Fintype U] [Fintype V]
    (J : ProbDist (Q × Wc × U × X × Xr × Y × Yr × V)) : ℝ :=
  -- t = (q, w, u, x, xr, y, yr, v)
  let c₁ := condMutualInfo (J.map fun t =>
        ((t.2.2.2.1, t.2.2.2.2.1), t.2.2.2.2.2.1, t.1)) -
      condMutualInfo (J.map fun t =>
        (t.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2,
          (t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1, t.1)))
  let c₂ := condMutualInfo (J.map fun t =>
        (t.2.2.2.1, (t.2.2.2.2.2.2.2, t.2.2.2.2.2.1), (t.2.2.1, t.2.2.2.2.1, t.1))) +
      condMutualInfo (J.map fun t =>
        (t.2.2.1, t.2.2.2.2.2.2.1, (t.2.1, t.2.2.2.2.1, t.1)))
  let c₃ := c₂ +
      condMutualInfo (J.map fun t => (t.2.2.2.2.1, t.2.2.2.2.2.1, (t.2.1, t.1))) -
      condMutualInfo (J.map fun t =>
        (t.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2, (t.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1, t.1)))
  min c₁ (min c₂ c₃)

/-- Cover–El Gamal (1979) Theorem 7 rate (partial decode-and-forward combined with
    compress-and-forward, with time sharing `Q`) for a discrete memoryless relay channel `W`,
    in the three-constraint form of Chong–Motani (2011, Lemma 2) and El Gamal–Gohari–Nair
    (Theorem 1): the supremum of `thm7MinRate (thm7Joint W …)` over all finite auxiliary
    alphabets and all kernels of the prescribed Markov structure. -/
noncomputable def coverElGamalTheorem7Rate {X Xr Y Yr : Type*}
    [Fintype X] [Fintype Xr] [Fintype Y] [Fintype Yr]
    (W : RelayChannel X Xr Y Yr) : ℝ :=
  sSup { r : ℝ | ∃ (kQ kW kU kV : ℕ) (pQ : ProbDist (Fin kQ)) (pW : DMC (Fin kQ) (Fin kW))
    (pU : DMC (Fin kW × Fin kQ) (Fin kU)) (pX : DMC (Fin kU × Fin kQ) X)
    (pXr : DMC (Fin kW × Fin kQ) Xr) (pV : DMC (Fin kU × Xr × Yr × Fin kQ) (Fin kV)),
    r = thm7MinRate (thm7Joint W pQ pW pU pX pXr pV) }

/-- Capacity of the General Relay Channel (van der Meulen 1971; Cover–El Gamal 1979):
    Does Cover–El Gamal's Theorem 7 (partial decode-and-forward combined with
    compress-and-forward, three-constraint form) achieve the exact capacity `relayCapacity W`
    of every finite-alphabet discrete memoryless relay channel? -/
def Statement : Prop :=
  ∀ (kX kXr kY kYr : ℕ) (W : RelayChannel (Fin kX) (Fin kXr) (Fin kY) (Fin kYr)),
    relayCapacity W = coverElGamalTheorem7Rate W

def problem : OpenProblem where
  id := "relay-channel"
  title := "Capacity of the Relay Channel"
  category := .networkInfoTheory
  status := .open
  posedBy := "van der Meulen"
  posedYear := 1971
  statement := Statement

end InfoTheory.Problems.RelayChannel
