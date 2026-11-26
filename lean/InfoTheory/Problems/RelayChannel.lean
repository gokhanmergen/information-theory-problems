import InfoTheory.Core

open scoped BigOperators

namespace InfoTheory.Problems.RelayChannel

/-- Combined Cover–El Gamal Theorem 7 hybrid partial-decode-and-forward + compress-and-forward
    achievable rate for a discrete memoryless relay channel `W` (El Gamal–Kim 2011, Sec. 16.7):
    strictly generalizes both `partialDecodeAndForwardRate` and `compressAndForwardRate`. -/
noncomputable def coverElGamalTheorem7Rate {X Xr Y Yr : Type*}
    [Fintype X] [Fintype Xr] [Fintype Y] [Fintype Yr]
    (W : RelayChannel X Xr Y Yr) : ℝ :=
  sSup { r : ℝ | ∃ (kU kYh : ℕ) (P : ProbDist (Fin kU × X × Xr))
    (Qcomp : DMC (Fin kU × Xr × Yr) (Fin kYh)),
    let J : ProbDist (Fin kU × X × Xr × Y × Yr × Fin kYh) :=
      { pmf := fun t =>
          P.pmf (t.1, t.2.1, t.2.2.1) *
          W.trans (t.2.1, t.2.2.1) (t.2.2.2.1, t.2.2.2.2.1) *
          Qcomp.trans (t.1, t.2.2.1, t.2.2.2.2.1) t.2.2.2.2.2
        nonneg := fun t => mul_nonneg (mul_nonneg (P.nonneg _) (W.nonneg _ _)) (Qcomp.nonneg _ _)
        sum_one := by
          simp_rw [Fintype.sum_prod_type]
          simp_rw [← Finset.mul_sum, Qcomp.sum_one, mul_one]
          have hW : ∀ x xr, ∑ y : Y, ∑ yr : Yr, W.trans (x, xr) (y, yr) = 1 := fun x xr => by
            rw [← Fintype.sum_prod_type]; exact W.sum_one (x, xr)
          simp_rw [← Finset.mul_sum, hW, mul_one]
          simpa [Fintype.sum_prod_type] using P.sum_one }
    let r1 := condMutualInfo (J.map (fun t => (t.1, t.2.2.2.2.1, t.2.2.1))) +
              condMutualInfo (J.map (fun t => (t.2.1, (t.2.2.2.1, t.2.2.2.2.2), (t.1, t.2.2.1))))
    let r2 := mutualInfo (J.map (fun t => ((t.2.1, t.2.2.1), t.2.2.2.1))) -
              condMutualInfo (J.map (fun t => (t.2.2.2.2.1, t.2.2.2.2.2, (t.1, t.2.1, t.2.2.1, t.2.2.2.1))))
    r = min r1 r2 }

/-- Capacity of the General Relay Channel (van der Meulen 1971; Cover–El Gamal 1979):
    Does Cover–El Gamal's unified Theorem 7 single-letter scheme (combining partial
    decode-and-forward with compress-and-forward) achieve the exact capacity `relayCapacity W`
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
