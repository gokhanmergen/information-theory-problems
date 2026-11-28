import InfoTheory.Problems.TimingChannelGeneralQueue
import InfoTheory.Known

/-!
# Certificate for `InfoTheory.Problems.TimingChannelGeneralQueue`

The (2026-11-27 fixed) Statement is the Anantharam–Verdú feedback conjecture for the FIFO
`·/G/1` timing channel ("Bits through queues", IEEE Trans. IT 42(1), 1996; Sahasranand–
Tchamkerten, arXiv:2309.14145): `C(S, λ) < C_fb(S, λ)` for non-exponential service densities.
This file certifies the queueing dynamics used by the operational capacity (the Lindley
recursion and the last-departure functional that now carries the rate constraint) and the
sign of the operational capacity.

## Certified
* `lindleyDepartures_zero`, `lindleyDepartures_succ`: the recursion is
  `D₁ = max(a₁, 0) + s₁`, `D_{k+1} = max(a_{k+1}, D_k) + s_{k+1}` (queue initially empty).
* `le_lindleyDepartures`: every packet departs no earlier than its arrival plus its service
  time, `a_k + s_k ≤ D_k`.
* `lindleyDepartures_mono`: FIFO order — departures are nondecreasing when `s ≥ 0`.
* `lindleyDepartures_simultaneous`, `lastDeparture_simultaneous`: **regression** — if all
  packets arrive at time `0` the server works back-to-back and `D_k = s₁ + ⋯ + s_k`; the last
  departure is the total work `∑ sᵢ` (so the zero-rate code meets `E[D_n] = n E[S] ≤ n/λ`
  exactly when `λ ≤ 1/E[S]`, matching the Statement's range `λ < 1/E[S]`).
* `queueNoFeedbackCapacity_nonneg`: `0 ≤ C(S, λ)`.

## Not certified
* That the operational set is bounded (a converse), the achievability of `λ ln(μ/λ)` for
  exponential service, the Anantharam–Verdú identification of `queueFeedbackCapacity` with the
  operational full-feedback capacity, nonemptiness of the `sSup` in `queueFeedbackCapacity`,
  and the Sahasranand–Tchamkerten bounded-support theorem. No `ServiceDensity` is constructed
  here (the exponential density's entropy-integrability is not yet in `Known`/`Bridge`).
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.TimingChannelGeneralQueue

open InfoTheory InfoTheory.Problems.TimingChannelGeneralQueue

variable {n : ℕ} (a s : Fin n → ℝ)

theorem lindleyDepartures_zero (h : 0 < n) :
    lindleyDepartures n a s ⟨0, h⟩ = max (a ⟨0, h⟩) 0 + s ⟨0, h⟩ := rfl

theorem lindleyDepartures_succ (k : ℕ) (hk : k + 1 < n) :
    lindleyDepartures n a s ⟨k + 1, hk⟩ =
      max (a ⟨k + 1, hk⟩) (lindleyDepartures n a s ⟨k, by omega⟩) + s ⟨k + 1, hk⟩ := by
  show (if hk' : k + 1 < n then _ else _) = _
  rw [dite_eq_left_of_eq_true (eq_true hk)]
  rfl

theorem le_lindleyDepartures (i : Fin n) : a i + s i ≤ lindleyDepartures n a s i := by
  obtain ⟨k, hk⟩ := i
  cases k with
  | zero => rw [lindleyDepartures_zero]; linarith [le_max_left (a ⟨0, hk⟩) 0]
  | succ k =>
      rw [lindleyDepartures_succ a s k hk]
      linarith [le_max_left (a ⟨k + 1, hk⟩) (lindleyDepartures n a s ⟨k, by omega⟩)]

theorem lindleyDepartures_mono (hs : ∀ i, 0 ≤ s i) (k : ℕ) (hk : k + 1 < n) :
    lindleyDepartures n a s ⟨k, by omega⟩ ≤ lindleyDepartures n a s ⟨k + 1, hk⟩ := by
  rw [lindleyDepartures_succ a s k hk]
  linarith [le_max_right (a ⟨k + 1, hk⟩) (lindleyDepartures n a s ⟨k, by omega⟩),
    hs ⟨k + 1, hk⟩]

/-- **Regression.** Simultaneous arrivals at time `0`: back-to-back service,
`D_k = s₁ + ⋯ + s_k`. -/
theorem lindleyDepartures_simultaneous (hs : ∀ i, 0 ≤ s i) :
    ∀ (k : ℕ) (hk : k < n),
      lindleyDepartures n (fun _ => 0) s ⟨k, hk⟩ =
        ∑ j : Fin (k + 1), s ⟨j.1, by omega⟩
  | 0, hk => by
      rw [lindleyDepartures_zero]
      simp
  | k + 1, hk => by
      rw [lindleyDepartures_succ _ s k hk, lindleyDepartures_simultaneous hs k (by omega),
        Fin.sum_univ_castSucc (n := k + 1)]
      have hnn : 0 ≤ ∑ j : Fin (k + 1), s ⟨j.1, by omega⟩ :=
        Finset.sum_nonneg (fun j _ => hs _)
      rw [max_eq_right hnn]
      simp

/-- **Regression.** Simultaneous arrivals: the last departure is the total work. -/
theorem lastDeparture_simultaneous (hs : ∀ i, 0 ≤ s i) :
    lastDeparture n (fun _ => 0) s = ∑ i : Fin n, s i := by
  unfold lastDeparture
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · rw [dite_eq_left_of_eq_true (eq_true h), lindleyDepartures_simultaneous s hs (n - 1) (by omega)]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rfl

/-- The no-feedback capacity is nonnegative (every rate in its defining set is `≥ 0`). -/
theorem queueNoFeedbackCapacity_nonneg (S : ServiceDensity) (lam : ℝ) :
    0 ≤ queueNoFeedbackCapacity S lam :=
  Real.sSup_nonneg (fun _ hR => hR.1)

end InfoTheory.Known.Certificates.TimingChannelGeneralQueue
