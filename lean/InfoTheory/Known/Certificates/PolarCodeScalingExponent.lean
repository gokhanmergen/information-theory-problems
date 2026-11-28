import InfoTheory.Problems.PolarCodeScalingExponent

/-!
# Certificate for `InfoTheory.Problems.PolarCodeScalingExponent`

The (fixed, 2026-11-27) statement asks whether a single fixed binary kernel achieves SC scaling
exponent `2 + ε` on every `BSC(p)`, `0 < p < 1/2`, with the decoder pinned to Arıkan's SC rule
`scDecoder` (bit-channel likelihood comparison, future bits summed over).

Certified here, about these exact objects:
* `arikan_invertible` — Arıkan's kernel `G₂ = [[1,0],[1,1]]` satisfies `IsInvertibleKernel`
  (so the kernel class is the intended `GL_ℓ(𝔽₂)` and is nonempty);
* `polarSCBlockError_nonneg`, `polarSCBlockError_empty` — the error functional is a genuine
  nonnegative quantity, vanishing for the empty information set;
* **regression** (blocklength `N = 1`, the uncoded bit): `bitChannelLik_uncoded` — for `m = 0`
  the bit-channel likelihood is the channel law `W(y | b)`, and `scError_uncoded` — the SC
  decoder with `A = {the bit}` has block error exactly `p` on `BSC(p)`, `p < 1/2` (the ML error
  of one uncoded BSC use). This checks that `polarIdx`, `polarEncode`, `bitChannelLik`,
  `scDecoder` and the genie-aided `polarSCBlockError` compose to the right number.

Not certified: channel polarization, the Hassani–Alishahi–Urbanke `3.579 ≤ μ(G₂) ≤ 4.714`
bounds, the Fazeli–Hassani–Mondelli–Vardy BEC result, or any scaling statement on the BSC.
The `Statement` is not settled by these facts.
-/

open scoped BigOperators

namespace InfoTheory.Known.Certificates.PolarCodeScalingExponent

open InfoTheory InfoTheory.Problems.PolarCodeScalingExponent

/-- Arıkan's kernel `G₂ = [[1,0],[1,1]]`. -/
def arikanKernel : Fin 2 → Fin 2 → ZMod 2 := fun i j => if j ≤ i then 1 else 0

/-- Arıkan's kernel is its own inverse over `𝔽₂`. -/
theorem arikan_invertible : IsInvertibleKernel 2 arikanKernel :=
  ⟨arikanKernel, by decide⟩

theorem encode_zero (G : Fin 2 → Fin 2 → ZMod 2) (u : (Fin 0 → Fin 2) → ZMod 2)
    (j : Fin 0 → Fin 2) : polarEncode 2 0 G u j = u j := by
  simp only [polarEncode, Finset.univ_unique, Finset.prod_empty, Finset.univ_eq_empty, mul_one,
    Finset.sum_singleton]
  exact congrArg u (Subsingleton.elim _ _)

theorem bitChannelLik_uncoded (G : Fin 2 → Fin 2 → ZMod 2) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (t : Fin (2 ^ 0)) (y : (Fin 0 → Fin 2) → Bool) (pre : Fin t.1 → ZMod 2) (b : ZMod 2) :
    bitChannelLik 2 0 two_pos G p hp0 hp1 t y pre b =
      (bsc p hp0 hp1).trans (decide (b = 1)) (y default) := by
  have ht : t.1 = 0 := by have := t.isLt; simp at this; omega
  rw [bitChannelLik, ← (Equiv.funUnique (Fin 0 → Fin 2) (ZMod 2)).symm.sum_comp]
  simp [encode_zero, Subsingleton.elim (polarIdx 2 0 two_pos t) default]
  exact congrArg _ (congrArg y (Subsingleton.elim _ _))

theorem sum_fun_unique {ι X M : Type*} [Unique ι] [Fintype X] [Fintype (ι → X)]
    [AddCommMonoid M] (f : (ι → X) → M) : ∑ x, f x = ∑ b : X, f (fun _ => b) :=
  Fintype.sum_equiv (Equiv.funUnique ι X) f _ fun x =>
    congrArg f (funext fun i => by rw [Subsingleton.elim i default]; rfl)

theorem sum_zmod2 (f : ZMod 2 → ℝ) : ∑ b, f b = f 0 + f 1 := Fin.sum_univ_two f

theorem t_eq (t : Fin (2 ^ 0)) : t = ⟨0, by norm_num⟩ := Fin.ext (by have := t.isLt; simp at this; omega)

theorem scError_uncoded (G : Fin 2 → Fin 2 → ZMod 2) (p : ℝ) (hp0 : 0 ≤ p) (hp : p < 1 / 2) :
    polarSCBlockError 2 0 two_pos G Finset.univ p hp0 (by linarith)
      (scDecoder 2 0 two_pos G p hp0 (by linarith)) = p := by
  have hex : ∀ (P : Fin (2 ^ 0) → Prop), (∃ t, P t) ↔ P ⟨0, by norm_num⟩ :=
    fun P => ⟨fun ⟨t, ht⟩ => t_eq t ▸ ht, fun h => ⟨_, h⟩⟩
  simp only [polarSCBlockError, scDecoder, bitChannelLik_uncoded, encode_zero, hex, Finset.mem_univ, true_and,
    Finset.card_univ]
  simp only [not_true_eq_false, false_implies, implies_true]
  rw [Finset.filter_true_of_mem (fun _ _ => trivial), sum_fun_unique]
  simp only [sum_fun_unique, Fintype.prod_unique, Fintype.card_unique, pow_one]
  simp only [sum_zmod2, Fintype.sum_bool]
  have c1 : p + p < 1 := by linarith
  have c2 : ¬ (1 - p < p) := by linarith
  have c3 : ¬ (1 ≤ p + p) := by linarith
  have c4 : p ≤ 1 - p := by linarith
  simp [bsc, c1, c2, c3, c4]
  ring

theorem polarSCBlockError_nonneg (ℓ m : ℕ) (hℓ : 0 < ℓ) (G : Fin ℓ → Fin ℓ → ZMod 2)
    (A : Finset (Fin m → Fin ℓ)) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (dec : ∀ t : Fin (ℓ ^ m), ((Fin m → Fin ℓ) → Bool) → (Fin t.1 → ZMod 2) → ZMod 2) :
    0 ≤ polarSCBlockError ℓ m hℓ G A p hp0 hp1 dec := by
  unfold polarSCBlockError
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun y _ => ?_)
  split_ifs
  · exact Finset.prod_nonneg fun j _ => (bsc p hp0 hp1).nonneg _ _
  · exact le_rfl

theorem polarSCBlockError_empty (ℓ m : ℕ) (hℓ : 0 < ℓ) (G : Fin ℓ → Fin ℓ → ZMod 2)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (dec : ∀ t : Fin (ℓ ^ m), ((Fin m → Fin ℓ) → Bool) → (Fin t.1 → ZMod 2) → ZMod 2) :
    polarSCBlockError ℓ m hℓ G ∅ p hp0 hp1 dec = 0 := by
  unfold polarSCBlockError
  simp

end InfoTheory.Known.Certificates.PolarCodeScalingExponent
