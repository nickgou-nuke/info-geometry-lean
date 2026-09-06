import InfoGeometry.Lie.CanonicalZornG2CartanMassieuStable
import InfoGeometry.Analytic.LogSumExpVariancePositivity

noncomputable section
open InfoGeometry.Lie.CanonicalZornG2CartanMassieuStable

namespace InfoGeometry.Lie.CanonicalZornG2MassieuConvexity

open InfoGeometry.Lie.CanonicalZornG2CartanSouriauCharacterBridge
open InfoGeometry.Analytic

variable {State : Type*} [Fintype State] [Nonempty State]
  (D : CartanSouriauDatum State)

theorem second_partial_nonneg (beta : Fin 2 → ℝ) (i : Fin 2) :
    0 ≤ deriv (fun t => deriv
      (fun t' => potential D (slice beta i t')) t) (beta i) := by
  rw [second_partial_eq_variance D beta i]
  exact logSumExpVariance_nonneg _ _ (fun x => Real.exp_pos _) _

theorem second_partial_pos_of_charge_ne
    (beta : Fin 2 → ℝ) (i : Fin 2)
    (hne : ∃ x y : State, D.momentMap x i ≠ D.momentMap y i) :
    0 < deriv (fun t => deriv
      (fun t' => potential D (slice beta i t')) t) (beta i) := by
  rw [second_partial_eq_variance D beta i]
  apply logSumExpVariance_pos_of_exists_ne
  · intro x
    exact Real.exp_pos _
  · obtain ⟨x, y, hxy⟩ := hne
    exact ⟨x, y, by simpa using hxy⟩

theorem second_partial_eq_zero_of_charge_constant
    (beta : Fin 2 → ℝ) (i : Fin 2) (c : ℝ)
    (hconst : ∀ x : State, D.momentMap x i = c) :
    deriv (fun t => deriv
      (fun t' => potential D (slice beta i t')) t) (beta i) = 0 := by
  rw [second_partial_eq_variance D beta i]
  apply logSumExpVariance_eq_zero_of_forall_eq (c := -c)
  · intro x
    exact Real.exp_pos _
  · intro x
    simp only [hconst]

end InfoGeometry.Lie.CanonicalZornG2MassieuConvexity
