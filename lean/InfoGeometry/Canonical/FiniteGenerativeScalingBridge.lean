import InfoGeometry.Canonical.CoarseGraining
import InfoGeometry.Algebra.StochasticGrammarCuntzKriegerBridge

/-!
# Finite generative scaling bridge

This is the finite, theorem-level core of the generative-model discussion.
It records the causal order without asserting empirical neural scaling laws:
microscopic weights are grouped into coarse fibres, transition rows are
probability distributions, and their square-root amplitudes lie on the unit
sphere.
-/

open scoped BigOperators

namespace InfoGeometry.Canonical

open FiniteCoarseGraining
open InfoGeometry.Algebra.StochasticGrammarCuntzKriegerBridge

theorem finite_coarse_graining_conserves_weight
    {X Y R : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    [AddCommMonoid R]
    (G : FiniteCoarseGraining X Y) (w : X → R) :
    totalWeight w = ∑ y, fiberWeight G w y := by
  exact totalWeight_eq_sum_fiberWeight G w

theorem finite_transition_row_is_probability
    {n : ℕ} (M : StochasticTransitionMatrix n) (i : Fin n) :
    (∀ j, 0 ≤ M.A i j) ∧
      (∑ j, M.A i j = 1) := by
  exact ⟨fun j => M.nonneg i j, M.row_sum i⟩

theorem finite_transition_amplitude_is_normalized
    {n : ℕ} (M : StochasticTransitionMatrix n) (i : Fin n) :
    ∑ j, (M.amplitudeMatrix i j) ^ 2 = 1 := by
  exact M.amplitude_row_l2_normalization i

theorem finite_generative_causal_synthesis
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    {n : ℕ} (G : FiniteCoarseGraining X Y) (w : X → ℝ)
    (M : StochasticTransitionMatrix n) (i : Fin n) :
    (totalWeight w = ∑ y, fiberWeight G w y) ∧
    (∀ j, 0 ≤ M.A i j) ∧
    (∑ j, M.A i j = 1) ∧
    (∑ j, (M.amplitudeMatrix i j) ^ 2 = 1) := by
  have hG := finite_coarse_graining_conserves_weight G w
  have hM := finite_transition_row_is_probability M i
  have hA := finite_transition_amplitude_is_normalized M i
  exact ⟨hG, hM.1, hM.2, hA⟩

end InfoGeometry.Canonical
