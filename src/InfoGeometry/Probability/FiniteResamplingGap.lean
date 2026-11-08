import InfoGeometry.Inference.GibbsFluctuation
import Mathlib.LinearAlgebra.Projection

noncomputable section

namespace InfoGeometry.Probability.FiniteResamplingGap

open InfoGeometry.Inference

variable {State : Type*} [Fintype State]

def pairing (weight observable test : State → ℝ) : ℝ :=
  ∑ state, weight state * observable state * test state

def dirichletEnergy (weight : State → ℝ) (kernel : State → State → ℝ)
    (observable : State → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ source, ∑ target,
    weight source * kernel source target * (observable source - observable target) ^ 2

theorem poincare_of_minorization (weight : State → ℝ) (kernel : State → State → ℝ)
    (normalized : ∑ state, weight state = 1) (positive : ∀ state, 0 ≤ weight state)
    (delta : ℝ) (minorization : ∀ source target, delta * weight target ≤ kernel source target)
    (observable : State → ℝ) :
    delta * weightedVariance weight observable ≤ dirichletEnergy weight kernel observable := by
  rw [weightedVariance_eq_half_pairwise weight observable normalized]
  unfold dirichletEnergy
  calc
    delta * ((1 / 2 : ℝ) * ∑ source, ∑ target,
        weight source * weight target * (observable source - observable target) ^ 2) =
        (1 / 2 : ℝ) * (delta * ∑ source, ∑ target,
          weight source * weight target * (observable source - observable target) ^ 2) := by ring
    _ = (1 / 2 : ℝ) * ∑ source, ∑ target,
        delta * (weight source * weight target * (observable source - observable target) ^ 2) := by
      simp only [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro source _
      apply Finset.sum_le_sum
      intro target _
      calc
        _ = weight source * (delta * weight target) *
            (observable source - observable target) ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (minorization source target) (positive source))
          (sq_nonneg _)

def resamplingKernel (weight : State → ℝ) (_source target : State) : ℝ := weight target

theorem resampling_stochastic (weight : State → ℝ)
    (normalized : ∑ state, weight state = 1) (source : State) :
    ∑ target, resamplingKernel weight source target = 1 := normalized

theorem resampling_detailed_balance (weight : State → ℝ) (source target : State) :
    weight source * resamplingKernel weight source target =
      weight target * resamplingKernel weight target source := mul_comm _ _

theorem resampling_stationary (weight : State → ℝ)
    (normalized : ∑ state, weight state = 1) (target : State) :
    ∑ source, weight source * resamplingKernel weight source target = weight target := by
  simp only [resamplingKernel, ← Finset.sum_mul, normalized, one_mul]

def resamplingProjection (weight : State → ℝ) : Module.End ℝ (State → ℝ) where
  toFun observable := fun _ => weightedMean weight observable
  map_add' observable test := by
    funext state
    simp [weightedMean, mul_add, Finset.sum_add_distrib]
  map_smul' scalar observable := by
    funext state
    change (∑ target, weight target * (scalar * observable target)) =
      scalar * ∑ target, weight target * observable target
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro target _
    ring

def hamiltonian (weight : State → ℝ) : Module.End ℝ (State → ℝ) :=
  1 - resamplingProjection weight

theorem hamiltonian_apply (weight observable : State → ℝ) (state : State) :
    hamiltonian weight observable state = observable state - weightedMean weight observable := rfl

theorem mean_constant (weight : State → ℝ) (normalized : ∑ state, weight state = 1)
    (value : ℝ) : weightedMean weight (fun _ => value) = value := by
  simp only [weightedMean, ← Finset.sum_mul, normalized, one_mul]

theorem resamplingProjection_idempotent (weight : State → ℝ)
    (normalized : ∑ state, weight state = 1) :
    IsIdempotentElem (resamplingProjection weight) := by
  ext observable state
  exact mean_constant weight normalized (weightedMean weight observable)

theorem resampling_self_adjoint (weight observable test : State → ℝ) :
    pairing weight observable (resamplingProjection weight test) =
      pairing weight (resamplingProjection weight observable) test := by
  change (∑ state, weight state * observable state * weightedMean weight test) =
    ∑ state, weight state * weightedMean weight observable * test state
  rw [← Finset.sum_mul]
  change weightedMean weight observable * weightedMean weight test = _
  unfold weightedMean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro state _
  ring

theorem hamiltonian_self_adjoint (weight observable test : State → ℝ) :
    pairing weight observable (hamiltonian weight test) =
      pairing weight (hamiltonian weight observable) test := by
  have symmetric := resampling_self_adjoint weight observable test
  simp only [pairing, hamiltonian_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]
  change pairing weight observable test - pairing weight observable (resamplingProjection weight test) =
    pairing weight observable test - pairing weight (resamplingProjection weight observable) test
  rw [symmetric]

theorem mean_centered (weight observable : State → ℝ)
    (normalized : ∑ state, weight state = 1) :
    ∑ state, weight state * (observable state - weightedMean weight observable) = 0 := by
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, normalized, one_mul]
  exact sub_self _

theorem hamiltonian_energy_eq_variance (weight observable : State → ℝ)
    (normalized : ∑ state, weight state = 1) :
    pairing weight observable (hamiltonian weight observable) = weightedVariance weight observable := by
  change (∑ state, weight state * observable state *
    (observable state - weightedMean weight observable)) = _
  calc
    _ = ∑ state, (weight state * (observable state - weightedMean weight observable) ^ 2 +
        weightedMean weight observable *
          (weight state * (observable state - weightedMean weight observable))) := by
      apply Finset.sum_congr rfl
      intro state _
      ring
    _ = weightedVariance weight observable := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, mean_centered weight observable normalized]
      simp [weightedVariance]

theorem resampling_dirichlet_eq_variance (weight observable : State → ℝ)
    (normalized : ∑ state, weight state = 1) :
    dirichletEnergy weight (resamplingKernel weight) observable = weightedVariance weight observable :=
  (weightedVariance_eq_half_pairwise weight observable normalized).symm

theorem centered_eigenvalue_one (weight observable : State → ℝ)
    (centered : weightedMean weight observable = 0) :
    hamiltonian weight observable = observable := by
  funext state
  rw [hamiltonian_apply, centered, sub_zero]

theorem poincare_gap_one (weight observable : State → ℝ)
    (normalized : ∑ state, weight state = 1) :
    1 * weightedVariance weight observable ≤ pairing weight observable (hamiltonian weight observable) := by
  rw [one_mul, hamiltonian_energy_eq_variance weight observable normalized]

end InfoGeometry.Probability.FiniteResamplingGap
