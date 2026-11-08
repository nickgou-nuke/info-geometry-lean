import InfoGeometry.Probability.FiniteResamplingGap
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Basic

noncomputable section

namespace InfoGeometry.Probability.FiniteResamplingGap

open InfoGeometry.Inference

variable {State : Type*} [Fintype State]

theorem hamiltonian_idempotent (weight : State → ℝ)
    (normalized : ∑ state, weight state = 1) :
    IsIdempotentElem (hamiltonian weight) := by
  have projection := (resamplingProjection_idempotent weight normalized).eq
  change (1 - resamplingProjection weight) * (1 - resamplingProjection weight) =
    1 - resamplingProjection weight
  simp [mul_sub, sub_mul, projection]

theorem hamiltonian_spectrum_subset (weight : State → ℝ)
    (normalized : ∑ state, weight state = 1) :
    spectrum ℝ (hamiltonian weight) ⊆ {0, 1} :=
  (hamiltonian_idempotent weight normalized).spectrum_subset ℝ

theorem zero_mem_hamiltonian_spectrum [Nonempty State] (weight : State → ℝ)
    (normalized : ∑ state, weight state = 1) :
    0 ∈ spectrum ℝ (hamiltonian weight) := by
  have eigenvector : (hamiltonian weight).HasEigenvector 0 (fun _ => 1) := by
    constructor
    · rw [Module.End.mem_eigenspace_iff]
      funext state
      simp [hamiltonian_apply, mean_constant weight normalized]
    · intro equal
      obtain ⟨state⟩ := ‹Nonempty State›
      have impossible := congrFun equal state
      norm_num at impossible
  exact (Module.End.hasEigenvalue_of_hasEigenvector eigenvector).mem_spectrum

def centeredIndicator [DecidableEq State] (weight : State → ℝ) (base : State) : State → ℝ :=
  fun state => (if state = base then 1 else 0) - weight base

theorem centeredIndicator_mean [DecidableEq State] (weight : State → ℝ)
    (normalized : ∑ state, weight state = 1) (base : State) :
    weightedMean weight (centeredIndicator weight base) = 0 := by
  simp [weightedMean, centeredIndicator, mul_sub, mul_ite, Finset.sum_sub_distrib,
    ← Finset.sum_mul, normalized]

theorem centeredIndicator_ne_zero [DecidableEq State] (weight : State → ℝ)
    (base other : State) (distinct : other ≠ base) :
    centeredIndicator weight base ≠ 0 := by
  intro equal
  have atBase := congrFun equal base
  have atOther := congrFun equal other
  simp [centeredIndicator, distinct] at atBase atOther
  linarith

theorem one_mem_hamiltonian_spectrum [Nontrivial State] (weight : State → ℝ)
    (normalized : ∑ state, weight state = 1) :
    1 ∈ spectrum ℝ (hamiltonian weight) := by
  classical
  obtain ⟨base, other, distinct⟩ := exists_pair_ne State
  have eigenvector : (hamiltonian weight).HasEigenvector 1
      (centeredIndicator weight base) := by
    constructor
    · rw [Module.End.mem_eigenspace_iff, one_smul]
      exact centered_eigenvalue_one weight _ (centeredIndicator_mean weight normalized base)
    · exact centeredIndicator_ne_zero weight base other distinct.symm
  exact (Module.End.hasEigenvalue_of_hasEigenvector eigenvector).mem_spectrum

theorem hamiltonian_spectrum_eq [Nontrivial State] (weight : State → ℝ)
    (normalized : ∑ state, weight state = 1) :
    spectrum ℝ (hamiltonian weight) = {0, 1} := by
  apply Set.Subset.antisymm (hamiltonian_spectrum_subset weight normalized)
  intro value member
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at member
  rcases member with rfl | rfl
  · exact zero_mem_hamiltonian_spectrum weight normalized
  · exact one_mem_hamiltonian_spectrum weight normalized

theorem no_spectrum_between_zero_and_one (weight : State → ℝ)
    (normalized : ∑ state, weight state = 1) (value : ℝ)
    (positive : 0 < value) (belowOne : value < 1) :
    value ∉ spectrum ℝ (hamiltonian weight) := by
  intro member
  have alternatives := hamiltonian_spectrum_subset weight normalized member
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at alternatives
  rcases alternatives with rfl | rfl <;> linarith

end InfoGeometry.Probability.FiniteResamplingGap
