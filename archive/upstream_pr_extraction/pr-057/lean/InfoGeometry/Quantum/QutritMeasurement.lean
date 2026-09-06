import InfoGeometry.Quantum.Qutrit
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Computational-basis measurement of a qutrit

This module formalizes the finite Born probabilities attached to the standard
computational basis of `EuclideanSpace ℂ (Fin 3)`.  It proves normalization,
bounds, deterministic basis-state outcomes, and invariance under global phase.
-/

noncomputable section

namespace InfoGeometry.Quantum.Qutrit

open InfoGeometry.OperatorAlgebra.ComplexBoundedOperators.FiniteMatrix

/-- Probability of a computational-basis outcome for a normalized qutrit. -/
def computationalProbability (ψ : QutritState) (i : Fin 3) : ℝ :=
  ‖(ψ : QutritSpace) i‖ ^ 2

@[simp] theorem computationalProbability_nonneg (ψ : QutritState) (i : Fin 3) :
    0 ≤ computationalProbability ψ i := by
  exact sq_nonneg _

/-- Computational-basis probabilities of a normalized qutrit sum to one. -/
theorem sum_computationalProbability (ψ : QutritState) :
    ∑ i, computationalProbability ψ i = 1 := by
  exact state_normalization ψ

/-- Every computational-basis outcome probability is at most one. -/
theorem computationalProbability_le_one (ψ : QutritState) (i : Fin 3) :
    computationalProbability ψ i ≤ 1 := by
  rw [← sum_computationalProbability ψ]
  exact Finset.single_le_sum
    (fun j _ => computationalProbability_nonneg ψ j) (Finset.mem_univ i)

/-- A computational-basis ket bundled as a normalized qutrit state. -/
def basisState (i : Fin 3) : QutritState :=
  ⟨ket i, by
    rw [mem_sphere_zero_iff_norm]
    exact ket_orthonormal.1 i⟩

/-- Measuring `|i⟩` in the computational basis returns `i` with probability one. -/
@[simp] theorem computationalProbability_basisState_self (i : Fin 3) :
    computationalProbability (basisState i) i = 1 := by
  simp [computationalProbability, basisState, ket, EuclideanSpace.basisFun_apply]

/-- Measuring `|i⟩` at a distinct computational label returns probability zero. -/
@[simp] theorem computationalProbability_basisState_of_ne {i j : Fin 3} (hji : j ≠ i) :
    computationalProbability (basisState i) j = 0 := by
  simp [computationalProbability, basisState, ket, EuclideanSpace.basisFun_apply, hji]

/-- A global phase does not alter computational-basis outcome probabilities. -/
theorem computationalProbability_globalPhaseAct
    (δ : ℝ) (ψ : QutritState) (i : Fin 3) :
    computationalProbability (globalPhaseAct δ ψ) i = computationalProbability ψ i := by
  change ‖(matrixOp (globalPhaseMatrix δ) (ψ : QutritSpace) : QutritSpace) i‖ ^ 2 =
    ‖(ψ : QutritSpace) i‖ ^ 2
  rw [globalPhaseMatrix_apply]
  simp [norm_phase]

/-- Computational-basis measurement as Mathlib's native finite probability mass function. -/
def computationalBasisPMF (ψ : QutritState) : PMF (Fin 3) :=
  PMF.ofFintype (fun i => ENNReal.ofReal (computationalProbability ψ i)) <| by
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · rw [sum_computationalProbability, ENNReal.ofReal_one]
    · intro i _
      exact computationalProbability_nonneg ψ i

@[simp] theorem computationalBasisPMF_apply (ψ : QutritState) (i : Fin 3) :
    computationalBasisPMF ψ i = ENNReal.ofReal (computationalProbability ψ i) :=
  rfl

end InfoGeometry.Quantum.Qutrit
