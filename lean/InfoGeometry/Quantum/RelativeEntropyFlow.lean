import InfoGeometry.Dynamics.KanDecomposition
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.OperatorAlgebra.VerifiedTrace
import Mathlib.Tactic
import InfoGeometryCore.Basic

noncomputable section

/-!
# RelativeEntropyFlow

Finite `2 × 2` quantum-state readouts for the parabolic `KAN` component.

This file records the theorem-safe linear algebra around the unipotent shear
`N(δ)`.  It separates two maps that are often conflated:

* the positive sandwich `ρ ↦ N(δ) ρ N(δ)ᴴ`, which is not trace-preserving for
  the non-unitary parabolic shear;
* the similarity update `ρ ↦ N(δ) ρ N(-δ)`, which is trace-preserving because
  `N(-δ)` is the two-sided inverse of `N(δ)`.

No von Neumann entropy, logarithm, positivity completion, or nonlinear quantum
proximal theorem is asserted here.
-/

namespace InfoGeometry.Quantum.RelativeEntropyFlow

open Matrix
open InfoGeometry.Dynamics.KanDecomposition
open InfoGeometryCore

/--
Finite trace-one Hermitian predicate.  Positivity is intentionally not included;
it belongs to a separate positive-semidefinite owner theorem.
-/
def IsTraceOneHermitian (ρ : M2C) : Prop :=
  ρ.conjTranspose = ρ ∧ Matrix.trace ρ = 1

/-- The maximally mixed qubit state `1 / 2 • I`. -/
def maximallyMixedState : M2C :=
  !![(1 / 2 : ℂ), 0; 0, (1 / 2 : ℂ)]

@[simp]
theorem maximallyMixedState_conjTranspose :
    maximallyMixedState.conjTranspose = maximallyMixedState := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [maximallyMixedState]

@[simp]
theorem maximallyMixedState_trace :
    Matrix.trace maximallyMixedState = 1 := by
  simp [maximallyMixedState, Matrix.trace, Fin.sum_univ_two]
  norm_num

/-- The maximally mixed qubit is trace-one Hermitian. -/
theorem maximallyMixedState_isTraceOneHermitian :
    IsTraceOneHermitian maximallyMixedState := by
  exact ⟨maximallyMixedState_conjTranspose, maximallyMixedState_trace⟩

/-- The zero parabolic component is the identity matrix. -/
@[simp]
theorem componentN_zero :
    componentN 0 = (1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [componentN_eq]

/-- The negative shear is a right inverse for the parabolic component. -/
theorem componentN_mul_neg (δ : ℂ) :
    componentN δ * componentN (-δ) = (1 : M2C) := by
  rw [componentN_composition]
  simp

/-- The negative shear is a left inverse for the parabolic component. -/
theorem componentN_neg_mul (δ : ℂ) :
    componentN (-δ) * componentN δ = (1 : M2C) := by
  rw [componentN_composition]
  simp [add_comm]

/--
Positive sandwich by the parabolic shear.  This is the finite linearized
`N ρ Nᴴ` envelope; since `N` is not unitary, this map is not trace-preserving
without a separate normalization.
-/
def quantumShearSandwich (ρ : M2C) (δ : ℂ) : M2C :=
  componentN δ * ρ * (componentN δ).conjTranspose

/--
Similarity update by the parabolic shear.  This is the trace-preserving finite
algebraic readout because `N(-δ)` is the inverse of `N(δ)`.
-/
def quantumShearSimilarity (ρ : M2C) (δ : ℂ) : M2C :=
  componentN δ * ρ * componentN (-δ)

/-- Recursive `n`-step positive sandwich flow. -/
def quantumShearSandwichIter (δ : ℂ) : Nat → M2C → M2C
  | 0, ρ => ρ
  | n + 1, ρ => quantumShearSandwich (quantumShearSandwichIter δ n ρ) δ

/-- Recursive `n`-step similarity flow. -/
def quantumShearSimilarityIter (δ : ℂ) : Nat → M2C → M2C
  | 0, ρ => ρ
  | n + 1, ρ => quantumShearSimilarity (quantumShearSimilarityIter δ n ρ) δ

/--
The positive sandwich flow accumulates the parabolic shear arithmetically.
-/
theorem quantumShearSandwichIter_eq
    (ρ : M2C) (δ : ℂ) (n : Nat) :
    quantumShearSandwichIter δ n ρ =
      componentN ((n : ℂ) * δ) * ρ *
        (componentN ((n : ℂ) * δ)).conjTranspose := by
  induction n with
  | zero =>
      simp [quantumShearSandwichIter]
  | succ n ih =>
      simp [quantumShearSandwichIter, quantumShearSandwich, ih]
      have hleft :
          componentN δ * componentN ((n : ℂ) * δ) =
            componentN (((n : ℂ) + 1) * δ) := by
        rw [componentN_composition]
        congr 1
        ring_nf
      have hright :
          (componentN ((n : ℂ) * δ)).conjTranspose *
              (componentN δ).conjTranspose =
            (componentN (((n : ℂ) + 1) * δ)).conjTranspose := by
        rw [← Matrix.conjTranspose_mul, componentN_composition]
        congr 1
        ring_nf
      calc
        componentN δ *
              (componentN ((n : ℂ) * δ) * ρ *
                (componentN ((n : ℂ) * δ)).conjTranspose) *
            (componentN δ).conjTranspose
            = (componentN δ * componentN ((n : ℂ) * δ)) * ρ *
                ((componentN ((n : ℂ) * δ)).conjTranspose *
                  (componentN δ).conjTranspose) := by
                noncomm_ring
        _ = componentN (((n : ℂ) + 1) * δ) * ρ *
                (componentN (((n : ℂ) + 1) * δ)).conjTranspose := by
              rw [hleft, hright]

/--
The similarity flow accumulates the parabolic shear arithmetically.
-/
theorem quantumShearSimilarityIter_eq
    (ρ : M2C) (δ : ℂ) (n : Nat) :
    quantumShearSimilarityIter δ n ρ =
      componentN ((n : ℂ) * δ) * ρ *
        componentN (-((n : ℂ) * δ)) := by
  induction n with
  | zero =>
      simp [quantumShearSimilarityIter]
  | succ n ih =>
      simp [quantumShearSimilarityIter, quantumShearSimilarity, ih]
      have hleft :
          componentN δ * componentN ((n : ℂ) * δ) =
            componentN (((n : ℂ) + 1) * δ) := by
        rw [componentN_composition]
        congr 1
        ring_nf
      have hright :
          componentN (-((n : ℂ) * δ)) * componentN (-δ) =
            componentN (-(((n : ℂ) + 1) * δ)) := by
        rw [componentN_composition]
        congr 1
        ring_nf
      calc
        componentN δ *
              (componentN ((n : ℂ) * δ) * ρ *
                componentN (-((n : ℂ) * δ))) *
            componentN (-δ)
            = (componentN δ * componentN ((n : ℂ) * δ)) * ρ *
                (componentN (-((n : ℂ) * δ)) * componentN (-δ)) := by
                noncomm_ring
        _ = componentN (((n : ℂ) + 1) * δ) * ρ *
                componentN (-(((n : ℂ) + 1) * δ)) := by
              rw [hleft, hright]

/-- The similarity update preserves finite matrix trace. -/
theorem quantumShearSimilarity_trace
    (ρ : M2C) (δ : ℂ) :
    Matrix.trace (quantumShearSimilarity ρ δ) = Matrix.trace ρ := by
  unfold quantumShearSimilarity
  exact InfoGeometry.OperatorAlgebra.VerifiedTrace.matrix_trace_conjugation_invariant
    ρ (componentN δ) (componentN (-δ)) (componentN_mul_neg δ) (componentN_neg_mul δ)

/-- The `n`-step similarity flow preserves finite matrix trace. -/
theorem quantumShearSimilarityIter_trace
    (ρ : M2C) (δ : ℂ) (n : Nat) :
    Matrix.trace (quantumShearSimilarityIter δ n ρ) = Matrix.trace ρ := by
  rw [quantumShearSimilarityIter_eq]
  exact InfoGeometry.OperatorAlgebra.VerifiedTrace.matrix_trace_conjugation_invariant
    ρ
    (componentN ((n : ℂ) * δ))
    (componentN (-((n : ℂ) * δ)))
    (componentN_mul_neg ((n : ℂ) * δ))
    (componentN_neg_mul ((n : ℂ) * δ))

/--
Audit counterexample: the positive sandwich by the non-unitary parabolic shear
does not preserve trace, even on the maximally mixed state.
-/
theorem quantumShearSandwich_maximallyMixed_trace_one_shear :
    Matrix.trace (quantumShearSandwich maximallyMixedState 1) = (3 / 2 : ℂ) := by
  rw [Matrix.trace_fin_two]
  simp [quantumShearSandwich, maximallyMixedState, componentN_eq, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_two]
  norm_num

/-- Therefore the unnormalized positive sandwich is not a density-state channel. -/
theorem quantumShearSandwich_maximallyMixed_not_trace_preserving :
    Matrix.trace (quantumShearSandwich maximallyMixedState 1) ≠ (1 : ℂ) := by
  rw [quantumShearSandwich_maximallyMixed_trace_one_shear]
  norm_num

end InfoGeometry.Quantum.RelativeEntropyFlow
