import Mathlib

/-!
# Finite graded quantum tetrad frames

This owner is the finite algebraic core of a quantum frame packet.  Four
operator directions are combined by tetrad coefficients into three colour
frame vectors; Cartan parameters then form a generator whose exponential is
the corresponding finite flow.  The grading and CPT twist are explicit
involutive linear data.  No manifold bundle, locality, or physical CPT
theorem is asserted here.
-/

namespace InfoGeometry.Quantum.GradedQuantumTetradFrame

noncomputable section

abbrev Operator := Matrix (Fin 2) (Fin 2) ℝ

structure Frame where
  coefficients : Fin 3 → Fin 4 → ℝ
  operatorBasis : Fin 4 → Operator
  grading : Operator →ₗ[ℝ] Operator
  cptTwist : Operator →ₗ[ℝ] Operator
  grading_sq : ∀ X, grading (grading X) = X
  cptTwist_sq : ∀ X, cptTwist (cptTwist X) = X
  cptTwist_grading : ∀ X,
    cptTwist (grading X) = -grading (cptTwist X)

def colorVector (F : Frame) (a : Fin 3) : Operator :=
  ∑ μ : Fin 4, F.coefficients a μ • F.operatorBasis μ

def cartanGenerator (F : Frame) (κ : Fin 3 → ℝ) : Operator :=
  ∑ a : Fin 3, κ a • colorVector F a

def cartanFlow (F : Frame) (κ : Fin 3 → ℝ) : Operator :=
  NormedSpace.exp (cartanGenerator F κ)

def cartanFlowAt (F : Frame) (κ : Fin 3 → ℝ) (t : ℝ) : Operator :=
  NormedSpace.exp (t • cartanGenerator F κ)

def internalComplexStructure (F : Frame) : Module.End ℝ Operator :=
  F.grading.comp F.cptTwist

def realComplexStructure (F : Frame) : Operator →ₗ[ℝ] Operator :=
  F.cptTwist.comp F.grading

theorem colorVector_reconstruction (F : Frame) (a : Fin 3) :
    colorVector F a =
      ∑ μ : Fin 4, F.coefficients a μ • F.operatorBasis μ :=
  rfl

theorem cartanGenerator_reconstruction (F : Frame) (κ : Fin 3 → ℝ) :
    cartanGenerator F κ =
      ∑ a : Fin 3, κ a •
        (∑ μ : Fin 4, F.coefficients a μ • F.operatorBasis μ) := by
  simp [cartanGenerator, colorVector]

theorem grading_involutive (F : Frame) (X : Operator) :
    F.grading (F.grading X) = X :=
  F.grading_sq X

theorem cptTwist_involutive (F : Frame) (X : Operator) :
    F.cptTwist (F.cptTwist X) = X :=
  F.cptTwist_sq X

theorem cptTwist_reverses_grading (F : Frame) (X : Operator) :
    F.cptTwist (F.grading X) = -F.grading (F.cptTwist X) :=
  F.cptTwist_grading X

theorem internalComplexStructure_sq (F : Frame) (X : Operator) :
    internalComplexStructure F (internalComplexStructure F X) = -X := by
  change F.grading (F.cptTwist (F.grading (F.cptTwist X))) = -X
  rw [F.cptTwist_grading]
  simp [F.grading_sq, F.cptTwist_sq]

theorem realComplexStructure_sq (F : Frame) (X : Operator) :
    realComplexStructure F (realComplexStructure F X) = -X := by
  simp only [realComplexStructure, LinearMap.coe_comp, Function.comp_apply]
  rw [F.cptTwist_grading]
  simp [F.cptTwist_sq, F.grading_sq]

theorem cartanFlow_zero (F : Frame) :
    cartanFlow F 0 = 1 := by
  simp [cartanFlow, cartanGenerator, colorVector]

theorem cartanFlowAt_zero (F : Frame) (κ : Fin 3 → ℝ) :
    cartanFlowAt F κ 0 = 1 := by
  simp [cartanFlowAt]

theorem cartanFlowAt_add (F : Frame) (κ : Fin 3 → ℝ) (s t : ℝ) :
    cartanFlowAt F κ (s + t) =
      cartanFlowAt F κ s * cartanFlowAt F κ t := by
  unfold cartanFlowAt
  have hcomm : Commute (s • cartanGenerator F κ) (t • cartanGenerator F κ) := by
    rw [Commute]
    ext i j
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  calc
    NormedSpace.exp ((s + t) • cartanGenerator F κ) =
        NormedSpace.exp (s • cartanGenerator F κ + t • cartanGenerator F κ) := by
          rw [add_smul]
    _ = NormedSpace.exp (s • cartanGenerator F κ) *
        NormedSpace.exp (t • cartanGenerator F κ) :=
          Matrix.exp_add_of_commute _ _ hcomm

theorem cartanFlowAt_neg_mul (F : Frame) (κ : Fin 3 → ℝ) (t : ℝ) :
    cartanFlowAt F κ (-t) * cartanFlowAt F κ t = 1 := by
  unfold cartanFlowAt
  have hcomm : Commute ((-t) • cartanGenerator F κ) (t • cartanGenerator F κ) := by
    rw [Commute]
    ext i j
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  calc
    NormedSpace.exp ((-t) • cartanGenerator F κ) *
        NormedSpace.exp (t • cartanGenerator F κ) =
        NormedSpace.exp ((-t) • cartanGenerator F κ + t • cartanGenerator F κ) :=
          (Matrix.exp_add_of_commute _ _ hcomm).symm
    _ = 1 := by simp

theorem cartanFlowAt_mul_neg (F : Frame) (κ : Fin 3 → ℝ) (t : ℝ) :
    cartanFlowAt F κ t * cartanFlowAt F κ (-t) = 1 := by
  unfold cartanFlowAt
  have hcomm : Commute (t • cartanGenerator F κ) ((-t) • cartanGenerator F κ) := by
    rw [Commute]
    ext i j
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  calc
    NormedSpace.exp (t • cartanGenerator F κ) *
        NormedSpace.exp ((-t) • cartanGenerator F κ) =
        NormedSpace.exp (t • cartanGenerator F κ + (-t) • cartanGenerator F κ) :=
          (Matrix.exp_add_of_commute _ _ hcomm).symm
    _ = 1 := by simp

end

end InfoGeometry.Quantum.GradedQuantumTetradFrame
