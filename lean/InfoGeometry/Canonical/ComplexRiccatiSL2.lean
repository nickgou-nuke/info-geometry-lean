import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# The finite complex `sl₂` Riccati bridge

For a traceless complex `2 × 2` matrix, this owner records the exact
projective numerator identity behind the Riccati vector field and the
Cartan--Weyl commutator table.  It deliberately stays finite and
algebraic: no Riemann-sphere quotient, ODE existence theorem, or global
flow classification is asserted here.
-/

noncomputable section

namespace InfoGeometry.Canonical.ComplexRiccatiSL2

abbrev M2C := InfoGeometry.Algebra.FiniteSpin.Mat2C

def riccatiMatrix (α β γ : ℂ) : M2C := !![α, β; γ, -α]

def riccatiField (α β γ z : ℂ) : ℂ :=
  β + 2 * α * z - γ * z ^ 2

def commutator (A B : M2C) : M2C := A * B - B * A

def basisE : M2C := !![0, 1; 0, 0]

def basisH : M2C := !![1, 0; 0, -1]

def basisF : M2C := !![0, 0; 1, 0]

theorem riccatiMatrix_trace_zero (α β γ : ℂ) :
    riccatiMatrix α β γ 0 0 + riccatiMatrix α β γ 1 1 = 0 := by
  simp [riccatiMatrix]

theorem riccatiMatrix_det (α β γ : ℂ) :
    Matrix.det (riccatiMatrix α β γ) = -(α ^ 2 + β * γ) := by
  simp [riccatiMatrix, Matrix.det_fin_two]
  ring

/-- The projective numerator identity for the Riccati vector field. -/
theorem riccati_numerator_identity (α β γ z : ℂ) :
    (α * z + β) - z * (γ * z - α) = riccatiField α β γ z := by
  unfold riccatiField
  ring

theorem riccatiMatrix_decompose (α β γ : ℂ) :
    riccatiMatrix α β γ = α • basisH + β • basisE + γ • basisF := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [riccatiMatrix, basisH, basisE, basisF]
  all_goals ring

@[simp] theorem riccatiField_basisE (z : ℂ) :
    riccatiField 0 1 0 z = 1 := by
  simp [riccatiField]

@[simp] theorem riccatiField_basisH (z : ℂ) :
    riccatiField 1 0 0 z = 2 * z := by
  simp [riccatiField]

@[simp] theorem riccatiField_basisF (z : ℂ) :
    riccatiField 0 0 1 z = -z ^ 2 := by
  simp [riccatiField]

theorem riccatiMatrix_sq (α β γ : ℂ) :
    riccatiMatrix α β γ * riccatiMatrix α β γ =
      (α ^ 2 + β * γ) • (1 : M2C) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [riccatiMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  · ring
  · ring
  · ring
  · ring

theorem commutator_basisH_basisE :
    commutator basisH basisE = (2 : ℂ) • basisE := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [commutator, basisH, basisE, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

theorem commutator_basisH_basisF :
    commutator basisH basisF = (-2 : ℂ) • basisF := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [commutator, basisH, basisF, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

theorem commutator_basisE_basisF :
    commutator basisE basisF = basisH := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [commutator, basisE, basisF, basisH, Matrix.mul_apply,
      Fin.sum_univ_two]
  all_goals ring

theorem basisE_sq : basisE * basisE = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [basisE, Matrix.mul_apply, Fin.sum_univ_two]

theorem basisF_sq : basisF * basisF = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [basisF, Matrix.mul_apply, Fin.sum_univ_two]


end InfoGeometry.Canonical.ComplexRiccatiSL2
