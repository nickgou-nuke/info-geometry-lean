import InfoGeometry.Lie.SplitOctonionAxialFlowDecomposition
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Closed flow of the diagonal split-octonion tripotent

The diagonal axial grading has the three native polynomial projectors
`axialPZero`, `axialPPlus`, and `axialPMinus`.  This owner defines its closed
hyperbolic flow directly from those projectors:

`Φ(t) = P₀ + exp(t) P₊ + exp(-t) P₋`.

The group law and the three sector actions are proved on the actual canonical
Zorn coordinates.  This is a linear flow; no claim that the uniform weights
preserve the nonassociative Zorn multiplication is made here.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionAxialClosedFlow

open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Lie.SplitOctonionAxialPeirceTrifactor

abbrev CZ := ZornMatrix ℝ
abbrev EndCZ := Module.End ℝ CZ

attribute [local simp] Pi.smul_apply Pi.add_apply Pi.neg_apply

/-- Projector-derived closed flow of the axial tripotent. -/
def axialClosedFlow (t : ℝ) : EndCZ :=
  axialPZero + (Real.exp t) • axialPPlus + (Real.exp (-t)) • axialPMinus

/-- Coordinate form of the closed flow: diagonal coordinates are stationary,
upper/color coordinates have weight `exp t`, and lower/anticolor coordinates
have weight `exp (-t)`. -/
@[simp] theorem axialClosedFlow_apply (t : ℝ) (X : CZ) :
    axialClosedFlow t X =
      { a := X.a
        b := X.b
        x := (Real.exp t) • X.x
        y := (Real.exp (-t)) • X.y } := by
  ext i
  · simp [axialClosedFlow, axialPZero_apply, axialPPlus_apply,
      axialPMinus_apply, colorProject_apply, anticolorProject_apply,
      Equiv.smul_def, coordEquiv]
  · simp [axialClosedFlow, axialPZero_apply, axialPPlus_apply,
      axialPMinus_apply, colorProject_apply, anticolorProject_apply,
      Equiv.smul_def, coordEquiv]
  · simp [axialClosedFlow, axialPZero_apply, axialPPlus_apply,
      axialPMinus_apply, colorProject_apply, anticolorProject_apply,
      Equiv.smul_def, coordEquiv]
  · simp [axialClosedFlow, axialPZero_apply, axialPPlus_apply,
      axialPMinus_apply, colorProject_apply, anticolorProject_apply,
      Equiv.smul_def, coordEquiv]

/-- At parameter zero the closed flow is the identity. -/
@[simp] theorem axialClosedFlow_zero : axialClosedFlow 0 = 1 := by
  apply LinearMap.ext
  intro X
  ext i <;> simp

/-- The projector-derived flow is a one-parameter representation of the
additive real group. -/
theorem axialClosedFlow_add (s t : ℝ) :
    axialClosedFlow (s + t) = axialClosedFlow s * axialClosedFlow t := by
  apply LinearMap.ext
  intro X
  ext i <;> simp [Real.exp_add]
  · ring
  · ring

/-- Reversing the parameter gives a two-sided inverse. -/
theorem axialClosedFlow_mul_neg (t : ℝ) :
    axialClosedFlow t * axialClosedFlow (-t) = 1 := by
  rw [← axialClosedFlow_add]
  simp

theorem axialClosedFlow_neg_mul (t : ℝ) :
    axialClosedFlow (-t) * axialClosedFlow t = 1 := by
  rw [← axialClosedFlow_add]
  simp

/-- The closed flow as a genuine real linear equivalence. -/
def axialClosedFlowEquiv (t : ℝ) : CZ ≃ₗ[ℝ] CZ where
  toLinearMap := axialClosedFlow t
  invFun := axialClosedFlow (-t)
  left_inv X := by
    have h := congrArg (fun F : EndCZ => F X) (axialClosedFlow_neg_mul t)
    simpa [Module.End.mul_apply] using h
  right_inv X := by
    have h := congrArg (fun F : EndCZ => F X) (axialClosedFlow_mul_neg t)
    simpa [Module.End.mul_apply] using h

@[simp] theorem axialClosedFlowEquiv_apply (t : ℝ) (X : CZ) :
    axialClosedFlowEquiv t X = axialClosedFlow t X :=
  rfl

@[simp] theorem axialClosedFlowEquiv_symm_apply (t : ℝ) (X : CZ) :
    (axialClosedFlowEquiv t).symm X = axialClosedFlow (-t) X :=
  rfl

/-- The stationary/Drazin-defect sector is fixed pointwise. -/
theorem axialClosedFlow_on_PZero (t : ℝ) (X : CZ) :
    axialClosedFlow t (axialPZero X) = axialPZero X := by
  rw [axialPZero_apply, axialClosedFlow_apply]
  ext i <;> simp

/-- The positive Peirce sector has weight `exp t`. -/
theorem axialClosedFlow_on_PPlus (t : ℝ) (X : CZ) :
    axialClosedFlow t (axialPPlus X) =
      (Real.exp t) • axialPPlus X := by
  rw [axialPPlus_apply, colorProject_apply, axialClosedFlow_apply]
  ext i <;> simp [Equiv.smul_def, coordEquiv]

/-- The negative Peirce sector has weight `exp (-t)`. -/
theorem axialClosedFlow_on_PMinus (t : ℝ) (X : CZ) :
    axialClosedFlow t (axialPMinus X) =
      (Real.exp (-t)) • axialPMinus X := by
  rw [axialPMinus_apply, anticolorProject_apply, axialClosedFlow_apply]
  ext i <;> simp [Equiv.smul_def, coordEquiv]

/-- Polynomial hyperbolic normal form of the full axial flow.

Because `axialGrading` is tripotent, its closed flow reduces to a polynomial
of degree two in the native endomorphism:

`Φ(t) = I + sinh(t) T + (cosh(t) - 1) T²`.

This is an equality in the actual noncommutative endomorphism ring; it does
not introduce an analytic operator exponential. -/
theorem axialClosedFlow_eq_hyperbolicPolynomial (t : ℝ) :
    axialClosedFlow t =
      1 + (Real.sinh t) • axialGrading +
        (Real.cosh t - 1) • (axialGrading * axialGrading) := by
  apply LinearMap.ext
  intro X
  ext i
  · simp [axialGrading, Module.End.mul_apply, Equiv.smul_def, coordEquiv]
  · simp [axialGrading, Module.End.mul_apply, Equiv.smul_def, coordEquiv]
  · simp [axialGrading, Module.End.mul_apply, Equiv.smul_def, coordEquiv]
    rw [← Real.cosh_add_sinh]
    ring
  · simp [axialGrading, Module.End.mul_apply, Equiv.smul_def, coordEquiv]
    rw [← Real.cosh_sub_sinh]
    ring

end InfoGeometry.Lie.SplitOctonionAxialClosedFlow
