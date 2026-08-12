import InfoGeometry.Physics.RegularBimoduleCommutant
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic

noncomputable section

/-!
# Finite relative modular operator

This owner is the finite algebraic state-dependent specialization of the
regular left/right carrier.  The inverse factors are supplied explicitly;
this keeps the theorem boundary independent of a particular matrix inverse
or logarithmic functional-calculus implementation.

The modular interpretation is intentionally not promoted to a Tomita--Takesaki
statement here.  The owner proves only the finite bimodule identities.
-/

namespace InfoGeometry.Physics.FiniteRelativeModularOperator

open InfoGeometry.Physics.RegularBimoduleCommutant

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]

/-- The relative modular operator with an explicitly supplied right inverse
factor.  For faithful states this is instantiated by
`L ρ ∘ R (σ⁻¹)`. -/
def relativeModularOperator (rho sigmaInv : A) : A →ₗ[R] A :=
  (leftAction (R := R) rho).comp (rightAction (R := R) sigmaInv)

@[simp] theorem relativeModularOperator_apply (rho sigmaInv X : A) :
    relativeModularOperator (R := R) rho sigmaInv X = rho * X * sigmaInv := by
  simp [relativeModularOperator, leftAction, rightAction,
    LinearMap.comp_apply, mul_assoc]

/-- Finite relative modular data with explicit left and right inverse witnesses.
The fields are deliberately algebraic rather than spectral. -/
structure RelativeModularData (R A : Type*) [CommSemiring R] [Ring A]
    [Algebra R A] where
  rho : A
  rhoInv : A
  sigma : A
  sigmaInv : A
  rho_left_inv : rhoInv * rho = 1
  rho_right_inv : rho * rhoInv = 1
  sigma_left_inv : sigmaInv * sigma = 1
  sigma_right_inv : sigma * sigmaInv = 1

namespace RelativeModularData

def delta (D : RelativeModularData R A) : A →ₗ[R] A :=
  relativeModularOperator (R := R) D.rho D.sigmaInv

def deltaInv (D : RelativeModularData R A) : A →ₗ[R] A :=
  relativeModularOperator (R := R) D.rhoInv D.sigma

@[simp] theorem delta_apply (D : RelativeModularData R A)
    (X : A) :
    D.delta X = D.rho * X * D.sigmaInv := by
  simp [delta]

@[simp] theorem deltaInv_apply (D : RelativeModularData R A)
    (X : A) :
    D.deltaInv X = D.rhoInv * X * D.sigma := by
  simp [deltaInv]

theorem deltaInv_comp_delta (D : RelativeModularData R A) :
    D.deltaInv.comp D.delta = LinearMap.id := by
  ext X
  simp only [LinearMap.comp_apply, delta_apply, deltaInv_apply,
    LinearMap.id_apply]
  calc
    D.rhoInv * (D.rho * X * D.sigmaInv) * D.sigma =
        (D.rhoInv * D.rho) * X * (D.sigmaInv * D.sigma) := by
          simp [mul_assoc]
    _ = X := by rw [D.rho_left_inv, D.sigma_left_inv]; simp

theorem delta_comp_deltaInv (D : RelativeModularData R A) :
    D.delta.comp D.deltaInv = LinearMap.id := by
  ext X
  simp only [LinearMap.comp_apply, delta_apply, deltaInv_apply,
    LinearMap.id_apply]
  calc
    D.rho * (D.rhoInv * X * D.sigma) * D.sigmaInv =
        (D.rho * D.rhoInv) * X * (D.sigma * D.sigmaInv) := by
          simp [mul_assoc]
    _ = X := by rw [D.rho_right_inv, D.sigma_right_inv]; simp

theorem delta_bimodule_formula
    (D : RelativeModularData R A) (X : A) :
    D.delta X = D.rho * X * D.sigmaInv :=
  delta_apply D X

end RelativeModularData

section DiagonalMatrixUnits

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The standard matrix unit, written using the native dependent function basis. -/
def matrixUnit (i j : ι) : Matrix ι ι ℂ :=
  fun k l => if k = i then if l = j then 1 else 0 else 0

/-- The diagonal finite relative modular action.  The function `q` is the
diagonal of the right-state factor; nonvanishing assumptions are deliberately
left to later inverse/logarithm owners. -/
def diagonalRelativeModularAction (p q : ι → ℂ) (X : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  Matrix.diagonal p * X * Matrix.diagonal (fun j => (q j)⁻¹)

theorem diagonalRelativeModularAction_matrixUnit (p q : ι → ℂ) (i j : ι) :
    diagonalRelativeModularAction p q (matrixUnit i j) =
      (p i * (q j)⁻¹) • matrixUnit i j := by
  ext k l
  by_cases hki : k = i <;> by_cases hlj : l = j <;>
    simp [diagonalRelativeModularAction, matrixUnit,
      Matrix.diagonal_mul, Matrix.mul_diagonal, hki, hlj]

end DiagonalMatrixUnits

end InfoGeometry.Physics.FiniteRelativeModularOperator
