import InfoGeometry.Physics.RegularBimoduleCommutant
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic

noncomputable section

/-!
# Finite relative modular operator

This owner is the finite algebraic state-dependent specialization of the
regular left/right carrier. The inverse factors are supplied explicitly;
this keeps the theorem boundary independent of a particular matrix inverse,
positivity theorem, or logarithmic functional-calculus implementation.

The modular interpretation is intentionally not promoted to a
Tomita--Takesaki statement here. The owner proves only finite bimodule
identities, their inverse laws, and the diagonal matrix-unit spectrum.
-/

namespace InfoGeometry.Physics.FiniteRelativeModularOperator

open InfoGeometry.Physics.RegularBimoduleCommutant

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]

/-- The regular-bimodule relative multiplication operator
`X ↦ ρ * X * σInv`.

The second argument is an explicitly supplied right factor. This definition
does not assert that it is the inverse of another element. -/
def relativeModularOperator (rho sigmaInv : A) : A →ₗ[R] A :=
  (leftAction (R := R) rho).comp (rightAction (R := R) sigmaInv)

@[simp] theorem relativeModularOperator_apply
    (rho sigmaInv X : A) :
    relativeModularOperator (R := R) rho sigmaInv X =
      rho * X * sigmaInv := by
  simp [relativeModularOperator, leftAction, rightAction,
    LinearMap.comp_apply, mul_assoc]

/-- Identity relative multiplication. -/
@[simp] theorem relativeModularOperator_one_one :
    relativeModularOperator (R := R) (1 : A) 1 = LinearMap.id := by
  ext X
  simp

/-- Composition in the regular bimodule.

The right factors occur in reverse order because right multiplication is an
action of the opposite algebra. -/
theorem relativeModularOperator_comp
    (rho₁ sigmaInv₁ rho₂ sigmaInv₂ : A) :
    (relativeModularOperator (R := R) rho₁ sigmaInv₁).comp
        (relativeModularOperator (R := R) rho₂ sigmaInv₂) =
      relativeModularOperator
        (R := R) (rho₁ * rho₂) (sigmaInv₂ * sigmaInv₁) := by
  ext X
  simp only [LinearMap.comp_apply, relativeModularOperator_apply]
  simp [mul_assoc]

/-- An intertwiner between the left and right factors is fixed by the relative
operator once the supplied right factor is a right inverse. -/
theorem relativeModularOperator_fixed_of_intertwines
    (rho sigma sigmaInv X : A)
    (hIntertwines : rho * X = X * sigma)
    (hRightInv : sigma * sigmaInv = 1) :
    relativeModularOperator (R := R) rho sigmaInv X = X := by
  rw [relativeModularOperator_apply, hIntertwines]
  calc
    (X * sigma) * sigmaInv = X * (sigma * sigmaInv) := by
      rw [mul_assoc]
    _ = X := by
      rw [hRightInv, mul_one]

/-- A scaled intertwiner is an eigenvector of the relative operator. -/
theorem relativeModularOperator_eigenvector_of_scaled_intertwines
    (rho sigma sigmaInv X : A)
    (c : R)
    (hIntertwines : rho * X = c • (X * sigma))
    (hRightInv : sigma * sigmaInv = 1) :
    relativeModularOperator (R := R) rho sigmaInv X = c • X := by
  rw [relativeModularOperator_apply, hIntertwines]
  calc
    (c • (X * sigma)) * sigmaInv =
        c • ((X * sigma) * sigmaInv) := by
      exact smul_mul_assoc c (X * sigma) sigmaInv
    _ = c • X := by
      rw [mul_assoc, hRightInv, mul_one]

/-- Finite relative modular data with explicit candidate left and right
inverse factors. The fields are algebraic rather than spectral. -/
structure RelativeModularData
    (R A : Type*) [CommSemiring R] [Ring A] [Algebra R A] where
  rho : A
  rhoInv : A
  sigma : A
  sigmaInv : A

namespace RelativeModularData

/-- Relative modular endomorphism `L_ρ R_{σInv}`. -/
def delta (D : RelativeModularData R A) : A →ₗ[R] A :=
  relativeModularOperator (R := R) D.rho D.sigmaInv

/-- Candidate inverse endomorphism `L_{rhoInv} R_σ`. -/
def deltaInv (D : RelativeModularData R A) : A →ₗ[R] A :=
  relativeModularOperator (R := R) D.rhoInv D.sigma

@[simp] theorem delta_apply
    (D : RelativeModularData R A)
    (X : A) :
    D.delta X = D.rho * X * D.sigmaInv := by
  simp [delta]

@[simp] theorem deltaInv_apply
    (D : RelativeModularData R A)
    (X : A) :
    D.deltaInv X = D.rhoInv * X * D.sigma := by
  simp [deltaInv]

/-- Left inverse identity for the candidate inverse operator. -/
theorem deltaInv_comp_delta
    (D : RelativeModularData R A)
    (hρ : D.rhoInv * D.rho = 1)
    (hσ : D.sigmaInv * D.sigma = 1) :
    D.deltaInv.comp D.delta = LinearMap.id := by
  ext X
  simp only [
    LinearMap.comp_apply,
    delta_apply,
    deltaInv_apply,
    LinearMap.id_apply
  ]
  calc
    D.rhoInv * (D.rho * X * D.sigmaInv) * D.sigma =
        (D.rhoInv * D.rho) * X *
          (D.sigmaInv * D.sigma) := by
      simp [mul_assoc]
    _ = X := by
      rw [hρ, hσ]
      simp

/-- Right inverse identity for the candidate inverse operator. -/
theorem delta_comp_deltaInv
    (D : RelativeModularData R A)
    (hρ : D.rho * D.rhoInv = 1)
    (hσ : D.sigma * D.sigmaInv = 1) :
    D.delta.comp D.deltaInv = LinearMap.id := by
  ext X
  simp only [
    LinearMap.comp_apply,
    delta_apply,
    deltaInv_apply,
    LinearMap.id_apply
  ]
  calc
    D.rho * (D.rhoInv * X * D.sigma) * D.sigmaInv =
        (D.rho * D.rhoInv) * X *
          (D.sigma * D.sigmaInv) := by
      simp [mul_assoc]
    _ = X := by
      rw [hρ, hσ]
      simp

/-- Proof-carrying two-sided invertibility of all supplied factors. -/
structure HasTwoSidedInverses
    (D : RelativeModularData R A) : Prop where
  rhoInv_mul_rho : D.rhoInv * D.rho = 1
  rho_mul_rhoInv : D.rho * D.rhoInv = 1
  sigmaInv_mul_sigma : D.sigmaInv * D.sigma = 1
  sigma_mul_sigmaInv : D.sigma * D.sigmaInv = 1

/-- A finite relative modular operator with two-sided inverse factors is a
native linear equivalence of the regular bimodule carrier. -/
def deltaEquiv
    (D : RelativeModularData R A)
    (hD : D.HasTwoSidedInverses) :
    A ≃ₗ[R] A where
  toLinearMap := D.delta
  invFun := D.deltaInv
  left_inv := by
    intro X
    have h :=
      congrArg
        (fun f : A →ₗ[R] A => f X)
        (deltaInv_comp_delta
          D
          hD.rhoInv_mul_rho
          hD.sigmaInv_mul_sigma)
    simpa using h
  right_inv := by
    intro X
    have h :=
      congrArg
        (fun f : A →ₗ[R] A => f X)
        (delta_comp_deltaInv
          D
          hD.rho_mul_rhoInv
          hD.sigma_mul_sigmaInv)
    simpa using h

@[simp] theorem deltaEquiv_apply
    (D : RelativeModularData R A)
    (hD : D.HasTwoSidedInverses)
    (X : A) :
    D.deltaEquiv hD X =
      D.rho * X * D.sigmaInv := by
  simp [deltaEquiv, D.delta_apply X]

@[simp] theorem deltaEquiv_symm_apply
    (D : RelativeModularData R A)
    (hD : D.HasTwoSidedInverses)
    (X : A) :
    (D.deltaEquiv hD).symm X =
      D.rhoInv * X * D.sigma := by
  simp [deltaEquiv, D.deltaInv_apply X]

/-- Re-export of the finite bimodule formula. -/
theorem delta_bimodule_formula
    (D : RelativeModularData R A)
    (X : A) :
    D.delta X = D.rho * X * D.sigmaInv :=
  D.delta_apply X

end RelativeModularData

section DiagonalMatrixUnits

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The standard matrix unit, written using the native dependent-function
basis. -/
def matrixUnit (i j : ι) : Matrix ι ι ℂ :=
  fun k l =>
    if k = i then
      if l = j then 1 else 0
    else
      0

/-- The diagonal finite relative modular action as an unbundled readout.

The function `q` is the diagonal of the right-state factor. -/
def diagonalRelativeModularAction
    (p q : ι → ℂ)
    (X : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  Matrix.diagonal p *
    X *
    Matrix.diagonal (fun j => (q j)⁻¹)

/-- Diagonal relative modular data with pointwise candidate inverses. -/
def diagonalRelativeModularData
    (p q : ι → ℂ) :
    RelativeModularData ℂ (Matrix ι ι ℂ) where
  rho := Matrix.diagonal p
  rhoInv := Matrix.diagonal fun i => (p i)⁻¹
  sigma := Matrix.diagonal q
  sigmaInv := Matrix.diagonal fun j => (q j)⁻¹

/-- The same diagonal action as a bundled complex-linear endomorphism, derived
from the generic relative modular owner. -/
def diagonalRelativeModularEnd
    (p q : ι → ℂ) :
    Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ :=
  (diagonalRelativeModularData p q).delta

@[simp] theorem diagonalRelativeModularEnd_apply
    (p q : ι → ℂ)
    (X : Matrix ι ι ℂ) :
    diagonalRelativeModularEnd p q X =
      diagonalRelativeModularAction p q X := by
  simp [
    diagonalRelativeModularEnd,
    diagonalRelativeModularData,
    diagonalRelativeModularAction
  ]

@[simp] theorem diagonalRelativeModularAction_entry
    (p q : ι → ℂ)
    (X : Matrix ι ι ℂ)
    (k l : ι) :
    diagonalRelativeModularAction p q X k l =
      p k * X k l * (q l)⁻¹ := by
  simp [diagonalRelativeModularAction]

/-- Every matrix unit is an eigenvector of the diagonal relative modular
operator, with eigenvalue `p i * (q j)⁻¹`. -/
theorem diagonalRelativeModularAction_matrixUnit
    (p q : ι → ℂ)
    (i j : ι) :
    diagonalRelativeModularAction p q (matrixUnit i j) =
      (p i * (q j)⁻¹) • matrixUnit i j := by
  ext k l
  by_cases hki : k = i <;>
    by_cases hlj : l = j <;>
      simp [
        diagonalRelativeModularAction,
        matrixUnit,
        Matrix.diagonal_mul,
        Matrix.mul_diagonal,
        hki,
        hlj
      ]

/-- Bundled form of the matrix-unit eigenvector theorem. -/
theorem diagonalRelativeModularEnd_matrixUnit
    (p q : ι → ℂ)
    (i j : ι) :
    diagonalRelativeModularEnd p q (matrixUnit i j) =
      (p i * (q j)⁻¹) • matrixUnit i j := by
  rw [diagonalRelativeModularEnd_apply]
  exact diagonalRelativeModularAction_matrixUnit p q i j

/-- Nonvanishing diagonal entries certify all four inverse-factor laws. -/
theorem diagonalRelativeModularData_hasTwoSidedInverses
    (p q : ι → ℂ)
    (hp : ∀ i, p i ≠ 0)
    (hq : ∀ i, q i ≠ 0) :
    (diagonalRelativeModularData p q).HasTwoSidedInverses := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    ext i j
    by_cases hij : i = j
    · subst j
      simp [diagonalRelativeModularData, hp, hq]
    · simp [diagonalRelativeModularData, hij]

/-- Faithful diagonal factors give a linear automorphism of the matrix
bimodule. -/
def diagonalRelativeModularEquiv
    (p q : ι → ℂ)
    (hp : ∀ i, p i ≠ 0)
    (hq : ∀ i, q i ≠ 0) :
    Matrix ι ι ℂ ≃ₗ[ℂ] Matrix ι ι ℂ :=
  (diagonalRelativeModularData p q).deltaEquiv
    (diagonalRelativeModularData_hasTwoSidedInverses
      p q hp hq)

@[simp] theorem diagonalRelativeModularEquiv_matrixUnit
    (p q : ι → ℂ)
    (hp : ∀ i, p i ≠ 0)
    (hq : ∀ i, q i ≠ 0)
    (i j : ι) :
    diagonalRelativeModularEquiv p q hp hq (matrixUnit i j) =
      (p i * (q j)⁻¹) • matrixUnit i j := by
  change
    diagonalRelativeModularEnd p q (matrixUnit i j) =
      (p i * (q j)⁻¹) • matrixUnit i j
  exact diagonalRelativeModularEnd_matrixUnit p q i j

end DiagonalMatrixUnits

end InfoGeometry.Physics.FiniteRelativeModularOperator

end noncomputable section
