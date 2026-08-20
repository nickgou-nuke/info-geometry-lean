import InfoGeometry.Physics.FiniteRelativeModularOperator
import InfoGeometry.Physics.HestenesSpinDensityXpQuantization

noncomputable section

/-!
# Finite spin-density relative modular bridge

The trace-normalized left and right Gram densities associated with a matrix
amplitude `A` satisfy

`densityMatrix A * A = A * rightDensityMatrix A`.

Consequently, whenever an explicit right inverse of `rightDensityMatrix A` is
supplied, `A` is fixed by the corresponding finite relative modular operator.
The adjoint amplitude satisfies the reversed statement.

No logarithmic functional calculus, Tomita--Takesaki theorem, polar
decomposition, KAN factorization, or unbounded-operator claim is asserted here.
The Gram operators `A * Aᴴ` and `Aᴴ * A` are the squares of the positive polar
factors, not the polar factors themselves.
-/

namespace InfoGeometry.Physics.FiniteSpinDensityRelativeModularBridge

open Matrix
open InfoGeometry.Physics.FiniteRelativeModularOperator
open InfoGeometry.Physics.HestenesSpinDensityXpQuantization
open scoped ComplexOrder MatrixOrder

abbrev M2C :=
  InfoGeometry.Physics.HestenesSpinDensityXpQuantization.M2C

/-- State-dependent relative modular operator determined by the left Gram
density and an explicitly supplied inverse of the right Gram density. -/
def spinRelativeModularOperator
    (A sigmaInv : M2C) : M2C →ₗ[ℂ] M2C :=
  relativeModularOperator (R := ℂ) (densityMatrix A) sigmaInv

@[simp] theorem spinRelativeModularOperator_apply
    (A sigmaInv X : M2C) :
    spinRelativeModularOperator A sigmaInv X =
      densityMatrix A * X * sigmaInv := by
  simp [spinRelativeModularOperator]

/-- The amplitude intertwines its normalized left and right Gram densities. -/
theorem spinDensity_intertwines (A : M2C) :
    densityMatrix A * A = A * rightDensityMatrix A :=
  densityMatrix_mul_affinity_eq_affinity_mul_rightDensityMatrix A

/-- The amplitude is a unit-eigenvalue vector of its relative modular operator
whenever the supplied right-density factor is a right inverse. -/
theorem spinRelativeModularOperator_affinity_fixed
    (A sigmaInv : M2C)
    (hSigma : rightDensityMatrix A * sigmaInv = 1) :
    spinRelativeModularOperator A sigmaInv A = A := by
  unfold spinRelativeModularOperator
  exact
    relativeModularOperator_fixed_of_intertwines
      (R := ℂ)
      (rho := densityMatrix A)
      (sigma := rightDensityMatrix A)
      (sigmaInv := sigmaInv)
      (X := A)
      (spinDensity_intertwines A)
      hSigma

/-- Raw relative modular data built from the two normalized Gram densities.
The inverse factors remain explicit candidate inverses. -/
def spinRelativeModularData
    (A rhoInv sigmaInv : M2C) :
    RelativeModularData ℂ M2C where
  rho := densityMatrix A
  rhoInv := rhoInv
  sigma := rightDensityMatrix A
  sigmaInv := sigmaInv

@[simp] theorem spinRelativeModularData_delta_apply
    (A rhoInv sigmaInv X : M2C) :
    (spinRelativeModularData A rhoInv sigmaInv).delta X =
      densityMatrix A * X * sigmaInv := by
  simp [spinRelativeModularData]

@[simp] theorem spinRelativeModularData_deltaInv_apply
    (A rhoInv sigmaInv X : M2C) :
    (spinRelativeModularData A rhoInv sigmaInv).deltaInv X =
      rhoInv * X * rightDensityMatrix A := by
  simp [spinRelativeModularData]

/-- Data-level form of the modular fixed-vector theorem. -/
theorem spinRelativeModularData_affinity_fixed
    (A rhoInv sigmaInv : M2C)
    (hSigma : rightDensityMatrix A * sigmaInv = 1) :
    (spinRelativeModularData A rhoInv sigmaInv).delta A = A := by
  change densityMatrix A * A * sigmaInv = A
  rw [spinDensity_intertwines]
  simpa [mul_assoc] using congrArg (fun X : M2C => A * X) hSigma

/-- The adjoint amplitude intertwines the right density with the left density. -/
theorem rightDensityMatrix_mul_conjTranspose_eq
    (A : M2C) :
    rightDensityMatrix A * Aᴴ = Aᴴ * densityMatrix A := by
  unfold rightDensityMatrix densityMatrix rightGram gram
  calc
    ((gramTrace A : ℂ)⁻¹ • (Aᴴ * A)) * Aᴴ =
        (gramTrace A : ℂ)⁻¹ • ((Aᴴ * A) * Aᴴ) := by
      simpa only [Matrix.smul_mul]
    _ = (gramTrace A : ℂ)⁻¹ • (Aᴴ * (A * Aᴴ)) := by
      rw [mul_assoc]
    _ = Aᴴ * ((gramTrace A : ℂ)⁻¹ • (A * Aᴴ)) := by
      simpa only [Matrix.mul_smul]

/-- The adjoint amplitude is fixed by the reversed relative modular operator
when the supplied left-density factor is a right inverse. -/
theorem reversedSpinRelativeModularOperator_conjTranspose_fixed
    (A rhoInv : M2C)
    (hRho : densityMatrix A * rhoInv = 1) :
    relativeModularOperator
        (R := ℂ) (rightDensityMatrix A) rhoInv Aᴴ = Aᴴ := by
  exact
    relativeModularOperator_fixed_of_intertwines
      (R := ℂ)
      (rho := rightDensityMatrix A)
      (sigma := densityMatrix A)
      (sigmaInv := rhoInv)
      (X := Aᴴ)
      (rightDensityMatrix_mul_conjTranspose_eq A)
      hRho

/-- The candidate inverse operator also fixes the amplitude when the supplied
left-density factor is a left inverse. -/
theorem spinRelativeModularData_deltaInv_affinity_fixed
    (A rhoInv sigmaInv : M2C)
    (hRho : rhoInv * densityMatrix A = 1) :
    (spinRelativeModularData A rhoInv sigmaInv).deltaInv A = A := by
  change rhoInv * A * rightDensityMatrix A = A
  calc
    rhoInv * A * rightDensityMatrix A =
        rhoInv * (A * rightDensityMatrix A) := by rw [mul_assoc]
    _ = rhoInv * (densityMatrix A * A) := by
      rw [← spinDensity_intertwines]
    _ = (rhoInv * densityMatrix A) * A := by rw [← mul_assoc]
    _ = A := by rw [hRho, one_mul]

/-- Two-sided inverse factors give the state-dependent relative modular linear
equivalence. -/
def spinRelativeModularEquiv
    (A rhoInv sigmaInv : M2C)
    (hInv :
      (spinRelativeModularData A rhoInv sigmaInv).HasTwoSidedInverses) :
    M2C ≃ₗ[ℂ] M2C :=
  (spinRelativeModularData A rhoInv sigmaInv).deltaEquiv hInv

@[simp] theorem spinRelativeModularEquiv_affinity_fixed
    (A rhoInv sigmaInv : M2C)
    (hInv :
      (spinRelativeModularData A rhoInv sigmaInv).HasTwoSidedInverses) :
    spinRelativeModularEquiv A rhoInv sigmaInv hInv A = A := by
  change (spinRelativeModularData A rhoInv sigmaInv).delta A = A
  exact spinRelativeModularData_affinity_fixed
    A rhoInv sigmaInv hInv.sigma_mul_sigmaInv

@[simp] theorem spinRelativeModularEquiv_symm_affinity_fixed
    (A rhoInv sigmaInv : M2C)
    (hInv :
      (spinRelativeModularData A rhoInv sigmaInv).HasTwoSidedInverses) :
    (spinRelativeModularEquiv A rhoInv sigmaInv hInv).symm A = A := by
  change (spinRelativeModularData A rhoInv sigmaInv).deltaInv A = A
  exact spinRelativeModularData_deltaInv_affinity_fixed
    A rhoInv sigmaInv hInv.rhoInv_mul_rho

/-- Consolidated finite state-dependent modular packet. -/
theorem finite_spin_density_relative_modular_chain
    {A : M2C} (hA : A ≠ 0)
    (sigmaInv : M2C)
    (hSigma : rightDensityMatrix A * sigmaInv = 1) :
    (densityMatrix A).PosSemidef ∧
      (rightDensityMatrix A).PosSemidef ∧
      (densityMatrix A).IsHermitian ∧
      (rightDensityMatrix A).IsHermitian ∧
      Matrix.trace (densityMatrix A) = 1 ∧
      Matrix.trace (rightDensityMatrix A) = 1 ∧
      spinRelativeModularOperator A sigmaInv A = A := by
  exact
    ⟨densityMatrix_posSemidef hA,
      rightDensityMatrix_posSemidef hA,
      densityMatrix_isHermitian_of_ne_zero hA,
      rightDensityMatrix_isHermitian_of_ne_zero hA,
      trace_densityMatrix_of_ne_zero hA,
      trace_rightDensityMatrix_of_ne_zero hA,
      spinRelativeModularOperator_affinity_fixed A sigmaInv hSigma⟩

end InfoGeometry.Physics.FiniteSpinDensityRelativeModularBridge

end noncomputable section
