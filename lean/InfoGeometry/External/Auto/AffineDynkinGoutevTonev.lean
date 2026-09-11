import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.External.Auto.iR
import InfoGeometry.External.Auto.GoutevTonevPrinciple

/-!
# Affine Dynkin null direction for the Goutev--Tonev unit

This module reads the active affine `A₁⁽¹⁾` Cartan lane before adding any new
interpretation.  The primitive imaginary root `δ = (1, 1)` is already proved to
be a null vector of the affine Cartan matrix in `iR.lean`.  Here we use that
finite null direction to select a Souriau modular generator and feed it into the
Goutev--Tonev operator information unit

`exp(ε K) - 1 - ε K`.

No analytic exponential convergence, positivity, or Dikin-ellipsoid geometry is
asserted.  The proved content is finite algebraic: Cartan-null plus operator
remainder identities.
-/

noncomputable section

namespace AffineDynkinGoutevTonev

open scoped BigOperators
open GoutevTonevPrinciple

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The affine `A₁⁽¹⁾` null quadratic form vanishes on the imaginary root. -/
theorem affine_delta_cartan_quadratic_zero :
    (Matrix.transpose imaginaryRootDelta * A1_1Cartan * imaginaryRootDelta) 0 0 = 0 := by
  norm_num [Matrix.mul_apply, A1_1Cartan, imaginaryRootDelta]

/-- Real coefficient of the affine imaginary root `δ`. -/
def affineDeltaCoeff (i : Fin 2) : ℝ :=
  (imaginaryRootDelta i 0 : ℝ)

@[simp] theorem affineDeltaCoeff_zero : affineDeltaCoeff 0 = 1 := by
  simp [affineDeltaCoeff, imaginaryRootDelta]

@[simp] theorem affineDeltaCoeff_one : affineDeltaCoeff 1 = 1 := by
  simp [affineDeltaCoeff, imaginaryRootDelta]

/-- Souriau modular generator selected by the affine null direction. -/
def affineNullSouriauGenerator (K : Fin 2 → A) : A :=
  ∑ i : Fin 2, affineDeltaCoeff i • K i

/-- Since `δ=(1,1)`, the null-direction generator is the sum of the two simple
operator directions. -/
theorem affineNullSouriauGenerator_eq_sum (K : Fin 2 → A) :
    affineNullSouriauGenerator K = K 0 + K 1 := by
  simp [affineNullSouriauGenerator, Fin.sum_univ_two]

/-- Goutev--Tonev information unit along the affine imaginary-root direction. -/
def affineNullInformationUnit (expOp : A → A) (ε : ℝ) (K : Fin 2 → A) : A :=
  informationUnit (A := A) expOp ε (affineNullSouriauGenerator K)

/-- Zero-coupling normalization along the affine null direction. -/
theorem affineNullInformationUnit_zero
    (expOp : A → A) (h0 : expOp 0 = (1 : A)) (K : Fin 2 → A) :
    affineNullInformationUnit expOp 0 K = 0 := by
  exact informationUnit_zero (A := A) expOp h0 (affineNullSouriauGenerator K)

/-- State readout of the affine-null Goutev--Tonev unit. -/
theorem expectation_affineNullInformationUnit
    (ω : A →ₗ[ℝ] ℝ) (expOp : A → A) (ε : ℝ) (K : Fin 2 → A) :
    ω (affineNullInformationUnit expOp ε K) =
      ω (expOp (ε • affineNullSouriauGenerator K)) - ω (1 : A) -
        ε * ω (affineNullSouriauGenerator K) := by
  exact expectation_informationUnit (A := A) (ω := ω) expOp ε (affineNullSouriauGenerator K)

end AffineDynkinGoutevTonev
