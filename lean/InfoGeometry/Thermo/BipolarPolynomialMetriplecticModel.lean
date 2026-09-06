import InfoGeometry.Thermo.BipolarObservableMetriplecticAlgebra
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Tactic

/-!
# Concrete polynomial model of the bipolar observable algebra

The abstract observable owner requires commuting `θ` and auxiliary
derivations. This file closes that local interface with the native polynomial
algebra

`ℝ[η, θ, a] = MvPolynomial (Fin 3) ℝ`.

The three coordinate derivatives are Mathlib's bundled
`MvPolynomial.pderiv`. Their commutation is proved by showing that the
commutator derivation vanishes on every polynomial generator. The resulting
frame therefore satisfies the Poisson Jacobi identity without an additional
hypothesis.

The coordinate observables

`H = θ`, `S = -η`

satisfy the mutual degeneracy laws. Their unified metriplectic evolution has
zero energy rate and unit entropy rate. Polynomial evaluation at any real
point supplies the ordered real readout required for nonnegativity.

This is an exact algebraic observable model. Extending the same construction
to a chosen algebra of smooth functions is a separate analytic theorem.
-/

noncomputable section

namespace InfoGeometry.Thermo.BipolarPolynomialMetriplecticModel

open InfoGeometry.Thermo.BipolarObservableMetriplecticAlgebra

abbrev ObservablePoly := MvPolynomial (Fin 3) ℝ

/-- Coordinate indices. -/
def etaIndex : Fin 3 := 0

def thetaIndex : Fin 3 := 1

def auxiliaryIndex : Fin 3 := 2

/-- Native coordinate observables. -/
def etaObservable : ObservablePoly := MvPolynomial.X etaIndex

def thetaObservable : ObservablePoly := MvPolynomial.X thetaIndex

def auxiliaryObservable : ObservablePoly := MvPolynomial.X auxiliaryIndex

/-- Formal partial derivatives commute on the native multivariate polynomial
algebra. -/
theorem pderiv_commute
    (i j : Fin 3) (F : ObservablePoly) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j F) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i F) := by
  classical
  let C : Derivation ℝ ObservablePoly ObservablePoly :=
    ⁅(MvPolynomial.pderiv i : Derivation ℝ ObservablePoly ObservablePoly),
      (MvPolynomial.pderiv j : Derivation ℝ ObservablePoly ObservablePoly)⁆
  have hC : C = 0 := by
    apply MvPolynomial.derivation_ext
    intro k
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp [C, Derivation.commutator_apply, MvPolynomial.pderiv_def]
  have hzero :
      MvPolynomial.pderiv i (MvPolynomial.pderiv j F) -
        MvPolynomial.pderiv j (MvPolynomial.pderiv i F) = 0 := by
    have h := Derivation.congr_fun hC F
    simpa [C, Derivation.commutator_apply] using h
  exact sub_eq_zero.mp hzero

/-- The concrete native derivation frame on `ℝ[η,θ,a]`. -/
def polynomialFrame : DerivationFrame ObservablePoly where
  Deta := MvPolynomial.pderiv etaIndex
  Dtheta := MvPolynomial.pderiv thetaIndex
  Da := MvPolynomial.pderiv auxiliaryIndex
  commute_theta_a := pderiv_commute thetaIndex auxiliaryIndex

@[simp] theorem Deta_eta :
    polynomialFrame.Deta etaObservable = 1 := by
  simp [polynomialFrame, etaObservable, etaIndex]

@[simp] theorem Deta_theta :
    polynomialFrame.Deta thetaObservable = 0 := by
  simp [polynomialFrame, etaObservable, thetaObservable,
    etaIndex, thetaIndex]

@[simp] theorem Deta_auxiliary :
    polynomialFrame.Deta auxiliaryObservable = 0 := by
  simp [polynomialFrame, auxiliaryObservable,
    etaIndex, auxiliaryIndex]

@[simp] theorem Dtheta_eta :
    polynomialFrame.Dtheta etaObservable = 0 := by
  simp [polynomialFrame, etaObservable, etaIndex, thetaIndex]

@[simp] theorem Dtheta_theta :
    polynomialFrame.Dtheta thetaObservable = 1 := by
  simp [polynomialFrame, thetaObservable, thetaIndex]

@[simp] theorem Dtheta_auxiliary :
    polynomialFrame.Dtheta auxiliaryObservable = 0 := by
  simp [polynomialFrame, auxiliaryObservable,
    thetaIndex, auxiliaryIndex]

@[simp] theorem Da_eta :
    polynomialFrame.Da etaObservable = 0 := by
  simp [polynomialFrame, etaObservable, etaIndex, auxiliaryIndex]

@[simp] theorem Da_theta :
    polynomialFrame.Da thetaObservable = 0 := by
  simp [polynomialFrame, thetaObservable, thetaIndex, auxiliaryIndex]

@[simp] theorem Da_auxiliary :
    polynomialFrame.Da auxiliaryObservable = 1 := by
  simp [polynomialFrame, auxiliaryObservable, auxiliaryIndex]

/-- Canonical coordinate Poisson relation `{θ,a}=1`. -/
theorem theta_auxiliary_poisson :
    poissonBracket polynomialFrame thetaObservable auxiliaryObservable = 1 := by
  simp [poissonBracket]

/-- Reverse coordinate relation `{a,θ}=-1`. -/
theorem auxiliary_theta_poisson :
    poissonBracket polynomialFrame auxiliaryObservable thetaObservable = -1 := by
  simp [poissonBracket]

/-- The longitudinal coordinate is central for the Poisson lane. -/
theorem eta_poisson_central (F : ObservablePoly) :
    poissonBracket polynomialFrame F etaObservable = 0 := by
  simp [poissonBracket]

/-- Polynomial evaluation at a real three-coordinate point. -/
def evalAt (x : Fin 3 → ℝ) : ObservablePoly →+* ℝ :=
  MvPolynomial.eval₂Hom (RingHom.id ℝ) x

/-- Hamiltonian and entropy observables in the concrete model. -/
def polynomialHamiltonian : ObservablePoly := thetaObservable

def polynomialEntropy : ObservablePoly := -etaObservable

/-- The entropy observable is a Poisson Casimir. -/
theorem polynomialEntropy_poissonCasimir :
    IsPoissonCasimir polynomialFrame polynomialEntropy := by
  apply isPoissonCasimir_of_invariant
  · simp [polynomialEntropy]
  · simp [polynomialEntropy]

/-- The Hamiltonian observable is in the metric kernel. -/
theorem polynomialHamiltonian_metricKernel :
    IsMetricKernel polynomialFrame polynomialHamiltonian := by
  apply isMetricKernel_of_eta_invariant
  simp [polynomialHamiltonian]

/-- Exact energy conservation in the concrete polynomial observable algebra. -/
theorem polynomial_first_law :
    metriplecticBracket polynomialFrame polynomialHamiltonian
      (polynomialHamiltonian + polynomialEntropy) = 0 := by
  exact metriplectic_first_law polynomialFrame
    polynomialHamiltonian polynomialEntropy
    polynomialEntropy_poissonCasimir
    polynomialHamiltonian_metricKernel

/-- The entropy rate is the unit polynomial. -/
theorem polynomial_second_law :
    metriplecticBracket polynomialFrame polynomialEntropy
      (polynomialHamiltonian + polynomialEntropy) = 1 := by
  rw [metriplectic_second_law polynomialFrame
    polynomialHamiltonian polynomialEntropy
    polynomialEntropy_poissonCasimir
    polynomialHamiltonian_metricKernel]
  simp [polynomialEntropy]

/-- Every point evaluation sees the normalized nonnegative entropy rate `1`. -/
theorem polynomial_second_law_evaluation
    (x : Fin 3 → ℝ) :
    evalAt x
      (metriplecticBracket polynomialFrame polynomialEntropy
        (polynomialHamiltonian + polynomialEntropy)) = 1 := by
  rw [polynomial_second_law]
  simp [evalAt]

/-- In particular every point evaluation sees nonnegative entropy production. -/
theorem polynomial_second_law_nonneg
    (x : Fin 3 → ℝ) :
    0 ≤ evalAt x
      (metriplecticBracket polynomialFrame polynomialEntropy
        (polynomialHamiltonian + polynomialEntropy)) := by
  rw [polynomial_second_law_evaluation]
  norm_num

/-- Jacobi is now a theorem for a concrete native observable algebra, not a
field supplied to an abstract structure. -/
theorem polynomial_poisson_jacobi (F G H : ObservablePoly) :
    poissonBracket polynomialFrame (poissonBracket polynomialFrame F G) H +
      poissonBracket polynomialFrame (poissonBracket polynomialFrame G H) F +
      poissonBracket polynomialFrame (poissonBracket polynomialFrame H F) G = 0 := by
  exact poissonBracket_jacobi polynomialFrame F G H

/-- Compact concrete model packet. -/
theorem bipolar_polynomial_metriplectic_packet
    (F G H : ObservablePoly) (x : Fin 3 → ℝ) :
    poissonBracket polynomialFrame (poissonBracket polynomialFrame F G) H +
        poissonBracket polynomialFrame (poissonBracket polynomialFrame G H) F +
        poissonBracket polynomialFrame (poissonBracket polynomialFrame H F) G = 0 ∧
      poissonBracket polynomialFrame thetaObservable auxiliaryObservable = 1 ∧
      metriplecticBracket polynomialFrame polynomialHamiltonian
        (polynomialHamiltonian + polynomialEntropy) = 0 ∧
      metriplecticBracket polynomialFrame polynomialEntropy
        (polynomialHamiltonian + polynomialEntropy) = 1 ∧
      0 ≤ evalAt x
        (metriplecticBracket polynomialFrame polynomialEntropy
          (polynomialHamiltonian + polynomialEntropy)) := by
  exact ⟨polynomial_poisson_jacobi F G H,
    theta_auxiliary_poisson,
    polynomial_first_law,
    polynomial_second_law,
    polynomial_second_law_nonneg x⟩

end InfoGeometry.Thermo.BipolarPolynomialMetriplecticModel
