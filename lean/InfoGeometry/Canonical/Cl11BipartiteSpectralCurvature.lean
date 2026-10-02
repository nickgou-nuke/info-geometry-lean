import Mathlib.Tactic

import InfoGeometry.Canonical.Cl11BipartiteOrderOneCondition
import InfoGeometry.Canonical.Cl11BipartiteDiracBridge

/-!
# Native finite gauge curvature on the Cl(1,1) left factor

This module formalizes the finite algebraic gauge-curvature identities on the
repository-owned stage-one matrix carrier.

For a fixed background operator D and fluctuation A, define

  D_cov(D,A) = D + A,

and the square-defect curvature

  F_D(A) = D_cov(D,A)^2 - D^2
         = D A + A D + A^2.

For a unit u, the affine gauge transform

  A^u = u (D + A) u^{-1} - D

satisfies the exact covariant-Dirac law

  D_cov(D,A^u) = u D_cov(D,A) u^{-1},

and hence the covariant square transforms homogeneously.

The fixed-background square defect obeys the exact correction formula

  F_D(A^u)
    = u F_D(A) u^{-1}
      + (u D^2 u^{-1} - D^2).

Therefore strict homogeneous curvature covariance follows when the background
square is invariant under u.

This distinction is essential: with the ordinary commutator
[D,A] = D A - A D, the expression [D,A] + A^2 is not equal to
(D+A)^2 - D^2 in an ordinary associative matrix algebra.

No analytic spectral-action, heat-kernel, or unbounded spectral-triple claim
is made here.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11BipartiteSpectralCurvature

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Canonical.Cl11BipartiteDiracBridge
open InfoGeometry.Canonical.Cl11BipartiteOrderOneCondition

abbrev StageOne := MatStage 1
abbrev StageTwo := MatStage 2
abbrev Atom := InfoGeometry.Clifford.Cl11Matrix.Mat2

/-- Conjugation by a unit of the native stage-one matrix algebra. -/
def unitConjugate (u : Units StageOne) (X : StageOne) : StageOne :=
  (u : StageOne) * X * (↑u⁻¹ : StageOne)

@[simp] theorem unitConjugate_zero (u : Units StageOne) :
    unitConjugate u 0 = 0 := by
  simp [unitConjugate]

@[simp] theorem unitConjugate_add
    (u : Units StageOne) (X Y : StageOne) :
    unitConjugate u (X + Y) =
      unitConjugate u X + unitConjugate u Y := by
  simp [unitConjugate, add_mul, mul_add]

@[simp] theorem unitConjugate_sub
    (u : Units StageOne) (X Y : StageOne) :
    unitConjugate u (X - Y) =
      unitConjugate u X - unitConjugate u Y := by
  simp [unitConjugate, sub_mul, mul_sub]

@[simp] theorem unitConjugate_mul
    (u : Units StageOne) (X Y : StageOne) :
    unitConjugate u (X * Y) =
      unitConjugate u X * unitConjugate u Y := by
  simp [unitConjugate, mul_assoc]

/-- Covariant Dirac operator D + A. -/
def covariantDirac (D A : StageOne) : StageOne :=
  D + A

/-- Affine gauge transform A ↦ u(D+A)u⁻¹ - D. -/
def gaugeTransform (u : Units StageOne) (D A : StageOne) : StageOne :=
  unitConjugate u (covariantDirac D A) - D

/-- Exact affine gauge law for the covariant Dirac operator. -/
theorem covariantDirac_gauge_law
    (u : Units StageOne) (D A : StageOne) :
    covariantDirac D (gaugeTransform u D A) =
      unitConjugate u (covariantDirac D A) := by
  simp [covariantDirac, gaugeTransform]

/-- Square of the covariant Dirac operator. -/
def covariantSquare (D A : StageOne) : StageOne :=
  covariantDirac D A * covariantDirac D A

/-- The covariant square transforms homogeneously without any extra
background-invariance hypothesis. -/
theorem covariantSquare_gauge_covariant
    (u : Units StageOne) (D A : StageOne) :
    covariantSquare D (gaugeTransform u D A) =
      unitConjugate u (covariantSquare D A) := by
  rw [covariantSquare, covariantDirac_gauge_law,
    unitConjugate_mul]
  rfl

/-- Fixed-background square-defect curvature. -/
def curvatureDefect (D A : StageOne) : StageOne :=
  covariantSquare D A - D * D

/-- Exact expansion:
F_D(A) = D A + A D + A². -/
theorem curvatureDefect_expansion (D A : StageOne) :
    curvatureDefect D A =
      D * A + A * D + A * A := by
  unfold curvatureDefect covariantSquare covariantDirac
  noncomm_ring

/-- Ordinary-commutator candidate [D,A] + A².  This is recorded explicitly
to audit the difference from the square-defect curvature. -/
def commutatorCurvatureCandidate (D A : StageOne) : StageOne :=
  (D * A - A * D) + A * A

/-- The square-defect curvature and ordinary-commutator candidate differ by
twice the right mixed term. -/
theorem curvatureDefect_eq_commutatorCandidate_add_two_right
    (D A : StageOne) :
    curvatureDefect D A =
      commutatorCurvatureCandidate D A + (2 : ℝ) • (A * D) := by
  rw [curvatureDefect_expansion]
  unfold commutatorCurvatureCandidate
  module

/-- Exact transformation law for the fixed-background curvature defect. -/
theorem curvatureDefect_gauge_correction
    (u : Units StageOne) (D A : StageOne) :
    curvatureDefect D (gaugeTransform u D A) =
      unitConjugate u (curvatureDefect D A) +
        (unitConjugate u (D * D) - D * D) := by
  unfold curvatureDefect
  rw [covariantSquare_gauge_covariant]
  rw [← unitConjugate_sub]
  abel

/-- Strict homogeneous curvature covariance under the necessary invariance of
the background square. -/
theorem curvatureDefect_gauge_covariant
    (u : Units StageOne) (D A : StageOne)
    (hDsq : unitConjugate u (D * D) = D * D) :
    curvatureDefect D (gaugeTransform u D A) =
      unitConjugate u (curvatureDefect D A) := by
  rw [curvatureDefect_gauge_correction, hDsq]
  simp

/-- A sufficient condition: if u commutes with D², then conjugation fixes D². -/
theorem unitConjugate_sq_eq_of_commute
    (u : Units StageOne) (D : StageOne)
    (hcomm : (u : StageOne) * (D * D) = (D * D) * (u : StageOne)) :
    unitConjugate u (D * D) = D * D := by
  calc
    unitConjugate u (D * D)
        = (D * D) * (u : StageOne) * (↑u⁻¹ : StageOne) := by
            rw [unitConjugate, hcomm]
    _ = D * D := by simp [mul_assoc]

/-- Homogeneous curvature covariance under the transparent commutation
hypothesis [u,D²]=0. -/
theorem curvatureDefect_gauge_covariant_of_commute
    (u : Units StageOne) (D A : StageOne)
    (hcomm : (u : StageOne) * (D * D) = (D * D) * (u : StageOne)) :
    curvatureDefect D (gaugeTransform u D A) =
      unitConjugate u (curvatureDefect D A) := by
  apply curvatureDefect_gauge_covariant
  exact unitConjugate_sq_eq_of_commute u D hcomm


/-! ## Finite spectral trace invariance -/

/-- Native matrix trace on the stage-one carrier. -/
def spectralTrace (X : StageOne) : ℝ :=
  Matrix.trace X

/-- Trace is invariant under conjugation by a unit. -/
theorem spectralTrace_unitConjugate
    (u : Units StageOne) (X : StageOne) :
    spectralTrace (unitConjugate u X) = spectralTrace X := by
  unfold spectralTrace unitConjugate
  calc
    Matrix.trace ((u : StageOne) * X * (↑u⁻¹ : StageOne))
        = Matrix.trace ((X * (↑u⁻¹ : StageOne)) * (u : StageOne)) := by
            rw [Matrix.trace_mul_comm]
    _ = Matrix.trace (X * ((↑u⁻¹ : StageOne) * (u : StageOne))) := by
            rw [Matrix.mul_assoc]
    _ = Matrix.trace X := by simp

/-- Quadratic spectral trace built from the covariant Dirac square. -/
def quadraticSpectralTrace (D A : StageOne) : ℝ :=
  spectralTrace (covariantSquare D A)

/-- Exact finite gauge invariance of the quadratic spectral trace. -/
theorem quadraticSpectralTrace_gauge_invariant
    (u : Units StageOne) (D A : StageOne) :
    quadraticSpectralTrace D (gaugeTransform u D A) =
      quadraticSpectralTrace D A := by
  unfold quadraticSpectralTrace
  rw [covariantSquare_gauge_covariant]
  exact spectralTrace_unitConjugate u (covariantSquare D A)

/-- Equivalent direct trace statement for the squared covariant Dirac. -/
theorem trace_covariantSquare_gauge_invariant
    (u : Units StageOne) (D A : StageOne) :
    Matrix.trace (covariantSquare D (gaugeTransform u D A)) =
      Matrix.trace (covariantSquare D A) := by
  exact quadraticSpectralTrace_gauge_invariant u D A

/-! ## Bipartite readout -/

/-- Left-sheet curvature embedded in the doubled stage-two carrier. -/
def bipartiteLeftCurvature (D A : StageOne) : StageTwo :=
  curvatureDefect D A ⊗ₖ (1 : Atom)

/-- The left curvature is entirely supported in the left tensor factor by
construction. -/
theorem bipartiteLeftCurvature_eq
    (D A : StageOne) :
    bipartiteLeftCurvature D A =
      curvatureDefect D A ⊗ₖ (1 : Atom) :=
  rfl

end InfoGeometry.Canonical.Cl11BipartiteSpectralCurvature
