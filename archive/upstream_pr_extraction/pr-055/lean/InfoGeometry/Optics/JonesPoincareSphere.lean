import Mathlib.Tactic
import InfoGeometry.Geometry.PauliParavectorBridge
import InfoGeometry.Optics.FiniteJonesModel
import InfoGeometry.Twistor.Incidence

/-!
# Finite Jones/Poincare-sphere bridge

This module formalizes the finite algebraic core behind the Jones-vector,
two-component spinor, Poincare-sphere, Pauli-paravector, and twistor-incidence
dictionary.

The proved content is deliberately finite:

* Jones vectors and Weyl spinors share the carrier `Fin 2 -> ℂ`;
* real coordinates of a Jones vector define Stokes coordinates;
* the Stokes coordinates satisfy the light-cone identity;
* unit-intensity Jones vectors land on the unit Poincare sphere;
* circular-basis projectors are the existing finite Jones projectors;
* the Stokes four-vector has zero Pauli/Hestenes determinant;
* twistor incidence null separation is re-exported from the twistor owner.

No smooth geodesy, Bures-curvature theorem, or global twistor reconstruction
theorem is asserted here.
-/

noncomputable section

namespace InfoGeometry.Optics.JonesPoincareSphere

open scoped Matrix
open InfoGeometry.Geometry.PauliParavectorBridge

/-! ## Jones vectors and spinors -/

/-- Finite Jones vector carrier. -/
abbrev JonesVec : Type :=
  Fin 2 → ℂ

/-- Finite two-component Weyl spinor carrier. -/
abbrev WeylSpinor : Type :=
  Fin 2 → ℂ

/-- In this finite model, Jones vectors and Weyl spinors are the same complex plane. -/
def jonesSpinorEquiv : JonesVec ≃ₗ[ℂ] WeylSpinor :=
  LinearEquiv.refl ℂ JonesVec

@[simp]
theorem jonesSpinorEquiv_apply (J : JonesVec) :
    jonesSpinorEquiv J = J :=
  rfl

/-! ## Stokes coordinates from real Jones coordinates -/

/--
Real coordinate presentation of a finite Jones spinor:
`alpha = aRe + i aIm`, `beta = bRe + i bIm`.
-/
def JonesSpinor : Type :=
  (ℝ × ℝ) × (ℝ × ℝ)

namespace JonesSpinor

@[simp] def aRe (J : JonesSpinor) : ℝ :=
  J.1.1

@[simp] def aIm (J : JonesSpinor) : ℝ :=
  J.1.2

@[simp] def bRe (J : JonesSpinor) : ℝ :=
  J.2.1

@[simp] def bIm (J : JonesSpinor) : ℝ :=
  J.2.2

/-- First component intensity. -/
def leftIntensity (J : JonesSpinor) : ℝ :=
  J.aRe ^ 2 + J.aIm ^ 2

/-- Second component intensity. -/
def rightIntensity (J : JonesSpinor) : ℝ :=
  J.bRe ^ 2 + J.bIm ^ 2

/-- Total intensity Stokes coordinate. -/
def stokes0 (J : JonesSpinor) : ℝ :=
  J.leftIntensity + J.rightIntensity

/-- Circular-basis population difference Stokes coordinate. -/
def stokes1 (J : JonesSpinor) : ℝ :=
  J.leftIntensity - J.rightIntensity

/-- Real coherence Stokes coordinate. -/
def stokes2 (J : JonesSpinor) : ℝ :=
  2 * (J.aRe * J.bRe + J.aIm * J.bIm)

/-- Imaginary coherence Stokes coordinate, with a fixed handedness convention. -/
def stokes3 (J : JonesSpinor) : ℝ :=
  2 * (J.aIm * J.bRe - J.aRe * J.bIm)

/-- Unit-intensity normalization for the Poincare-sphere readout. -/
def UnitIntensity (J : JonesSpinor) : Prop :=
  J.stokes0 = 1

/-- The finite Stokes vector lies on the light cone. -/
theorem stokes_lightcone_identity (J : JonesSpinor) :
    J.stokes1 ^ 2 + J.stokes2 ^ 2 + J.stokes3 ^ 2 = J.stokes0 ^ 2 := by
  rcases J with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  simp [stokes0, stokes1, stokes2, stokes3, leftIntensity, rightIntensity]
  ring

/-- Unit-intensity Jones spinors land on the unit Poincare sphere. -/
theorem poincare_sphere_identity_of_unitIntensity
    {J : JonesSpinor}
    (hJ : J.UnitIntensity) :
    J.stokes1 ^ 2 + J.stokes2 ^ 2 + J.stokes3 ^ 2 = 1 := by
  rw [stokes_lightcone_identity, hJ]
  norm_num

/-! ## Circular-basis poles and projectors -/

/-- Positive circular-basis pole. -/
def plusCircular : JonesSpinor :=
  ((1, 0), (0, 0))

/-- Negative circular-basis pole. -/
def minusCircular : JonesSpinor :=
  ((0, 0), (1, 0))

theorem plusCircular_stokes :
    plusCircular.stokes0 = 1 ∧ plusCircular.stokes1 = 1 ∧
      plusCircular.stokes2 = 0 ∧ plusCircular.stokes3 = 0 := by
  norm_num [plusCircular, stokes0, stokes1, stokes2, stokes3, leftIntensity,
    rightIntensity]

theorem minusCircular_stokes :
    minusCircular.stokes0 = 1 ∧ minusCircular.stokes1 = -1 ∧
      minusCircular.stokes2 = 0 ∧ minusCircular.stokes3 = 0 := by
  norm_num [minusCircular, stokes0, stokes1, stokes2, stokes3, leftIntensity,
    rightIntensity]

/-- Positive circular-basis projector, reusing the finite Jones owner. -/
def circularPlusProjector : InfoGeometry.Optics.FiniteJonesModel.JonesMat :=
  InfoGeometry.Optics.FiniteJonesModel.sProjector

/-- Negative circular-basis projector, reusing the finite Jones owner. -/
def circularMinusProjector : InfoGeometry.Optics.FiniteJonesModel.JonesMat :=
  InfoGeometry.Optics.FiniteJonesModel.pProjector

theorem circularPlusProjector_idem :
    circularPlusProjector * circularPlusProjector = circularPlusProjector :=
  InfoGeometry.Optics.FiniteJonesModel.sProjector_idem

theorem circularMinusProjector_idem :
    circularMinusProjector * circularMinusProjector = circularMinusProjector :=
  InfoGeometry.Optics.FiniteJonesModel.pProjector_idem

theorem circularProjectors_orthogonal_left :
    circularPlusProjector * circularMinusProjector = 0 :=
  InfoGeometry.Optics.FiniteJonesModel.sProjector_mul_pProjector

theorem circularProjectors_orthogonal_right :
    circularMinusProjector * circularPlusProjector = 0 :=
  InfoGeometry.Optics.FiniteJonesModel.pProjector_mul_sProjector

theorem circularProjectors_sum_one :
    circularPlusProjector + circularMinusProjector = 1 :=
  InfoGeometry.Optics.FiniteJonesModel.sProjector_add_pProjector

/-! ## Pauli/Hestenes null readout -/

/-- Stokes four-vector as a real Pauli/Hestenes paravector. -/
def stokesMinkowski4 (J : JonesSpinor) : Minkowski4 := fun
  | 0 => J.stokes0
  | 1 => J.stokes2
  | 2 => J.stokes3
  | 3 => J.stokes1

/-- The Stokes four-vector is lightlike for the Pauli/Hestenes metric. -/
theorem stokesMinkowski4_q (J : JonesSpinor) :
    (stokesMinkowski4 J).q = 0 := by
  change J.stokes0 ^ 2 - J.stokes2 ^ 2 - J.stokes3 ^ 2 - J.stokes1 ^ 2 = 0
  nlinarith [stokes_lightcone_identity J]

/-- The Stokes four-vector is a null Pauli/Hestenes vector. -/
theorem stokesMinkowski4_isNull (J : JonesSpinor) :
    (stokesMinkowski4 J).IsNull :=
  stokesMinkowski4_q J

/-- The Pauli representative of the Stokes four-vector is singular. -/
theorem stokesPauli_det_zero (J : JonesSpinor) :
    Matrix.det (pauliMatrix (stokesMinkowski4 J)) = 0 :=
  det_pauliMatrix_eq_zero_of_null (stokesMinkowski4_isNull J)

end JonesSpinor

/-! ## Twistor-incidence readout -/

namespace TwistorIncidenceReadout

open InfoGeometry.Clifford.Soldering
open InfoGeometry.Twistor.Incidence

/--
Two spacetime points incident with the same nonzero-primary-spinor twistor.

This is a finite packet for reusing the already-owned twistor incidence theorem.
-/
structure IncidentPair where
  twistor : Twistor
  X : Vec22
  Y : Vec22
  incidentX : Incident twistor X
  incidentY : Incident twistor Y
  primary_nonzero : twistor.2 ≠ 0

namespace IncidentPair

/-- Incidence with a fixed nonzero-primary-spinor twistor gives null separation. -/
theorem null_separation (P : IncidentPair) :
    q22 (P.X - P.Y) = 0 :=
  incident_points_null_separated P.twistor P.X P.Y P.incidentX P.incidentY P.primary_nonzero

end IncidentPair

end TwistorIncidenceReadout

end InfoGeometry.Optics.JonesPoincareSphere
