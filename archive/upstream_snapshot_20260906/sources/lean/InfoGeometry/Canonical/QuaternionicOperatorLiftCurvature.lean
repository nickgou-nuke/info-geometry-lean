/-
InfoGeometry/Canonical/QuaternionicOperatorLiftCurvature.lean

The operator-level residue left after lifting the quaternionic/Pauli corridor.

This owner has two deliberately separate finite readouts:

* a genuine S²-family of complex structures on the native real quaternion
  carrier, obtained from the three imaginary quaternion directions;
* the ordered Pauli factorization defect for operator-valued causal
  coordinates.  Over a noncommutative coefficient algebra this defect is not
  silently called a determinant: its antisymmetric part is recorded explicitly
  as a commutator curvature.

The existing OperatorCausalSoldering owner supplies the faithful doubled
carrier and the connection-curvature transport.  No new Clifford carrier,
determinant on a noncommutative ring, or unbounded Dirac operator is introduced.
-/

import Mathlib.Algebra.Quaternion
import Mathlib.Tactic
import InfoGeometry.Canonical.QuaternionCoaxialOrbit
import InfoGeometry.Canonical.QuaternionicOperatorComplexStructure
import InfoGeometry.Canonical.OperatorCliffordOddEvenSquareBridge
import InfoGeometry.Optics.OperatorCausalSoldering

noncomputable section

namespace InfoGeometry.Canonical.QuaternionicOperatorLiftCurvature

open InfoGeometry.Canonical.QuaternionicOperatorComplexStructure
open InfoGeometry.Canonical.QuaternionCoaxialOrbit
open InfoGeometry.Optics.OperatorCausalSoldering

/-! ## The quaternionic twistor sphere -/

/-- A unit direction in the three imaginary quaternion axes. -/
structure QuaternionicTwistorSpherePoint where
  a : ℝ
  b : ℝ
  c : ℝ
  unit : a ^ 2 + b ^ 2 + c ^ 2 = 1

/-- The pure quaternion represented by a point of the twistor sphere. -/
def twistorQuaternion (p : QuaternionicTwistorSpherePoint) : Quaternion ℝ :=
  { re := 0, imI := p.a, imJ := p.b, imK := p.c }

@[simp] theorem twistorQuaternion_re
    (p : QuaternionicTwistorSpherePoint) :
    (twistorQuaternion p).re = 0 :=
  rfl

/-- The Euclidean norm square of the imaginary direction. -/
theorem twistorQuaternion_normSq
    (p : QuaternionicTwistorSpherePoint) :
    Quaternion.normSq (twistorQuaternion p) =
      p.a ^ 2 + p.b ^ 2 + p.c ^ 2 := by
  simp [twistorQuaternion, Quaternion.normSq_def']

/-- The sphere equation is exactly the square-minus-one law. -/
theorem twistorQuaternion_sq
    (p : QuaternionicTwistorSpherePoint) :
    twistorQuaternion p ^ 2 = -(1 : Quaternion ℝ) := by
  have hpure : (twistorQuaternion p).re = 0 :=
    twistorQuaternion_re p
  have hsq := (Quaternion.sq_eq_neg_normSq).2 hpure
  rw [hsq, twistorQuaternion_normSq, p.unit]
  norm_num

/-- The real quaternionic operator obtained by left multiplication. -/
def quaternionLeftAction (q : Quaternion ℝ) :
    Quaternion ℝ →ₗ[ℝ] Quaternion ℝ where
  toFun x := q * x
  map_add' x y := by
    exact mul_add q x y
  map_smul' r x := by
    simp [mul_smul_comm]

/-- Left multiplication is a representation of the quaternion algebra. -/
theorem quaternionLeftAction_mul (q r : Quaternion ℝ) :
    (quaternionLeftAction q).comp (quaternionLeftAction r) =
      quaternionLeftAction (q * r) := by
  apply LinearMap.ext
  intro x
  simp [quaternionLeftAction, LinearMap.comp_apply, mul_assoc]

/-- The lifted twistor-sphere point is a real-linear complex structure. -/
def twistorComplexStructure
    (p : QuaternionicTwistorSpherePoint) :
    Quaternion ℝ →ₗ[ℝ] Quaternion ℝ :=
  quaternionLeftAction (twistorQuaternion p)

theorem twistorComplexStructure_sq
    (p : QuaternionicTwistorSpherePoint) :
    (twistorComplexStructure p).comp (twistorComplexStructure p) =
      -(LinearMap.id : Quaternion ℝ →ₗ[ℝ] Quaternion ℝ) := by
  apply LinearMap.ext
  intro x
  change twistorQuaternion p * (twistorQuaternion p * x) = -(x)
  rw [← mul_assoc, twistorQuaternion_sq p]
  simp

theorem twistorComplexStructure_isRealComplexStructure
    (p : QuaternionicTwistorSpherePoint) :
    InfoGeometry.Canonical.IsRealComplexStructure
      (twistorComplexStructure p) :=
  twistorComplexStructure_sq p

/-! ## The same sphere in the existing 2 by 2 Pauli realization -/

abbrev PauliMatrix :=
  InfoGeometry.Clifford.QuaternionPauliRealForm.Mat2C

/-- The Pauli matrix represented by the imaginary quaternion direction. -/
def pauliTwistorMatrix (p : QuaternionicTwistorSpherePoint) : PauliMatrix :=
  InfoGeometry.Clifford.QuaternionPauliRealForm.quaternionPauli
    (0, p.a, p.b, p.c)

/-- Its determinant is the unit norm of the chosen sphere direction. -/
theorem pauliTwistorMatrix_det
    (p : QuaternionicTwistorSpherePoint) :
    Matrix.det (pauliTwistorMatrix p) = (1 : ℂ) := by
  rw [pauliTwistorMatrix,
    InfoGeometry.Clifford.QuaternionPauliRealForm.quaternionPauli_det]
  have hunit :
      (p.a : ℂ) ^ 2 + (p.b : ℂ) ^ 2 + (p.c : ℂ) ^ 2 = (1 : ℂ) := by
    exact_mod_cast p.unit
  simpa using hunit

/-- The Pauli-column action of the sphere direction. -/
def pauliTwistorAction
    (p : QuaternionicTwistorSpherePoint) :
    PauliSpinor →ₗ[ℂ] PauliSpinor :=
  pauliSpinorAction (pauliTwistorMatrix p)

/-- A matrix-square witness transports immediately to the Pauli operator. -/
theorem pauliTwistorAction_sq_of
    (p : QuaternionicTwistorSpherePoint)
    (hSq : pauliTwistorMatrix p * pauliTwistorMatrix p =
      -(1 : PauliMatrix)) :
    (pauliTwistorAction p).comp (pauliTwistorAction p) =
      -(LinearMap.id : PauliSpinor →ₗ[ℂ] PauliSpinor) := by
  exact pauliSpinorAction_sq_of (pauliTwistorMatrix p) hSq

/-! ## Noncommutative Pauli factorization and its curvature residue -/

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- The ordered Pauli factorization of an operator-valued causal four-vector. -/
def orderedPauliFactor (v : OperatorFourVector W) : EndW W :=
  (v 0 + v 3) * (v 0 - v 3) -
    (v 1 - Complex.I • v 2) * (v 1 + Complex.I • v 2)

/-- The factorization with the two factors reversed. -/
def reversePauliFactor (v : OperatorFourVector W) : EndW W :=
  (v 0 - v 3) * (v 0 + v 3) -
    (v 1 + Complex.I • v 2) * (v 1 - Complex.I • v 2)

/-- The symmetric quadratic readout before the commutator residue. -/
def symmetricPauliQuadratic (v : OperatorFourVector W) : EndW W :=
  v 0 * v 0 - v 1 * v 1 - v 2 * v 2 - v 3 * v 3

/-- Commutator in an arbitrary associative operator coefficient algebra. -/
def operatorCommutator {A : Type*} [Ring A] (x y : A) : A :=
  x * y - y * x

private theorem scalarImaginary_square :
    (algebraMap ℂ (EndW W) Complex.I) *
        algebraMap ℂ (EndW W) Complex.I =
      -(1 : EndW W) := by
  rw [← map_mul, Complex.I_mul_I, map_neg, map_one]
  simp

theorem orderedPauliFactor_eq_symmetric_sub_commutators
    (v : OperatorFourVector W) :
    orderedPauliFactor v =
      symmetricPauliQuadratic v -
        operatorCommutator (v 0) (v 3) -
        Complex.I • operatorCommutator (v 1) (v 2) := by
  have h0 :
      algebraMap ℂ (EndW W) Complex.I * v 0 =
        v 0 * algebraMap ℂ (EndW W) Complex.I :=
    Algebra.commutes _ _
  have h1 :
      algebraMap ℂ (EndW W) Complex.I * v 1 =
        v 1 * algebraMap ℂ (EndW W) Complex.I :=
    Algebra.commutes _ _
  have h2 :
      algebraMap ℂ (EndW W) Complex.I * v 2 =
        v 2 * algebraMap ℂ (EndW W) Complex.I :=
    Algebra.commutes _ _
  have h3 :
      algebraMap ℂ (EndW W) Complex.I * v 3 =
        v 3 * algebraMap ℂ (EndW W) Complex.I :=
    Algebra.commutes _ _
  unfold orderedPauliFactor symmetricPauliQuadratic operatorCommutator
  simp only [Algebra.smul_def]
  noncomm_ring [scalarImaginary_square, h0, h1, h2, h3]

theorem reversePauliFactor_eq_symmetric_add_commutators
    (v : OperatorFourVector W) :
    reversePauliFactor v =
      symmetricPauliQuadratic v +
        operatorCommutator (v 0) (v 3) +
        Complex.I • operatorCommutator (v 1) (v 2) := by
  have h0 :
      algebraMap ℂ (EndW W) Complex.I * v 0 =
        v 0 * algebraMap ℂ (EndW W) Complex.I :=
    Algebra.commutes _ _
  have h1 :
      algebraMap ℂ (EndW W) Complex.I * v 1 =
        v 1 * algebraMap ℂ (EndW W) Complex.I :=
    Algebra.commutes _ _
  have h2 :
      algebraMap ℂ (EndW W) Complex.I * v 2 =
        v 2 * algebraMap ℂ (EndW W) Complex.I :=
    Algebra.commutes _ _
  have h3 :
      algebraMap ℂ (EndW W) Complex.I * v 3 =
        v 3 * algebraMap ℂ (EndW W) Complex.I :=
    Algebra.commutes _ _
  unfold reversePauliFactor symmetricPauliQuadratic operatorCommutator
  simp only [Algebra.smul_def]
  noncomm_ring [scalarImaginary_square, h0, h1, h2, h3]

/-- The antisymmetric part of the ordered determinant proxy is curvature. -/
def pauliFactorizationCurvature
    (v : OperatorFourVector W) : EndW W :=
  orderedPauliFactor v - reversePauliFactor v

theorem pauliFactorizationCurvature_eq_commutator_residue
    (v : OperatorFourVector W) :
    pauliFactorizationCurvature v =
      (-2 : ℂ) •
        (operatorCommutator (v 0) (v 3) +
          Complex.I • operatorCommutator (v 1) (v 2)) := by
  unfold pauliFactorizationCurvature
  rw [orderedPauliFactor_eq_symmetric_sub_commutators,
    reversePauliFactor_eq_symmetric_add_commutators]
  module

/-- The symmetric part forgets exactly the commutator curvature. -/
theorem ordered_add_reverse_eq_two_symmetric
    (v : OperatorFourVector W) :
    orderedPauliFactor v + reversePauliFactor v =
      (2 : ℂ) • symmetricPauliQuadratic v := by
  rw [orderedPauliFactor_eq_symmetric_sub_commutators,
    reversePauliFactor_eq_symmetric_add_commutators]
  module

theorem pauliFactorizationCurvature_eq_zero_of_commuting
    (v : OperatorFourVector W)
    (h03 : operatorCommutator (v 0) (v 3) = 0)
    (h12 : operatorCommutator (v 1) (v 2) = 0) :
    pauliFactorizationCurvature v = 0 := by
  rw [pauliFactorizationCurvature_eq_commutator_residue, h03, h12]
  simp

/-! ## Reuse of the existing operator-valued connection owner -/

section Connection

variable {Point Tangent : Type*}

/-- The existing connection curvature readout, expressed with this owner's
commutator notation. -/
theorem matrixConnection_curvature_eq_derivative_add_commutator
    (C : CausalOperatorConnection W Point Tangent)
    (p : Point) (X Y : Tangent) :
    matrixAction (curvature (matrixConnection C) p X Y) =
      matrixAction (reconstruct_causal (C.derivative p X Y)) +
        operatorCommutator
          (matrixAction (reconstruct_causal (C.form p X)))
          (matrixAction (reconstruct_causal (C.form p Y))) := by
  simpa [operatorCommutator] using
    (matrixAction_curvature_explicit C p X Y)

end Connection

end InfoGeometry.Canonical.QuaternionicOperatorLiftCurvature
