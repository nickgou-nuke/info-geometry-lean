import Mathlib.Tactic
import InfoGeometry.Canonical.QuaternionicOperatorComplexStructure

/-!
# InfoGeometry.Canonical.QuaternionicTwistorSphereOperator

The repository already realizes the three quaternion units `I,J,K` as
square-minus-one Pauli and Dirac operators.  The missing algebraic completion
is not another preferred complex unit but the full two-sphere of normalized
imaginary quaternion directions.

For real `a,b,c`, define

`J(a,b,c) = a I + b J + c K`.

The quaternion relations imply

`J(a,b,c)^2 = -(a^2+b^2+c^2) I`.

Hence every point of the unit sphere gives a genuine real complex structure.
This file proves that statement in the existing two-by-two Pauli realization
and transports it to the native Pauli spinor endomorphism.  No Berry
connection or holonomy is asserted: those require a varying family together
with differential/topological data, not merely the pointwise quaternion
identity proved here.
-/

noncomputable section

namespace InfoGeometry.Canonical.QuaternionicTwistorSphereOperator

open Matrix
open InfoGeometry.Clifford.QuaternionPauliRealForm
open InfoGeometry.Canonical.QuaternionicOperatorComplexStructure

/-- Euclidean squared norm of an imaginary quaternion direction. -/
def twistorNormSq (a b c : ℝ) : ℝ :=
  a ^ 2 + b ^ 2 + c ^ 2

/-- Predicate selecting the unit quaternionic imaginary sphere. -/
def OnTwistorSphere (a b c : ℝ) : Prop :=
  twistorNormSq a b c = 1

/-- Normalized or non-normalized imaginary quaternion direction in the
repository's two-by-two Pauli realization. -/
def pauliTwistorUnit (a b c : ℝ) : PauliMatrix :=
  (a : ℂ) • qi + (b : ℂ) • qj + (c : ℂ) • qk

/-- The square of an arbitrary imaginary quaternion direction is the negative
Euclidean norm squared times the identity. -/
theorem pauliTwistorUnit_sq (a b c : ℝ) :
    pauliTwistorUnit a b c * pauliTwistorUnit a b c =
      -((twistorNormSq a b c : ℂ) • (1 : PauliMatrix)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliTwistorUnit, twistorNormSq,
      qi, qj, qk, sigma1, sigma2, sigma3,
      Matrix.mul_apply, Fin.sum_univ_two, Complex.I_sq] <;>
    ring

/-- Every point of the quaternionic unit two-sphere is a square-minus-one
matrix complex structure. -/
theorem pauliTwistorUnit_sq_of_sphere
    {a b c : ℝ} (h : OnTwistorSphere a b c) :
    pauliTwistorUnit a b c * pauliTwistorUnit a b c =
      -(1 : PauliMatrix) := by
  rw [pauliTwistorUnit_sq]
  simp [OnTwistorSphere, twistorNormSq] at h
  rw [h]
  simp

/-- The twistor direction acting on the native two-component Pauli spinor. -/
noncomputable def pauliTwistorComplexStructure
    (a b c : ℝ) : PauliSpinorOperator :=
  pauliSpinorAction (pauliTwistorUnit a b c)

/-- Pointwise unit-sphere directions act as genuine complex structures on the
Pauli spinor carrier. -/
theorem pauliTwistorComplexStructure_sq
    {a b c : ℝ} (h : OnTwistorSphere a b c) :
    (pauliTwistorComplexStructure a b c).comp
        (pauliTwistorComplexStructure a b c) =
      -(LinearMap.id : PauliSpinorOperator) := by
  simpa [pauliTwistorComplexStructure] using
    (pauliSpinorAction_sq_of
      (pauliTwistorUnit a b c)
      (pauliTwistorUnit_sq_of_sphere h))

/-- The three coordinate axes recover the previously defined quaternionic
operator complex structures. -/
theorem pauliTwistorComplexStructure_axis_I :
    pauliTwistorComplexStructure 1 0 0 = pauliComplexI := by
  simp [pauliTwistorComplexStructure, pauliTwistorUnit, pauliComplexI]

/-- Second quaternionic coordinate axis. -/
theorem pauliTwistorComplexStructure_axis_J :
    pauliTwistorComplexStructure 0 1 0 = pauliComplexJ := by
  simp [pauliTwistorComplexStructure, pauliTwistorUnit, pauliComplexJ]

/-- Third quaternionic coordinate axis. -/
theorem pauliTwistorComplexStructure_axis_K :
    pauliTwistorComplexStructure 0 0 1 = pauliComplexK := by
  simp [pauliTwistorComplexStructure, pauliTwistorUnit, pauliComplexK]

/-- All three coordinate axes satisfy the unit-sphere predicate. -/
theorem coordinate_axes_on_twistor_sphere :
    OnTwistorSphere 1 0 0 ∧
      OnTwistorSphere 0 1 0 ∧
      OnTwistorSphere 0 0 1 := by
  norm_num [OnTwistorSphere, twistorNormSq]

end InfoGeometry.Canonical.QuaternionicTwistorSphereOperator
