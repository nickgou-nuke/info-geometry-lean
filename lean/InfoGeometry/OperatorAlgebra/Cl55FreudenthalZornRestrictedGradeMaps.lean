import InfoGeometry.OperatorAlgebra.Cl55FreudenthalZornGradeIntertwiner
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ConformalFiveGradeInversion
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.OperatorAlgebra.Cl55FreudenthalZornRestrictedGradeMaps

open InfoGeometry.OperatorAlgebra.FaithfulOperatorZornEnvelope
open InfoGeometry.OperatorAlgebra.Cl55FreudenthalZornGradeIntertwiner
open InfoGeometry.Clifford.ConformalLieAlgebra55
open InfoGeometry.Canonical.ConformalFiveGradeInversion
open InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (datum : CubicJordanDatum J)

/-- Common target grade as an adjoint eigenspace. -/
def jointGradeSpace (k : ℤ) :
    Submodule ℝ (JointEnvelope (J := J)) where
  carrier := {X | HasJointGrade datum k X}
  zero_mem' := by
    dsimp [HasJointGrade, HasAdjointGrade]
    unfold InfoGeometry.OperatorAlgebra.FaithfulOperatorZornEnvelope.commutator
    simp
  add_mem' := by
    intro X Y hX hY
    dsimp [HasJointGrade, HasAdjointGrade] at hX hY ⊢
    unfold InfoGeometry.OperatorAlgebra.FaithfulOperatorZornEnvelope.commutator at hX hY ⊢
    have h : diagonal (jointEulerCoefficient datum) * (X + Y) - (X + Y) * diagonal (jointEulerCoefficient datum) =
        (diagonal (jointEulerCoefficient datum) * X - X * diagonal (jointEulerCoefficient datum)) +
        (diagonal (jointEulerCoefficient datum) * Y - Y * diagonal (jointEulerCoefficient datum)) := by
      noncomm_ring
    rw [h, hX, hY, smul_add]
  smul_mem' := by
    intro r X hX
    dsimp [HasJointGrade, HasAdjointGrade] at hX ⊢
    unfold InfoGeometry.OperatorAlgebra.FaithfulOperatorZornEnvelope.commutator at hX ⊢
    rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, hX, smul_comm]

@[simp] theorem mem_jointGradeSpace
    (k : ℤ) (X : JointEnvelope (J := J)) :
    X ∈ jointGradeSpace datum k ↔ HasJointGrade datum k X := Iff.rfl

theorem commutator_assoc_jacobi {A : Type*} [Ring A] (H X Y : Envelope A) :
    commutator H (commutator X Y) =
      commutator (commutator H X) Y + commutator X (commutator H Y) := by
  unfold InfoGeometry.OperatorAlgebra.FaithfulOperatorZornEnvelope.commutator
  noncomm_ring

theorem commutator_smul_left {A : Type*} [Ring A] [Algebra ℝ A] (r : ℝ) (X Y : Envelope A) :
    commutator (r • X) Y = r • commutator X Y := by
  unfold InfoGeometry.OperatorAlgebra.FaithfulOperatorZornEnvelope.commutator
  simp [smul_sub]

theorem commutator_smul_right {A : Type*} [Ring A] [Algebra ℝ A] (r : ℝ) (X Y : Envelope A) :
    commutator X (r • Y) = r • commutator X Y := by
  unfold InfoGeometry.OperatorAlgebra.FaithfulOperatorZornEnvelope.commutator
  simp [smul_sub]

/-- Commutators in the common envelope add adjoint grades. -/
theorem commutator_mem_jointGradeSpace_add
    {k l : ℤ} {X Y : JointEnvelope (J := J)}
    (hX : X ∈ jointGradeSpace datum k)
    (hY : Y ∈ jointGradeSpace datum l) :
    commutator X Y ∈ jointGradeSpace datum (k + l) := by
  rw [mem_jointGradeSpace] at hX hY ⊢
  dsimp [HasJointGrade, HasAdjointGrade] at hX hY ⊢
  rw [commutator_assoc_jacobi, hX, hY, commutator_smul_left, commutator_smul_right, ← add_smul]
  push_cast
  rfl

/-- Native Cl(5,5) grade map into the common target grade. -/
def cl55RestrictedGradeMap (g : ConformalGrade) :
    gradeSpace g →ₗ[ℝ] jointGradeSpace datum (toInt g) where
  toFun x :=
    ⟨cl55EnvelopeMap (J := J) x.1,
      cl55EnvelopeMap_preserves_grade datum g x.2⟩
  map_add' x y := by
    apply Subtype.ext
    exact (cl55EnvelopeLinear (J := J)).map_add x.1 y.1
  map_smul' r x := by
    apply Subtype.ext
    exact (cl55EnvelopeLinear (J := J)).map_smul r x.1

/-- Corrected Freudenthal contact grade map into the same target grade. -/
def contactRestrictedGradeMap (k : ℤ) :
    symplecticContactGradeSpace datum k →ₗ[ℝ]
      jointGradeSpace datum k where
  toFun u :=
    ⟨contactEnvelopeMap datum u.1,
      contactEnvelopeMap_preserves_grade datum k u.2⟩
  map_add' u v := by
    apply Subtype.ext
    exact (contactEnvelopeLinear datum).map_add u.1 v.1
  map_smul' r u := by
    apply Subtype.ext
    exact (contactEnvelopeLinear datum).map_smul r u.1

/-- The restricted Cl(5,5) grade map is faithful. -/
theorem cl55RestrictedGradeMap_injective (g : ConformalGrade) :
    Function.Injective (cl55RestrictedGradeMap datum g) := by
  intro x y hxy
  apply Subtype.ext
  apply cl55EnvelopeMap_injective (J := J)
  exact congrArg Subtype.val hxy

/-- The restricted Freudenthal grade map is faithful. -/
theorem contactRestrictedGradeMap_injective (k : ℤ) :
    Function.Injective (contactRestrictedGradeMap datum k) := by
  intro u v huv
  apply Subtype.ext
  apply contactEnvelopeMap_injective datum
  exact congrArg Subtype.val huv

/-- The two restricted representations remain mutually commuting. -/
theorem restricted_cross_commutator_zero
    (g : ConformalGrade) (k : ℤ)
    (x : gradeSpace g)
    (u : symplecticContactGradeSpace datum k) :
    commutator
        (cl55RestrictedGradeMap datum g x).1
        (contactRestrictedGradeMap datum k u).1 = 0 :=
  cl55_contact_cross_commutator_zero datum x.1 u.1

end InfoGeometry.OperatorAlgebra.Cl55FreudenthalZornRestrictedGradeMaps
