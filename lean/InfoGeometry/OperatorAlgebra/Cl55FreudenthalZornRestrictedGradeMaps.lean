import InfoGeometry.OperatorAlgebra.Cl55FreudenthalZornGradeIntertwiner
import Mathlib.Tactic

/-!
# Restricted grade maps into the common operator-Zorn envelope

This owner packages the target adjoint eigenspaces as Mathlib submodules and
restricts both source maps to actual linear maps between the corresponding
grade spaces.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.Cl55FreudenthalZornRestrictedGradeMaps

open InfoGeometry.OperatorAlgebra.FaithfulOperatorZornEnvelope
open InfoGeometry.OperatorAlgebra.Cl55FreudenthalZornGradeIntertwiner
open InfoGeometry.Clifford.ConformalLieAlgebra55
open InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (datum : CubicJordanDatum J)

/-- Common target grade as an adjoint eigenspace. -/
def jointGradeSpace (k : ℤ) :
    Submodule ℝ (JointEnvelope (J := J)) where
  carrier := {X | HasJointGrade datum k X}
  zero_mem' := by
    simp [HasJointGrade, HasAdjointGrade, commutator]
  add_mem' := by
    intro X Y hX hY
    change ⁅diagonal (jointEulerCoefficient datum), X⁆ =
      (k : ℝ) • X at hX
    change ⁅diagonal (jointEulerCoefficient datum), Y⁆ =
      (k : ℝ) • Y at hY
    change ⁅diagonal (jointEulerCoefficient datum), X + Y⁆ =
      (k : ℝ) • (X + Y)
    rw [lie_add, hX, hY, smul_add]
  smul_mem' := by
    intro r X hX
    change ⁅diagonal (jointEulerCoefficient datum), X⁆ =
      (k : ℝ) • X at hX
    change ⁅diagonal (jointEulerCoefficient datum), r • X⁆ =
      (k : ℝ) • (r • X)
    rw [lie_smul, hX]
    simp [smul_smul, mul_comm]

@[simp] theorem mem_jointGradeSpace
    (k : ℤ) (X : JointEnvelope (J := J)) :
    X ∈ jointGradeSpace datum k ↔ HasJointGrade datum k X := Iff.rfl

/-- Commutators in the common envelope add adjoint grades. -/
theorem commutator_mem_jointGradeSpace_add
    {k l : ℤ} {X Y : JointEnvelope (J := J)}
    (hX : X ∈ jointGradeSpace datum k)
    (hY : Y ∈ jointGradeSpace datum l) :
    commutator X Y ∈ jointGradeSpace datum (k + l) := by
  change ⁅diagonal (jointEulerCoefficient datum), X⁆ =
    (k : ℝ) • X at hX
  change ⁅diagonal (jointEulerCoefficient datum), Y⁆ =
    (l : ℝ) • Y at hY
  change
    ⁅diagonal (jointEulerCoefficient datum), ⁅X, Y⁆⁆ =
      ((k + l : ℤ) : ℝ) • ⁅X, Y⁆
  rw [leibniz_lie, hX, hY, smul_lie, lie_smul, ← add_smul]
  simp only [Int.cast_add]

/-- Native Cl(5,5) grade map into the common target grade. -/
def cl55RestrictedGradeMap (g : ConformalGrade) :
    gradeSpace g →ₗ[ℝ] jointGradeSpace datum (toInt g) where
  toFun x :=
    ⟨cl55EnvelopeMap (J := J) x.1,
      cl55EnvelopeMap_preserves_grade datum g x.2⟩
  map_add' x y := by
    apply Subtype.ext
    simp [cl55EnvelopeMap, cl55Coefficient, leftMultiply_add]
  map_smul' r x := by
    apply Subtype.ext
    simp [cl55EnvelopeMap, cl55Coefficient, leftMultiply_smul]

/-- Corrected Freudenthal contact grade map into the same target grade. -/
def contactRestrictedGradeMap (k : ℤ) :
    symplecticContactGradeSpace datum k →ₗ[ℝ]
      jointGradeSpace datum k where
  toFun u :=
    ⟨contactEnvelopeMap datum u.1,
      contactEnvelopeMap_preserves_grade datum k u.2⟩
  map_add' u v := by
    apply Subtype.ext
    simp [contactEnvelopeMap, contactCoefficient]
  map_smul' r u := by
    apply Subtype.ext
    simp [contactEnvelopeMap, contactCoefficient]

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
