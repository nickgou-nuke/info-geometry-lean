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
    unfold HasJointGrade HasAdjointGrade commutator
    simp
  add_mem' := by
    intro X Y hX hY
    unfold HasJointGrade HasAdjointGrade commutator at hX hY ⊢
    calc
      diagonal (jointEulerCoefficient datum) * (X + Y) -
          (X + Y) * diagonal (jointEulerCoefficient datum) =
        (diagonal (jointEulerCoefficient datum) * X -
            X * diagonal (jointEulerCoefficient datum)) +
          (diagonal (jointEulerCoefficient datum) * Y -
            Y * diagonal (jointEulerCoefficient datum)) := by
              noncomm_ring
      _ = (k : ℝ) • X + (k : ℝ) • Y := by rw [hX, hY]
      _ = (k : ℝ) • (X + Y) := by rw [smul_add]
  smul_mem' := by
    intro r X hX
    unfold HasJointGrade HasAdjointGrade commutator at hX ⊢
    calc
      diagonal (jointEulerCoefficient datum) * (r • X) -
          (r • X) * diagonal (jointEulerCoefficient datum) =
        r • (diagonal (jointEulerCoefficient datum) * X -
          X * diagonal (jointEulerCoefficient datum)) := by
            rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_sub]
      _ = r • ((k : ℝ) • X) := by rw [hX]
      _ = (k : ℝ) • (r • X) := by
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
  unfold jointGradeSpace HasJointGrade HasAdjointGrade at hX hY ⊢
  unfold commutator at hX hY ⊢
  let H := diagonal (jointEulerCoefficient datum)
  change H * X - X * H = (k : ℝ) • X at hX
  change H * Y - Y * H = (l : ℝ) • Y at hY
  change
    H * (X * Y - Y * X) - (X * Y - Y * X) * H =
      ((k + l : ℤ) : ℝ) • (X * Y - Y * X)
  calc
    H * (X * Y - Y * X) - (X * Y - Y * X) * H =
        (H * X - X * H) * Y + X * (H * Y - Y * H) -
          ((H * Y - Y * H) * X + Y * (H * X - X * H)) := by
            noncomm_ring
    _ = ((k : ℝ) • X) * Y + X * ((l : ℝ) • Y) -
          (((l : ℝ) • Y) * X + Y * ((k : ℝ) • X)) := by
            rw [hX, hY]
    _ = (((k : ℝ) + (l : ℝ)) • (X * Y - Y * X)) := by
          simp [Algebra.smul_mul_assoc, Algebra.mul_smul_comm,
            smul_sub, add_smul]
          noncomm_ring
    _ = ((k + l : ℤ) : ℝ) • (X * Y - Y * X) := by
          rw [Int.cast_add]

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
