import InfoGeometry.OperatorAlgebra.Cl55FreudenthalZornRestrictedGradeMaps
import Mathlib.Tactic

/-!
# Native Lie representations into the common operator-Zorn envelope

The two already-proved component maps are bundled as Mathlib Lie
homomorphisms.  Their direct product gives one faithful Lie representation

`Cl(5,5)_Lie x g_contact -> JointEnvelope`.

The product is external: the two source factors commute in the target.  A
separate restricted map packages synchronized equal-grade pairs.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.Cl55FreudenthalZornLieRepresentation

open InfoGeometry.OperatorAlgebra.FaithfulOperatorZornEnvelope
open InfoGeometry.OperatorAlgebra.Cl55FreudenthalZornGradeIntertwiner
open InfoGeometry.OperatorAlgebra.Cl55FreudenthalZornRestrictedGradeMaps
open InfoGeometry.Clifford.ConformalLieAlgebra55
open InfoGeometry.Exceptional.Freudenthal

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (datum : CubicJordanDatum J)

/-- Native Cl(5,5) Lie homomorphism into the common Zorn envelope. -/
def cl55EnvelopeLieHom :
    Cl55 →ₗ⁅ℝ⁆ JointEnvelope (J := J) where
  toLinearMap := cl55EnvelopeLinear (J := J)
  map_lie' x y := by
    change cl55EnvelopeMap (J := J) (x * y - y * x) =
      cl55EnvelopeMap (J := J) x * cl55EnvelopeMap (J := J) y -
        cl55EnvelopeMap (J := J) y * cl55EnvelopeMap (J := J) x
    simpa [commutator] using
      cl55EnvelopeMap_commutator (J := J) x y

/-- Corrected Freudenthal contact Lie homomorphism into the same envelope. -/
def contactEnvelopeLieHom :
    FiveGradedCarrier datum →ₗ⁅ℝ⁆ JointEnvelope (J := J) where
  toLinearMap := contactEnvelopeLinear datum
  map_lie' u v := by
    change contactEnvelopeMap datum ⁅u, v⁆ =
      contactEnvelopeMap datum u * contactEnvelopeMap datum v -
        contactEnvelopeMap datum v * contactEnvelopeMap datum u
    simpa [commutator] using contactEnvelopeMap_bracket datum u v

/-- External direct product of the native Clifford Lie algebra and the
corrected contact Lie algebra. -/
abbrev JointSource := Cl55 × FiveGradedCarrier datum

/-- Single common representation map. -/
def jointSourceEnvelopeMap
    (z : JointSource datum) : JointEnvelope (J := J) :=
  diagonal
    (leftMultiply z.1,
      symplecticContactCommonRepresentation datum z.2)

/-- The common map is the sum of the two commuting factor maps. -/
theorem jointSourceEnvelopeMap_eq_add
    (x : Cl55) (u : FiveGradedCarrier datum) :
    jointSourceEnvelopeMap datum (x, u) =
      cl55EnvelopeMap (J := J) x + contactEnvelopeMap datum u := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jointSourceEnvelopeMap, cl55EnvelopeMap,
      contactEnvelopeMap, cl55Coefficient, contactCoefficient, diagonal]

/-- Real-linear form of the joint representation. -/
def jointSourceEnvelopeLinear :
    JointSource datum →ₗ[ℝ] JointEnvelope (J := J) where
  toFun := jointSourceEnvelopeMap datum
  map_add' z w := by
    rcases z with ⟨x, u⟩
    rcases w with ⟨y, v⟩
    simp [jointSourceEnvelopeMap, leftMultiply_add]
  map_smul' r z := by
    rcases z with ⟨x, u⟩
    simp [jointSourceEnvelopeMap, leftMultiply_smul]

/-- One native Lie homomorphism from the external direct product into the
operator-Zorn envelope. -/
def jointSourceEnvelopeLieHom :
    JointSource datum →ₗ⁅ℝ⁆ JointEnvelope (J := J) where
  toLinearMap := jointSourceEnvelopeLinear datum
  map_lie' := by
    rintro ⟨x, u⟩ ⟨y, v⟩
    change
      diagonal
          (leftMultiply (x * y - y * x),
            symplecticContactCommonRepresentation datum ⁅u, v⁆) =
        diagonal
            (leftMultiply x,
              symplecticContactCommonRepresentation datum u) *
          diagonal
            (leftMultiply y,
              symplecticContactCommonRepresentation datum v) -
        diagonal
            (leftMultiply y,
              symplecticContactCommonRepresentation datum v) *
          diagonal
            (leftMultiply x,
              symplecticContactCommonRepresentation datum u)
    rw [← diagonal_mul, ← diagonal_mul, ← diagonal_sub]
    apply congrArg diagonal
    apply Prod.ext
    · exact leftRegular_commutator x y
    · change
        symplecticContactCommonRepresentation datum ⁅u, v⁆ =
          symplecticContactCommonRepresentation datum u *
              symplecticContactCommonRepresentation datum v -
            symplecticContactCommonRepresentation datum v *
              symplecticContactCommonRepresentation datum u
      exact symplecticContactCommonRepresentation_bracket datum u v

/-- The single joint representation is faithful. -/
theorem jointSourceEnvelopeLieHom_injective :
    Function.Injective (jointSourceEnvelopeLieHom datum) := by
  rintro ⟨x, u⟩ ⟨y, v⟩ h
  have hentry := congrArg
    (fun M : JointEnvelope (J := J) => M 0 0) h
  have hxEnd : leftMultiply x = leftMultiply y :=
    congrArg Prod.fst hentry
  have huRep :
      symplecticContactCommonRepresentation datum u =
        symplecticContactCommonRepresentation datum v :=
    congrArg Prod.snd hentry
  apply Prod.ext
  · have h1 := congrArg (fun T : Cl55RegularEnd => T 1) hxEnd
    simpa using h1
  · exact symplecticContactCommonRepresentation_injective datum huRep

/-- Synchronized source grade: both independent factors have the same integer
adjoint weight. -/
abbrev SynchronizedGradeSource (g : ConformalGrade) :=
  gradeSpace g × symplecticContactGradeSpace datum (toInt g)

/-- Actual restricted map from synchronized source grades into one target
grade space. -/
def synchronizedGradeMap (g : ConformalGrade) :
    SynchronizedGradeSource datum g →ₗ[ℝ]
      jointGradeSpace datum (toInt g) where
  toFun z :=
    ⟨jointSourceEnvelopeMap datum (z.1.1, z.2.1), by
      rw [jointSourceEnvelopeMap_eq_add]
      exact (jointGradeSpace datum (toInt g)).add_mem
        (cl55EnvelopeMap_preserves_grade datum g z.1.2)
        (contactEnvelopeMap_preserves_grade datum (toInt g) z.2.2)⟩
  map_add' z w := by
    apply Subtype.ext
    rcases z with ⟨x, u⟩
    rcases w with ⟨y, v⟩
    simp [jointSourceEnvelopeMap, leftMultiply_add]
  map_smul' r z := by
    apply Subtype.ext
    rcases z with ⟨x, u⟩
    simp [jointSourceEnvelopeMap, leftMultiply_smul]

/-- The synchronized restricted map is faithful. -/
theorem synchronizedGradeMap_injective (g : ConformalGrade) :
    Function.Injective (synchronizedGradeMap datum g) := by
  intro z w h
  apply Prod.ext
  · apply Subtype.ext
    apply cl55EnvelopeMap_injective (J := J)
    have hval := congrArg Subtype.val h
    rw [jointSourceEnvelopeMap_eq_add,
        jointSourceEnvelopeMap_eq_add] at hval
    have hentry := congrArg
      (fun M : JointEnvelope (J := J) => M 0 0) hval
    exact congrArg Prod.fst hentry
  · apply Subtype.ext
    apply contactEnvelopeMap_injective datum
    have hval := congrArg Subtype.val h
    rw [jointSourceEnvelopeMap_eq_add,
        jointSourceEnvelopeMap_eq_add] at hval
    have hentry := congrArg
      (fun M : JointEnvelope (J := J) => M 0 0) hval
    exact congrArg Prod.snd hentry

/-- The component Lie homomorphisms commute pointwise in the common target. -/
theorem component_lieHom_cross_commutator_zero
    (x : Cl55) (u : FiveGradedCarrier datum) :
    commutator (cl55EnvelopeLieHom (J := J) x)
      (contactEnvelopeLieHom datum u) = 0 :=
  cl55_contact_cross_commutator_zero datum x u

end InfoGeometry.OperatorAlgebra.Cl55FreudenthalZornLieRepresentation
