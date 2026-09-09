import InfoGeometry.OperatorAlgebra.Cl55FreudenthalZornRestrictedGradeMaps
import InfoGeometry.Canonical.ConformalFiveGradeInversion
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.OperatorAlgebra.Cl55FreudenthalZornLieRepresentation

open InfoGeometry.OperatorAlgebra.FaithfulOperatorZornEnvelope
open InfoGeometry.OperatorAlgebra.Cl55FreudenthalZornGradeIntertwiner
open InfoGeometry.OperatorAlgebra.Cl55FreudenthalZornRestrictedGradeMaps
open InfoGeometry.Clifford.ConformalLieAlgebra55
open InfoGeometry.Canonical.ConformalFiveGradeInversion
open InfoGeometry.Exceptional.Freudenthal

instance instBracketProd {A B : Type*} [Bracket A A] [Bracket B B] : Bracket (A × B) (A × B) where
  bracket x y := (⁅x.1, y.1⁆, ⁅x.2, y.2⁆)

instance instLieRingProd {A B : Type*} [LieRing A] [LieRing B] :
    LieRing (A × B) where
  add_lie x y z := by
    ext
    · dsimp [Bracket.bracket]
      exact LieRing.add_lie x.1 y.1 z.1
    · dsimp [Bracket.bracket]
      exact LieRing.add_lie x.2 y.2 z.2
  lie_add x y z := by
    ext
    · dsimp [Bracket.bracket]
      exact LieRing.lie_add x.1 y.1 z.1
    · dsimp [Bracket.bracket]
      exact LieRing.lie_add x.2 y.2 z.2
  lie_self x := by
    ext
    · dsimp [Bracket.bracket]
      exact LieRing.lie_self x.1
    · dsimp [Bracket.bracket]
      exact LieRing.lie_self x.2
  leibniz_lie x y z := by
    ext
    · dsimp [Bracket.bracket]
      exact LieRing.leibniz_lie x.1 y.1 z.1
    · dsimp [Bracket.bracket]
      exact LieRing.leibniz_lie x.2 y.2 z.2

instance instLieAlgebraProd {R A B : Type*} [CommRing R] [LieRing A] [LieRing B] [LieAlgebra R A] [LieAlgebra R B] :
    LieAlgebra R (A × B) where
  lie_smul r x y := by
    ext
    · dsimp [Bracket.bracket]
      exact LieAlgebra.lie_smul r x.1 y.1
    · dsimp [Bracket.bracket]
      exact LieAlgebra.lie_smul r x.2 y.2

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (datum : CubicJordanDatum J)

/-- Native Cl(5,5) Lie homomorphism into the common Zorn envelope. -/
def cl55EnvelopeLieHom :
    Cl55 →ₗ⁅ℝ⁆ JointEnvelope (J := J) where
  toLinearMap := cl55EnvelopeLinear (J := J)
  map_lie' {x y} := by
    exact cl55EnvelopeMap_commutator (J := J) x y

/-- Corrected Freudenthal contact Lie homomorphism into the same envelope. -/
def contactEnvelopeLieHom :
    FiveGradedCarrier datum →ₗ⁅ℝ⁆ JointEnvelope (J := J) where
  toLinearMap := contactEnvelopeLinear datum
  map_lie' {u v} := by
    exact contactEnvelopeMap_bracket datum u v

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
  dsimp [jointSourceEnvelopeMap, cl55EnvelopeMap, contactEnvelopeMap,
    cl55Coefficient, contactCoefficient]
  rw [← FaithfulOperatorZornEnvelope.diagonal_add]
  congr 1
  ext <;> simp

/-- Real-linear form of the joint representation. -/
def jointSourceEnvelopeLinear :
    JointSource datum →ₗ[ℝ] JointEnvelope (J := J) where
  toFun := jointSourceEnvelopeMap datum
  map_add' z w := by
    rcases z with ⟨x, u⟩
    rcases w with ⟨y, v⟩
    rw [jointSourceEnvelopeMap_eq_add, jointSourceEnvelopeMap_eq_add,
      jointSourceEnvelopeMap_eq_add]
    dsimp
    have h1 : cl55EnvelopeMap (J := J) (x + y) = cl55EnvelopeMap (J := J) x + cl55EnvelopeMap (J := J) y :=
      (cl55EnvelopeLinear (J := J)).map_add x y
    have h2 : contactEnvelopeMap datum (u + v) = contactEnvelopeMap datum u + contactEnvelopeMap datum v :=
      (contactEnvelopeLinear datum).map_add u v
    rw [h1, h2]
    abel
  map_smul' r z := by
    rcases z with ⟨x, u⟩
    rw [jointSourceEnvelopeMap_eq_add, jointSourceEnvelopeMap_eq_add]
    dsimp
    have h1 : cl55EnvelopeMap (J := J) (r • x) = r • cl55EnvelopeMap (J := J) x :=
      (cl55EnvelopeLinear (J := J)).map_smul r x
    have h2 : contactEnvelopeMap datum (r • u) = r • contactEnvelopeMap datum u :=
      (contactEnvelopeLinear datum).map_smul r u
    rw [h1, h2, smul_add]

/-- One native Lie homomorphism from the external direct product into the
operator-Zorn envelope. -/
def jointSourceEnvelopeLieHom :
    JointSource datum →ₗ⁅ℝ⁆ JointEnvelope (J := J) where
  toLinearMap := jointSourceEnvelopeLinear datum
  map_lie' {z w} := by
    rcases z with ⟨x, u⟩
    rcases w with ⟨y, v⟩
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
    apply congrArg FaithfulOperatorZornEnvelope.diagonal
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
    exact (jointSourceEnvelopeLinear datum).map_add (z.1.1, z.2.1) (w.1.1, w.2.1)
  map_smul' r z := by
    apply Subtype.ext
    exact (jointSourceEnvelopeLinear datum).map_smul r (z.1.1, z.2.1)

/-- The synchronized restricted map is faithful. -/
theorem synchronizedGradeMap_injective (g : ConformalGrade) :
    Function.Injective (synchronizedGradeMap datum g) := by
  intro z w h
  have hval := congrArg Subtype.val h
  have hinj := jointSourceEnvelopeLieHom_injective datum hval
  have hx : z.1.1 = w.1.1 := congrArg Prod.fst hinj
  have hu : z.2.1 = w.2.1 := congrArg Prod.snd hinj
  apply Prod.ext
  · exact Subtype.ext hx
  · exact Subtype.ext hu

/-- The component Lie homomorphisms commute pointwise in the common target. -/
theorem component_lieHom_cross_commutator_zero
    (x : Cl55) (u : FiveGradedCarrier datum) :
    commutator (cl55EnvelopeLieHom (J := J) x)
      (contactEnvelopeLieHom datum u) = 0 := by
  exact cl55_contact_cross_commutator_zero datum x u

end InfoGeometry.OperatorAlgebra.Cl55FreudenthalZornLieRepresentation
