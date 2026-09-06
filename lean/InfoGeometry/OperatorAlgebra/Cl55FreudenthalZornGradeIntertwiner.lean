import InfoGeometry.OperatorAlgebra.FaithfulOperatorZornEnvelope
import InfoGeometry.Clifford.SpinorRep
import InfoGeometry.Clifford.ConformalLieAlgebra55
import InfoGeometry.Canonical.O55FiveGradeClosure
import InfoGeometry.Exceptional.FreudenthalSymplecticContactCommonCARCCR
import Mathlib.Tactic

/-!
# Grade-preserving Cl(5,5) and Freudenthal maps into one Zorn envelope

The common coefficient algebra is a direct product of two faithful operator
algebras:

* the left-regular endomorphism algebra of the native `Cl(5,5)` algebra;
* the existing common CAR--CCR endomorphism algebra carrying the corrected
  Freudenthal symplectic-contact representation.

Both are placed diagonally in the same `2 x 2` operator-Zorn envelope.  The
images commute because they occupy distinct direct-product factors.  This is a
proved product representation, not an identification of the two source
algebras.

The native real `32 x 32` Clifford spin representation is retained separately
and is linked to the faithful regular representation by the algebra-homomorphism
intertwining law.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.Cl55FreudenthalZornGradeIntertwiner

open Matrix
open InfoGeometry.OperatorAlgebra.FaithfulOperatorZornEnvelope
open InfoGeometry.Clifford.ClNN
open InfoGeometry.Clifford.SpinorRep
open InfoGeometry.Clifford.ConformalLieAlgebra55
open InfoGeometry.Canonical.O55FiveGradeClosure
open InfoGeometry.Exceptional.Freudenthal

abbrev Cl55 := Alg 5
abbrev Cl55RegularEnd := Module.End ℝ Cl55
abbrev Cl55Spinor := SpinorSpace 5
abbrev Cl55SpinorMatrix := SpinorMatrix 5

variable {J : Type*} [AddCommGroup J] [Module ℝ J]
variable (datum : CubicJordanDatum J)

/-- Direct-product coefficient algebra for the two independent symmetry
sources. -/
abbrev JointCoefficient :=
  Cl55RegularEnd × SymplecticContactCommonEnd (J := J)

/-- One common associative operator-Zorn envelope. -/
abbrev JointEnvelope := Envelope (JointCoefficient (J := J))

/-- Cl(5,5) source coefficient in the first product factor. -/
def cl55Coefficient (x : Cl55) : JointCoefficient (J := J) :=
  (leftMultiply x, 0)

/-- Freudenthal source coefficient in the second product factor. -/
def contactCoefficient
    (u : FiveGradedCarrier datum) : JointCoefficient (J := J) :=
  (0, symplecticContactCommonRepresentation datum u)

/-- Faithful Cl(5,5) map into the common Zorn envelope. -/
def cl55EnvelopeMap (x : Cl55) : JointEnvelope (J := J) :=
  diagonal (cl55Coefficient (J := J) x)

/-- Faithful Freudenthal contact map into the common Zorn envelope. -/
def contactEnvelopeMap
    (u : FiveGradedCarrier datum) : JointEnvelope (J := J) :=
  diagonal (contactCoefficient datum u)

/-- Bundled real-linear Cl(5,5) envelope map. -/
def cl55EnvelopeLinear :
    Cl55 →ₗ[ℝ] JointEnvelope (J := J) where
  toFun := cl55EnvelopeMap (J := J)
  map_add' x y := by
    simp [cl55EnvelopeMap, cl55Coefficient, leftMultiply_add]
  map_smul' r x := by
    simp [cl55EnvelopeMap, cl55Coefficient, leftMultiply_smul]

/-- Bundled real-linear Freudenthal envelope map. -/
def contactEnvelopeLinear :
    FiveGradedCarrier datum →ₗ[ℝ] JointEnvelope (J := J) where
  toFun := contactEnvelopeMap datum
  map_add' u v := by
    simp [contactEnvelopeMap, contactCoefficient]
  map_smul' r u := by
    simp [contactEnvelopeMap, contactCoefficient]

/-- Cl(5,5) commutators are represented by envelope commutators. -/
theorem cl55EnvelopeMap_commutator (x y : Cl55) :
    cl55EnvelopeMap (J := J) (x * y - y * x) =
      commutator (cl55EnvelopeMap (J := J) x)
        (cl55EnvelopeMap (J := J) y) := by
  unfold cl55EnvelopeMap cl55Coefficient
  rw [diagonal_commutator]
  apply congrArg diagonal
  apply Prod.ext
  · exact leftRegular_commutator x y
  · simp

/-- The corrected Freudenthal Lie bracket is represented by the same envelope
commutator. -/
theorem contactEnvelopeMap_bracket
    (u v : FiveGradedCarrier datum) :
    contactEnvelopeMap datum ⁅u, v⁆ =
      commutator (contactEnvelopeMap datum u)
        (contactEnvelopeMap datum v) := by
  unfold contactEnvelopeMap contactCoefficient
  rw [diagonal_commutator]
  apply congrArg diagonal
  apply Prod.ext
  · simp
  · have h := symplecticContactCommonRepresentation_bracket datum u v
    change symplecticContactCommonRepresentation datum ⁅u, v⁆ =
      symplecticContactCommonRepresentation datum u *
          symplecticContactCommonRepresentation datum v -
        symplecticContactCommonRepresentation datum v *
          symplecticContactCommonRepresentation datum u at h
    exact h

/-- The two independently represented source factors commute in the common
direct-product envelope. -/
theorem cl55_contact_cross_commutator_zero
    (x : Cl55) (u : FiveGradedCarrier datum) :
    commutator (cl55EnvelopeMap (J := J) x)
      (contactEnvelopeMap datum u) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [commutator, cl55EnvelopeMap, contactEnvelopeMap,
      cl55Coefficient, contactCoefficient, diagonal,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The Cl(5,5) envelope map is faithful by the regular representation. -/
theorem cl55EnvelopeMap_injective :
    Function.Injective (cl55EnvelopeMap (J := J)) := by
  intro x y hxy
  have hp : cl55Coefficient (J := J) x =
      cl55Coefficient (J := J) y :=
    diagonal_injective hxy
  have hreg : leftMultiply x = leftMultiply y :=
    congrArg Prod.fst hp
  have h1 := congrArg (fun T : Cl55RegularEnd => T 1) hreg
  simpa using h1

/-- The Freudenthal envelope map remains faithful. -/
theorem contactEnvelopeMap_injective :
    Function.Injective (contactEnvelopeMap datum) := by
  intro u v huv
  have hp : contactCoefficient datum u = contactCoefficient datum v :=
    diagonal_injective huv
  have hrho :
      symplecticContactCommonRepresentation datum u =
        symplecticContactCommonRepresentation datum v :=
    congrArg Prod.snd hp
  exact symplecticContactCommonRepresentation_injective datum hrho

/-- Euler coefficient combining the two independent grading generators. -/
def jointEulerCoefficient : JointCoefficient (J := J) :=
  (leftMultiply InfoGeometry.Clifford.ConformalLieAlgebra55.D,
    symplecticContactCommonRepresentation datum
      (symplecticContactEuler datum))

/-- Adjoint grade in the common envelope. -/
def HasJointGrade (k : ℤ) (X : JointEnvelope (J := J)) : Prop :=
  HasAdjointGrade (jointEulerCoefficient datum) k X

/-- Extract the adjoint eigenvalue equation from native Clifford grade
membership. -/
theorem cl55_grade_equation
    (g : ConformalGrade) {x : Cl55}
    (hx : x ∈ gradeSpace g) :
    InfoGeometry.Clifford.ConformalLieAlgebra55.D * x -
        x * InfoGeometry.Clifford.ConformalLieAlgebra55.D =
      (toInt g : ℝ) • x := by
  have hx0 :
      (adD - (toInt g : ℝ) • (LinearMap.id : Cl55 →ₗ[ℝ] Cl55)) x = 0 :=
    LinearMap.mem_ker.mp hx
  have hx1 : adD x - (toInt g : ℝ) • x = 0 := by
    simpa using hx0
  have hx2 : adD x = (toInt g : ℝ) • x :=
    sub_eq_zero.mp hx1
  simpa [adD] using hx2

/-- Every native Cl(5,5) conformal grade is preserved by the faithful envelope
map. -/
theorem cl55EnvelopeMap_preserves_grade
    (g : ConformalGrade) {x : Cl55}
    (hx : x ∈ gradeSpace g) :
    HasJointGrade datum (toInt g) (cl55EnvelopeMap (J := J) x) := by
  unfold HasJointGrade jointEulerCoefficient cl55EnvelopeMap cl55Coefficient
  apply diagonal_preserves_adjoint_grade
  apply Prod.ext
  · exact leftRegular_preserves_adjoint_grade
      InfoGeometry.Clifford.ConformalLieAlgebra55.D x (toInt g)
      (cl55_grade_equation g hx)
  · simp

/-- Every corrected Freudenthal contact grade is preserved in the same common
envelope. -/
theorem contactEnvelopeMap_preserves_grade
    (k : ℤ) {u : FiveGradedCarrier datum}
    (hu : u ∈ symplecticContactGradeSpace datum k) :
    HasJointGrade datum k (contactEnvelopeMap datum u) := by
  change SymplecticContactHasGrade datum k u at hu
  have hrho := congrArg
    (fun w : FiveGradedCarrier datum =>
      symplecticContactCommonRepresentation datum w) hu
  rw [symplecticContactCommonRepresentation_bracket] at hrho
  rw [map_smul] at hrho
  change
    symplecticContactCommonRepresentation datum
          (symplecticContactEuler datum) *
        symplecticContactCommonRepresentation datum u -
      symplecticContactCommonRepresentation datum u *
        symplecticContactCommonRepresentation datum
          (symplecticContactEuler datum) =
      (k : ℝ) • symplecticContactCommonRepresentation datum u at hrho
  unfold HasJointGrade jointEulerCoefficient contactEnvelopeMap
  apply diagonal_preserves_adjoint_grade
  apply Prod.ext
  · simp
  · exact hrho

/-! ## Native real Cl(5,5) spin representation -/

/-- Real `32 x 32` spin action of a Clifford element. -/
def cl55SpinAction (x : Cl55) (psi : Cl55Spinor) : Cl55Spinor :=
  (spinorRepresentation 5 x).mulVec psi

@[simp] theorem cl55SpinAction_one (psi : Cl55Spinor) :
    cl55SpinAction 1 psi = psi := by
  simp [cl55SpinAction]

/-- The spin action is a representation of Clifford multiplication. -/
theorem cl55SpinAction_mul (x y : Cl55) (psi : Cl55Spinor) :
    cl55SpinAction (x * y) psi =
      cl55SpinAction x (cl55SpinAction y psi) := by
  simp [cl55SpinAction, Matrix.mulVec_mulVec]

/-- The native spinor representation intertwines the faithful left-regular
action with matrix left multiplication. -/
theorem spinorRepresentation_intertwines_leftRegular
    (x y : Cl55) :
    spinorRepresentation 5 (leftMultiply x y) =
      spinorRepresentation 5 x * spinorRepresentation 5 y := by
  exact map_mul (spinorRepresentation 5) x y

/-- Spin-matrix envelope of a native Cl(5,5) element. -/
def cl55SpinorEnvelopeMap (x : Cl55) :
    Envelope Cl55SpinorMatrix :=
  diagonal (spinorRepresentation 5 x)

/-- Native conformal grades remain grades after the real spin representation
and the diagonal Zorn-envelope lift. -/
theorem cl55SpinorEnvelopeMap_preserves_grade
    (g : ConformalGrade) {x : Cl55}
    (hx : x ∈ gradeSpace g) :
    HasAdjointGrade
      (spinorRepresentation 5
        InfoGeometry.Clifford.ConformalLieAlgebra55.D)
      (toInt g) (cl55SpinorEnvelopeMap x) := by
  have hmap := congrArg (spinorRepresentation 5)
    (cl55_grade_equation g hx)
  have hcomm :
      spinorRepresentation 5
          InfoGeometry.Clifford.ConformalLieAlgebra55.D *
          spinorRepresentation 5 x -
        spinorRepresentation 5 x *
          spinorRepresentation 5
            InfoGeometry.Clifford.ConformalLieAlgebra55.D =
      (toInt g : ℝ) • spinorRepresentation 5 x := by
    simpa using hmap
  exact diagonal_preserves_adjoint_grade _ _ _ hcomm

/-- The five selected native Cl(5,5) lanes all land in the corresponding
operator-Zorn grades. -/
theorem selected_cl55_five_grade_packet :
    HasJointGrade datum (-2)
        (cl55EnvelopeMap (J := J) (v5 * v4 - v4 * v5)) ∧
      HasJointGrade datum (-1) (cl55EnvelopeMap (J := J) v5) ∧
      HasJointGrade datum 0
        (cl55EnvelopeMap (J := J)
          InfoGeometry.Clifford.ConformalLieAlgebra55.D) ∧
      HasJointGrade datum 1 (cl55EnvelopeMap (J := J) u5) ∧
      HasJointGrade datum 2
        (cl55EnvelopeMap (J := J) (u5 * u4 - u4 * u5)) := by
  exact ⟨
    cl55EnvelopeMap_preserves_grade datum ConformalGrade.negTwo
      v5_v4_commutator_grade_neg_two,
    cl55EnvelopeMap_preserves_grade datum ConformalGrade.negOne v5_grade,
    cl55EnvelopeMap_preserves_grade datum ConformalGrade.zero D_grade,
    cl55EnvelopeMap_preserves_grade datum ConformalGrade.posOne u5_grade,
    cl55EnvelopeMap_preserves_grade datum ConformalGrade.posTwo
      u5_u4_commutator_grade_pos_two⟩

/-- The named Freudenthal five-grade generators land in the same common target
grade convention. -/
theorem selected_freudenthal_five_grade_packet
    (xMinus xPlus : FreudenthalCharge J)
    (T : SymplecticTKKZero datum) :
    HasJointGrade datum (-2) (contactEnvelopeMap datum (genEminus datum 1)) ∧
      HasJointGrade datum (-1)
        (contactEnvelopeMap datum (injChargeMinus datum xMinus)) ∧
      HasJointGrade datum 0
        (contactEnvelopeMap datum (injSympZero datum T)) ∧
      HasJointGrade datum 1
        (contactEnvelopeMap datum (injChargePlus datum xPlus)) ∧
      HasJointGrade datum 2 (contactEnvelopeMap datum (genEplus datum 1)) := by
  exact ⟨
    contactEnvelopeMap_preserves_grade datum (-2)
      (genEminus_contact_grade datum 1),
    contactEnvelopeMap_preserves_grade datum (-1)
      (injChargeMinus_contact_grade datum xMinus),
    contactEnvelopeMap_preserves_grade datum 0
      (injSympZero_contact_grade datum T),
    contactEnvelopeMap_preserves_grade datum 1
      (injChargePlus_contact_grade datum xPlus),
    contactEnvelopeMap_preserves_grade datum 2
      (genEplus_contact_grade datum 1)⟩

end InfoGeometry.OperatorAlgebra.Cl55FreudenthalZornGradeIntertwiner
