import InfoGeometry.OperatorAlgebra.FiniteTwoTermDiracHodgeZorn
import InfoGeometry.OperatorAlgebra.RealWeylAdjointSpinRepresentation
import InfoGeometry.OperatorAlgebra.Cl55FreudenthalZornGradeIntertwiner

/-!
# Dirac--Hodge, real spin, and graded Zorn intertwiner closure

This capstone joins three proved interfaces while retaining their distinct
carriers:

1. a specified finite differential-form complex with `D=d+delta`;
2. the real Lorentz/Weyl spin action with a dagger right multiplier and an
   inverse-dagger right spinor representation;
3. faithful, grade-preserving Cl(5,5) and Freudenthal maps into one direct-
   product operator-Zorn envelope.

No equality between the Cl(5,5) and Freudenthal source algebras is asserted.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.DiracHodgeSpinZornIntertwinerClosure

open InfoGeometry.OperatorAlgebra.FiniteTwoTermDiracHodgeZorn
open InfoGeometry.OperatorAlgebra.RealWeylAdjointSpinRepresentation
open InfoGeometry.OperatorAlgebra.Cl55FreudenthalZornGradeIntertwiner
open InfoGeometry.Clifford.ConformalLieAlgebra55
open InfoGeometry.Exceptional.Freudenthal

/-- Complete finite differential-form/Zorn packet. -/
theorem finite_dirac_hodge_zorn_packet
    {n0 n1 : ℕ}
    (B : Matrix (Fin n1) (Fin n0) ℝ)
    (omega eta : TotalForms n0 n1) :
    sumSheets (blockAction (diracZornBlock B) (diagonalForm omega)) =
        diracHodge B omega ∧
      diracHodge B * diracHodge B = hodgeLaplacian B ∧
      diracHodge B * chirality = -(chirality * diracHodge B) ∧
      hodgeLaplacian B * chirality = chirality * hodgeLaplacian B ∧
      formPairing (exteriorDerivative B omega) eta =
        formPairing omega (codifferential B eta) := by
  exact ⟨sumSheets_diracZornBlock_intertwines B omega,
    diracHodge_sq_eq_hodgeLaplacian B,
    diracHodge_anticommutes_chirality B,
    hodgeLaplacian_commutes_chirality B,
    exterior_codifferential_adjoint B omega eta⟩

/-- Complete real Weyl-spin packet.  The theorem records both meanings of the
right factor and therefore prevents the dagger/representation conflation. -/
theorem real_spin_right_factor_packet
    (g h : SL2C) (X : Mat2C) (hX : star X = X)
    (psi : WeylPair) :
    InfoGeometry.Canonical.HestenesSpinAction.spinAction g X =
        (g : Mat2C) * X * rightAdjointMultiplier g ∧
      rightAdjointMultiplier (g * h) =
        rightAdjointMultiplier h * rightAdjointMultiplier g ∧
      rightWeyl (g * h) = rightWeyl g * rightWeyl h ∧
      actWeylPair (g * h) psi = actWeylPair g (actWeylPair h psi) ∧
      star (InfoGeometry.Canonical.HestenesSpinAction.spinAction g X) =
        InfoGeometry.Canonical.HestenesSpinAction.spinAction g X := by
  exact ⟨spinAction_eq_left_mul_rightAdjoint g X,
    rightAdjointMultiplier_mul_reverse g h,
    rightWeyl_mul g h,
    actWeylPair_mul g h psi,
    spinAction_preserves_hermitian g X hX⟩

/-- Joint faithful representation and grade-preservation packet. -/
theorem cl55_freudenthal_joint_envelope_packet
    {J : Type*} [AddCommGroup J] [Module ℝ J]
    (datum : CubicJordanDatum J)
    (g : ConformalGrade) (x y : Cl55)
    (hx : x ∈ gradeSpace g)
    (k : ℤ) (u v : FiveGradedCarrier datum)
    (hu : u ∈ symplecticContactGradeSpace datum k) :
    cl55EnvelopeMap (J := J) (x * y - y * x) =
        InfoGeometry.OperatorAlgebra.FaithfulOperatorZornEnvelope.commutator
          (cl55EnvelopeMap (J := J) x)
          (cl55EnvelopeMap (J := J) y) ∧
      contactEnvelopeMap datum ⁅u, v⁆ =
        InfoGeometry.OperatorAlgebra.FaithfulOperatorZornEnvelope.commutator
          (contactEnvelopeMap datum u) (contactEnvelopeMap datum v) ∧
      InfoGeometry.OperatorAlgebra.FaithfulOperatorZornEnvelope.commutator
          (cl55EnvelopeMap (J := J) x) (contactEnvelopeMap datum u) = 0 ∧
      Function.Injective (cl55EnvelopeMap (J := J)) ∧
      Function.Injective (contactEnvelopeMap datum) ∧
      HasJointGrade datum (toInt g) (cl55EnvelopeMap (J := J) x) ∧
      HasJointGrade datum k (contactEnvelopeMap datum u) := by
  exact ⟨cl55EnvelopeMap_commutator (J := J) x y,
    contactEnvelopeMap_bracket datum u v,
    cl55_contact_cross_commutator_zero datum x u,
    cl55EnvelopeMap_injective (J := J),
    contactEnvelopeMap_injective datum,
    cl55EnvelopeMap_preserves_grade datum g hx,
    contactEnvelopeMap_preserves_grade datum k hu⟩

/-- The real spin representation is an explicit quotient/readout of the same
native Cl(5,5) multiplication used by the faithful regular envelope. -/
theorem cl55_regular_to_spin_intertwiner_packet
    {J : Type*} [AddCommGroup J] [Module ℝ J]
    (datum : CubicJordanDatum J)
    (x y : Cl55) (psi : Cl55Spinor) :
    cl55SpinAction (x * y) psi =
        cl55SpinAction x (cl55SpinAction y psi) ∧
      spinorRepresentation 5
          (InfoGeometry.OperatorAlgebra.FaithfulOperatorZornEnvelope.
            leftMultiply x y) =
        spinorRepresentation 5 x * spinorRepresentation 5 y ∧
      Function.Injective (cl55EnvelopeMap (J := J)) ∧
      Function.Injective (contactEnvelopeMap datum) := by
  exact ⟨cl55SpinAction_mul x y psi,
    spinorRepresentation_intertwines_leftRegular x y,
    cl55EnvelopeMap_injective (J := J),
    contactEnvelopeMap_injective datum⟩

end InfoGeometry.OperatorAlgebra.DiracHodgeSpinZornIntertwinerClosure
