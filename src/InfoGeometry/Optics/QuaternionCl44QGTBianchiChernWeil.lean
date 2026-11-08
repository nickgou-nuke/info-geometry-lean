import InfoGeometry.Optics.QuaternionCl44QGTCurvatureCovariance
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Optics.OperatorQGTChernWeil

set_option autoImplicit false

/-!
# Quaternionic `Cl(4,4)` QGT Bianchi and Chern--Weil covariance

The positive scalar Clifford implementer is packaged as a constant native
right gauge frame.  Its Maurer--Cartan form vanishes, so the generic local
gauge derivative is exactly coefficientwise inner conjugation.  This gives
an iff transport theorem for the adjoint Bianchi equation and closedness of
every traced curvature-power derivative in the twisted quaternionic frame.
-/

noncomputable section

namespace InfoGeometry.Optics.QuaternionCl44QGTBianchiChernWeil

open CanonicalZornCliffordRepresentation
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.OperatorAlgebra
open InfoGeometry.Optics.LocalGaugeAdjointAction
open InfoGeometry.Optics.LocalGaugeCovariantDerivative
open InfoGeometry.Optics.LocalGaugeGroupAction
open InfoGeometry.Optics.LocalGaugeQGTCovariance
open InfoGeometry.Optics.OperatorQGTBogoliubovNaturality
open InfoGeometry.Optics.OperatorQGTChernWeil
open InfoGeometry.Optics.OperatorQGTConnectionCovariance
open InfoGeometry.Optics.OperatorValuedConnection
open InfoGeometry.Optics.QuaternionCl44QGTCurvatureCovariance
open InfoGeometry.Optics.QuaternionCl44QGTDiracCovariance

/-- The positive scalar Clifford implementer as a constant gauge frame on
the doubled complex Dirac carrier. -/
def scalarPositiveDiracGaugeFrame {Point Tangent : Type*} :
    RightGaugeGroup
      (Point := Point) (Tangent := Tangent) (A := DiracDoubledEnd) where
  frame _ := doubledInternalUnit scalarPositiveComplexGammaUnit
  theta _ _ := 0

@[simp] theorem scalarPositiveDiracGaugeFrame_frame
    {Point Tangent : Type*} (p : Point) :
    (scalarPositiveDiracGaugeFrame
      (Point := Point) (Tangent := Tangent)).frame p =
        doubledInternalUnit scalarPositiveComplexGammaUnit :=
  rfl

@[simp] theorem scalarPositiveDiracGaugeFrame_theta
    {Point Tangent : Type*} (p : Point) (X : Tangent) :
    (scalarPositiveDiracGaugeFrame
      (Point := Point) (Tangent := Tangent)).theta p X = 0 :=
  rfl

/-- The constant local gauge action is exactly the existing homogeneous
internal-frame connection action. -/
theorem scalarPositiveDiracGaugeFrame_smul_eq_internalFrame
    {Point Tangent : Type*}
    (C : Connection
      (Point := Point) (Tangent := Tangent) (Value := DiracDoubledEnd)) :
    (scalarPositiveDiracGaugeFrame
      (Point := Point) (Tangent := Tangent)) • C =
      internalFrameConnection scalarPositiveComplexGammaUnit C := by
  apply connection_ext
  · funext p X
    change innerConjugation
        (doubledInternalUnit scalarPositiveComplexGammaUnit) (C.form p X) - 0 =
      innerConjugation
        (doubledInternalUnit scalarPositiveComplexGammaUnit) (C.form p X)
    exact sub_zero _
  · apply connection_derivative_eq_of_form_curvature_eq
    · funext p X
      change innerConjugation
          (doubledInternalUnit scalarPositiveComplexGammaUnit) (C.form p X) - 0 =
        innerConjugation
          (doubledInternalUnit scalarPositiveComplexGammaUnit) (C.form p X)
      exact sub_zero _
    · intro p X Y
      rw [rightGaugeGroup_smul_curvature,
        internalFrameConnection_curvature]
      rfl

/-- The generic gauge curvature derivative reduces to plain inner
conjugation because this Clifford frame is constant. -/
theorem scalarPositiveDiracGaugeFrame_gaugeCurvatureDerivative
    {Point Tangent : Type*}
    (C : Connection
      (Point := Point) (Tangent := Tangent) (Value := DiracDoubledEnd))
    (dF : Point → Tangent → Tangent → Tangent → DiracDoubledEnd)
    (p : Point) (X U V : Tangent) :
    gaugeCurvatureDerivative scalarPositiveDiracGaugeFrame C dF p X U V =
      innerConjugation
        (doubledInternalUnit scalarPositiveComplexGammaUnit) (dF p X U V) := by
  change innerConjugation
      (doubledInternalUnit scalarPositiveComplexGammaUnit) (dF p X U V) +
        associativeCommutator 0
          (innerConjugation
            (doubledInternalUnit scalarPositiveComplexGammaUnit)
            (curvature C p U V)) = _
  unfold associativeCommutator
  simp only [zero_mul, mul_zero, sub_self, add_zero]

/-- Curvature differential transported by the quaternionic Clifford frame. -/
def conjugateDiracCurvatureDifferential {Point Tangent : Type*}
    (dF : Point → Tangent → Tangent → Tangent → DiracDoubledEnd) :
    Point → Tangent → Tangent → Tangent → DiracDoubledEnd :=
  fun p X U V ↦ innerConjugation
    (doubledInternalUnit scalarPositiveComplexGammaUnit) (dF p X U V)

/-- The adjoint Bianchi equation is both preserved and reflected by the
constant split-quaternion/Clifford frame. -/
theorem internalFrame_satisfiesAdjointBianchi_iff
    {Point Tangent : Type*}
    (C : Connection
      (Point := Point) (Tangent := Tangent) (Value := DiracDoubledEnd))
    (dF : Point → Tangent → Tangent → Tangent → DiracDoubledEnd) :
    SatisfiesAdjointBianchi
        (internalFrameConnection scalarPositiveComplexGammaUnit C)
        (conjugateDiracCurvatureDifferential dF) ↔
      SatisfiesAdjointBianchi C dF := by
  rw [← scalarPositiveDiracGaugeFrame_smul_eq_internalFrame C]
  have h := satisfiesAdjointBianchi_smul_iff
    (scalarPositiveDiracGaugeFrame
      (Point := Point) (Tangent := Tangent)) C dF
  have hd : gaugeCurvatureDerivative
      (scalarPositiveDiracGaugeFrame
        (Point := Point) (Tangent := Tangent)) C dF =
      conjugateDiracCurvatureDifferential dF := by
    funext p X U V
    exact scalarPositiveDiracGaugeFrame_gaugeCurvatureDerivative C dF p X U V
  rw [hd] at h
  exact h

/-- Coordinate-level quaternionic form of Bianchi covariance for the
gamma-valued soldered QGT connection. -/
theorem solderedDiracQGTConnection_twistedConj_satisfiesAdjointBianchi_iff
    {Point Tangent : Type*}
    (symmetric antisymmetric :
      Point → Tangent → Fin 4 → CartesianCoordinates)
    (dQ : Point → Tangent → Tangent → DiracDoubledEnd)
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0)
    (dF : Point → Tangent → Tangent → Tangent → DiracDoubledEnd) :
    SatisfiesAdjointBianchi
        (solderedQGTConnection
          (diracQGTField
            (twistedConjCoordinateField symmetric)
            (twistedConjCoordinateField antisymmetric))
          (conjugateDiracTwoForm dQ)
          (conjugateDiracTwoForm_swap dQ dQ_swap)
          (conjugateDiracTwoForm_same dQ dQ_same))
        (conjugateDiracCurvatureDifferential dF) ↔
      SatisfiesAdjointBianchi
        (solderedQGTConnection
          (diracQGTField symmetric antisymmetric)
          dQ dQ_swap dQ_same) dF := by
  rw [solderedDiracQGTConnection_twistedConj_eq_internalFrame]
  exact internalFrame_satisfiesAdjointBianchi_iff
    (solderedQGTConnection
      (diracQGTField symmetric antisymmetric)
      dQ dQ_swap dQ_same) dF

/-- The ordered noncommutative power derivative is equivariant under the
constant Clifford-frame automorphism.  This is the algebraic differential
statement available on the finite Zorn carrier without postulating a norm. -/
theorem operatorPowerDerivative_scalarPositive_innerConjugation
    (n : ℕ) (F dF : DiracDoubledEnd) :
    operatorPowerDerivative n
        (innerConjugation
          (doubledInternalUnit scalarPositiveComplexGammaUnit) F)
        (innerConjugation
          (doubledInternalUnit scalarPositiveComplexGammaUnit) dF) =
      innerConjugation
        (doubledInternalUnit scalarPositiveComplexGammaUnit)
        (operatorPowerDerivative n F dF) := by
  induction n with
  | zero =>
      change 0 = (innerConjugationRingEquiv
        (doubledInternalUnit scalarPositiveComplexGammaUnit)) 0
      exact (map_zero
        (innerConjugationRingEquiv
          (doubledInternalUnit scalarPositiveComplexGammaUnit))).symm
  | succ n ih =>
      rw [operatorPowerDerivative_succ, operatorPowerDerivative_succ, ih]
      change
        (innerConjugationRingEquiv
          (doubledInternalUnit scalarPositiveComplexGammaUnit))
            (operatorPowerDerivative n F dF) *
          (innerConjugationRingEquiv
            (doubledInternalUnit scalarPositiveComplexGammaUnit)) F +
        (innerConjugationRingEquiv
          (doubledInternalUnit scalarPositiveComplexGammaUnit)) F ^ n *
          (innerConjugationRingEquiv
            (doubledInternalUnit scalarPositiveComplexGammaUnit)) dF =
        (innerConjugationRingEquiv
          (doubledInternalUnit scalarPositiveComplexGammaUnit))
          (operatorPowerDerivative n F dF * F + F ^ n * dF)
      simp only [map_add, map_mul, map_pow]

/-- The trace of the ordered curvature-power differential is unchanged by
the split-quaternion Clifford frame, independently of a Bianchi hypothesis. -/
theorem trace_operatorPowerDerivative_scalarPositive_innerConjugation
    (n : ℕ) (F dF : DiracDoubledEnd) :
    LinearMap.trace ℂ (Fin 2 → DiracSpinor16)
        (operatorPowerDerivative n
          (innerConjugation
            (doubledInternalUnit scalarPositiveComplexGammaUnit) F)
          (innerConjugation
            (doubledInternalUnit scalarPositiveComplexGammaUnit) dF)) =
      LinearMap.trace ℂ (Fin 2 → DiracSpinor16)
        (operatorPowerDerivative n F dF) := by
  rw [operatorPowerDerivative_scalarPositive_innerConjugation]
  exact InfoGeometry.Optics.OperatorQGTGaugeInvariants.trace_innerConjugation
    (doubledInternalUnit scalarPositiveComplexGammaUnit)
    (operatorPowerDerivative n F dF)

/-- Full Chern--Weil closedness in the coordinatewise twisted quaternionic
frame: every traced ordered derivative of a curvature power vanishes. -/
theorem trace_twistedConj_curvaturePowerDerivative_zero_of_bianchi
    {Point Tangent : Type*}
    (n : ℕ)
    (symmetric antisymmetric :
      Point → Tangent → Fin 4 → CartesianCoordinates)
    (dQ : Point → Tangent → Tangent → DiracDoubledEnd)
    (dQ_swap : ∀ p X Y, dQ p Y X = -dQ p X Y)
    (dQ_same : ∀ p X, dQ p X X = 0)
    (dF : Point → Tangent → Tangent → Tangent → DiracDoubledEnd)
    (hBianchi : SatisfiesAdjointBianchi
      (solderedQGTConnection
        (diracQGTField symmetric antisymmetric)
        dQ dQ_swap dQ_same) dF)
    (p : Point) (X U V : Tangent) :
    LinearMap.trace ℂ (Fin 2 → DiracSpinor16)
      (operatorPowerDerivative n
        (curvature
          (solderedQGTConnection
            (diracQGTField
              (twistedConjCoordinateField symmetric)
              (twistedConjCoordinateField antisymmetric))
            (conjugateDiracTwoForm dQ)
            (conjugateDiracTwoForm_swap dQ dQ_swap)
            (conjugateDiracTwoForm_same dQ dQ_same)) p U V)
        (conjugateDiracCurvatureDifferential dF p X U V)) = 0 := by
  apply trace_curvaturePowerDerivative_zero_of_bianchi n
  exact (solderedDiracQGTConnection_twistedConj_satisfiesAdjointBianchi_iff
    symmetric antisymmetric dQ dQ_swap dQ_same dF).2 hBianchi

end InfoGeometry.Optics.QuaternionCl44QGTBianchiChernWeil

end noncomputable section
