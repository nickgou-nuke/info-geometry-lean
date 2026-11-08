import InfoGeometry.Optics.QuaternionCl44DiracImplementer
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Optics.OperatorQGTBogoliubovNaturality

set_option autoImplicit false

/-!
# Quaternionic `Cl(4,4)` Dirac covariance of operator QGT soldering

The maintained real gamma action is obtained by restricting complex-linear
Zorn Dirac operators.  Hence the complex Dirac spinor is a canonical internal
carrier for the operator-valued QGT calculus.  This file uses that carrier to
prove that coefficientwise conjugation by the positive scalar gamma operator
is exactly quaternionic twisted conjugation of every BKM and Berry coordinate,
and that QGT soldering transports this action to the doubled sheet carrier.
-/

noncomputable section

namespace InfoGeometry.Optics.QuaternionCl44QGTDiracCovariance

open CanonicalZornCliffordRepresentation
open CanonicalZornRealSpin44
open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation
open InfoGeometry.Optics.OperatorCausalSoldering
open InfoGeometry.Optics.OperatorQGTBogoliubovNaturality
open InfoGeometry.Optics.QuaternionCl44DiracOperatorBridge
open InfoGeometry.Optics.QuaternionCl44DiracImplementer
open InfoGeometry.Optics.QuaternionCl44TwistedConjugationLift
open InfoGeometry.OperatorAlgebra
open InfoGeometry.Unified

abbrev ComplexDiracEnd44 := Module.End ℂ DiracSpinor16

/-- Complex-linear gamma operator attached to a real quaternionic `(4+4)`
coordinate. -/
def cartesianComplexGamma (X : CartesianCoordinates) : ComplexDiracEnd44 :=
  diracGamma (realSplit44ToVector8 (cartesianToRealSplit44 X))

@[simp] theorem cartesianComplexGamma_apply (X : CartesianCoordinates) :
    cartesianComplexGamma X =
      diracGamma (realSplit44ToVector8 (cartesianToRealSplit44 X)) :=
  rfl

@[simp] theorem cartesianComplexGamma_add
    (X Y : CartesianCoordinates) :
    cartesianComplexGamma (X + Y) =
      cartesianComplexGamma X + cartesianComplexGamma Y := by
  unfold cartesianComplexGamma
  rw [map_add, map_add]
  exact diracGammaLinear.map_add _ _

@[simp] theorem cartesianComplexGamma_smul_real
    (r : ℝ) (X : CartesianCoordinates) :
    cartesianComplexGamma (r • X) =
      (r : ℂ) • cartesianComplexGamma X := by
  change diracGamma
      (realSplit44ToVector8 (cartesianToRealSplit44 (r • X))) = _
  rw [map_smul, map_smul]
  exact diracGammaLinear.map_smul (r : ℂ) _

@[simp] theorem cartesianComplexGamma_sq (X : CartesianCoordinates) :
    cartesianComplexGamma X * cartesianComplexGamma X =
      algebraMap ℝ ComplexDiracEnd44 (cartesianQuadratic44 X) := by
  rw [cartesianComplexGamma, diracGamma_sq,
    vectorQuadratic_realSplit44ToVector8]
  rfl

/-- The real Clifford algebra represented by the original complex-linear
Dirac operators. -/
def cartesianComplexCliffordRepresentation :
    CartesianCl44 →ₐ[ℝ] ComplexDiracEnd44 :=
  CliffordAlgebra.lift cartesianQuadratic44
    ⟨{ toFun := cartesianComplexGamma
       map_add' := cartesianComplexGamma_add
       map_smul' := by
         intro r X
         exact cartesianComplexGamma_smul_real r X },
      cartesianComplexGamma_sq⟩

set_option synthInstance.maxHeartbeats 100000 in
@[simp] theorem cartesianComplexCliffordRepresentation_ι
    (X : CartesianCoordinates) :
    cartesianComplexCliffordRepresentation
        (CliffordAlgebra.ι cartesianQuadratic44 X) =
      cartesianComplexGamma X := by
  exact CliffordAlgebra.lift_ι_apply _ cartesianComplexGamma_sq X

/-- Complex-linear gamma on the positive scalar direction. -/
def scalarPositiveComplexGamma : ComplexDiracEnd44 :=
  cartesianComplexGamma scalarPositiveDirection

@[simp] theorem scalarPositiveComplexGamma_sq :
    scalarPositiveComplexGamma * scalarPositiveComplexGamma = 1 := by
  rw [scalarPositiveComplexGamma, cartesianComplexGamma_sq,
    cartesianQuadratic44_scalarPositiveDirection]
  exact map_one (algebraMap ℝ ComplexDiracEnd44)

/-- The Dirac implementer as an invertible internal complex-linear frame. -/
def scalarPositiveComplexGammaUnit : ComplexDiracEnd44ˣ where
  val := scalarPositiveComplexGamma
  inv := scalarPositiveComplexGamma
  val_inv := scalarPositiveComplexGamma_sq
  inv_val := scalarPositiveComplexGamma_sq

@[simp] theorem scalarPositiveComplexGammaUnit_val :
    (scalarPositiveComplexGammaUnit : ComplexDiracEnd44) =
      scalarPositiveComplexGamma :=
  rfl

@[simp] theorem scalarPositiveComplexGammaUnit_inv_val :
    (↑(scalarPositiveComplexGammaUnit⁻¹) : ComplexDiracEnd44) =
      scalarPositiveComplexGamma :=
  rfl

/-- Complex-linear Dirac form of the quaternionic twisted-conjugation
implementer theorem. -/
theorem scalarPositiveComplexGamma_conjugates
    (X : CartesianCoordinates) :
    scalarPositiveComplexGamma * cartesianComplexGamma X *
        scalarPositiveComplexGamma =
      cartesianComplexGamma (cartesianTwistedConj X) := by
  have h := congrArg (fun a : CartesianCl44 =>
      cartesianComplexCliffordRepresentation a)
    (scalarPositiveClifford_conj_ι X)
  simpa [scalarPositiveClifford, scalarPositiveComplexGamma,
    cartesianComplexCliffordRepresentation_ι] using h

/-- A gamma-valued QGT whose symmetric and antisymmetric channels are both
specified by real quaternionic `(4+4)` coordinate fields. -/
def diracQGTFourVector
    (symmetric antisymmetric : Fin 4 → CartesianCoordinates) :
    QGTFourVector DiracSpinor16 where
  symmetricBKM := fun i => cartesianComplexGamma (symmetric i)
  antisymmetricBerry := fun i => cartesianComplexGamma (antisymmetric i)

@[simp] theorem diracQGTFourVector_symmetricBKM_apply
    (symmetric antisymmetric : Fin 4 → CartesianCoordinates) (i : Fin 4) :
    (diracQGTFourVector symmetric antisymmetric).symmetricBKM i =
      cartesianComplexGamma (symmetric i) :=
  rfl

@[simp] theorem diracQGTFourVector_antisymmetricBerry_apply
    (symmetric antisymmetric : Fin 4 → CartesianCoordinates) (i : Fin 4) :
    (diracQGTFourVector symmetric antisymmetric).antisymmetricBerry i =
      cartesianComplexGamma (antisymmetric i) :=
  rfl

/-- Apply transported canonical Zorn conjugation to every coordinate in a
four-vector field. -/
def twistedConjCoordinates
    (v : Fin 4 → CartesianCoordinates) : Fin 4 → CartesianCoordinates :=
  fun i => cartesianTwistedConj (v i)

/-- Internal Dirac-frame conjugation of both QGT channels is exactly
coordinatewise quaternionic twisted conjugation. -/
theorem qgtInternalConjugation_diracQGTFourVector
    (symmetric antisymmetric : Fin 4 → CartesianCoordinates) :
    qgtInternalConjugation scalarPositiveComplexGammaUnit
        (diracQGTFourVector symmetric antisymmetric) =
      diracQGTFourVector
        (twistedConjCoordinates symmetric)
        (twistedConjCoordinates antisymmetric) := by
  unfold qgtInternalConjugation diracQGTFourVector
  congr 1
  · funext i
    exact scalarPositiveComplexGamma_conjugates (symmetric i)
  · funext i
    exact scalarPositiveComplexGamma_conjugates (antisymmetric i)

/-- Full cross-layer covariance: quaternionic twisted conjugation may be
performed on every BKM/Berry coordinate before QGT soldering or by inner
Dirac conjugation on the doubled spinor carrier afterwards. -/
theorem QGTSoldering_dirac_twistedConj_covariant
    (symmetric antisymmetric : Fin 4 → CartesianCoordinates) :
    QGTSoldering
        (diracQGTFourVector
          (twistedConjCoordinates symmetric)
          (twistedConjCoordinates antisymmetric)) =
      innerConjugation
        (doubledInternalUnit scalarPositiveComplexGammaUnit)
        (QGTSoldering (diracQGTFourVector symmetric antisymmetric)) := by
  rw [← qgtInternalConjugation_diracQGTFourVector]
  exact QGTSoldering_internalConjugation
    scalarPositiveComplexGammaUnit
    (diracQGTFourVector symmetric antisymmetric)

/-- Closure packet joining the quaternionic coordinates, complex Dirac
operators, QGT channels, and doubled-sheet soldering action. -/
theorem quaternion_cl44_qgt_dirac_covariance_packet
    (symmetric antisymmetric : Fin 4 → CartesianCoordinates) :
    (∀ X : CartesianCoordinates,
      scalarPositiveComplexGamma * cartesianComplexGamma X *
          scalarPositiveComplexGamma =
        cartesianComplexGamma (cartesianTwistedConj X)) ∧
    qgtInternalConjugation scalarPositiveComplexGammaUnit
        (diracQGTFourVector symmetric antisymmetric) =
      diracQGTFourVector
        (twistedConjCoordinates symmetric)
        (twistedConjCoordinates antisymmetric) ∧
    QGTSoldering
        (diracQGTFourVector
          (twistedConjCoordinates symmetric)
          (twistedConjCoordinates antisymmetric)) =
      innerConjugation
        (doubledInternalUnit scalarPositiveComplexGammaUnit)
        (QGTSoldering (diracQGTFourVector symmetric antisymmetric)) := by
  exact ⟨scalarPositiveComplexGamma_conjugates,
    qgtInternalConjugation_diracQGTFourVector symmetric antisymmetric,
    QGTSoldering_dirac_twistedConj_covariant symmetric antisymmetric⟩

end InfoGeometry.Optics.QuaternionCl44QGTDiracCovariance

end noncomputable section
