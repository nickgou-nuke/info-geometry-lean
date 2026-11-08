import InfoGeometry.Lie.SplitOctonionQuaternionParityOrientation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation
import InfoGeometry.Optics.QuaternionCl44QGTCurvatureCovariance

/-!
# Mirror/rail compatibility of the quaternionic QGT coordinate fields

The native mirror/rail isometry is real and acts on the Cartesian Zorn
coordinates.  The QGT owner already has a coordinatewise twisted-conjugation
field.  This file proves their exact commutation at the common real
coordinate level; it does not claim a complex Bogoliubov implementer.
-/

namespace InfoGeometry.Optics.SplitOctonionMirrorQGTCoordinateTransport

open InfoGeometry.Lie.SplitOctonionQuaternionZornCoordinates
open InfoGeometry.Lie.SplitOctonionQuaternionParityOrientation
open InfoGeometry.Lie.SplitOctonionQuaternionTwistedConjugation
open InfoGeometry.Optics.OperatorQGTBogoliubovNaturality
open InfoGeometry.Optics.QuaternionCl44QGTCurvatureCovariance

def mirrorRailCoordinateField {Point Tangent : Type*}
    (v : Point → Tangent → Fin 4 → CartesianCoordinates) :
    Point → Tangent → Fin 4 → CartesianCoordinates :=
  fun p X i ↦ mirrorRailSwapJK (v p X i)

theorem mirrorRailCoordinateField_twistedConj_commute
    {Point Tangent : Type*}
    (v : Point → Tangent → Fin 4 → CartesianCoordinates)
    (p : Point) (X : Tangent) (i : Fin 4) :
    cartesianTwistedConj
        (mirrorRailCoordinateField v p X i) =
      mirrorRailCoordinateField
        (twistedConjCoordinateField v) p X i := by
  simp [mirrorRailCoordinateField, twistedConjCoordinateField,
    cartesianTwistedConj, mirrorRailSwapJK]

theorem mirrorRailCoordinateField_involutive
    {Point Tangent : Type*}
    (v : Point → Tangent → Fin 4 → CartesianCoordinates)
    (p : Point) (X : Tangent) (i : Fin 4) :
    mirrorRailCoordinateField
        (mirrorRailCoordinateField v) p X i = v p X i := by
  exact mirrorRailSwapJK_involutive (v p X i)

theorem mirrorRail_diracQGTField_twistedConj
    {Point Tangent : Type*}
    (symmetric antisymmetric :
      Point → Tangent → Fin 4 → CartesianCoordinates)
    (p : Point) (X : Tangent) :
    diracQGTField
        (twistedConjCoordinateField
          (mirrorRailCoordinateField symmetric))
        (twistedConjCoordinateField
          (mirrorRailCoordinateField antisymmetric)) p X =
      qgtInternalConjugation
        InfoGeometry.Optics.QuaternionCl44QGTDiracCovariance.scalarPositiveComplexGammaUnit
        (diracQGTField
          (mirrorRailCoordinateField symmetric)
          (mirrorRailCoordinateField antisymmetric) p X) := by
  exact diracQGTField_twistedConj
    (mirrorRailCoordinateField symmetric)
    (mirrorRailCoordinateField antisymmetric) p X

end InfoGeometry.Optics.SplitOctonionMirrorQGTCoordinateTransport
