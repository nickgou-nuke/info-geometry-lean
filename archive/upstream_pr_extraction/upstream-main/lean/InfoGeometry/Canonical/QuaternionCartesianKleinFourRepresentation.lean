import InfoGeometry.Canonical.KleinFourTagRootNormalization
import InfoGeometry.Canonical.QuaternionCoordinateBogoliubovEquiv
import InfoGeometry.Lie.SplitOctonionQuaternionParityOrientation

/-!
# Canonical quaternion-coordinate Klein-four bridge

This file is a compatibility bridge only.  The coordinate carrier, its
quadratic form, the mirror/rail involution, and the Clifford lift are owned
by the quaternion-coordinate and twisted-conjugation modules.  The common
Klein source is the normalized multiplicative wrapper of the canonical
additive `KleinFourTag.Tag` owner.
-/

noncomputable section

namespace InfoGeometry.Canonical.QuaternionCartesianKleinFourRepresentation

abbrev V4 := InfoGeometry.Canonical.KleinFourTagRootNormalization.V4
abbrev Carrier :=
  InfoGeometry.Canonical.QuaternionCoordinateBogoliubovEquiv.CartesianCoordinates

open InfoGeometry.Canonical.QuaternionCoordinateBogoliubovEquiv
open InfoGeometry.Lie.SplitOctonionQuaternionParityOrientation

noncomputable abbrev mirrorRailSwapJKLinearEquiv : Carrier ≃ₗ[ℝ] Carrier :=
  InfoGeometry.Canonical.QuaternionCoordinateBogoliubovEquiv.mirrorRailSwapJKLinearEquiv

theorem mirrorRailSwapJKLinearEquiv_apply (X : Carrier) :
    mirrorRailSwapJKLinearEquiv X = mirrorRailSwapJK X :=
  rfl

theorem mirrorRailSwapJKLinearEquiv_square (X : Carrier) :
    mirrorRailSwapJKLinearEquiv (mirrorRailSwapJKLinearEquiv X) = X := by
  exact mirrorRailSwapJK_involutive X

end InfoGeometry.Canonical.QuaternionCartesianKleinFourRepresentation
