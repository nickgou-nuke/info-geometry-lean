/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Exceptional.G2ArtinWeylBridge
import InfoGeometry.Exceptional.G2ThreePlaneWeightBridge

/-!
# Artin G₂ longest-element readback on the three-plane labels

This owner connects the already-proved Artin coordinate action to the finite
upper/lower weight labels.  It makes no claim about a Lie-module structure or
about a physical interpretation of the labels.
-/

namespace InfoGeometry.Exceptional.G2ArtinThreePlaneIntertwiner

open InfoGeometry.Algebra.Zorn.G2CanonicalWeylWords
open InfoGeometry.Algebra.Zorn.G2CoordinateSignedBridge
open InfoGeometry.Algebra.Zorn.G2CoordinateWeylAction
open InfoGeometry.Algebra.Zorn.G2CoordinateWordActionBridge
open InfoGeometry.Algebra.Zorn.G2LongestElementBridge
open InfoGeometry.Algebra.Zorn.G2ReducedWords
open InfoGeometry.Exceptional.G2ArtinPresentation
open InfoGeometry.Exceptional.G2ArtinWeylBridge
open InfoGeometry.Exceptional.G2ThreePlaneWeightBridge

theorem artin_garside_upperWeightLabel (i : Fin 3) :
    coordinateAction garside (signedRootCoordinate (upperWeightLabel i)) =
      signedRootCoordinate (lowerWeightLabel i) := by
  rw [artinToWeyl_garside]
  rw [dihedralToPerm, coordinateWordAction_apply_signed,
    g2LongestNF_word_canonical]
  exact congrArg signedRootCoordinate (canonical_w0_upperWeightLabel i)

theorem artin_garside_lowerWeightLabel (i : Fin 3) :
    coordinateAction garside (signedRootCoordinate (lowerWeightLabel i)) =
      signedRootCoordinate (upperWeightLabel i) := by
  rw [artinToWeyl_garside]
  rw [dihedralToPerm, coordinateWordAction_apply_signed,
    g2LongestNF_word_canonical]
  exact congrArg signedRootCoordinate (canonical_w0_lowerWeightLabel i)

end InfoGeometry.Exceptional.G2ArtinThreePlaneIntertwiner
