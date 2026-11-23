/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Canonical.SplitOctonionCayleyDickson
import InfoGeometry.Canonical.SplitOctonionLeftMultiplicationCAR
import InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner
import InfoGeometry.Clifford.RealSpacetimeQuaternion
import InfoGeometry.Lie.SplitOctonionDaviauPeirce13Bridge

set_option autoImplicit false

namespace InfoGeometry.Lie.SplitOctonionE2ETier1FeatureTest

open InfoGeometry.Canonical.SplitOctonionCayleyDickson
open InfoGeometry.Canonical.SplitOctonionLeftMultiplicationCAR
open InfoGeometry.Canonical.SplitOctonionClifford33Soldering
open InfoGeometry.Canonical.SplitOctonionParaKahlerNullCone
open InfoGeometry.Canonical.ZornSplitOctonionFin8Bridge
open InfoGeometry.Canonical.SplitOctonionCARRightRegularBridge
open InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner
open InfoGeometry.Lie.SplitOctonionEllPolarization
open InfoGeometry.Lie.SplitOctonionDaviauPeirce13Bridge

 theorem cayley_dickson_zorn_unit :
    splitOctCDEquivZornMatrix oneCD = (1 : InfoGeometry.Canonical.ZornMatrix ℝ) :=
  splitOctCDEquivZornMatrix_one

theorem left_multiplication_square (x : SplitOctCD) :
    leftMulMat x * leftMulMat x = leftMulMat (x * x) :=
  leftMulMat_sq x

theorem seven_operator_anticommutator {a b : Fin 7} (h : a ≠ b) :
    sevenAnticommOps a * sevenAnticommOps b +
        sevenAnticommOps b * sevenAnticommOps a = 0 :=
  sevenAnticommOps_anticomm h

theorem zorn_matrix_anticommutator
    (x y : InfoGeometry.Canonical.SplitOctonionLeftMultiplicationCAR.Oct) :
    zornLeftActMatrix x * zornLeftActMatrix y +
        zornLeftActMatrix y * zornLeftActMatrix x =
      zornLeftActMatrix (zornAdd (zornMul x y) (zornMul y x)) :=
  zornLeftActMatrix_anticommutator x y

theorem right_regular_root_car (i : Fin 3) :
    rightRegular (rootMinus i) * rightRegular (rootPlus i) +
        rightRegular (rootPlus i) * rightRegular (rootMinus i) = 1 :=
  rightRegular_root_CAR i

theorem fock_creation_intertwiner (i : Fin 3) :
    rightRegular (InfoGeometry.Lie.SplitOctonionEllPolarization.rootPlus i) ∘ₗ
        (fockBdGEquiv : Exterior3 →ₗ[ℝ]
          InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner.CZ) =
      (fockBdGEquiv : Exterior3 →ₗ[ℝ]
          InfoGeometry.Canonical.SplitOctonionExteriorRightRegularBdGIntertwiner.CZ) ∘ₗ
        InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge.exteriorWedge3
          (InfoGeometry.Canonical.SplitOctonionCARBdGRegularLift.modeVector i) :=
  fockBdGEquiv_creation_intertwines i

theorem spacetime_gamma_noncommutative :
    HestenesCl14.gamma 1 * HestenesCl14.gamma 2 ≠
      HestenesCl14.gamma 2 * HestenesCl14.gamma 1 :=
  InfoGeometry.Clifford.RealSpacetimeQuaternion.gamma_one_two_ne

theorem daviau_left_embedding_injective :
    Function.Injective ⇑cl33ToCl44EvenLeft :=
  cl33_embeds_into_cl44EvenLeft

end InfoGeometry.Lie.SplitOctonionE2ETier1FeatureTest
