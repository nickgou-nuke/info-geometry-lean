/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ZornNullPairDensity
import InfoGeometry.Canonical.PeirceWeylDensityTransport

/-! Joint transport of the native Zorn weight and ambient observable by the
completed null-pair Weyl unit. This is an algebraic trace identity. -/
noncomputable section
namespace InfoGeometry.Canonical.ZornNullWeylDensity
open _root_.InfoGeometry.Canonical.ZornVectorMatrixExplicit
open ZornPolarizationMetricBridge ZornPolarKetBra ZornNullPeirceWeyl
open ZornNullPairDensity PeirceWeightedTrace PeirceWeylDensityTransport
open InfoGeometry.OperatorAlgebra.TracialCARDensity

theorem nullPair_weyl_weight_covariance (X Y : ZornCoord)
    (hX : polarPair X X = 0) (hY : polarPair Y Y = 0) (h : polarPair X Y = 1)
    (a b : ℝ) (T : Module.End ℝ ZornCoord) :
    weighted zornEndTrace (supportWeight b a (ketBra X X) (ketBra Y Y))
      ((nullPairWeylUnit X Y hX hY h : Module.End ℝ ZornCoord) * T *
        (↑((nullPairWeylUnit X Y hX hY h)⁻¹) : Module.End ℝ ZornCoord)) =
      weighted zornEndTrace (supportWeight a b (ketBra X X) (ketBra Y Y)) T :=
  weyl_weight_joint_covariance (ketBra_sq_zero X X hX) (ketBra_sq_zero Y Y hY)
    (nullPair_reflexive X Y h) (nullPair_reflexive Y X (by rwa [polarPair_symm]))
    zornEndTrace a b T

end InfoGeometry.Canonical.ZornNullWeylDensity
