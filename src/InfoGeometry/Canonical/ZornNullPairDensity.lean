/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ZornNullPeirceWeyl
import InfoGeometry.Canonical.PeirceWeightedTrace

/-! Actual endomorphism trace and proper-support weights for split-polar null
pairs. No positivity, normalization, or analytic KMS condition is asserted. -/
noncomputable section
namespace InfoGeometry.Canonical.ZornNullPairDensity
open _root_.InfoGeometry.Canonical.ZornVectorMatrixExplicit
open ZornPolarizationMetricBridge ZornPolarKetBra ZornNullPeirceWeyl PeirceWeightedTrace
open InfoGeometry.NCG InfoGeometry.OperatorAlgebra.TracialCARDensity

def zornEndTrace : TracialFunctional ℝ (Module.End ℝ ZornCoord) where
  toLinearMap := LinearMap.trace ℝ ZornCoord
  cyclic' := LinearMap.trace_mul_comm ℝ

theorem nullPair_weight_trace (X Y : ZornCoord) (h : polarPair X Y = 1) (a b : ℝ) :
    zornEndTrace (supportWeight a b (ketBra X X) (ketBra Y Y)) = a + b := by
  change LinearMap.trace ℝ ZornCoord _ = _
  simp only [supportWeight, ketBra_mul, polarPair_symm Y X, h, one_smul,
    map_add, map_smul, ketBra_trace, smul_eq_mul, mul_one]

theorem nullPair_weighted_trace_d (X Y : ZornCoord)
    (hX : polarPair X X = 0) (hY : polarPair Y Y = 0) (h : polarPair X Y = 1)
    (a b : ℝ) (T : Module.End ℝ ZornCoord) :
    a * weighted zornEndTrace (supportWeight a b (ketBra X X) (ketBra Y Y))
      (ketBra X X * T) =
    b * weighted zornEndTrace (supportWeight a b (ketBra X X) (ketBra Y Y))
      (T * ketBra X X) :=
  (weighted_trace_boundary zornEndTrace (ketBra_sq_zero X X hX)
    (ketBra_sq_zero Y Y hY) (nullPair_reflexive X Y h)
    (nullPair_reflexive Y X (by rwa [polarPair_symm])) a b T).1

theorem nullPair_weighted_trace_B (X Y : ZornCoord)
    (hX : polarPair X X = 0) (hY : polarPair Y Y = 0) (h : polarPair X Y = 1)
    (a b : ℝ) (T : Module.End ℝ ZornCoord) :
    b * weighted zornEndTrace (supportWeight a b (ketBra X X) (ketBra Y Y))
      (ketBra Y Y * T) =
    a * weighted zornEndTrace (supportWeight a b (ketBra X X) (ketBra Y Y))
      (T * ketBra Y Y) :=
  (weighted_trace_boundary zornEndTrace (ketBra_sq_zero X X hX)
    (ketBra_sq_zero Y Y hY) (nullPair_reflexive X Y h)
    (nullPair_reflexive Y X (by rwa [polarPair_symm])) a b T).2

end InfoGeometry.Canonical.ZornNullPairDensity
