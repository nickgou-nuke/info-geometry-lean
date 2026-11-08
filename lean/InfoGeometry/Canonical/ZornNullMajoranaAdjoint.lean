/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ZornNullSupportAdjoint

/-! Majorana combinations of the null ket-bra pair, not the color-unit
left-regular operators. Both real combinations are split-polar self-adjoint;
the product commutator is split-polar skew-adjoint. -/
noncomputable section
namespace InfoGeometry.Canonical.ZornNullMajoranaAdjoint
open _root_.InfoGeometry.Canonical.ZornVectorMatrixExplicit
open ZornPolarizationMetricBridge ZornPolarKetBra ZornNullSupportAdjoint
open ReflexiveNilpotentFlows GrassmannianBundleCyclotomicOrientability

theorem nullSum_self_adjoint (X Y : ZornCoord) :
    LinearMap.IsAdjointPair polarForm polarForm
      (ketBra X X + ketBra Y Y : Module.End ℝ ZornCoord)
      (ketBra X X + ketBra Y Y : Module.End ℝ ZornCoord) := by
  intro U V
  simp only [LinearMap.add_apply, map_add]
  rw [ketBra_adjoint X X U V, ketBra_adjoint Y Y U V]

theorem nullDifference_self_adjoint (X Y : ZornCoord) :
    LinearMap.IsAdjointPair polarForm polarForm
      (ketBra X X - ketBra Y Y : Module.End ℝ ZornCoord)
      (ketBra X X - ketBra Y Y : Module.End ℝ ZornCoord) := by
  intro U V
  simp only [LinearMap.sub_apply, map_sub]
  rw [ketBra_adjoint X X U V, ketBra_adjoint Y Y U V]

theorem nullCommutator_skew_adjoint (X Y : ZornCoord) :
    LinearMap.IsAdjointPair polarForm polarForm
      (ketBra X X * ketBra Y Y - ketBra Y Y * ketBra X X : Module.End ℝ ZornCoord)
      (-(ketBra X X * ketBra Y Y - ketBra Y Y * ketBra X X) : Module.End ℝ ZornCoord) := by
  intro U V
  simp only [LinearMap.sub_apply, LinearMap.neg_apply, map_sub, map_neg]
  rw [nullProducts_adjoint X Y U V, nullProducts_adjoint Y X U V]
  abel

theorem nullDifference_sq (X Y : ZornCoord)
    (hX : polarPair X X = 0) (hY : polarPair Y Y = 0) :
    (ketBra X X - ketBra Y Y) * (ketBra X X - ketBra Y Y) =
      -support (ketBra X X) (ketBra Y Y) :=
  cyclotomic4Op_sq (ketBra_sq_zero X X hX) (ketBra_sq_zero Y Y hY)

end InfoGeometry.Canonical.ZornNullMajoranaAdjoint
