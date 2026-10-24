/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ZornNullPeirceWeyl

/-! The split-polar adjoint exchanges the two null-pair support projections.
Their sum is self-adjoint, but the individual projections need not be.
This is not a positive Hilbert adjoint or a Moore–Penrose identification. -/
noncomputable section
namespace InfoGeometry.Canonical.ZornNullSupportAdjoint
open _root_.InfoGeometry.Canonical.ZornVectorMatrixExplicit
open ZornPolarizationMetricBridge ZornPolarKetBra ZornPolarOperatorAdjoint
open ReflexiveNilpotentFlows

theorem nullProducts_adjoint (X Y : ZornCoord) :
    LinearMap.IsAdjointPair polarForm polarForm
      (ketBra X X * ketBra Y Y : Module.End ℝ ZornCoord)
      (ketBra Y Y * ketBra X X : Module.End ℝ ZornCoord) := by
  intro U V
  exact (ketBra_adjoint X X (ketBra Y Y U) V).trans
    (ketBra_adjoint Y Y U (ketBra X X V))

theorem nullSupport_self_adjoint (X Y : ZornCoord) :
    LinearMap.IsAdjointPair polarForm polarForm
      (support (ketBra X X) (ketBra Y Y) : Module.End ℝ ZornCoord) (support (ketBra X X) (ketBra Y Y) : Module.End ℝ ZornCoord) := by
  intro U V
  simp only [support, LinearMap.add_apply, map_add]
  rw [nullProducts_adjoint X Y U V, nullProducts_adjoint Y X U V]
  exact add_comm _ _

theorem nullProducts_ne (X Y : ZornCoord)
    (hX : polarPair X X = 0) (h : polarPair X Y = 1) :
    ketBra X X * ketBra Y Y ≠ ketBra Y Y * ketBra X X := by
  intro he
  have hv := congrArg (fun T : Module.End ℝ ZornCoord => T X) he
  simp only [ketBra_mul, polarPair_symm Y X, h, one_smul] at hv
  change polarPair Y X • X = polarPair X X • Y at hv
  rw [polarPair_symm Y X, h, hX, one_smul, zero_smul] at hv
  subst X
  norm_num [polarPair, zornA, zornB, zornX, zornY, dot3] at h

theorem nullProduct_not_self_adjoint (X Y : ZornCoord)
    (hX : polarPair X X = 0) (h : polarPair X Y = 1) :
    ¬ LinearMap.IsAdjointPair polarForm polarForm
      (ketBra X X * ketBra Y Y : Module.End ℝ ZornCoord)
      (ketBra X X * ketBra Y Y : Module.End ℝ ZornCoord) := by
  intro ha
  exact nullProducts_ne X Y hX h
    (polar_adjoint_unique _ _ _ ha (nullProducts_adjoint X Y))

end InfoGeometry.Canonical.ZornNullSupportAdjoint
