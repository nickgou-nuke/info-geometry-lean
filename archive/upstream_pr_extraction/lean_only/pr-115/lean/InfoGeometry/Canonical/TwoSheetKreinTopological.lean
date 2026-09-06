import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.Matrix
import InfoGeometry.Canonical.TwoSheetKreinAdjoint

noncomputable section

namespace InfoGeometry.Canonical.TwoSheetKreinTopological

open InfoGeometry.Canonical.TwoSheetOperatorCoordinates
open InfoGeometry.Canonical.TwoSheetKreinAdjoint

theorem continuous_kreinAdjoint :
    Continuous kreinAdjoint := by
  unfold kreinAdjoint
  exact (continuous_const.matrix_mul ContinuousStar.continuous_star).matrix_mul
    continuous_const

noncomputable def kreinAdjointHomeomorph : M6C ≃ₜ M6C where
  toFun := kreinAdjoint
  invFun := kreinAdjoint
  left_inv A := kreinAdjoint_involutive A
  right_inv A := kreinAdjoint_involutive A
  continuous_toFun := continuous_kreinAdjoint
  continuous_invFun := continuous_kreinAdjoint

theorem kreinAdjointHomeomorph_apply (A : M6C) :
    kreinAdjointHomeomorph A = kreinAdjoint A := rfl

theorem kreinAdjointHomeomorph_symm_apply (A : M6C) :
    kreinAdjointHomeomorph.symm A = kreinAdjoint A := rfl

end InfoGeometry.Canonical.TwoSheetKreinTopological
