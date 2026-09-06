import Mathlib.Analysis.Normed.Module.FiniteDimension
import InfoGeometry.Canonical.TwoSheetKreinTopological

noncomputable section

namespace InfoGeometry.Canonical.TwoSheetKreinRealLinear

open InfoGeometry.Canonical.TwoSheetOperatorCoordinates
open InfoGeometry.Canonical.TwoSheetKreinAdjoint
open InfoGeometry.Canonical.TwoSheetKreinTopological

def kreinAdjointRealLinear : M6C →ₗ[ℝ] M6C where
  toFun := kreinAdjoint
  map_add' A B := by
    simp [kreinAdjoint, star_add, add_mul, mul_add]
  map_smul' c A := by
    change kreinSymmetry * star (c • A) * kreinSymmetry = c • kreinAdjoint A
    simp [star_smul, star_trivial, smul_mul_assoc, mul_smul_comm]
    rfl

theorem kreinAdjointRealLinear_apply (A : M6C) :
    kreinAdjointRealLinear A = kreinAdjoint A := rfl

def kreinAdjointRealLinearEquiv : M6C ≃ₗ[ℝ] M6C where
  toLinearMap := kreinAdjointRealLinear
  invFun := kreinAdjoint
  left_inv A := kreinAdjoint_involutive A
  right_inv A := kreinAdjoint_involutive A

theorem kreinAdjointRealLinearEquiv_apply (A : M6C) :
    kreinAdjointRealLinearEquiv A = kreinAdjoint A := rfl

def kreinAdjointContinuousLinearEquiv : M6C ≃L[ℝ] M6C :=
  ContinuousLinearEquiv.mk kreinAdjointRealLinearEquiv
    (by
      exact continuous_kreinAdjoint)
    (by
      exact continuous_kreinAdjoint)

theorem kreinAdjointContinuousLinearEquiv_apply (A : M6C) :
    kreinAdjointContinuousLinearEquiv A = kreinAdjoint A := by
  exact kreinAdjointRealLinearEquiv_apply A

end InfoGeometry.Canonical.TwoSheetKreinRealLinear
