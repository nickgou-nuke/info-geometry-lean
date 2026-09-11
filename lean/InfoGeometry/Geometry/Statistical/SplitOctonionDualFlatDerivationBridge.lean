import InfoGeometry.Geometry.Statistical.DualFlatCurvature
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Lie.CanonicalZornDerivation
import InfoGeometry.Lie.CanonicalZornDerivationCentralKernel
import InfoGeometry.Lie.SplitOctonionStandardDerivation

/-!
# Dual-flat curvature through split-octonion derivations

This file supplies the concrete downstream bridge from the algebraic
dual-flat curvature packet to the native canonical split-octonion derivation
Lie algebra.  The statistical correction is identified with a derivation
operator; it is not identified with the octonion associator.
-/

namespace InfoGeometry.Geometry.Statistical.SplitOctonionDualFlatDerivationBridge

noncomputable section

open InfoGeometry.Geometry.Statistical
open InfoGeometry.Lie.CanonicalZornDerivation

structure SplitOctonionDualFlatDatum extends
    DualFlatCurvatureDatum
      (T := InfoGeometry.Lie.CanonicalZornDerivation.CZ) where
  theta : InfoGeometry.Lie.CanonicalZornDerivation.CZ →
    canonicalZornDerivations
  cubicCorrection_eq : ∀ X : InfoGeometry.Lie.CanonicalZornDerivation.CZ,
    cubicCorrection nabla nablaStar X =
      (theta X : Module.End ℝ InfoGeometry.Lie.CanonicalZornDerivation.CZ)

theorem differenceOperator_eq_neg_two_derivation
    (C : SplitOctonionDualFlatDatum)
    (X : InfoGeometry.Lie.CanonicalZornDerivation.CZ) :
    differenceOperator C.nabla C.nablaStar X =
      (-2 : ℝ) •
        (C.theta X : Module.End ℝ InfoGeometry.Lie.CanonicalZornDerivation.CZ) := by
  rw [differenceOperator_eq_neg_two_cubicCorrection,
    C.cubicCorrection_eq]

theorem derivation_bracket_coe
    (D E : canonicalZornDerivations) :
    ((⁅D, E⁆ : canonicalZornDerivations) :
        Module.End ℝ InfoGeometry.Lie.CanonicalZornDerivation.CZ) =
      operatorCommutator
        (D : Module.End ℝ InfoGeometry.Lie.CanonicalZornDerivation.CZ)
        (E : Module.End ℝ InfoGeometry.Lie.CanonicalZornDerivation.CZ) := by
  rfl

noncomputable def derivationRepresentation :
    canonicalZornDerivations →ₗ[ℝ]
      Module.End ℝ InfoGeometry.Lie.CanonicalZornDerivation.CZ where
  toFun D := D.1
  map_add' D E := rfl
  map_smul' r D := rfl

@[simp] theorem derivationRepresentation_apply
    (D : canonicalZornDerivations) :
    derivationRepresentation D =
      (D : Module.End ℝ InfoGeometry.Lie.CanonicalZornDerivation.CZ) := rfl

theorem curvature_eq_neg_derivation_commutator
    (C : SplitOctonionDualFlatDatum)
    (X Y : InfoGeometry.Lie.CanonicalZornDerivation.CZ) :
    C.R0 X Y =
      -operatorCommutator
        (C.theta X : Module.End ℝ InfoGeometry.Lie.CanonicalZornDerivation.CZ)
        (C.theta Y : Module.End ℝ InfoGeometry.Lie.CanonicalZornDerivation.CZ) := by
  rw [InfoGeometry.Geometry.Statistical.represented_curvature_eq_neg_representation_bracket
    C.toDualFlatCurvatureDatum C.theta derivationRepresentation]
  · rw [derivationRepresentation_apply, derivation_bracket_coe]
  · intro X
    exact C.cubicCorrection_eq X
  · intro D E
    exact derivation_bracket_coe D E

theorem curvature_eq_neg_derivation_bracket
    (C : SplitOctonionDualFlatDatum)
    (X Y : InfoGeometry.Lie.CanonicalZornDerivation.CZ) :
    C.R0 X Y =
      -((⁅C.theta X, C.theta Y⁆ : canonicalZornDerivations) :
        Module.End ℝ InfoGeometry.Lie.CanonicalZornDerivation.CZ) := by
  rw [curvature_eq_neg_derivation_commutator C X Y,
    derivation_bracket_coe]

noncomputable def derivationCurvature
    (C : SplitOctonionDualFlatDatum)
    (X Y : InfoGeometry.Lie.CanonicalZornDerivation.CZ) :
    canonicalZornDerivations :=
  -⁅C.theta X, C.theta Y⁆

@[simp] theorem derivationCurvature_coe
    (C : SplitOctonionDualFlatDatum)
    (X Y : InfoGeometry.Lie.CanonicalZornDerivation.CZ) :
    (derivationCurvature C X Y :
        Module.End ℝ InfoGeometry.Lie.CanonicalZornDerivation.CZ) =
      C.R0 X Y := by
  rw [derivationCurvature]
  rw [curvature_eq_neg_derivation_bracket C X Y]
  rfl

theorem curvature_mem_derivationRepresentation_range
    (C : SplitOctonionDualFlatDatum)
    (X Y : InfoGeometry.Lie.CanonicalZornDerivation.CZ) :
    C.R0 X Y ∈ LinearMap.range derivationRepresentation := by
  refine ⟨derivationCurvature C X Y, ?_⟩
  exact derivationCurvature_coe C X Y

theorem curvature_apply_one
    (C : SplitOctonionDualFlatDatum)
    (X Y : InfoGeometry.Lie.CanonicalZornDerivation.CZ) :
    C.R0 X Y (1 : InfoGeometry.Lie.CanonicalZornDerivation.CZ) = 0 := by
  rw [curvature_eq_neg_derivation_bracket C X Y]
  simp [InfoGeometry.Lie.CanonicalZornDerivation.derivation_apply_one]

theorem curvature_apply_scalar
    (C : SplitOctonionDualFlatDatum)
    (X Y : InfoGeometry.Lie.CanonicalZornDerivation.CZ) (c : ℝ) :
    C.R0 X Y (c • (1 : InfoGeometry.Lie.CanonicalZornDerivation.CZ)) = 0 := by
  rw [map_smul, curvature_apply_one, smul_zero]

end
end InfoGeometry.Geometry.Statistical.SplitOctonionDualFlatDerivationBridge
