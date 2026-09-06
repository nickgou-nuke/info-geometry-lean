import InfoGeometry.Geometry.Statistical.DualFlatCurvature
import InfoGeometry.Lie.CanonicalZornDerivation

/-!
# Weyl plus split-octonion derivation bridge

The scalar identity direction is kept in the ambient endomorphism algebra;
only the noncentral component is required to lie in the canonical derivation
Lie subalgebra.
-/

namespace InfoGeometry.Geometry.Statistical.WeylSplitOctonionDualFlatBridge

noncomputable section

open InfoGeometry.Geometry.Statistical
open InfoGeometry.Lie.CanonicalZornDerivation

abbrev CZ := InfoGeometry.Lie.CanonicalZornDerivation.CZ
abbrev EndCZ := Module.End ℝ CZ
abbrev Der := canonicalZornDerivations

structure WeylSplitOctonionDualFlatDatum extends
    DualFlatCurvatureDatum (T := CZ) where
  weyl : CZ → ℝ
  theta : CZ → Der
  cubicCorrection_eq : ∀ X,
    cubicCorrection nabla nablaStar X =
      weyl X • LinearMap.id + (theta X : EndCZ)

theorem scalar_add_derivation_commutator
    (a b : ℝ) (D E : Der) :
    operatorCommutator
        (a • LinearMap.id + (D : EndCZ))
        (b • LinearMap.id + (E : EndCZ)) =
      ((⁅D, E⁆ : Der) : EndCZ) := by
  calc
    operatorCommutator
        (a • LinearMap.id + (D : EndCZ))
        (b • LinearMap.id + (E : EndCZ)) =
        operatorCommutator (D : EndCZ) (E : EndCZ) := by
          exact operatorCommutator_add_smul_id a b (D : EndCZ) (E : EndCZ)
    _ = ((⁅D, E⁆ : Der) : EndCZ) := by
      rfl

theorem curvature_eq_neg_derivation_bracket
    (C : WeylSplitOctonionDualFlatDatum) (X Y : CZ) :
    C.R0 X Y = -((⁅C.theta X, C.theta Y⁆ : Der) : EndCZ) := by
  have h := C.curvature_sum X Y
  rw [C.cubicCorrection_eq X, C.cubicCorrection_eq Y] at h
  rw [scalar_add_derivation_commutator] at h
  rw [C.flat X Y, C.flatStar X Y] at h
  have hzero : C.R0 X Y +
      ((⁅C.theta X, C.theta Y⁆ : Der) : EndCZ) = 0 := by
    simpa using h
  exact eq_neg_of_add_eq_zero_left hzero

theorem curvature_invariant_under_central_shift
    (C : WeylSplitOctonionDualFlatDatum)
    (δ : CZ → ℝ) (X Y : CZ) :
    operatorCommutator
        ((C.weyl X + δ X) • LinearMap.id + (C.theta X : EndCZ))
        ((C.weyl Y + δ Y) • LinearMap.id + (C.theta Y : EndCZ)) =
      operatorCommutator
        (C.weyl X • LinearMap.id + (C.theta X : EndCZ))
        (C.weyl Y • LinearMap.id + (C.theta Y : EndCZ)) := by
  rw [scalar_add_derivation_commutator, scalar_add_derivation_commutator]

end
end InfoGeometry.Geometry.Statistical.WeylSplitOctonionDualFlatBridge
