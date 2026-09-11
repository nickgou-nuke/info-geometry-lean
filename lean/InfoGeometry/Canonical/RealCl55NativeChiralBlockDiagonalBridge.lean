import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealCl55NativeChiralSectorBridge

/-!
# Block-diagonal action in the native chiral decomposition

The native chiral-sector owner supplies the linear equivalence
`S ≃ₗ[ℝ] S₊ × S₋` and the two restricted actions.  This consumer records the
pointwise conjugation identity saying that the supplied integrated action is
block diagonal in those coordinates.  It does not identify the supplied
group with a particular Lie group and does not add a representation-theoretic
dimension or irreducibility claim.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealCl55NativeChiralBlockDiagonalBridge

open InfoGeometry.Canonical.RealCl55FiniteModuleEndBridge
open InfoGeometry.Canonical.RealCl55NativeIntegratedActionBridge
open InfoGeometry.Canonical.RealCl55NativeChiralSectorBridge
open InfoGeometry.Canonical.G2IntegratedKasparovEquivarianceBridge

variable {G : Type*} [Group G]

noncomputable def nativeChiralBlockAction
    (act : G2IntegratedAction G) (g : G) :
    (nativePlusSector × nativeMinusSector) →ₗ[ℝ]
      (nativePlusSector × nativeMinusSector) where
  toFun x :=
    (nativePlusSectorAction act g x.1,
      nativeMinusSectorAction act g x.2)
  map_add' x y := by
    apply Prod.ext <;> simp
  map_smul' c x := by
    apply Prod.ext <;> simp

theorem nativeChiralDecomposition_intertwines_action
    (act : G2IntegratedAction G) (g : G) (x : NativeSpinorCarrier) :
    nativeChiralDecomposition (nativeIntegratedAction act g x) =
      (nativePlusSectorAction act g (nativeChiralDecomposition x).1,
        nativeMinusSectorAction act g (nativeChiralDecomposition x).2) := by
  apply Prod.ext
  · apply Subtype.ext
    change nativeChiralProjectorPlus (nativeIntegratedAction act g x) =
      nativeIntegratedAction act g (nativeChiralProjectorPlus x)
    exact nativeIntegratedAction_preserves_projectorPlus act g x
  · apply Subtype.ext
    change nativeChiralProjectorMinus (nativeIntegratedAction act g x) =
      nativeIntegratedAction act g (nativeChiralProjectorMinus x)
    exact nativeIntegratedAction_preserves_projectorMinus act g x

theorem nativeChiralDecomposition_intertwines_action_linear
    (act : G2IntegratedAction G) (g : G) :
    nativeChiralDecomposition.toLinearMap.comp
        (nativeIntegratedAction act g).toLinearMap =
      (nativeChiralBlockAction act g).comp
        nativeChiralDecomposition.toLinearMap := by
  apply LinearMap.ext
  intro x
  exact nativeChiralDecomposition_intertwines_action act g x

end InfoGeometry.Canonical.RealCl55NativeChiralBlockDiagonalBridge
