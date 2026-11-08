import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.RealCl55NativeConcreteEmbeddingBridge

/-!
# Native image-level Hestenes commutation

The concrete phase and Dirac/Laplacian operators already intertwine on the
embedded doubled carrier pointwise.  This consumer upgrades those statements
to equalities of endomorphisms of the native image submodule.  It does not
identify the image with the full 32-dimensional Cl(5,5) carrier.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealCl55ConcreteHestenesImageCommutationBridge

open InfoGeometry.Canonical.RealCl55NativeConcreteEmbeddingBridge
open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge

theorem nativeConcretePhaseOnImage_commutes_dirac
    (v : V3) (φ : Module.Dual ℝ V3) :
    nativeConcretePhaseOnImage.comp (nativeConcreteDiracOnImage v φ) =
      (nativeConcreteDiracOnImage v φ).comp nativeConcretePhaseOnImage := by
  apply LinearMap.ext
  intro z
  rcases z.2 with ⟨x, hx⟩
  apply Subtype.ext
  change nativeConcretePhaseAction
      (nativeConcreteDiracAction v φ z.1) =
    nativeConcreteDiracAction v φ (nativeConcretePhaseAction z.1)
  rw [← hx]
  exact nativeConcretePhaseAction_intertwines_dirac v φ x

theorem nativeConcretePhaseOnImage_commutes_laplacian
    (v : V3) (φ : Module.Dual ℝ V3) :
    nativeConcretePhaseOnImage.comp (nativeConcreteLaplacianOnImage v φ) =
      (nativeConcreteLaplacianOnImage v φ).comp nativeConcretePhaseOnImage := by
  apply LinearMap.ext
  intro z
  rcases z.2 with ⟨x, hx⟩
  apply Subtype.ext
  change nativeConcretePhaseAction
      (nativeConcreteLaplacianAction v φ z.1) =
    nativeConcreteLaplacianAction v φ (nativeConcretePhaseAction z.1)
  rw [← hx]
  exact nativeConcretePhaseAction_intertwines_laplacian v φ x

end InfoGeometry.Canonical.RealCl55ConcreteHestenesImageCommutationBridge
