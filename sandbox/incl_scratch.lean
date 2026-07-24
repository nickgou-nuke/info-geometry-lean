import InfoGeometry.Lie.SplitOctonionNonmultiplicativity
import InfoGeometry.Physics.SplitCliffordAlgebras
import InfoGeometry.Canonical.WittenMoebiusChiralParityIndex
import InfoGeometry.Clifford.Cl55SpinorChirality
import InfoGeometry.Canonical.ZornSpinor
import InfoGeometry.Canonical.ZornVectorMatrixExplicit
import Mathlib.LinearAlgebra.BilinearMap

noncomputable section
namespace InfoGeometry.Lie.Pin55KreinConformalBridge

open SplitClifford
open InfoGeometry.Canonical
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.CliffordTower
open InfoGeometry.Lie.SplitOctonionNonmultiplicativity
open InfoGeometry.Lie.SplitOctonionImaginaryAction
open InfoGeometry.Clifford.SplitCl44CausalEnvelope
open InfoGeometry.Algebra.Zorn
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

structure Pin55KreinConformalPackage where
  K : Type
  [addCommGroup : AddCommGroup K]
  [moduleReal : Module ℝ K]
  [finiteDimensional : FiniteDimensional ℝ K]
  B : LinearMap.BilinForm ℝ K
  J : K →ₗ[ℝ] K
  χ : K →ₗ[ℝ] K
  ε : K →ₗ[ℝ] K
  ρ : Clnn 5 →ₐ[ℝ] Module.End ℝ K
  J_sq : J ∘ₗ J = LinearMap.id
  χ_sq : χ ∘ₗ χ = LinearMap.id
  ε_sq : ε ∘ₗ ε = LinearMap.id
  ρ_preserves_B : ∀ (v : SplitClifford.SplitSpace 5),
    ∀ (x y : K), B (ρ (CliffordAlgebra.ι (SplitClifford.Qsplit 5) v) x) (ρ (CliffordAlgebra.ι (SplitClifford.Qsplit 5) v) y) = B x y
  anomaly_index_zero : LinearMap.trace ℝ K (χ ∘ₗ ε) = 0

attribute [instance] Pin55KreinConformalPackage.addCommGroup
attribute [instance] Pin55KreinConformalPackage.moduleReal
attribute [instance] Pin55KreinConformalPackage.finiteDimensional

theorem exists_pin55_krein_conformal_package :
    ∃ (pkg : Pin55KreinConformalPackage),
      ∃ (e : CanonicalZorn ≃ₗ[ℝ] SplitClifford.SplitSpace 4),
        ∃ (ι_K : SplitClifford.SplitSpace 4 →ₗ[ℝ] pkg.K),
          ∀ (X : Imaginary),
            (pkg.ρ (embedPrev 4 (CliffordAlgebra.ι (SplitClifford.Qsplit 4) (e X.1)))) ∘ₗ (ι_K ∘ₗ e) = (ι_K ∘ₗ e) ∘ₗ (imaginaryLeftMul X) := by
  sorry

end InfoGeometry.Lie.Pin55KreinConformalBridge
