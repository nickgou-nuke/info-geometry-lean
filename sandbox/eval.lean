import Mathlib
import InfoGeometry.Lie.Pin55KreinConformalBridge

open InfoGeometry.Lie.Pin55KreinConformalBridge
open InfoGeometry.Lie.SplitOctonionImaginaryAction
open InfoGeometry.Algebra.Zorn
open InfoGeometry.Canonical.ZornMatrix
open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Clifford

def Pin55FiniteCarrierCompatibility : Prop :=
  ∀ X : Imaginary,
    P_K_concrete ∘ₗ
        (ρ_spinor
          (SpinorRep.incl_Cl_split 4
            (CliffordAlgebra.ι (SpinorRep.SplitQuad 4)
              (InfoGeometry.Lie.SplitOctonionNonmultiplicativity.e X.1)))) ∘ₗ
      ι_K_concrete =
    InfoGeometry.Lie.SplitOctonionNonmultiplicativity.e ∘ₗ
      imaginaryLeftMul X ∘ₗ
      InfoGeometry.Lie.SplitOctonionNonmultiplicativity.e.symm

theorem exists_pin55_krein_conformal_package_proved
    (hcompat : Pin55FiniteCarrierCompatibility) :
    ∃ (pkg : Pin55KreinConformalPackage),
      ∃ (e : CanonicalZorn ≃ₗ[ℝ] InfoGeometry.CliffordTower.SplitSpace 4),
        ∃ (ι_K : InfoGeometry.CliffordTower.SplitSpace 4 →ₗ[ℝ] pkg.K),
          ∃ (P_K : pkg.K →ₗ[ℝ] InfoGeometry.CliffordTower.SplitSpace 4),
            ∀ (X : Imaginary),
              P_K ∘ₗ (pkg.ρ (SpinorRep.incl_Cl_split 4 (CliffordAlgebra.ι (SpinorRep.SplitQuad 4) (e X.1)))) ∘ₗ ι_K = e ∘ₗ imaginaryLeftMul X ∘ₗ e.symm := by
  use pkg_concrete, InfoGeometry.Lie.SplitOctonionNonmultiplicativity.e, ι_K_concrete, P_K_concrete
  exact hcompat
