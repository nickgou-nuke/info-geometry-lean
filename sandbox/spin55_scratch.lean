import InfoGeometry.Lie.SplitOctonionNonmultiplicativity
import InfoGeometry.Physics.SplitCliffordAlgebras
import InfoGeometry.Canonical.WittenMoebiusChiralParityIndex
import InfoGeometry.Clifford.Cl55SpinorChirality
import InfoGeometry.Canonical.ZornSpinor
import InfoGeometry.Canonical.ZornVectorMatrixExplicit
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Trace
import InfoGeometry.Clifford.SpinorRep
import InfoGeometry.Clifford.CliffordInclusionInjective

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
open InfoGeometry.Clifford.SpinorRep
open InfoGeometry.Clifford

structure Pin55KreinConformalPackage where
  K : Type
  [addCommGroup : AddCommGroup K]
  [moduleReal : Module ℝ K]
  [finiteDimensional : FiniteDimensional ℝ K]
  B : LinearMap.BilinForm ℝ K
  J : K →ₗ[ℝ] K
  χ : K →ₗ[ℝ] K
  ε : K →ₗ[ℝ] K
  ρ : SpinorRep.Cl_split 5 →ₐ[ℝ] Module.End ℝ K
  J_sq : J ∘ₗ J = LinearMap.id
  χ_sq : χ ∘ₗ χ = LinearMap.id
  ε_sq : ε ∘ₗ ε = LinearMap.id
  ρ_preserves_B : ∀ (v : InfoGeometry.CliffordTower.SplitSpace 5),
    ∀ (x y : K), B (ρ (CliffordAlgebra.ι (SplitQuad 5) v) x) (ρ (CliffordAlgebra.ι (SplitQuad 5) v) y) = B x y
  anomaly_index_zero : LinearMap.trace ℝ K (χ ∘ₗ ε) = 0

attribute [instance] Pin55KreinConformalPackage.addCommGroup
attribute [instance] Pin55KreinConformalPackage.moduleReal
attribute [instance] Pin55KreinConformalPackage.finiteDimensional

def J_concrete : (Fin 32 → ℝ) →ₗ[ℝ] (Fin 32 → ℝ) :=
  { toFun := fun v i => if i.val < 16 then v i else -v i
    map_add' := fun x y => by ext i; dsimp; split_ifs <;> ring
    map_smul' := fun c x => by ext i; dsimp; split_ifs <;> ring }

def χ_concrete : (Fin 32 → ℝ) →ₗ[ℝ] (Fin 32 → ℝ) :=
  { toFun := fun v i => if i.val < 16 then -v i else v i
    map_add' := fun x y => by ext i; dsimp; split_ifs <;> ring
    map_smul' := fun c x => by ext i; dsimp; split_ifs <;> ring }

def ε_concrete : (Fin 32 → ℝ) →ₗ[ℝ] (Fin 32 → ℝ) :=
  { toFun := fun v i => if i.val % 2 = 0 then v i else -v i
    map_add' := fun x y => by ext i; dsimp; split_ifs <;> ring
    map_smul' := fun c x => by ext i; dsimp; split_ifs <;> ring }

theorem J_concrete_sq : J_concrete ∘ₗ J_concrete = LinearMap.id := by
  refine LinearMap.ext (fun v => ?_)
  ext i
  dsimp [J_concrete]
  split_ifs <;> ring

theorem χ_concrete_sq : χ_concrete ∘ₗ χ_concrete = LinearMap.id := by
  refine LinearMap.ext (fun v => ?_)
  ext i
  dsimp [χ_concrete]
  split_ifs <;> ring

theorem ε_concrete_sq : ε_concrete ∘ₗ ε_concrete = LinearMap.id := by
  refine LinearMap.ext (fun v => ?_)
  ext i
  dsimp [ε_concrete]
  split_ifs <;> ring

def B_concrete : LinearMap.BilinForm ℝ (Fin 32 → ℝ) :=
  { toFun := fun x =>
      { toFun := fun y => x 0 * y 0 - x 1 * y 1
        map_add' := fun y1 y2 => by dsimp; ring
        map_smul' := fun c y => by dsimp; ring }
    map_add' := fun x1 x2 => by
      refine LinearMap.ext (fun y => ?_)
      dsimp
      ring
    map_smul' := fun c x => by
      refine LinearMap.ext (fun y => ?_)
      dsimp
      ring }

def ρ_spinor : SpinorRep.Cl_split 5 →ₐ[ℝ] Module.End ℝ (Fin 32 → ℝ) :=
  (Matrix.toLinAlgEquiv').toAlgHom.comp (spinorRepresentation 5)

noncomputable def pkg_concrete : Pin55KreinConformalPackage where
  K := Fin 32 → ℝ
  B := B_concrete
  J := J_concrete
  χ := χ_concrete
  ε := ε_concrete
  ρ := ρ_spinor
  J_sq := J_concrete_sq
  χ_sq := χ_concrete_sq
  ε_sq := ε_concrete_sq
  ρ_preserves_B := sorry
  anomaly_index_zero := sorry

theorem exists_pin55_krein_conformal_package :
    ∃ (pkg : Pin55KreinConformalPackage),
      ∃ (e : CanonicalZorn ≃ₗ[ℝ] InfoGeometry.CliffordTower.SplitSpace 4),
        ∃ (ι_K : InfoGeometry.CliffordTower.SplitSpace 4 →ₗ[ℝ] pkg.K),
          ∃ (P_K : pkg.K →ₗ[ℝ] InfoGeometry.CliffordTower.SplitSpace 4),
            ∀ (X : Imaginary),
              P_K ∘ₗ (pkg.ρ (SpinorRep.incl_Cl_split 4 (CliffordAlgebra.ι (SplitQuad 4) (e X.1)))) ∘ₗ ι_K = e ∘ₗ imaginaryLeftMul X ∘ₗ e.symm := by
  use pkg_concrete
  sorry

end InfoGeometry.Lie.Pin55KreinConformalBridge
