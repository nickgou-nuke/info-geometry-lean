import InfoGeometry.Categorical.LogJordanTensorPowerStabilization
import InfoGeometry.Spectral.Colimit.SequentialModule
import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Colimit compatibility of the logarithmic braid tensor-power tower

The stage carriers `J^{⊗(n+2)}` and primary-spectator bonding maps form a
sequence in `ModuleCat ℂ`.  We use Mathlib's actual categorical colimit through
the repository-owned `Spectral.Colimit.SequentialModule` API.

This file proves that a finite braid action and its stabilized action determine
the same element of the module colimit.  It deliberately does not yet claim a
global `B_∞` representation on the colimit carrier.
-/

noncomputable section

namespace InfoGeometry.Categorical.LogJordanBraidTensorPowerColimit

open CategoryTheory
open CategoryTheory.Limits
open Braid

open InfoGeometry.Categorical.LogNilpotentTensorPowerBraid
open InfoGeometry.Categorical.LogJordanCheckedRBraidBridge
open InfoGeometry.Categorical.LogJordanBraidProjectTensorPowerRepresentation
open InfoGeometry.Categorical.LogJordanTensorPowerStabilization
open InfoGeometry.Categorical.BraidGroupFiniteInfiniteColimitBridge
open InfoGeometry.Spectral.Colimit.SequentialModule

/-- Sequence of finite logarithmic tensor-power carriers, beginning at the
2-fold tensor power. -/
def standardTensorPowerModuleDiagram : ℕ ⥤ ModuleCat ℂ :=
  Functor.ofSequence
    (fun n => ModuleCat.ofHom (appendPrimaryBonding (n + 1)).hom)

/-- The actual Mathlib module colimit of the stabilized logarithmic tensor
powers. -/
abbrev StandardTensorPowerColimit : ModuleCat ℂ :=
  SequentialModule.Carrier ℂ standardTensorPowerModuleDiagram

/-- Canonical inclusion of stage `n`, whose carrier is `J^{⊗(n+2)}`. -/
abbrev stageInclusion (n : ℕ) :
    standardTensorPowerModuleDiagram.obj n ⟶ StandardTensorPowerColimit :=
  SequentialModule.inclusion ℂ n

/-- Successor map in the module diagram is exactly right append by the primary
spectator. -/
theorem standardTensorPowerModuleDiagram_map_succ (n : ℕ) :
    standardTensorPowerModuleDiagram.map (homOfLE (Nat.le_succ n)) =
      ModuleCat.ofHom (appendPrimaryBonding (n + 1)).hom := by
  simpa [standardTensorPowerModuleDiagram] using
    (Functor.ofSequence_map_homOfLE_succ
      (f := fun n => ModuleCat.ofHom (appendPrimaryBonding (n + 1)).hom) n)

/-- Stage inclusions identify a vector with its primary-spectator stabilization. -/
theorem stageInclusion_bonding
    (n : ℕ)
    (v : tensorPowerObj standardJordanObject (n + 2)) :
    (stageInclusion (n + 1)).hom
        ((appendPrimaryBonding (n + 1)).hom v) =
      (stageInclusion n).hom v := by
  have hnat :=
    SequentialModule.inclusion_naturality ℂ
      (F := standardTensorPowerModuleDiagram) (Nat.le_succ n)
  rw [standardTensorPowerModuleDiagram_map_succ] at hnat
  have happ := congrArg (fun f => f.hom v) hnat
  simpa [stageInclusion, SequentialModule.inclusion, ModuleCat.comp_apply] using happ

/-- A finite braid action and the corresponding stabilized braid action have the
same colimit image.  This is the exact representation-level compatibility
needed before constructing any global infinite-braid action. -/
theorem stabilized_braid_same_colimit_image
    (n : ℕ) (g : braid_group (n + 2))
    (v : tensorPowerObj standardJordanObject (n + 2)) :
    (stageInclusion (n + 1)).hom
        (standardHadjiivanovBraidProjectHom (n + 1)
          (finiteSuccGroupHom (n + 1) g)
          ((appendPrimaryBonding (n + 1)).hom v)) =
      (stageInclusion n).hom
        (standardHadjiivanovBraidProjectHom n g v) := by
  have hcompat := appendPrimaryBonding_braid_compat n g
  have hpoint := LinearMap.congr_fun hcompat v
  rw [← hpoint]
  exact stageInclusion_bonding n
    (standardHadjiivanovBraidProjectHom n g v)

/-- Generator specialization of stable colimit readback. -/
theorem stabilized_generator_same_colimit_image
    (n : ℕ) (i : Fin (n + 1))
    (v : tensorPowerObj standardJordanObject (n + 2)) :
    (stageInclusion (n + 1)).hom
        (standardHadjiivanovBraidProjectHom (n + 1)
          (finiteSuccGroupHom (n + 1) (σ' (n + 1) i))
          ((appendPrimaryBonding (n + 1)).hom v)) =
      (stageInclusion n).hom
        (standardTensorPowerGenerator n i v) := by
  simpa using stabilized_braid_same_colimit_image n (σ' (n + 1) i) v

end InfoGeometry.Categorical.LogJordanBraidTensorPowerColimit
