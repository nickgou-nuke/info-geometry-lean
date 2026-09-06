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
open InfoGeometry.Categorical.LogJordanTensorPowerBraidRelations
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
  InfoGeometry.Spectral.Colimit.SequentialModule.Carrier ℂ standardTensorPowerModuleDiagram

/-- Canonical inclusion of stage `n`, whose carrier is `J^{⊗(n+2)}`. -/
abbrev stageInclusion (n : ℕ) :
    standardTensorPowerModuleDiagram.obj n ⟶ StandardTensorPowerColimit :=
  InfoGeometry.Spectral.Colimit.SequentialModule.inclusion ℂ n

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
    InfoGeometry.Spectral.Colimit.SequentialModule.inclusion_naturality ℂ
      (F := standardTensorPowerModuleDiagram) (Nat.le_succ n)
  rw [standardTensorPowerModuleDiagram_map_succ] at hnat
  have happ := congrArg (fun f => f.hom v) hnat
  simpa [stageInclusion, InfoGeometry.Spectral.Colimit.SequentialModule.inclusion,
    ModuleCat.comp_apply] using happ

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
  have hpoint' :
      standardHadjiivanovBraidProjectHom (n + 1)
          (finiteSuccGroupHom (n + 1) g)
          ((appendPrimaryBonding (n + 1)).hom v) =
        (appendPrimaryBonding (n + 1)).hom
          (standardHadjiivanovBraidProjectHom n g v) := by
    simpa [LinearMap.comp_apply] using hpoint.symm
  rw [hpoint']
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


/-- A compatible family of stage endomorphisms for the stabilized tensor-power
diagram.  The naturality law is stated for every comparison map in the
sequence, so the family is exactly the data needed to act on the categorical
colimit. -/
structure CompatibleStageEndomorphism where
  map : ∀ n : ℕ,
    standardTensorPowerModuleDiagram.obj n ⟶
      standardTensorPowerModuleDiagram.obj n
  naturality : ∀ {m n : ℕ} (h : m ≤ n),
    standardTensorPowerModuleDiagram.map (homOfLE h) ≫ map n =
      map m ≫ standardTensorPowerModuleDiagram.map (homOfLE h)

/-- The cocone obtained by postcomposing each stage inclusion with a
compatible stage endomorphism. -/
def compatibleStageEndomorphismCocone
    (A : CompatibleStageEndomorphism) :
    CategoryTheory.Limits.Cocone standardTensorPowerModuleDiagram where
  pt := StandardTensorPowerColimit
  ι :=
    { app := fun n => A.map n ≫ stageInclusion n
      naturality := by
        intro m n h
        have hh : h = homOfLE h.down.down := Subsingleton.elim _ _
        rw [hh]
        dsimp
        calc
          standardTensorPowerModuleDiagram.map (homOfLE h.down.down) ≫ A.map n ≫ stageInclusion n =
              (A.map m ≫ standardTensorPowerModuleDiagram.map (homOfLE h.down.down)) ≫ stageInclusion n := by
                simpa [Category.assoc] using
                  congrArg (fun k => k ≫ stageInclusion n)
                    (A.naturality h.down.down)
          _ = A.map m ≫
                (standardTensorPowerModuleDiagram.map (homOfLE h.down.down) ≫ stageInclusion n) := by
                simp only [Category.assoc]
          _ = A.map m ≫ stageInclusion m := by
                simpa [Category.assoc] using
                  congrArg (fun k => A.map m ≫ k)
                    (InfoGeometry.Spectral.Colimit.SequentialModule.inclusion_naturality ℂ
                      (F := standardTensorPowerModuleDiagram) h.down.down)
          _ = (A.map m ≫ stageInclusion m) ≫ 𝟙 _ := by simp }

/-- The unique endomorphism of the module colimit induced by a compatible
family of finite-stage endomorphisms. -/
def colimitEndomorphism (A : CompatibleStageEndomorphism) :
  StandardTensorPowerColimit ⟶ StandardTensorPowerColimit :=
  InfoGeometry.Spectral.Colimit.SequentialModule.descend ℂ
    (compatibleStageEndomorphismCocone A)

/-- Stage readback for the induced colimit endomorphism. -/
@[simp]
theorem colimitEndomorphism_stage
    (A : CompatibleStageEndomorphism) (n : ℕ) :
    stageInclusion n ≫ colimitEndomorphism A =
      A.map n ≫ stageInclusion n := by
  unfold colimitEndomorphism stageInclusion
  rw [InfoGeometry.Spectral.Colimit.SequentialModule.descend_fac ℂ
    (compatibleStageEndomorphismCocone A) n]
  rfl

/-- The colimit endomorphism is uniquely determined by all of its stage
readbacks. -/
theorem colimitEndomorphism_unique
    (A : CompatibleStageEndomorphism)
    (f : StandardTensorPowerColimit ⟶ StandardTensorPowerColimit)
    (hf : ∀ n : ℕ,
      stageInclusion n ≫ f = A.map n ≫ stageInclusion n) :
    f = colimitEndomorphism A := by
  apply colimit.hom_ext
  intro n
  exact (hf n).trans (colimitEndomorphism_stage A n).symm

end InfoGeometry.Categorical.LogJordanBraidTensorPowerColimit
