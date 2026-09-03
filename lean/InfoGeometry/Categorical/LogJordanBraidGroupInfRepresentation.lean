import Mathlib
import InfoGeometry.Categorical.LogJordanBraidInfiniteGeneratorColimit
import proofs.BraidProject.BraidGroup

/-!
# Global B-infinity action on the Hadjiivanov tensor-power colimit

The finite logarithmic braid representations are already compatible under
right stabilization, and each fixed Artin generator has therefore been
promoted to an automorphism of the single `ModuleCat` tensor-power colimit.
This file proves that those global generator automorphisms satisfy the defining
relations of the repository-owned presented infinite braid group and applies
`Braid.braid_group_inf.toGroup`.

No identification `B_∞ ≅ colim B_n` is needed for this construction: the
module-colimit action is obtained directly from the compatible finite-stage
operators, while the existing presented-group universal property supplies the
group action.
-/

noncomputable section

namespace InfoGeometry.Categorical.LogJordanBraidGroupInfRepresentation

open CategoryTheory
open CategoryTheory.Limits
open Braid

open InfoGeometry.Categorical.LogJordanCheckedRBraidBridge
open InfoGeometry.Categorical.LogJordanTensorPowerBraidRelations
open InfoGeometry.Categorical.LogJordanBraidProjectTensorPowerRepresentation
open InfoGeometry.Categorical.LogJordanBraidTensorPowerColimit
open InfoGeometry.Categorical.BraidGroupFiniteInfiniteColimit
open InfoGeometry.Categorical.LogJordanBraidInfiniteGeneratorColimit
open InfoGeometry.Spectral.Colimit.SequentialModule

/-- Adjacent global checked-R generators satisfy the Artin relation on the
single tensor-power colimit. -/
theorem infiniteGenerator_artin (i : ℕ) :
    infiniteGeneratorAut i * infiniteGeneratorAut (i + 1) *
        infiniteGeneratorAut i =
      infiniteGeneratorAut (i + 1) * infiniteGeneratorAut i *
        infiniteGeneratorAut (i + 1) := by
  apply Iso.ext
  apply colimit.hom_ext
  intro n
  let m : ℕ := max n (i + 1)
  have hnm : n ≤ m := Nat.le_max_left _ _
  have him : i ≤ m := by
    dsimp [m]
    omega
  have hi1m : i + 1 ≤ m := by
    dsimp [m]
    exact Nat.le_max_right _ _
  have hmpos : 1 ≤ m := by omega
  let ii : Fin m := ⟨i, by omega⟩
  have hfinite := standardTensorPower_artin (m - 1) ii
  have hinc :=
    SequentialModule.inclusion_naturality ℂ
      (F := standardTensorPowerModuleDiagram) hnm
  change
    stageInclusion n ≫
        (infiniteGeneratorAut i * infiniteGeneratorAut (i + 1) *
          infiniteGeneratorAut i).hom =
      stageInclusion n ≫
        (infiniteGeneratorAut (i + 1) * infiniteGeneratorAut i *
          infiniteGeneratorAut (i + 1)).hom
  rw [← hinc, Category.assoc, Category.assoc]
  rw [show
      stageInclusion m ≫ (infiniteGeneratorAut i).hom =
        ModuleCat.ofHom
            (standardTensorPowerGenerator m ⟨i, by omega⟩).toLinearMap ≫
          stageInclusion m by
        exact infiniteGeneratorAut_stage_of_le i m him]
  rw [show
      stageInclusion m ≫ (infiniteGeneratorAut (i + 1)).hom =
        ModuleCat.ofHom
            (standardTensorPowerGenerator m ⟨i + 1, by omega⟩).toLinearMap ≫
          stageInclusion m by
        exact infiniteGeneratorAut_stage_of_le (i + 1) m hi1m]
  simp only [Category.assoc]
  have hfinite' :
      standardTensorPowerGenerator m ⟨i, by omega⟩ *
          standardTensorPowerGenerator m ⟨i + 1, by omega⟩ *
          standardTensorPowerGenerator m ⟨i, by omega⟩ =
        standardTensorPowerGenerator m ⟨i + 1, by omega⟩ *
          standardTensorPowerGenerator m ⟨i, by omega⟩ *
          standardTensorPowerGenerator m ⟨i + 1, by omega⟩ := by
    simpa [ii, Nat.sub_add_cancel hmpos] using hfinite
  have hlin := congrArg
    (fun e : tensorPowerObj standardJordanObject (m + 2) ≃ₗ[ℂ]
        tensorPowerObj standardJordanObject (m + 2) => e.toLinearMap)
    hfinite'
  simpa [LinearEquiv.mul_apply, ModuleCat.comp_apply, Category.assoc] using
    congrArg (fun f => ModuleCat.ofHom f ≫ stageInclusion m) hlin

/-- Global generators with at least one untouched strand between them commute. -/
theorem infiniteGenerator_far
    (i j : ℕ) (hij : i + 2 ≤ j) :
    infiniteGeneratorAut i * infiniteGeneratorAut j =
      infiniteGeneratorAut j * infiniteGeneratorAut i := by
  apply Iso.ext
  apply colimit.hom_ext
  intro n
  let m : ℕ := max n (j + 1)
  have hnm : n ≤ m := Nat.le_max_left _ _
  have him : i ≤ m := by
    dsimp [m]
    omega
  have hjm : j ≤ m := by
    dsimp [m]
    omega
  have hmj : j < m + 1 := by omega
  let a : Fin (m + 1) := ⟨i, by omega⟩
  let b : Fin (m + 1) := ⟨j - 2, by omega⟩
  have hab : a ≤ b := by
    apply Fin.mk_le_mk.mpr
    dsimp [a, b]
    omega
  have hfinite := standardTensorPower_far m a b hab
  have hinc :=
    SequentialModule.inclusion_naturality ℂ
      (F := standardTensorPowerModuleDiagram) hnm
  change
    stageInclusion n ≫
        (infiniteGeneratorAut i * infiniteGeneratorAut j).hom =
      stageInclusion n ≫
        (infiniteGeneratorAut j * infiniteGeneratorAut i).hom
  rw [← hinc, Category.assoc, Category.assoc]
  rw [show
      stageInclusion m ≫ (infiniteGeneratorAut i).hom =
        ModuleCat.ofHom
            (standardTensorPowerGenerator m ⟨i, by omega⟩).toLinearMap ≫
          stageInclusion m by
        exact infiniteGeneratorAut_stage_of_le i m him]
  rw [show
      stageInclusion m ≫ (infiniteGeneratorAut j).hom =
        ModuleCat.ofHom
            (standardTensorPowerGenerator m ⟨j, by omega⟩).toLinearMap ≫
          stageInclusion m by
        exact infiniteGeneratorAut_stage_of_le j m hjm]
  simp only [Category.assoc]
  have hfinite' :
      standardTensorPowerGenerator m ⟨i, by omega⟩ *
          standardTensorPowerGenerator m ⟨j, by omega⟩ =
        standardTensorPowerGenerator m ⟨j, by omega⟩ *
          standardTensorPowerGenerator m ⟨i, by omega⟩ := by
    simpa [a, b, Nat.sub_add_cancel (by omega : 2 ≤ j)] using hfinite
  have hlin := congrArg
    (fun e : tensorPowerObj standardJordanObject (m + 2) ≃ₗ[ℂ]
        tensorPowerObj standardJordanObject (m + 2) => e.toLinearMap)
    hfinite'
  simpa [LinearEquiv.mul_apply, ModuleCat.comp_apply, Category.assoc] using
    congrArg (fun f => ModuleCat.ofHom f ≫ stageInclusion m) hlin

/-- Every defining relation of the repository-owned infinite braid group is
satisfied by the global Hadjiivanov colimit generators. -/
theorem infiniteGenerator_relations :
    ∀ r ∈ braid_rels_inf,
      FreeGroup.lift infiniteGeneratorAut r =
        (1 : Aut StandardTensorPowerColimit) := by
  intro r hr
  rcases hr with hArtin | hFar
  · rcases hArtin with ⟨i, rfl⟩
    have h := infiniteGenerator_artin i
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [h]
    group
  · rcases hFar with ⟨i, j, hij, rfl⟩
    have h := infiniteGenerator_far i j hij
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    rw [h]
    group

/-- Global non-involutive Hadjiivanov braid action of the repository-owned
presented `B_∞` on the stabilized logarithmic tensor-power colimit. -/
def hadjiivanovBraidGroupInfHom :
    braid_group_inf →* Aut StandardTensorPowerColimit :=
  braid_group_inf.toGroup infiniteGeneratorAut infiniteGenerator_relations

/-- Infinite generator readback. -/
@[simp]
theorem hadjiivanovBraidGroupInfHom_sigma (i : ℕ) :
    hadjiivanovBraidGroupInfHom (σi i) = infiniteGeneratorAut i := by
  exact braid_group_inf.toGroup_sigma
    infiniteGeneratorAut infiniteGenerator_relations i

/-- The global `B_∞` action restricts on every sufficiently late finite stage
to the corresponding adjacent Hadjiivanov checked-R slice. -/
theorem hadjiivanovBraidGroupInf_sigma_stage
    (i n : ℕ) (h : i ≤ n) :
    stageInclusion n ≫ (hadjiivanovBraidGroupInfHom (σi i)).hom =
      ModuleCat.ofHom
          (standardTensorPowerGenerator n ⟨i, by omega⟩).toLinearMap ≫
        stageInclusion n := by
  rw [hadjiivanovBraidGroupInfHom_sigma]
  exact infiniteGeneratorAut_stage_of_le i n h

/-- Finite-stage braids whose global action agrees with the finite tensor-power
representation after passage to the module colimit. -/
def finiteStageReadbackSubgroup (n : ℕ) :
    Subgroup (braid_group (n + 2)) where
  carrier := {g |
    stageInclusion n ≫
        (hadjiivanovBraidGroupInfHom
          (finiteToInfiniteGroupHom (n + 1) g)).hom =
      ModuleCat.ofHom
          (standardHadjiivanovBraidProjectHom n g).toLinearMap ≫
        stageInclusion n}
  one_mem' := by
    apply ModuleCat.hom_ext
    ext x
    simp [ModuleCat.comp_apply]
  mul_mem' := by
    intro g h hg hh
    change
      stageInclusion n ≫
          (hadjiivanovBraidGroupInfHom
            (finiteToInfiniteGroupHom (n + 1) g)).hom =
        ModuleCat.ofHom
            (standardHadjiivanovBraidProjectHom n g).toLinearMap ≫
          stageInclusion n at hg
    change
      stageInclusion n ≫
          (hadjiivanovBraidGroupInfHom
            (finiteToInfiniteGroupHom (n + 1) h)).hom =
        ModuleCat.ofHom
            (standardHadjiivanovBraidProjectHom n h).toLinearMap ≫
          stageInclusion n at hh
    apply ModuleCat.hom_ext
    ext x
    have hhx := congrArg
      (fun f : standardTensorPowerModuleDiagram.obj n ⟶
          StandardTensorPowerColimit => f.hom x) hh
    have hgx := congrArg
      (fun f : standardTensorPowerModuleDiagram.obj n ⟶
          StandardTensorPowerColimit =>
        f.hom (standardHadjiivanovBraidProjectHom n h x)) hg
    have hhx' :
        (hadjiivanovBraidGroupInfHom
            (finiteToInfiniteGroupHom (n + 1) h)).hom.hom
            ((stageInclusion n).hom x) =
          (stageInclusion n).hom
            (standardHadjiivanovBraidProjectHom n h x) := by
      simpa [ModuleCat.comp_apply] using hhx
    have hgx' :
        (hadjiivanovBraidGroupInfHom
            (finiteToInfiniteGroupHom (n + 1) g)).hom.hom
            ((stageInclusion n).hom
              (standardHadjiivanovBraidProjectHom n h x)) =
          (stageInclusion n).hom
            (standardHadjiivanovBraidProjectHom n g
              (standardHadjiivanovBraidProjectHom n h x)) := by
      simpa [ModuleCat.comp_apply] using hgx
    calc
      (stageInclusion n ≫
          (hadjiivanovBraidGroupInfHom
            (finiteToInfiniteGroupHom (n + 1) (g * h))).hom).hom x =
          (hadjiivanovBraidGroupInfHom
            (finiteToInfiniteGroupHom (n + 1) (g * h))).hom.hom
            ((stageInclusion n).hom x) := by
              simp [ModuleCat.comp_apply]
      _ = (hadjiivanovBraidGroupInfHom
            (finiteToInfiniteGroupHom (n + 1) g)).hom.hom
            ((hadjiivanovBraidGroupInfHom
              (finiteToInfiniteGroupHom (n + 1) h)).hom.hom
              ((stageInclusion n).hom x)) := by
              simp [map_mul, CategoryTheory.Aut.Aut_mul_def,
                Iso.trans_hom, ModuleCat.comp_apply]
      _ = (hadjiivanovBraidGroupInfHom
            (finiteToInfiniteGroupHom (n + 1) g)).hom.hom
            ((stageInclusion n).hom
              (standardHadjiivanovBraidProjectHom n h x)) := by
              rw [hhx']
      _ = (stageInclusion n).hom
          (standardHadjiivanovBraidProjectHom n g
            (standardHadjiivanovBraidProjectHom n h x)) := by
              rw [hgx']
      _ = (stageInclusion n).hom
          (standardHadjiivanovBraidProjectHom n (g * h) x) := by
              simp [map_mul, LinearEquiv.mul_apply]
      _ = (ModuleCat.ofHom
          (standardHadjiivanovBraidProjectHom n (g * h)).toLinearMap ≫
            stageInclusion n).hom x := by
              simp [ModuleCat.comp_apply]
  inv_mem' := by
    intro g hg
    change
      stageInclusion n ≫
          (hadjiivanovBraidGroupInfHom
            (finiteToInfiniteGroupHom (n + 1) g)).hom =
        ModuleCat.ofHom
            (standardHadjiivanovBraidProjectHom n g).toLinearMap ≫
          stageInclusion n at hg
    change
      stageInclusion n ≫
          (hadjiivanovBraidGroupInfHom
            (finiteToInfiniteGroupHom (n + 1) g⁻¹)).hom =
        ModuleCat.ofHom
            (standardHadjiivanovBraidProjectHom n g⁻¹).toLinearMap ≫
          stageInclusion n
    apply ModuleCat.hom_ext
    ext x
    have h := congrArg
      (fun f : standardTensorPowerModuleDiagram.obj n ⟶
          StandardTensorPowerColimit =>
        f.hom ((standardHadjiivanovBraidProjectHom n g).symm x)) hg
    have h' := congrArg
      (fun y =>
        (hadjiivanovBraidGroupInfHom
          (finiteToInfiniteGroupHom (n + 1) g)).inv.hom.hom y) h
    simpa [ModuleCat.comp_apply, map_inv, CategoryTheory.Aut.Aut_inv_def]
      using h'.symm

/-- Arbitrary finite braid-element compatibility with the global `B_∞` action.
For every `g : B_{n+2}`, its finite tensor-power action agrees, after the
stage inclusion, with the action of its canonical image in the presented
infinite braid group. -/
theorem hadjiivanovBraidGroupInf_finite_stage
    (n : ℕ) (g : braid_group (n + 2)) :
    stageInclusion n ≫
        (hadjiivanovBraidGroupInfHom
          (finiteToInfiniteGroupHom (n + 1) g)).hom =
      ModuleCat.ofHom
          (standardHadjiivanovBraidProjectHom n g).toLinearMap ≫
        stageInclusion n := by
  exact Braid.generated_by (n + 1)
    (finiteStageReadbackSubgroup n)
    (by
      intro i
      change
        stageInclusion n ≫
            (hadjiivanovBraidGroupInfHom
              (finiteToInfiniteGroupHom (n + 1)
                (σ' (n + 1) i))).hom =
          ModuleCat.ofHom
              (standardHadjiivanovBraidProjectHom n
                (σ' (n + 1) i)).toLinearMap ≫
            stageInclusion n
      have hi : (i : ℕ) ≤ n := by omega
      rw [finiteToInfiniteGroupHom_sigma]
      rw [hadjiivanovBraidGroupInfHom_sigma]
      rw [standardHadjiivanovBraidProject_sigma]
      exact infiniteGeneratorAut_stage_of_le i n hi) g
end InfoGeometry.Categorical.LogJordanBraidGroupInfRepresentation
