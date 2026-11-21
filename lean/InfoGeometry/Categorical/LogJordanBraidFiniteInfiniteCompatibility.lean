/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Categorical.LogJordanBraidGroupInfRepresentation
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Pointwise finite/infinite Hadjiivanov braid compatibility

The arbitrary-element intertwining theorem is owned by
`LogJordanBraidGroupInfRepresentation.hadjiivanovBraidGroupInf_finite_stage`.
This existing public interface evaluates that categorical equality on tensor
vectors. It does not construct a second compatibility subgroup or repeat the
presented-group induction.
-/

noncomputable section

namespace InfoGeometry.Categorical.LogJordanBraidFiniteInfiniteCompatibility

open CategoryTheory Braid
open InfoGeometry.Categorical.LogNilpotentTensorPowerBraid
open InfoGeometry.Categorical.LogJordanCheckedRBraidBridge
open InfoGeometry.Categorical.BraidGroupFiniteInfiniteColimitBridge
open InfoGeometry.Categorical.LogJordanBraidProjectTensorPowerRepresentation
open InfoGeometry.Categorical.LogJordanBraidTensorPowerColimit
open InfoGeometry.Categorical.LogJordanBraidGroupInfRepresentation

/-- Act on a finite tensor stage and include, or include and act on the colimit. -/
def BraidElementCompatible (n : ℕ) (g : braid_group (n + 2)) : Prop :=
  ∀ v : tensorPowerObj standardJordanObject (n + 2),
    (stageInclusion n).hom (standardHadjiivanovBraidProjectHom n g v) =
      (hadjiivanovBraidGroupInfHom (finiteToInfiniteGroupHom (n + 1) g)).hom
        ((stageInclusion n).hom v)

/-- Evaluation of the owner intertwining equality at a finite-stage vector. -/
theorem hadjiivanov_finite_infinite_compatibility
    (n : ℕ) (g : braid_group (n + 2)) :
    BraidElementCompatible n g := by
  intro v
  have h := congrArg
    (fun f : standardTensorPowerModuleDiagram.obj n ⟶
        StandardTensorPowerColimit => f.hom v)
    (hadjiivanovBraidGroupInf_finite_stage n g)
  exact h.symm

/-- Categorical morphism form, retaining the established public orientation. -/
theorem hadjiivanov_finite_infinite_compatibility_hom
    (n : ℕ) (g : braid_group (n + 2)) :
    ModuleCat.ofHom (standardHadjiivanovBraidProjectHom n g).toLinearMap ≫
        stageInclusion n =
      stageInclusion n ≫
        (hadjiivanovBraidGroupInfHom (finiteToInfiniteGroupHom (n + 1) g)).hom := by
  apply ModuleCat.hom_ext
  ext v
  exact hadjiivanov_finite_infinite_compatibility n g v

private theorem compatible_one (n : ℕ) :
    BraidElementCompatible n 1 :=
  hadjiivanov_finite_infinite_compatibility n 1

private theorem compatible_mul
    (n : ℕ) {g h : braid_group (n + 2)}
    (hg : BraidElementCompatible n g)
    (hh : BraidElementCompatible n h) :
    BraidElementCompatible n (g * h) :=
  hadjiivanov_finite_infinite_compatibility n (g * h)

private theorem compatible_inv
    (n : ℕ) {g : braid_group (n + 2)}
    (hg : BraidElementCompatible n g) :
    BraidElementCompatible n g⁻¹ :=
  hadjiivanov_finite_infinite_compatibility n g⁻¹

private theorem compatible_sigma
    (n : ℕ) (i : Fin (n + 1)) :
    BraidElementCompatible n (σ' (n + 1) i) :=
  hadjiivanov_finite_infinite_compatibility n (σ' (n + 1) i)

end InfoGeometry.Categorical.LogJordanBraidFiniteInfiniteCompatibility
