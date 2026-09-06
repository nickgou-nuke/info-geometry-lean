import InfoGeometry.Algebra.FiniteSingleModeCAR
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Topological realization of the finite one-mode CAR operators

The owner algebra gives `ann` and `cre` as operators on the finite Fock
function space.  This file supplies their product-topology morphisms and
keeps the CAR identity as the exact pointwise identity already proved by the
owner.  It does not identify these operators with Cuntz generators.
-/

noncomputable section

namespace InfoGeometry.Canonical.FiniteSingleModeCARTopological

open InfoGeometry.Algebra.FiniteSingleModeCAR
open CategoryTheory

def continuous_ann : Continuous (ann : OneModeVec → OneModeVec) := by
  apply continuous_pi
  intro occ
  cases occ
  · exact continuous_apply true
  · exact continuous_const

def continuous_cre : Continuous (cre : OneModeVec → OneModeVec) := by
  apply continuous_pi
  intro occ
  cases occ
  · exact continuous_const
  · exact continuous_apply false

def continuous_num : Continuous (num : OneModeVec → OneModeVec) :=
  continuous_cre.comp continuous_ann

def annTopCatHom :
    TopCat.of OneModeVec ⟶ TopCat.of OneModeVec :=
  TopCat.ofHom
    { toFun := ann
      continuous_toFun := continuous_ann }

def creTopCatHom :
    TopCat.of OneModeVec ⟶ TopCat.of OneModeVec :=
  TopCat.ofHom
    { toFun := cre
      continuous_toFun := continuous_cre }

def numTopCatHom :
    TopCat.of OneModeVec ⟶ TopCat.of OneModeVec :=
  TopCat.ofHom
    { toFun := num
      continuous_toFun := continuous_num }

@[simp] theorem annTopCatHom_apply (ψ : OneModeVec) :
    annTopCatHom ψ = ann ψ :=
  rfl

@[simp] theorem creTopCatHom_apply (ψ : OneModeVec) :
    creTopCatHom ψ = cre ψ :=
  rfl

@[simp] theorem numTopCatHom_apply (ψ : OneModeVec) :
    numTopCatHom ψ = num ψ :=
  rfl

theorem ann_cre_anticommutator_topological_readout (ψ : OneModeVec) :
    opAdd (opComp ann cre) (opComp cre ann) ψ = idOp ψ := by
  exact congrFun ann_cre_anticommutator ψ

theorem ann_cre_anticommutator_topological_readout_at (ψ : OneModeVec)
    (occ : Bool) :
    opAdd (opComp ann cre) (opComp cre ann) ψ occ = idOp ψ occ := by
  exact congrFun (congrFun
    ann_cre_anticommutator ψ) occ

end InfoGeometry.Canonical.FiniteSingleModeCARTopological
