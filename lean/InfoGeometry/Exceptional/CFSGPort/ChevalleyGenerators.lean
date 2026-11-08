/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/-
Adapted from AxiomMath/CFSG, Apache-2.0. Module and namespace paths are
adapted for this repository's Lean 4.34.1 / mathlib pin.
-/
module

public import InfoGeometry.Exceptional.CFSGPort.ChevalleyRoots
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyUnits
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyRootCheck

public section

namespace InfoGeometry.Exceptional.CFSGPort.Chevalley

theorem simple_root_operator_units_of_tag (τ : Tag) (R : Type*) [CommRing R] (i : Fin τ.rank)
    (c : R) :
    (∀ a b : Label τ, b.Precedes a → xOp τ R i c (Finsupp.single b 1) a = 0) ∧
      (∀ b : Label τ, xOp τ R i c (Finsupp.single b 1) b = 1) ∧
      (∀ a b : Label τ, a.Precedes b → yOp τ R i c (Finsupp.single b 1) a = 0) ∧
      (∀ b : Label τ, yOp τ R i c (Finsupp.single b 1) b = 1) ∧
      LinearMap.det (xOp τ R i c) = 1 ∧ LinearMap.det (yOp τ R i c) = 1 ∧
      IsUnit (xOp τ R i c) ∧ IsUnit (yOp τ R i c) :=
  simple_root_operator_units i c

theorem xOp_yOp_mem_adjointGroup (τ : Tag) (K : Type*) [Field K] (i : Fin τ.rank) (c : K) :
    (∃ g ∈ adjointGroup τ K, (g : Module.End K (RootModule τ K)) = xOp τ K i c) ∧
      ∃ g ∈ adjointGroup τ K, (g : Module.End K (RootModule τ K)) = yOp τ K i c :=
  ⟨exists_mem_adjointGroup_xOp i c, exists_mem_adjointGroup_yOp i c⟩

end InfoGeometry.Exceptional.CFSGPort.Chevalley
