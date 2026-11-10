/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.HeisenbergFiniteModeStages
import InfoGeometry.Canonical.HeisenbergCyclotomicModeBridge

/-!
# Cyclotomic Labels on Finite Heisenberg Mode Stages

This module assigns the `ZMod 3` cyclotomic degree `heisenbergBasisCyclotomicDegree`
to basis indices `Option ℤ` of `HeisenbergAlgebra 𝕜` (`none ↦ 0`, `some k ↦ (k : ZMod 3)`),
defines the finite stage degree set `stageCyclotomicDegreeSet`, and proves stage
monotonicity, membership, continuity, and local constancy.

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * `InfoGeometry.Canonical.HeisenbergFiniteModeStages`: `heisenbergFiniteModeStage`.
  * `InfoGeometry.Canonical.HeisenbergCyclotomicModeBridge`: `heisenbergModeDegree`,
    `heisenbergModeDegree_neg`.
- BUCKET 2 (Deconfabulation):
  * All evaluation, stage monotonicity, and topological theorems are proved constructively.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `heisenbergBasisCyclotomicDegree`, `stageCyclotomicDegreeSet`.
  * `heisenbergBasisCyclotomicDegree_none`, `heisenbergBasisCyclotomicDegree_some`,
    `heisenbergBasisCyclotomicDegree_neg`.
  * `stageCyclotomicDegreeSet_mono`, `basisJK_stage_degree_mem`.
  * `continuous_heisenbergBasisCyclotomicDegree`,
    `isLocallyConstant_heisenbergBasisCyclotomicDegree`.
-/

namespace InfoGeometry.Topology.HeisenbergFiniteModeCyclotomicTopological

open InfoGeometry.Canonical

noncomputable section

instance heisenbergBasisIndexTopologicalSpace :
    TopologicalSpace (Option ℤ) := ⊥

instance heisenbergBasisIndexDiscreteTopology :
    DiscreteTopology (Option ℤ) := DiscreteTopology.mk (Eq.refl _)

/-- The central basis label `none` has degree zero; a current mode `some k` has its
residue modulo three. -/
def heisenbergBasisCyclotomicDegree : Option ℤ → ZMod 3
  | none => 0
  | some k => heisenbergModeDegree k

/-- The central basis index `none` has cyclotomic degree `0`. -/
@[simp] theorem heisenbergBasisCyclotomicDegree_none :
    heisenbergBasisCyclotomicDegree none = 0 := by
  unfold heisenbergBasisCyclotomicDegree
  exact Eq.refl _

/-- The mode basis index `some k` has cyclotomic degree `heisenbergModeDegree k`. -/
@[simp] theorem heisenbergBasisCyclotomicDegree_some (k : ℤ) :
    heisenbergBasisCyclotomicDegree (some k) = heisenbergModeDegree k := by
  unfold heisenbergBasisCyclotomicDegree
  exact Eq.refl _

/-- Negating the integer mode index negates its cyclotomic basis degree in `ZMod 3`. -/
theorem heisenbergBasisCyclotomicDegree_neg (k : ℤ) :
    heisenbergBasisCyclotomicDegree (some (-k)) =
      -heisenbergBasisCyclotomicDegree (some k) := by
  rw [heisenbergBasisCyclotomicDegree_some, heisenbergBasisCyclotomicDegree_some]
  exact heisenbergModeDegree_neg k

/-- The finite set of cyclotomic labels visible at a finite mode stage `s`. -/
def stageCyclotomicDegreeSet (s : Finset (Option ℤ)) : Finset (ZMod 3) :=
  s.image heisenbergBasisCyclotomicDegree

/-- Stage inclusion `s ⊆ t` preserves the visible cyclotomic degree set. -/
theorem stageCyclotomicDegreeSet_mono
    {s t : Finset (Option ℤ)} (hst : s ⊆ t) :
    stageCyclotomicDegreeSet s ⊆ stageCyclotomicDegreeSet t := by
  intro d hd
  rcases Finset.mem_image.mp hd with ⟨i, hi, rfl⟩
  exact Finset.mem_image.mpr ⟨i, hst hi, Eq.refl _⟩

/-- Every basis index `i ∈ s` contributes its cyclotomic degree to `stageCyclotomicDegreeSet s`. -/
theorem basisJK_stage_degree_mem
    (s : Finset (Option ℤ)) (i : Option ℤ) (hi : i ∈ s) :
    heisenbergBasisCyclotomicDegree i ∈ stageCyclotomicDegreeSet s := by
  unfold stageCyclotomicDegreeSet
  exact Finset.mem_image.mpr ⟨i, hi, Eq.refl _⟩

/-- The index-to-degree readout is continuous for the discrete index topology. -/
theorem continuous_heisenbergBasisCyclotomicDegree :
    Continuous heisenbergBasisCyclotomicDegree := by
  unfold heisenbergBasisCyclotomicDegree
  exact continuous_of_discreteTopology

/-- The index-to-degree readout is locally constant for the discrete index topology. -/
theorem isLocallyConstant_heisenbergBasisCyclotomicDegree :
    IsLocallyConstant heisenbergBasisCyclotomicDegree := by
  intro s
  exact isOpen_discrete _

end
end InfoGeometry.Topology.HeisenbergFiniteModeCyclotomicTopological
