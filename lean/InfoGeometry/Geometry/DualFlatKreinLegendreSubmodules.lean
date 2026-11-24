/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Geometry.DualFlatKreinLegendreGraph
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Prod

/-!
# Orthogonal complements of primal, dual, and symmetric graphs

This file uses the existing evaluation-paired carrier `V × Module.Dual ℝ V`,
its neutral bilinear form, and its skew bilinear form. Graphs and coordinate
planes are native Mathlib submodules. A symmetric duality graph equals its
symplectic orthogonal complement; its neutral orthogonal complement is the
graph of the negative duality map. The coordinate planes are self-orthogonal
for both forms. These are linear statements, with no manifold construction.
-/

namespace InfoGeometry.Geometry.DualFlatKreinLegendreGraph

open InfoGeometry.Clifford.NeutralPhaseSpaceCore

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Symmetry of a duality map makes its native graph self-orthogonal for the
canonical symplectic form. This includes maximality, not only isotropy. -/
theorem neutralOmega_orthogonal_graph
    (L : V →ₗ[ℝ] Module.Dual ℝ V) (hL : IsSymmetricDuality L) :
    (neutralOmega (E := V)).orthogonal L.graph = L.graph := by
  ext X
  change (∀ Y ∈ L.graph, neutralOmega Y X = 0) ↔ X.2 = L X.1
  constructor
  · intro hX
    apply LinearMap.ext
    intro v
    have h := hX (graphLift L v) (by simp [graphLift])
    have hv : X.2 v - (L v) X.1 = 0 := by
      simpa [neutralOmega_apply, graphLift] using h
    rw [hL v X.1] at hv
    exact sub_eq_zero.mp hv
  · intro hX Y hY
    change Y.2 = L Y.1 at hY
    rw [neutralOmega_apply, hX, hY, hL Y.1 X.1]
    exact sub_self _

/-- For the neutral metric, the orthogonal complement of a symmetric graph
has the opposite sign. A nonzero symmetric graph need not be neutral-null. -/
theorem canonicalNeutralBilin_orthogonal_graph
    (L : V →ₗ[ℝ] Module.Dual ℝ V) (hL : IsSymmetricDuality L) :
    (canonicalNeutralBilin (E := V)).orthogonal L.graph = (-L).graph := by
  ext X
  change (∀ Y ∈ L.graph, canonicalNeutralBilin Y X = 0) ↔ X.2 = (-L) X.1
  constructor
  · intro hX
    apply LinearMap.ext
    intro v
    change X.2 v = -((L X.1) v)
    have h := hX (graphLift L v) (by simp [graphLift])
    have hv : (L v) X.1 + X.2 v = 0 := by
      simpa [canonicalNeutralBilin_apply, graphLift] using h
    rw [hL v X.1] at hv
    linarith
  · intro hX Y hY
    change Y.2 = L Y.1 at hY
    rw [canonicalNeutralBilin_apply, hY, hX]
    change (L Y.1) X.1 + -((L X.1) Y.1) = 0
    rw [hL Y.1 X.1]
    exact add_neg_cancel _

/-- The primal coordinate plane is a symplectic Lagrangian submodule. -/
theorem neutralOmega_orthogonal_primal :
    (neutralOmega (E := V)).orthogonal
        ((⊤ : Submodule ℝ V).prod (⊥ : Submodule ℝ (Module.Dual ℝ V))) =
      (⊤ : Submodule ℝ V).prod (⊥ : Submodule ℝ (Module.Dual ℝ V)) := by
  have hzero : (0 : V →ₗ[ℝ] Module.Dual ℝ V).graph =
      (⊤ : Submodule ℝ V).prod (⊥ : Submodule ℝ (Module.Dual ℝ V)) := by
    ext X
    simp
  simpa only [hzero] using
    neutralOmega_orthogonal_graph (0 : V →ₗ[ℝ] Module.Dual ℝ V)
      (by intro u v; simp)

/-- The primal coordinate plane is maximally isotropic for the neutral form. -/
theorem canonicalNeutralBilin_orthogonal_primal :
    (canonicalNeutralBilin (E := V)).orthogonal
        ((⊤ : Submodule ℝ V).prod (⊥ : Submodule ℝ (Module.Dual ℝ V))) =
      (⊤ : Submodule ℝ V).prod (⊥ : Submodule ℝ (Module.Dual ℝ V)) := by
  have hzero : (0 : V →ₗ[ℝ] Module.Dual ℝ V).graph =
      (⊤ : Submodule ℝ V).prod (⊥ : Submodule ℝ (Module.Dual ℝ V)) := by
    ext X
    simp
  simpa only [neg_zero, hzero] using
    canonicalNeutralBilin_orthogonal_graph (0 : V →ₗ[ℝ] Module.Dual ℝ V)
      (by intro u v; simp)

section DualPlane

variable [Module.Projective ℝ V]

/-- Separation by algebraic covectors makes the dual coordinate plane equal
to its symplectic orthogonal complement. -/
theorem neutralOmega_orthogonal_dual :
    (neutralOmega (E := V)).orthogonal
        ((⊥ : Submodule ℝ V).prod (⊤ : Submodule ℝ (Module.Dual ℝ V))) =
      (⊥ : Submodule ℝ V).prod (⊤ : Submodule ℝ (Module.Dual ℝ V)) := by
  ext X
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro hX
    have hx : X.1 = 0 := by
      apply (Module.forall_dual_apply_eq_zero_iff ℝ X.1).mp
      intro φ
      have h := hX (0, φ) (by simp)
      have hneg : -(φ X.1) = 0 := by
        simpa [neutralOmega_apply] using h
      exact neg_eq_zero.mp hneg
    simpa using hx
  · intro hX Y hY
    have hx : X.1 = 0 := by simpa using hX
    have hy : Y.1 = 0 := by simpa using hY
    simp [neutralOmega_apply, hx, hy]

/-- The dual coordinate plane is also maximally isotropic for the neutral
form. The hypothesis is the same dual-separation hypothesis as in the core. -/
theorem canonicalNeutralBilin_orthogonal_dual :
    (canonicalNeutralBilin (E := V)).orthogonal
        ((⊥ : Submodule ℝ V).prod (⊤ : Submodule ℝ (Module.Dual ℝ V))) =
      (⊥ : Submodule ℝ V).prod (⊤ : Submodule ℝ (Module.Dual ℝ V)) := by
  ext X
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro hX
    have hx : X.1 = 0 := by
      apply (Module.forall_dual_apply_eq_zero_iff ℝ X.1).mp
      intro φ
      have h := hX (0, φ) (by simp)
      simpa [canonicalNeutralBilin_apply] using h
    simpa using hx
  · intro hX Y hY
    have hx : X.1 = 0 := by simpa using hX
    have hy : Y.1 = 0 := by simpa using hY
    simp [canonicalNeutralBilin_apply, hx, hy]

end DualPlane

end InfoGeometry.Geometry.DualFlatKreinLegendreGraph
