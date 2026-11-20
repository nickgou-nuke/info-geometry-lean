/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Prod
import InfoGeometry.Clifford.NeutralPhaseSpaceCore
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

/-!
# Dual-flat Legendre graphs in a neutral primal/dual carrier

The carrier is `V × V*`, not two geometric sheets.  The existing neutral
bilinear form is reused.  A symmetric linear duality map supplies the finite
Hessian/Legendre graph; its induced neutral metric is the symmetric duality
pairing and the canonical skew form vanishes on the graph.

Convexity and smooth Legendre theory are intentionally separate assumptions.
-/

namespace InfoGeometry.Geometry.DualFlatKreinLegendreGraph

open InfoGeometry.Clifford.NeutralPhaseSpaceCore

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

abbrev DualCarrier (V : Type*) [AddCommGroup V] [Module ℝ V] :=
  PhaseSpaceCarrier V
abbrev Covector (V : Type*) [AddCommGroup V] [Module ℝ V] :=
  Module.Dual ℝ V

/-- The canonical skew pairing on the primal/dual carrier. -/
def canonicalSymplectic (X Y : DualCarrier V) : ℝ :=
  Y.2 X.1 - X.2 Y.1

/-- The normalized neutral pairing used for the primal/dual graph metric. -/
noncomputable def normalizedNeutralPairing (X Y : DualCarrier V) : ℝ :=
  (1 / 2 : ℝ) * canonicalNeutralBilin X Y

/-- Primal/dual grading of the neutral carrier. -/
def primalDualGrading (X : DualCarrier V) : DualCarrier V :=
  (X.1, -X.2)

/-- A linear duality map is symmetric when it defines a Hessian pairing. -/
def IsSymmetricDuality (L : V →ₗ[ℝ] Covector V) : Prop :=
  ∀ u v, (L u) v = (L v) u

/-- Tangent lift of a primal vector to the graph of a duality map. -/
def graphLift (L : V →ₗ[ℝ] Covector V) (u : V) : DualCarrier V :=
  (u, L u)

theorem neutralPairing_symmetric (X Y : DualCarrier V) :
    normalizedNeutralPairing X Y = normalizedNeutralPairing Y X := by
  unfold normalizedNeutralPairing
  rw [canonicalNeutralBilin_apply, canonicalNeutralBilin_apply]
  ring

theorem canonicalSymplectic_skew (X Y : DualCarrier V) :
    canonicalSymplectic X Y = -canonicalSymplectic Y X := by
  unfold canonicalSymplectic
  ring

theorem primal_isotropic (u v : V) :
    normalizedNeutralPairing (u, 0) (v, 0) = 0 := by
  simp [normalizedNeutralPairing, canonicalNeutralBilin_apply]

theorem dual_isotropic (α β : Covector V) :
    normalizedNeutralPairing (0, α) (0, β) = 0 := by
  simp [normalizedNeutralPairing, canonicalNeutralBilin_apply]

theorem grading_squared (X : DualCarrier V) :
    primalDualGrading (primalDualGrading X) = X := by
  rcases X with ⟨u, α⟩
  simp [primalDualGrading]

theorem graph_neutral_pairing
    (L : V →ₗ[ℝ] Covector V)
    (hL : IsSymmetricDuality L)
    (u v : V) :
    normalizedNeutralPairing (graphLift L u) (graphLift L v) = (L u) v := by
  unfold normalizedNeutralPairing
  rw [canonicalNeutralBilin_apply]
  dsimp [graphLift]
  rw [hL u v]
  ring

theorem graph_symplectic_isotropic
    (L : V →ₗ[ℝ] Covector V)
    (hL : IsSymmetricDuality L)
    (u v : V) :
    canonicalSymplectic (graphLift L u) (graphLift L v) = 0 := by
  unfold canonicalSymplectic graphLift
  rw [hL u v]
  ring

theorem graph_is_lagrangian_in_finite_pairing_sense
    (L : V →ₗ[ℝ] Covector V)
    (hL : IsSymmetricDuality L)
    (u v : V) :
    canonicalSymplectic (graphLift L u) (graphLift L v) = 0 :=
  graph_symplectic_isotropic L hL u v


/-- The symplectic orthogonal of a linear graph is the graph of its
transposed bilinear form.  No symmetry or invertibility is assumed. -/
theorem graph_orthogonal_eq_flip_graph (L : V →ₗ[ℝ] Covector V) :
    L.graph.orthogonalBilin (neutralOmega (E := V)) = L.flip.graph := by
  ext X
  rw [Submodule.mem_orthogonalBilin, LinearMap.mem_graph_iff]
  constructor
  · intro h
    apply LinearMap.ext
    intro v
    have hv := h (v, L v) (by rfl)
    simpa only [neutralOmega_apply, sub_eq_zero, LinearMap.flip_apply] using hv
  · intro h Y hY
    change Y.2 = L Y.1 at hY
    simp only [neutralOmega_apply, hY, h, LinearMap.flip_apply, sub_self]

/-- A graph equals its own symplectic orthogonal exactly when its defining
bilinear form is symmetric. -/
theorem graph_self_orthogonal_iff_symmetric (L : V →ₗ[ℝ] Covector V) :
    L.graph.orthogonalBilin (neutralOmega (E := V)) = L.graph ↔
      IsSymmetricDuality L := by
  rw [graph_orthogonal_eq_flip_graph]
  constructor
  · intro h u v
    have hu : (u, L u) ∈ L.flip.graph := by
      rw [h]
      rfl
    change L u = L.flip u at hu
    exact LinearMap.congr_fun hu v
  · intro h
    ext X
    simp only [LinearMap.mem_graph_iff]
    have hflip : L.flip X.1 = L X.1 := by
      apply LinearMap.ext
      intro v
      exact h v X.1
    rw [hflip]

/-- Every isotropic submodule containing a symmetric graph is that graph.
This is maximal isotropy, beyond the existing pairwise-vanishing theorem. -/
theorem graph_maximal_isotropic_of_symmetric
    (L : V →ₗ[ℝ] Covector V) (hL : IsSymmetricDuality L)
    (S : Submodule ℝ (DualCarrier V)) (hgraph : L.graph ≤ S)
    (hS : S ≤ S.orthogonalBilin (neutralOmega (E := V))) :
    S = L.graph := by
  apply le_antisymm _ hgraph
  calc
    S ≤ S.orthogonalBilin (neutralOmega (E := V)) := hS
    _ ≤ L.graph.orthogonalBilin (neutralOmega (E := V)) :=
      Submodule.orthogonalBilin_le hgraph
    _ = L.graph := (graph_self_orthogonal_iff_symmetric L).mpr hL

end InfoGeometry.Geometry.DualFlatKreinLegendreGraph
