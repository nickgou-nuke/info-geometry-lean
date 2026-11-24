/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# Finite incidence curvature and rectangular Stokes identities

The first result is an incidence-counting identity with explicit column-sum
hypotheses. Its alternating count becomes a surface Euler characteristic only
after a separate realization as a finite cell complex.

The second result is exact cancellation of interior edges on a finite
rectangular grid. Its coefficients may lie in any additive commutative group,
including a noncommutative real matrix algebra under addition. No smooth
manifold, analytic Stokes theorem, curvature form or heat kernel is inferred.
-/

open scoped BigOperators

namespace InfoGeometry.Canonical.FiniteIncidenceGaussBonnetStokes

/-- Local normalized incidence defect. The incidence weights and face sizes
are supplied explicitly. -/
noncomputable def vertexCurvature {V E F : Type*} [Fintype E] [Fintype F]
    (edgeInc : V → E → ℝ) (faceInc : V → F → ℝ) (faceCard : F → ℝ)
    (v : V) : ℝ :=
  1 - (1 / 2 : ℝ) * (∑ e : E, edgeInc v e) +
    ∑ f : F, faceInc v f / faceCard f

/-- Double-counting each edge twice and each face with total normalized
weight one gives the alternating vertex/edge/face count. -/
theorem incidence_curvature_sum
    {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
    (edgeInc : V → E → ℝ) (faceInc : V → F → ℝ) (faceCard : F → ℝ)
    (hFaceNe : ∀ f, faceCard f ≠ 0)
    (hEdge : ∀ e, (∑ v : V, edgeInc v e) = 2)
    (hFace : ∀ f, (∑ v : V, faceInc v f) = faceCard f) :
    (∑ v : V, vertexCurvature edgeInc faceInc faceCard v) =
      (Fintype.card V : ℝ) - (Fintype.card E : ℝ) + (Fintype.card F : ℝ) := by
  classical
  have hEdges : (∑ v : V, ∑ e : E, edgeInc v e) =
      2 * (Fintype.card E : ℝ) := by
    rw [Finset.sum_comm]
    simp [hEdge, mul_comm]
  have hFaces : (∑ v : V, ∑ f : F, faceInc v f / faceCard f) =
      (Fintype.card F : ℝ) := by
    have hEach (f : F) : (∑ v : V, faceInc v f / faceCard f) = 1 := by
      rw [← Finset.sum_div, hFace f, div_self (hFaceNe f)]
    rw [Finset.sum_comm]
    simp [hEach]
  calc
    (∑ v : V, vertexCurvature edgeInc faceInc faceCard v) =
        (∑ _v : V, (1 : ℝ)) -
          (1 / 2 : ℝ) * (∑ v : V, ∑ e : E, edgeInc v e) +
          (∑ v : V, ∑ f : F, faceInc v f / faceCard f) := by
      simp [vertexCurvature, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, Finset.mul_sum]
    _ = (Fintype.card V : ℝ) -
          (1 / 2 : ℝ) * (2 * (Fintype.card E : ℝ)) +
          (Fintype.card F : ℝ) := by
      rw [hEdges, hFaces]
      simp
    _ = (Fintype.card V : ℝ) - (Fintype.card E : ℝ) +
          (Fintype.card F : ℝ) := by ring

/-- Oriented bottom-minus-top plus right-minus-left circulation of one cell. -/
def cellCirculation {G : Type*} [AddCommGroup G]
    (horizontal vertical : ℕ → ℕ → G) (i j : ℕ) : G :=
  (horizontal i j - horizontal i (j + 1)) +
    (vertical (i + 1) j - vertical i j)

/-- The cell sum on an `M × N` rectangle is its boundary circulation,
including the zero-width and zero-height cases. -/
theorem rectangular_stokes {G : Type*} [AddCommGroup G]
    (horizontal vertical : ℕ → ℕ → G) (M N : ℕ) :
    (∑ i ∈ Finset.range M, ∑ j ∈ Finset.range N,
      cellCirculation horizontal vertical i j) =
      (∑ i ∈ Finset.range M, (horizontal i 0 - horizontal i N)) +
      (∑ j ∈ Finset.range N, (vertical M j - vertical 0 j)) := by
  unfold cellCirculation
  simp_rw [Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    exact Finset.sum_range_sub' (horizontal i) N
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    exact Finset.sum_range_sub (fun i => vertical i j) M

/-- An exact edge difference has zero circulation on each cell. -/
theorem cellCirculation_exact {G : Type*} [AddCommGroup G]
    (potential : ℕ → ℕ → G) (i j : ℕ) :
    cellCirculation
      (fun a b => potential (a + 1) b - potential a b)
      (fun a b => potential a (b + 1) - potential a b) i j = 0 := by
  dsimp only [cellCirculation]
  abel

end InfoGeometry.Canonical.FiniteIncidenceGaussBonnetStokes
