/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.PeirceCompressionDefect
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Topology.MetricSpace.Basic

/-!
# Coordinate compression and finite propagation

A finite coordinate cut is the native diagonal matrix of its indicator.
The compression defect is the ordered sum over two-step paths whose middle
coordinate lies outside the cut. Finite propagation adds under matrix
multiplication, and the exterior return vanishes at points farther than the
propagation radius from every omitted coordinate.

The proofs use matrix multiplication and the triangle inequality. They do
not provide a localization norm estimate depending on the volume or radius
of a large region.
-/

namespace InfoGeometry.OperatorAlgebra.FinitePropagationCompression

open InfoGeometry.Core.PeirceCompressionDefect
open scoped BigOperators Matrix

section CoordinateCut

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- The actual matrix projection onto a finite set of coordinate vectors. -/
def coordinateProjection (s : Finset ι) : Matrix ι ι R :=
  Matrix.diagonal (fun i => if i ∈ s then 1 else 0)

@[simp] theorem coordinateProjection_mul_self (s : Finset ι) :
    coordinateProjection (R := R) s * coordinateProjection (R := R) s =
      coordinateProjection (R := R) s := by
  unfold coordinateProjection
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hi : i ∈ s <;> simp [hi]

/-- The complementary cut is the projection onto the complementary coordinates. -/
theorem one_sub_coordinateProjection (s : Finset ι) :
    1 - coordinateProjection (R := R) s = coordinateProjection (R := R) sᶜ := by
  rw [coordinateProjection, coordinateProjection, ← Matrix.diagonal_one,
    Matrix.diagonal_sub]
  congr 1
  funext i
  by_cases hi : i ∈ s <;> simp [hi]

@[simp] theorem coordinateProjection_mul_apply (s : Finset ι) (a : Matrix ι ι R)
    (i j : ι) :
    (coordinateProjection (R := R) s * a) i j = if i ∈ s then a i j else 0 := by
  by_cases hi : i ∈ s <;> simp [coordinateProjection, Matrix.diagonal_mul, hi]

@[simp] theorem mul_coordinateProjection_apply (s : Finset ι) (a : Matrix ι ι R)
    (i j : ι) :
    (a * coordinateProjection (R := R) s) i j = if j ∈ s then a i j else 0 := by
  by_cases hj : j ∈ s <;> simp [coordinateProjection, Matrix.mul_diagonal, hj]

/-- A coordinate compression retains exactly the entries with both endpoints inside. -/
theorem coordinate_compression_apply (s : Finset ι) (a : Matrix ι ι R) (i j : ι) :
    (coordinateProjection (R := R) s * a * coordinateProjection (R := R) s) i j =
      if i ∈ s ∧ j ∈ s then a i j else 0 := by
  by_cases hi : i ∈ s <;> by_cases hj : j ∈ s <;> simp [hi, hj]

variable [StarRing R]

omit [Fintype ι] in
@[simp] theorem star_coordinateProjection (s : Finset ι) :
    star (coordinateProjection (R := R) s) = coordinateProjection (R := R) s := by
  change (coordinateProjection (R := R) s)ᴴ = coordinateProjection (R := R) s
  simp only [coordinateProjection, Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  by_cases hi : i ∈ s <;> simp [hi]

end CoordinateCut

section Collar

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- Every exterior return follows an ordered two-step path through an omitted
coordinate. This statement preserves multiplication order even for noncommutative scalars. -/
theorem exterior_return_apply (s : Finset ι) (a b : Matrix ι ι R)
    (i j : ι) (hi : i ∈ s) (hj : j ∈ s) :
    (coordinateProjection (R := R) s * a * (1 - coordinateProjection (R := R) s) * b *
        coordinateProjection (R := R) s) i j =
      ∑ k ∈ sᶜ, a i k * b k j := by
  rw [one_sub_coordinateProjection, mul_coordinateProjection_apply, ite_eq_left hj,
    Matrix.mul_apply]
  simp only [mul_coordinateProjection_apply, coordinateProjection_mul_apply,
    ite_eq_left hi, ite_mul, zero_mul]
  exact Finset.sum_ite_mem_eq sᶜ (fun k => a i k * b k j)

/-- Squaring after the cut omits exactly the two-step paths that leave the cut. -/
theorem square_compression_defect_apply (s : Finset ι) (a : Matrix ι ι R)
    (i j : ι) (hi : i ∈ s) (hj : j ∈ s) :
    (coordinateProjection (R := R) s * (a * a) * coordinateProjection (R := R) s -
        (coordinateProjection (R := R) s * a * coordinateProjection (R := R) s) *
          (coordinateProjection (R := R) s * a * coordinateProjection (R := R) s)) i j =
      ∑ k ∈ sᶜ, a i k * a k j := by
  rw [compression_mul_defect _ a a (coordinateProjection_mul_self s)]
  exact exterior_return_apply s a a i j hi hj

end Collar

section Propagation

variable {ι R X : Type*} [Fintype ι] [Ring R]
variable [PseudoMetricSpace X]

/-- Entries vanish beyond the given radius, measured at the coordinate locations. -/
def HasPropagationAtMost (position : ι → X) (radius : ℝ) (a : Matrix ι ι R) : Prop :=
  ∀ i j, radius < dist (position i) (position j) → a i j = 0

/-- The radius of a matrix product is at most the sum of the two radii. -/
theorem HasPropagationAtMost.mul {position : ι → X} {r t : ℝ}
    {a b : Matrix ι ι R} (ha : HasPropagationAtMost position r a)
    (hb : HasPropagationAtMost position t b) :
    HasPropagationAtMost position (r + t) (a * b) := by
  intro i j hfar
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : r < dist (position i) (position k)
  · rw [ha i k hik, zero_mul]
  · have hkj : t < dist (position k) (position j) := by
      by_contra hnot
      have htriangle := dist_triangle (position i) (position k) (position j)
      have hsum := add_le_add (le_of_not_gt hik) (le_of_not_gt hnot)
      exact (not_lt_of_ge (htriangle.trans hsum)) hfar
    rw [hb k j hkj, mul_zero]

/-- A two-step matrix path has radius at most twice the original radius. -/
theorem HasPropagationAtMost.square {position : ι → X} {r : ℝ}
    {a : Matrix ι ι R} (ha : HasPropagationAtMost position r a) :
    HasPropagationAtMost position (2 * r) (a * a) := by
  simpa only [two_mul] using ha.mul ha

variable [DecidableEq ι]

/-- Removing coordinates cannot enlarge the propagation radius. -/
theorem HasPropagationAtMost.coordinate_compression {position : ι → X} {r : ℝ}
    {a : Matrix ι ι R} (ha : HasPropagationAtMost position r a) (s : Finset ι) :
    HasPropagationAtMost position r
      (coordinateProjection (R := R) s * a * coordinateProjection (R := R) s) := by
  intro i j hfar
  rw [coordinate_compression_apply, ha i j hfar]
  simp

/-- The exterior return is zero in a row that cannot reach any omitted coordinate
in one propagation step. No estimate on the second operator is required. -/
theorem exterior_return_apply_eq_zero_of_deepInterior
    {position : ι → X} {r : ℝ} {a : Matrix ι ι R}
    (ha : HasPropagationAtMost position r a) (s : Finset ι) (b : Matrix ι ι R)
    (i j : ι) (hi : i ∈ s) (hj : j ∈ s)
    (hdeep : ∀ k, k ∉ s → r < dist (position i) (position k)) :
    (coordinateProjection (R := R) s * a * (1 - coordinateProjection (R := R) s) * b *
        coordinateProjection (R := R) s) i j = 0 := by
  rw [exterior_return_apply s a b i j hi hj]
  apply Finset.sum_eq_zero
  intro k hk
  rw [ha i k (hdeep k (Finset.mem_compl.mp hk)), zero_mul]

end Propagation

end InfoGeometry.OperatorAlgebra.FinitePropagationCompression
