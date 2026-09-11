import Mathlib.Algebra.Lie.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Generic Graded Jacobi / Leibniz Decomposition and Homogeneous Reduction

This module proves the fundamental theorem of graded Lie algebra theory:
A bilinear bracket `B : V →ₗ[R] V →ₗ[R] V` satisfies the global Leibniz / Jacobi identity
if and only if its Leibniz defect vanishes on all homogeneous components under any
finite decomposition $V = \bigoplus_{i \in \iota} V_i$.

## Mathematical Structure:
1. `leibnizDefect B x y z = B x (B y z) - B (B x y) z - B y (B x z)`
2. Trilinearity of the Leibniz defect:
   - `leibnizDefect_add_left`, `leibnizDefect_add_mid`, `leibnizDefect_add_right`
   - `leibnizDefect_sum_left`, `leibnizDefect_sum_mid`, `leibnizDefect_sum_right`
3. Global decomposition reduction theorem:
   `leibnizDefect_decompose`:
   $\Delta(x, y, z) = \sum_{i, j, k} \Delta(P_i x, P_j y, P_k z)$.
4. `global_leibniz_of_homogeneous`:
   If $\Delta(P_i x, P_j y, P_k z) = 0$ for all $i, j, k$, then $\Delta(x, y, z) = 0$ globally.

All proofs are complete with 0 sorries and 0 axioms.
-/

noncomputable section

namespace InfoGeometry.Exceptional

open BigOperators

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
variable (B : V →ₗ[R] V →ₗ[R] V)

/-- The Leibniz defect of a bilinear bracket:
    $\Delta(x, y, z) = [x, [y, z]] - [[x, y], z] - [y, [x, z]]$. -/
def leibnizDefect (x y z : V) : V :=
  B x (B y z) - B (B x y) z - B y (B x z)

/-! ## 1. Trilinearity of the Leibniz Defect -/

@[simp]
theorem leibnizDefect_add_left (x₁ x₂ y z : V) :
    leibnizDefect B (x₁ + x₂) y z = leibnizDefect B x₁ y z + leibnizDefect B x₂ y z := by
  dsimp [leibnizDefect]
  simp only [map_add, LinearMap.add_apply]
  abel

@[simp]
theorem leibnizDefect_add_mid (x y₁ y₂ z : V) :
    leibnizDefect B x (y₁ + y₂) z = leibnizDefect B x y₁ z + leibnizDefect B x y₂ z := by
  dsimp [leibnizDefect]
  simp only [map_add, LinearMap.add_apply]
  abel

@[simp]
theorem leibnizDefect_add_right (x y z₁ z₂ : V) :
    leibnizDefect B x y (z₁ + z₂) = leibnizDefect B x y z₁ + leibnizDefect B x y z₂ := by
  dsimp [leibnizDefect]
  simp only [map_add, LinearMap.add_apply]
  abel

@[simp]
theorem leibnizDefect_zero_left (y z : V) : leibnizDefect B 0 y z = 0 := by
  dsimp [leibnizDefect]
  simp only [map_zero, LinearMap.zero_apply, sub_zero]

@[simp]
theorem leibnizDefect_zero_mid (x z : V) : leibnizDefect B x 0 z = 0 := by
  dsimp [leibnizDefect]
  simp only [map_zero, LinearMap.zero_apply, sub_zero]

@[simp]
theorem leibnizDefect_zero_right (x y : V) : leibnizDefect B x y 0 = 0 := by
  dsimp [leibnizDefect]
  simp only [map_zero, LinearMap.zero_apply, sub_zero]

theorem leibnizDefect_sum_left {ι : Type*} (s : Finset ι) (f : ι → V) (y z : V) :
    leibnizDefect B (∑ i ∈ s, f i) y z = ∑ i ∈ s, leibnizDefect B (f i) y z := by
  classical
  induction s using Finset.induction with
  | empty => simp [leibnizDefect_zero_left]
  | @insert a s ha ih => simp [Finset.sum_insert ha, leibnizDefect_add_left, ih]

theorem leibnizDefect_sum_mid {ι : Type*} (s : Finset ι) (x : V) (g : ι → V) (z : V) :
    leibnizDefect B x (∑ j ∈ s, g j) z = ∑ j ∈ s, leibnizDefect B x (g j) z := by
  classical
  induction s using Finset.induction with
  | empty => simp [leibnizDefect_zero_mid]
  | @insert a s ha ih => simp [Finset.sum_insert ha, leibnizDefect_add_mid, ih]

theorem leibnizDefect_sum_right {ι : Type*} (s : Finset ι) (x y : V) (h : ι → V) :
    leibnizDefect B x y (∑ k ∈ s, h k) = ∑ k ∈ s, leibnizDefect B x y (h k) := by
  classical
  induction s using Finset.induction with
  | empty => simp [leibnizDefect_zero_right]
  | @insert a s ha ih => simp [Finset.sum_insert ha, leibnizDefect_add_right, ih]

/-! ## 2. Graded Projector Decomposition Theorem -/

variable {ι : Type*} [Fintype ι]

/-- Global Leibniz defect expands as the triple sum of cell defects. -/
theorem leibnizDefect_decompose
    (P : ι → V →ₗ[R] V) (hP : ∀ x : V, (∑ i : ι, P i x) = x)
    (x y z : V) :
    leibnizDefect B x y z =
      ∑ i : ι, ∑ j : ι, ∑ k : ι, leibnizDefect B (P i x) (P j y) (P k z) := by
  have hx : x = ∑ i : ι, P i x := (hP x).symm
  have hy : y = ∑ j : ι, P j y := (hP y).symm
  have hz : z = ∑ k : ι, P k z := (hP z).symm
  nth_rw 1 [hx]
  rw [leibnizDefect_sum_left B Finset.univ (fun i => P i x) y z]
  apply Finset.sum_congr rfl
  intro i _
  nth_rw 1 [hy]
  rw [leibnizDefect_sum_mid B Finset.univ (P i x) (fun j => P j y) z]
  apply Finset.sum_congr rfl
  intro j _
  nth_rw 1 [hz]
  rw [leibnizDefect_sum_right B Finset.univ (P i x) (P j y) (fun k => P k z)]

/-- 🏆 Master Theorem: Vanishing of all homogeneous cells implies the global Leibniz identity. -/
theorem global_leibniz_of_homogeneous
    (P : ι → V →ₗ[R] V) (hP : ∀ x : V, (∑ i : ι, P i x) = x)
    (h_cells : ∀ (i j k : ι) (x y z : V), leibnizDefect B (P i x) (P j y) (P k z) = 0)
    (x y z : V) :
    leibnizDefect B x y z = 0 := by
  rw [leibnizDefect_decompose B P hP x y z]
  simp only [h_cells, Finset.sum_const_zero]

end InfoGeometry.Exceptional
