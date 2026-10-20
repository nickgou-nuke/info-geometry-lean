/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.SuperGrassmannian.KantorTanakaSuperGrassmannian
import InfoGeometry.Algebra.SupergradedBracket
import InfoGeometry.SuperGrassmannian.RealSuperGrassmannianOperatorBlocks
import InfoGeometry.SuperGrassmannian.GradedBracketComparison

/-!
# Superbracket covariance of the finite Kantor--Tanaka sheet swap

The Kantor--Tanaka owner proves covariance of the ordinary matrix commutator
under `X ↦ J X J`.  The parity-aware bracket has a separate odd--odd channel,
so its covariance is a genuinely stronger compatibility statement.
-/

namespace InfoGeometry.SuperGrassmannian.KantorTanakaSuperGrassmannian

open InfoGeometry.Algebra.SupergradedBracket

variable {R : Type*} [CommRing R]

private def matI : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => if i = 0 ∧ j = 1 then 1 else 0

private def matJ : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => if i = 1 ∧ j = 0 then 1 else 0

/-- Concrete matrix units witness that the matrix carrier is noncommutative. -/
theorem explicit_matrix_noncommutativity_witness :
    matI * matJ ≠ matJ * matI := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 0) h
  have h11 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 1 1) h
  simp [matI, matJ, Matrix.mul_apply, Fin.sum_univ_three] at h00 h11

/-- Bilateral conjugation by the involution `J` preserves matrix products. -/
private theorem swap_mul (X Y : Matrix (Fin 3) (Fin 3) R) :
    swap (X * Y) = swap X * swap Y := by
  unfold swap
  have hJ : (J R) * (J R) = 1 := J_involutive
  calc
    (J R) * (X * Y) * (J R) =
        (J R) * X * ((J R) * (J R)) * Y * (J R) := by
      simp only [hJ, mul_one, one_mul]
      noncomm_ring
    _ = ((J R) * X * (J R)) * ((J R) * Y * (J R)) := by
      noncomm_ring

/-- Bilateral conjugation by the involution `J` preserves sums. -/
private theorem swap_add (X Y : Matrix (Fin 3) (Fin 3) R) :
    swap (X + Y) = swap X + swap Y := by
  unfold swap
  noncomm_ring

/-- The finite Kantor--Tanaka sheet swap preserves the full parity-aware
superbracket, including its odd--odd anticommutator channel. -/
theorem swap_superBracket_covariant (p q : Bool)
    (X Y : Matrix (Fin 3) (Fin 3) R) :
    swap (superBracket p q X Y) =
      superBracket p q (swap X) (swap Y) := by
  cases p <;> cases q
  · change swap (commutator X Y) = commutator (swap X) (swap Y)
    exact J_lie_automorphism X Y
  · change swap (commutator X Y) = commutator (swap X) (swap Y)
    exact J_lie_automorphism X Y
  · change swap (commutator X Y) = commutator (swap X) (swap Y)
    exact J_lie_automorphism X Y
  · change swap (anticommutator X Y) = anticommutator (swap X) (swap Y)
    unfold anticommutator
    rw [swap_add, swap_mul, swap_mul]

end InfoGeometry.SuperGrassmannian.KantorTanakaSuperGrassmannian
