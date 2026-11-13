/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

/-!
# Finite Gabor frame and Gram operators over a noncommutative star ring

For a finite family `φ : Fin m → B` in an associative coefficient ring, this
file defines its frame operator `∑ φᵢ φᵢ⋆` and Gram matrix
`(φᵢ⋆ φⱼ)`.  The identities are algebraic and do not assert positivity or
analytic frame bounds.  In particular, the Parseval hypothesis below is an
explicit equality in `B`.
-/

namespace InfoGeometry.OperatorAlgebra.NoncommutativeGaborFrame

open Matrix

variable {B : Type*} [Ring B] [StarRing B] {m : ℕ}

/-- The finite-family frame operator `∑ᵢ φᵢ φᵢ⋆` in the coefficient ring. -/
def frameOperator (φ : Fin m → B) : B :=
  ∑ i : Fin m, φ i * star (φ i)

/-- The finite-family multiplier with operator-valued symbol `b`. -/
def gaborMultiplier (φ b : Fin m → B) : B :=
  ∑ i : Fin m, φ i * b i * star (φ i)

/-- The Gram matrix with `(i,j)` entry `φᵢ⋆ φⱼ`. -/
def gramMatrix (φ : Fin m → B) : Matrix (Fin m) (Fin m) B :=
  Matrix.of fun i j => star (φ i) * φ j

/-- The frame operator is self-adjoint. -/
theorem frameOperator_isSelfAdjoint (φ : Fin m → B) :
    star (frameOperator φ) = frameOperator φ := by
  simp [frameOperator, star_sum, star_mul]

/-- Adjointing a multiplier adjoints its symbol, preserving the order of
the noncommuting coefficient factors. -/
theorem gaborMultiplier_star (φ b : Fin m → B) :
    star (gaborMultiplier φ b) = gaborMultiplier φ (fun i => star (b i)) := by
  simp [gaborMultiplier, star_sum, star_mul, mul_assoc]

/-- Complementary symbols sum to the frame operator. -/
theorem gaborMultiplier_complement (φ b : Fin m → B) :
    gaborMultiplier φ b + gaborMultiplier φ (fun i => 1 - b i) =
      frameOperator φ := by
  simp only [gaborMultiplier, frameOperator, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  noncomm_ring

/-- The Gram matrix is self-adjoint over any star ring. -/
theorem gramMatrix_isSelfAdjoint (φ : Fin m → B) :
    (gramMatrix φ)ᴴ = gramMatrix φ := by
  ext i j
  simp [gramMatrix, star_mul]

/-- The square of the Gram matrix records the frame operator between its
two family elements.  No commutativity of `B` is assumed. -/
theorem gramMatrix_sq_apply (φ : Fin m → B) (i j : Fin m) :
    (gramMatrix φ * gramMatrix φ) i j =
      star (φ i) * frameOperator φ * φ j := by
  rw [Matrix.mul_apply]
  change (∑ k : Fin m, (star (φ i) * φ k) * (star (φ k) * φ j)) = _
  calc
    (∑ k : Fin m, (star (φ i) * φ k) * (star (φ k) * φ j))
        = ∑ k : Fin m, star (φ i) * (φ k * star (φ k)) * φ j := by
            apply Finset.sum_congr rfl
            intro k hk
            simp only [mul_assoc]
    _ = star (φ i) * (∑ k : Fin m, φ k * star (φ k)) * φ j := by
          simp only [Finset.mul_sum, Finset.sum_mul]

/-- A Parseval family has an idempotent Gram matrix. -/
theorem gramMatrix_idempotent_of_parseval {φ : Fin m → B}
    (hφ : frameOperator φ = 1) :
    gramMatrix φ * gramMatrix φ = gramMatrix φ := by
  ext i j
  rw [gramMatrix_sq_apply, hφ, mul_one]
  rfl

/-- Thus a Parseval Gram matrix is a self-adjoint idempotent. -/
theorem gramMatrix_projection_of_parseval {φ : Fin m → B}
    (hφ : frameOperator φ = 1) :
    (gramMatrix φ)ᴴ = gramMatrix φ ∧
      gramMatrix φ * gramMatrix φ = gramMatrix φ :=
  ⟨gramMatrix_isSelfAdjoint φ, gramMatrix_idempotent_of_parseval hφ⟩

end InfoGeometry.OperatorAlgebra.NoncommutativeGaborFrame
