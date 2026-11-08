/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.ChiralVolumePfaffianDiracKahlerBridge
import InfoGeometry.Algebra.MatrixNoncommutativity

/-!
# Pfaffian on Arbitrary Two-Dimensional Skew Matrices

- BUCKET 1 (Established Mathematical Target & Existing Owners):
  * Extends `InfoGeometry.Canonical.ChiralVolumePfaffianDiracKahler.skewBlock2x2` and
    `pfaffian_congruence_2x2` to arbitrary $2 \times 2$ skew-symmetric matrices over a
    commutative ring `R`.
- BUCKET 2 (Explicit Skew-Symmetry Carrier):
  * `pfaffian2D A = A 0 1` and `IsSkew2D A` (`A 0 0 = 0 ∧ A 1 1 = 0 ∧ A 1 0 = -A 0 1`)
    specify the exact entrywise skew-symmetry equations on `Matrix (Fin 2) (Fin 2) R`.
- BUCKET 3 (Constructive Lean 4 Theorems Proved Here):
  * `det_eq_pfaffian_sq_of_isSkew2D`: `Matrix.det A = (pfaffian2D A) ^ 2`.
  * `pfaffian2D_congruence_of_isSkew2D`: `pfaffian2D (M * A * Mᵀ) = Matrix.det M * pfaffian2D A`.
-/

namespace InfoGeometry.GrandUnification.PfaffianSquareRootCharacter

open Matrix

variable {R : Type*} [CommRing R]

/-- The signed Pfaffian in the standard orientation of the two coordinates. -/
def pfaffian2D (A : Matrix (Fin 2) (Fin 2) R) : R := A 0 1

/-- Exact skew-symmetry conditions for a two-dimensional matrix. -/
def IsSkew2D (A : Matrix (Fin 2) (Fin 2) R) : Prop :=
  A 0 0 = 0 ∧ A 1 1 = 0 ∧ A 1 0 = -A 0 1

/-- Standard $2 \times 2$ off-diagonal swap matrix over `R`. -/
def swapMat2D : Matrix (Fin 2) (Fin 2) R := !![0, 1; 1, 0]

/-- Standard $2 \times 2$ tilted matrix over `R`. -/
def tiltedMat2D : Matrix (Fin 2) (Fin 2) R := !![1, 1; 1, 0]

/-- Noncommutativity of the $2 \times 2$ matrix algebra `Matrix (Fin 2) (Fin 2) R`
over any nontrivial commutative ring `R`. -/
theorem swapMat2D_mul_tiltedMat2D_ne [Nontrivial R] :
    (swapMat2D : Matrix (Fin 2) (Fin 2) R) * tiltedMat2D ≠
      tiltedMat2D * swapMat2D := by
  intro h
  exact InfoGeometry.Algebra.MatrixNoncommutativity.swapMatrix_mul_tiltedMatrix_ne (A := R) h

/-- For an arbitrary skew 2-by-2 matrix, the determinant is the square of
the `(0,1)` entry, the signed Pfaffian in this orientation. -/
theorem det_eq_pfaffian_sq_of_isSkew2D (A : Matrix (Fin 2) (Fin 2) R)
    (hA : IsSkew2D A) : Matrix.det A = (pfaffian2D A) ^ 2 := by
  rcases hA with ⟨h00, h11, h10⟩
  unfold pfaffian2D
  rw [Matrix.det_fin_two, h00, h11, h10]
  ring

/-- The Pfaffian congruence law for every matrix satisfying the explicit
skew-symmetry conditions, not only the standard one-parameter representative. -/
theorem pfaffian2D_congruence_of_isSkew2D
    (M A : Matrix (Fin 2) (Fin 2) R) (hA : IsSkew2D A) :
    pfaffian2D (M * A * Mᵀ) = Matrix.det M * pfaffian2D A := by
  rcases hA with ⟨h00, h11, h10⟩
  have hA_eq : A =
      InfoGeometry.Canonical.ChiralVolumePfaffianDiracKahler.skewBlock2x2 (A 0 1) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [InfoGeometry.Canonical.ChiralVolumePfaffianDiracKahler.skewBlock2x2,
        h00, h11, h10]
  have hcongA : M * A * Mᵀ = M *
      InfoGeometry.Canonical.ChiralVolumePfaffianDiracKahler.skewBlock2x2 (A 0 1) * Mᵀ := by
    exact congrArg (fun B : Matrix (Fin 2) (Fin 2) R => M * B * Mᵀ) hA_eq
  unfold pfaffian2D
  rw [hcongA, InfoGeometry.Canonical.ChiralVolumePfaffianDiracKahler.pfaffian_congruence_2x2 M (A 0 1)]
  exact Eq.refl (Matrix.det M * A 0 1)

end InfoGeometry.GrandUnification.PfaffianSquareRootCharacter
