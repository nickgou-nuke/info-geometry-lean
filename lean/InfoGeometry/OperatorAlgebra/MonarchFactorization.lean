/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Core.IdempotencyDefect
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Ordered two-stage Monarch matrices and their reshuffled minors

Rows and columns are indexed by `(coarse, fine)`. The right stage fixes the
coarse index and mixes the fine index; the left stage fixes the fine index
and mixes the coarse index. Both stages are native block-diagonal matrices,
with the right stage reindexed by the coordinate swap.

The entry formula holds over an arbitrary, possibly noncommutative semiring.
Only the subsequent scalar-minor obstruction assumes commutative coefficients.
It fixes the output fine index and input coarse index, not an ordinary coarse
block. A four-dimensional controlled-switch example proves failure of closure
under squaring by violating this necessary minor identity.
The same construction also escapes the class under the existing operator
idempotency defect `M * M - M`.
-/

namespace InfoGeometry.OperatorAlgebra.MonarchFactorization

open Matrix
open scoped BigOperators

variable {C F A : Type*}
variable [Fintype C] [Fintype F] [DecidableEq C] [DecidableEq F]

section Semiring

variable [Semiring A]

/-- First mix fine indices inside each coarse block, then coarse indices
inside each fine block. Multiplication is native matrix multiplication. -/
def monarch (L : F → Matrix C C A) (R : C → Matrix F F A) :
    Matrix (C × F) (C × F) A :=
  Matrix.blockDiagonal L * (Matrix.blockDiagonal R).submatrix Prod.swap Prod.swap

/-- The intermediate index is uniquely fixed by the two support constraints.
The factor order remains valid for operator-valued, noncommuting entries. -/
@[simp] theorem monarch_apply (L : F → Matrix C C A) (R : C → Matrix F F A)
    (c d : C) (f g : F) :
    monarch L R (c, f) (d, g) = L f c d * R d f g := by
  simp [monarch, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.blockDiagonal_apply, Matrix.submatrix_apply, mul_ite, ite_mul]

/-- Reversing the two physical stages changes both the sampled indices and
the order of the coefficient product. -/
theorem reversed_stages_apply (L : F → Matrix C C A) (R : C → Matrix F F A)
    (c d : C) (f g : F) :
    ((Matrix.blockDiagonal R).submatrix Prod.swap Prod.swap *
      Matrix.blockDiagonal L) (c, f) (d, g) = R c f g * L g c d := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.blockDiagonal_apply, Matrix.submatrix_apply, mul_ite, ite_mul]

/-- Identity stages give the identity operator; not every square leaves the
two-stage class. -/
theorem monarch_one_one :
    monarch (fun _ : F => (1 : Matrix C C A))
      (fun _ : C => (1 : Matrix F F A)) = 1 := by
  ext ⟨c, f⟩ ⟨d, g⟩
  by_cases hcd : c = d <;> by_cases hfg : f = g <;>
    simp [monarch_apply, Matrix.one_apply, hcd, hfg]

end Semiring

section Commutative

variable [CommRing A]

/-- The rank-one minor is taken after reshuffling: hold `f` and `d` fixed,
and vary `c` and `g`. It is not the minor of an ordinary coarse block. -/
theorem reshuffled_minor_eq_zero (L : F → Matrix C C A) (R : C → Matrix F F A)
    (c₀ c₁ d : C) (f g₀ g₁ : F) :
    monarch L R (c₀, f) (d, g₀) * monarch L R (c₁, f) (d, g₁) -
      monarch L R (c₀, f) (d, g₁) * monarch L R (c₁, f) (d, g₀) = 0 := by
  simp only [monarch_apply]
  apply sub_eq_zero.mpr
  ac_rfl

/-- A single nonzero reshuffled minor obstructs every two-stage
factorization of the stated type. -/
theorem ne_monarch_of_reshuffled_minor_ne_zero (M : Matrix (C × F) (C × F) A)
    (c₀ c₁ d : C) (f g₀ g₁ : F)
    (hminor : M (c₀, f) (d, g₀) * M (c₁, f) (d, g₁) -
      M (c₀, f) (d, g₁) * M (c₁, f) (d, g₀) ≠ 0)
    (L : F → Matrix C C A) (R : C → Matrix F F A) : M ≠ monarch L R := by
  intro h
  subst M
  exact hminor (reshuffled_minor_eq_zero L R c₀ c₁ d f g₀ g₁)

end Commutative

section ControlledSwitch

variable (A) [Semiring A]

/-- A two-point switch controlled by the block label: identity at zero and
coordinate exchange at one. -/
def switchBlocks (b : Fin 2) : Matrix (Fin 2) (Fin 2) A :=
  if b = 0 then 1 else !![0, 1; 1, 0]

/-- This four-dimensional matrix is constructed from the two actual stages.
On basis indices it sends `(c, g)` to `(g, c XOR g)`. -/
def switchMonarch : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A :=
  monarch (switchBlocks A) (switchBlocks A)

variable {A}

/-- The square has the identity two-by-two reshuffled slice at fixed
output fine index zero and input coarse index zero. -/
theorem switchMonarch_square_reshuffled_entries :
    let M := switchMonarch A * switchMonarch A
    M (0, 0) (0, 0) = 1 ∧ M (0, 0) (0, 1) = 0 ∧
      M (1, 0) (0, 0) = 0 ∧ M (1, 0) (0, 1) = 1 := by
  simp [switchMonarch, Matrix.mul_apply, Fintype.sum_prod_type,
    monarch_apply, switchBlocks, Matrix.one_apply]

end ControlledSwitch

section Nonclosure

variable [CommRing A]

/-- An ordinary coarse block can have a nonzero minor even for the identity
Monarch matrix. The reshuffling in `reshuffled_minor_eq_zero` is essential. -/
theorem identity_coarse_minor :
    let M := monarch (fun _ : Fin 2 => (1 : Matrix (Fin 2) (Fin 2) A))
      (fun _ : Fin 2 => (1 : Matrix (Fin 2) (Fin 2) A))
    M (0, 0) (0, 0) * M (0, 1) (0, 1) -
      M (0, 0) (0, 1) * M (0, 1) (0, 0) = 1 := by
  simp [monarch_apply]

/-- The square of this two-stage matrix has a nonzero reshuffled minor. -/
theorem switchMonarch_square_minor :
    let M := switchMonarch A * switchMonarch A
    M (0, 0) (0, 0) * M (1, 0) (0, 1) -
      M (0, 0) (0, 1) * M (1, 0) (0, 0) = 1 := by
  obtain ⟨h00, h01, h10, h11⟩ := switchMonarch_square_reshuffled_entries (A := A)
  simp only [h00, h01, h10, h11, mul_one, zero_mul, sub_zero]

/-- No choice of new left and right blocks refactors this square into the
same two-stage architecture. -/
theorem switchMonarch_square_ne_monarch [Nontrivial A]
    (L R : Fin 2 → Matrix (Fin 2) (Fin 2) A) :
    switchMonarch A * switchMonarch A ≠ monarch L R := by
  apply ne_monarch_of_reshuffled_minor_ne_zero _ 0 1 0 0 0 1
  rw [switchMonarch_square_minor]
  exact one_ne_zero

/-- The existing idempotency defect has the reshuffled slice
`[[-1, 1], [1, 0]]` at fixed output fine index one and input coarse index one. -/
theorem switchMonarch_defect_minor :
    let D := Core.IdempotencyDefect.defect (switchMonarch A)
    D (0, 1) (1, 0) * D (1, 1) (1, 1) -
      D (0, 1) (1, 1) * D (1, 1) (1, 0) = -1 := by
  simp [Core.IdempotencyDefect.defect, switchMonarch, Matrix.sub_apply,
    Matrix.mul_apply, Fintype.sum_prod_type, monarch_apply, switchBlocks,
    Matrix.one_apply]

/-- The quadratic defect of this actual two-stage operator cannot be
represented by another operator with the same two-stage factorization. -/
theorem switchMonarch_defect_ne_monarch [Nontrivial A]
    (L R : Fin 2 → Matrix (Fin 2) (Fin 2) A) :
    Core.IdempotencyDefect.defect (switchMonarch A) ≠ monarch L R := by
  apply ne_monarch_of_reshuffled_minor_ne_zero _ 0 1 1 1 0 1
  rw [switchMonarch_defect_minor]
  exact neg_ne_zero.mpr one_ne_zero

/-- The two-stage class is not closed under squaring, already at size four. -/
theorem exists_monarch_square_not_monarch [Nontrivial A] :
    ∃ L R : Fin 2 → Matrix (Fin 2) (Fin 2) A,
      ∀ L' R' : Fin 2 → Matrix (Fin 2) (Fin 2) A,
        monarch L R * monarch L R ≠ monarch L' R' := by
  refine ⟨switchBlocks A, switchBlocks A, ?_⟩
  exact switchMonarch_square_ne_monarch

end Nonclosure

end InfoGeometry.OperatorAlgebra.MonarchFactorization
