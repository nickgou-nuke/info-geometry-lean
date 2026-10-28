/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic.NoncommRing

/-!
# Native identities in the full matrix operator algebra

These bridges use the associative Lie bracket, native adjoint submodules,
star projections, and unitary star-algebra automorphisms. No separate
commutator, projection, or conjugation structure is introduced.
-/

namespace InfoGeometry.OperatorAlgebra.MatrixOperatorIdentities

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The antisymmetric and symmetric products recover ordinary multiplication. -/
theorem lie_jordan_decomposition (A B : Matrix n n ℂ) :
    (2 : ℂ) • (A * B) = ⁅A, B⁆ + (A * B + B * A) := by
  simp only [Ring.lie_def, two_smul]
  abel

/-- The existing Hermitian/skew-Hermitian decomposition is real-linear. -/
theorem adjoint_decomposition (A : Matrix n n ℂ) :
    (selfAdjointPart ℝ A : Matrix n n ℂ) +
      (skewAdjointPart ℝ A : Matrix n n ℂ) = A :=
  StarModule.selfAdjointPart_add_skewAdjointPart ℝ A

/-- The adjoint reverses the order of the native Lie bracket. -/
theorem star_lie (A B : Matrix n n ℂ) :
    star ⁅A, B⁆ = ⁅star B, star A⁆ := by
  simp only [Ring.lie_def, star_sub, star_mul]

/-- The symmetric product is compatible with the adjoint. -/
theorem star_anticommutator (A B : Matrix n n ℂ) :
    star (A * B + B * A) = star A * star B + star B * star A := by
  simp only [star_add, star_mul]
  exact add_comm _ _

/-- The Lie product of Hermitian matrices is skew-Hermitian. -/
theorem star_lie_of_isSelfAdjoint {A B : Matrix n n ℂ}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    star ⁅A, B⁆ = -⁅A, B⁆ := by
  rw [star_lie, hA.star_eq, hB.star_eq]
  simp only [Ring.lie_def]
  abel

/-- The symmetric product of Hermitian matrices is Hermitian. -/
theorem isSelfAdjoint_anticommutator {A B : Matrix n n ℂ}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (A * B + B * A) := by
  change star (A * B + B * A) = A * B + B * A
  rw [star_anticommutator, hA.star_eq, hB.star_eq]

/-- Associative Leibniz for the native inner Lie action. -/
theorem lie_mul (H A B : Matrix n n ℂ) :
    ⁅H, A * B⁆ = ⁅H, A⁆ * B + A * ⁅H, B⁆ := by
  simp only [Ring.lie_def]
  noncomm_ring

/-- The native matrix Lie algebra satisfies Jacobi. -/
theorem matrix_jacobi (A B C : Matrix n n ℂ) :
    ⁅A, ⁅B, C⁆⁆ + ⁅B, ⁅C, A⁆⁆ + ⁅C, ⁅A, B⁆⁆ = 0 :=
  lie_jacobi A B C

/-- The adjoint representation acts by matrix multiplication commutators. -/
theorem ad_apply (H A : Matrix n n ℂ) :
    LieAlgebra.ad ℂ (Matrix n n ℂ) H A = H * A - A * H := rfl

/-- An exact nested-commutator identity, without a commutation premise. -/
theorem lie_lie_expansion (A B : Matrix n n ℂ) :
    ⁅A, ⁅A, B⁆⁆ = (A * A) * B - (2 : ℂ) • (A * B * A) + B * (A * A) := by
  simp only [Ring.lie_def, two_smul]
  noncomm_ring

/-- The compressed first commutator vanishes for every idempotent. -/
theorem projection_sandwich_lie_zero {p : Matrix n n ℂ}
    (hp : IsIdempotentElem p) (A : Matrix n n ℂ) : p * ⁅p, A⁆ * p = 0 := by
  change p * (p * A - A * p) * p = 0
  calc
    _ = (p * p) * A * p - p * A * (p * p) := by noncomm_ring
    _ = 0 := by rw [hp.eq, sub_self]

/-- The second commutator gives the algebraic off-diagonal expression. -/
theorem projection_double_lie {p : Matrix n n ℂ}
    (hp : IsIdempotentElem p) (A : Matrix n n ℂ) :
    ⁅p, ⁅p, A⁆⁆ = p * A + A * p - (2 : ℂ) • (p * A * p) := by
  rw [lie_lie_expansion, hp.eq]
  abel

/-- Compression of a Hermitian matrix by a Hermitian matrix is Hermitian;
idempotence is not required for this conclusion. -/
theorem compression_isSelfAdjoint {p A : Matrix n n ℂ}
    (hp : IsSelfAdjoint p) (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (p * A * p) :=
  hA.conjugate_self hp

/-- Native unitary conjugation preserves the Lie product. -/
theorem conjStarAlgAut_lie (u : unitary (Matrix n n ℂ)) (A B : Matrix n n ℂ) :
    Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) u ⁅A, B⁆ =
      ⁅Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) u A,
        Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) u B⁆ := by
  simp only [Ring.lie_def, map_sub, map_mul]

/-- Native unitary conjugation also preserves the symmetric product. -/
theorem conjStarAlgAut_anticommutator (u : unitary (Matrix n n ℂ))
    (A B : Matrix n n ℂ) :
    Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) u (A * B + B * A) =
      Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) u A *
        Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) u B +
      Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) u B *
        Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) u A := by
  simp only [map_add, map_mul]

end InfoGeometry.OperatorAlgebra.MatrixOperatorIdentities
