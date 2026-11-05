/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Action.ConjAct
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.NoncommRing

/-!
# Symmetric filters and causal support

Lower-triangular support is relative to a specified linear order on tokens.
A symmetric matrix with this support is diagonal. Thus a nontrivial symmetric
Walsh-type filter cannot acquire autoregressive support merely by being
called causal. For a data-dependent matrix, even triangular support of the
frozen operator leaves the dependence of its coefficients to be checked.

Conjugation uses the native action of units. Its product law preserves
operator-valued coefficient order; only the scalar specialization commutes.
The final starred-ring identity corrects the sign of the normality defect.
-/

namespace InfoGeometry.Routing.SymmetricCausalBoundary

open Matrix

/-- Symmetry and forward-only linear support force diagonality, without
finiteness or multiplication assumptions. -/
theorem isDiag_of_isSymm_isLowerTriangular {I A : Type*} [LinearOrder I] [Zero A]
    {M : Matrix I I A} (hs : M.IsSymm) (hl : M.IsLowerTriangular) : M.IsDiag := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hl h
  · rw [← hs.apply i j]
    exact hl h

section ConjugatedDiagonal

variable {I A : Type*} [Fintype I] [DecidableEq I]

/-- Fixed involution conjugation preserves the full ordered coefficient
product. The coefficient semiring is not assumed commutative. -/
theorem conjugated_diagonal_mul [Semiring A] (H : Matrix I I A)
    (hH : H * H = 1) (a b : I → A) :
    (H * diagonal a * H) * (H * diagonal b * H) = H * diagonal (a * b) * H := by
  let u : (Matrix I I A)ˣ := ⟨H, H, hH, hH⟩
  let e := MulSemiringAction.toRingEquiv (ConjAct (Matrix I I A)ˣ) (Matrix I I A)
    (ConjAct.toConjAct u)
  have hm := e.map_mul (diagonal a) (diagonal b)
  change H * (diagonal a * diagonal b) * H =
    (H * diagonal a * H) * (H * diagonal b * H) at hm
  rw [diagonal_mul_diagonal] at hm
  exact hm.symm

/-- Conjugation transports the coefficient commutator rather than erasing
it. This identity still allows noncommuting operator-valued entries. -/
theorem conjugated_diagonal_commutator [Ring A] (H : Matrix I I A)
    (hH : H * H = 1) (a b : I → A) :
    (H * diagonal a * H) * (H * diagonal b * H) -
        (H * diagonal b * H) * (H * diagonal a * H) =
      H * diagonal (a * b - b * a) * H := by
  rw [conjugated_diagonal_mul H hH, conjugated_diagonal_mul H hH]
  have hd := (diagonalRingHom I A).map_sub (a * b) (b * a)
  change diagonal (a * b - b * a) = diagonal (a * b) - diagonal (b * a) at hd
  rw [hd, mul_sub, sub_mul]

/-- Scalar diagonal coefficients commute, so their fixed conjugates commute.
This is not asserted for arbitrary operator-valued coefficients. -/
theorem conjugated_diagonals_commute [CommSemiring A] (H : Matrix I I A)
    (hH : H * H = 1) (a b : I → A) :
    Commute (H * diagonal a * H) (H * diagonal b * H) := by
  change _ * _ = _ * _
  rw [conjugated_diagonal_mul H hH, conjugated_diagonal_mul H hH, mul_comm a b]

/-- A diagonal filter sandwiched by a symmetric matrix is symmetric. -/
theorem conjugated_diagonal_isSymm [CommSemiring A] (H : Matrix I I A)
    (hH : H.IsSymm) (a : I → A) : (H * diagonal a * H).IsSymm := by
  change (H * diagonal a * H)ᵀ = H * diagonal a * H
  rw [transpose_mul, transpose_mul, hH.eq, diagonal_transpose, mul_assoc]

/-- A symmetric conjugated diagonal filter can have lower-triangular
token support only when the resulting matrix is diagonal. -/
theorem conjugated_diagonal_isDiag_of_lower [LinearOrder I] [CommSemiring A]
    (H : Matrix I I A) (hH : H.IsSymm) (a : I → A)
    (hl : (H * diagonal a * H).IsLowerTriangular) :
    (H * diagonal a * H).IsDiag :=
  isDiag_of_isSymm_isLowerTriangular (conjugated_diagonal_isSymm H hH a) hl

end ConjugatedDiagonal

/-- For self-adjoint `S` and skew-adjoint `K`, the ordinary commutator
`[S+K, star (S+K)]` has the negative sign. Nonnormality is not causal support. -/
theorem normality_defect_self_add_skew {A : Type*} [Ring A] [StarRing A]
    (S K : A) (hS : star S = S) (hK : star K = -K) :
    (S + K) * star (S + K) - star (S + K) * (S + K) =
      -(2 • (S * K - K * S)) := by
  rw [star_add, hS, hK]
  simp only [two_nsmul]
  noncomm_ring

end InfoGeometry.Routing.SymmetricCausalBoundary
