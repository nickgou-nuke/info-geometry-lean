import Mathlib.Algebra.Module.LinearMap.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Hodge-Star Self-Dual Algebra

This file proves the finite algebraic core of the Hodge-star split used in
the canonical Hodge/Krein corridor.  The operator `S` is an abstract
involutive self-adjoint linear map, modeling the split-signature Hodge-star
law `S^2 = id`.  From this explicit data we construct the two eigensector
projectors and prove their self-dual/anti-self-dual orthogonality.

No manifold, exterior algebra, curvature tensor, or analytic Hodge theorem is
asserted here.  Those geometric realizations remain outside this algebraic
owner file.

## Audit Protocol Map
- BUCKET 1: CLOSED FINITE THEOREMS:
  `S_S`, `B_S_S`, `P_plus`, `P_minus`, `P_plus_apply`,
  `P_minus_apply`, `S_P_plus`, `S_P_minus`, `B_neg_right`,
  `self_dual_anti_self_dual_orthogonal`.
- BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES:
  The orthogonality theorem is conditional on the explicitly named involution,
  self-adjointness, symmetry, and scalar-linearity hypotheses.
- BUCKET 3: OPEN CLOSURE DEBT:
  Geometric construction of the Hodge star on differential forms and analytic
  self-dual curvature decomposition are not asserted here.
-/

namespace InfoGeometry.Canonical.HodgeStarSelfDualAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The `+1` eigensector projector associated to an involutive Hodge-star shadow. -/
def P_plus (half : ℝ) (S : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  half • ((LinearMap.id : V →ₗ[ℝ] V) + S)

/-- The `-1` eigensector projector associated to an involutive Hodge-star shadow. -/
def P_minus (half : ℝ) (S : V →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  half • ((LinearMap.id : V →ₗ[ℝ] V) - S)

/-- An involutive linear map squares to the identity on each vector. -/
theorem S_S
    (S : V →ₗ[ℝ] V)
    (hS2 : S.comp S = LinearMap.id)
    (x : V) :
    S (S x) = x := by
  have h : S (S x) = (S.comp S) x := rfl
  rw [h, hS2]
  rfl

/-- A self-adjoint involution preserves the bilinear pairing. -/
theorem B_S_S
    (B : V → V → ℝ)
    (S : V →ₗ[ℝ] V)
    (hS2 : S.comp S = LinearMap.id)
    (hSadj : ∀ x y, B (S x) y = B x (S y))
    (x y : V) :
    B (S x) (S y) = B x y := by
  rw [hSadj]
  rw [S_S S hS2]

/-- Pointwise form of the positive Hodge-star eigensector projector. -/
@[simp]
theorem P_plus_apply (half : ℝ) (S : V →ₗ[ℝ] V) (x : V) :
    P_plus half S x = half • (x + S x) := by
  rfl

/-- Pointwise form of the negative Hodge-star eigensector projector. -/
@[simp]
theorem P_minus_apply (half : ℝ) (S : V →ₗ[ℝ] V) (x : V) :
    P_minus half S x = half • (x - S x) := by
  rfl

/-- `P_plus` lands in the `+1` eigensector of the involution. -/
theorem S_P_plus
    (half : ℝ)
    (S : V →ₗ[ℝ] V)
    (hS2 : S.comp S = LinearMap.id)
    (x : V) :
    S (P_plus half S x) = P_plus half S x := by
  rw [P_plus_apply]
  rw [map_smul, map_add]
  rw [S_S S hS2]
  rw [add_comm]

/-- `P_minus` lands in the `-1` eigensector of the involution. -/
theorem S_P_minus
    (half : ℝ)
    (S : V →ₗ[ℝ] V)
    (hS2 : S.comp S = LinearMap.id)
    (x : V) :
    S (P_minus half S x) = -P_minus half S x := by
  rw [P_minus_apply]
  rw [map_smul, map_sub]
  rw [S_S S hS2]
  have h : S x - x = -(x - S x) := by abel
  rw [h, smul_neg]

/-- Right negation exits a symmetric left-linear bilinear form. -/
theorem B_neg_right
    (B : V → V → ℝ)
    (B_comm : ∀ x y, B x y = B y x)
    (B_smul_left : ∀ c x y, B (c • x) y = c * B x y)
    (u v : V) :
    B u (-v) = -B u v := by
  rw [B_comm u (-v)]
  have hneg : -v = (-1 : ℝ) • v := by
    exact (neg_one_smul ℝ v).symm
  rw [hneg]
  rw [B_smul_left (-1) v u]
  rw [B_comm v u]
  ring

/--
The self-dual and anti-self-dual Hodge-star eigensector projectors are
orthogonal under any symmetric pairing for which the involution is self-adjoint.
-/
theorem self_dual_anti_self_dual_orthogonal
    (B : V → V → ℝ)
    (B_comm : ∀ x y, B x y = B y x)
    (B_smul_left : ∀ c x y, B (c • x) y = c * B x y)
    (S : V →ₗ[ℝ] V)
    (hS2 : S.comp S = LinearMap.id)
    (hSadj : ∀ x y, B (S x) y = B x (S y))
    (half : ℝ)
    (x y : V) :
    B (P_plus half S x) (P_minus half S y) = 0 := by
  have h1 :
      B (P_plus half S x) (P_minus half S y) =
        B (S (P_plus half S x)) (S (P_minus half S y)) := by
    exact (B_S_S B S hS2 hSadj (P_plus half S x) (P_minus half S y)).symm
  rw [S_P_plus half S hS2 x] at h1
  rw [S_P_minus half S hS2 y] at h1
  rw [B_neg_right B B_comm B_smul_left (P_plus half S x) (P_minus half S y)] at h1
  linarith

end InfoGeometry.Canonical.HodgeStarSelfDualAlgebra
