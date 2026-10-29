/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.LieJordanHodgeBridge
import InfoGeometry.OperatorAlgebra.LieJordanHodgeCoercivity
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Linarith

/-!
# Positive real adjoints of the doubled Lie–Jordan boundary

Full real matrix algebras use Mathlib's weight-one Hilbert–Schmidt structure.
The double is the native L2 product, not the max-norm product. The algebraic
boundary is transported by an explicit linear equivalence. No complex scalar,
Krein-adjoint identification, diagonal restriction, or gap assumption is used.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.LieJordanHodgeReal

attribute [local instance 100] LieRing.ofAssociativeRing

open Matrix
open InfoGeometry.Core.JordanMultiplicationClosure
open InfoGeometry.OperatorAlgebra.LieJordanCliffordDouble
open InfoGeometry.OperatorAlgebra.LieJordanBoundaryCalculus
open InfoGeometry.OperatorAlgebra.LieJordanHodgeBridge

variable {n : Type*} [Fintype n] [DecidableEq n]

local instance : NormedAddCommGroup (Matrix n n ℝ) :=
  Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one

local instance : InnerProductSpace ℝ (Matrix n n ℝ) :=
  Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

/-- A positive real Hilbert–Schmidt pairing, not the cyclic pairing tr(XY). -/
theorem inner_eq_trace (x y : Matrix n n ℝ) :
    inner ℝ x y = Matrix.trace (y * xᴴ) := by
  change Matrix.trace (y * (1 : Matrix n n ℝ) * xᴴ) = _
  rw [Matrix.mul_one]

theorem adjoint_mulLeft (u : Matrix n n ℝ) :
    (LinearMap.mulLeft ℝ u).adjoint = LinearMap.mulLeft ℝ uᴴ := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).2
  intro x y
  simp only [LinearMap.mulLeft_apply, inner_eq_trace,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle y xᴴ u

theorem adjoint_mulRight (u : Matrix n n ℝ) :
    (LinearMap.mulRight ℝ u).adjoint = LinearMap.mulRight ℝ uᴴ := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).2
  intro x y
  simp only [LinearMap.mulRight_apply, inner_eq_trace,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

theorem adjoint_ad (u : Matrix n n ℝ) :
    (LieAlgebra.ad ℝ (Matrix n n ℝ) u).adjoint =
      LieAlgebra.ad ℝ (Matrix n n ℝ) uᴴ := by
  have h : LieAlgebra.ad ℝ (Matrix n n ℝ) u =
      LinearMap.mulLeft ℝ u - LinearMap.mulRight ℝ u := by
    ext x
    rfl
  rw [h, map_sub, adjoint_mulLeft, adjoint_mulRight]
  rfl

theorem adjoint_jordan (u : Matrix n n ℝ) :
    (jordanLeft (R := ℝ) u).adjoint = jordanLeft (R := ℝ) uᴴ := by
  have h : jordanLeft (R := ℝ) u =
      LinearMap.mulLeft ℝ u + LinearMap.mulRight ℝ u := by
    ext x
    rfl
  rw [h, map_add, adjoint_mulLeft, adjoint_mulRight]
  rfl

theorem ad_inner (u x y : Matrix n n ℝ) :
    inner ℝ (LieAlgebra.ad ℝ (Matrix n n ℝ) u x) y =
      inner ℝ x (LieAlgebra.ad ℝ (Matrix n n ℝ) uᴴ y) := by
  simpa only [adjoint_ad] using
    (LinearMap.adjoint_inner_right (LieAlgebra.ad ℝ (Matrix n n ℝ) u) x y).symm

theorem jordan_inner (u x y : Matrix n n ℝ) :
    inner ℝ (jordanLeft (R := ℝ) u x) y =
      inner ℝ x (jordanLeft (R := ℝ) uᴴ y) := by
  simpa only [adjoint_jordan] using
    (LinearMap.adjoint_inner_right (jordanLeft (R := ℝ) u) x y).symm

/-- Transport an existing algebraic double to its native L2 product. -/
def onDouble (t : Module.End ℝ (Matrix n n ℝ × Matrix n n ℝ)) :
    Module.End ℝ (WithLp 2 (Matrix n n ℝ × Matrix n n ℝ)) :=
  ((WithLp.linearEquiv 2 ℝ (Matrix n n ℝ × Matrix n n ℝ)).symm.toLinearMap.comp t).comp
    (WithLp.linearEquiv 2 ℝ (Matrix n n ℝ × Matrix n n ℝ)).toLinearMap

omit [Fintype n] [DecidableEq n] in
@[simp] theorem onDouble_apply
    (t : Module.End ℝ (Matrix n n ℝ × Matrix n n ℝ))
    (z : WithLp 2 (Matrix n n ℝ × Matrix n n ℝ)) :
    (onDouble t z).ofLp = t z.ofLp := rfl

omit [Fintype n] [DecidableEq n] in
theorem onDouble_mul (s t : Module.End ℝ (Matrix n n ℝ × Matrix n n ℝ)) :
    onDouble (s * t) = onDouble s * onDouble t := by
  ext z
  rfl

omit [Fintype n] [DecidableEq n] in
theorem onDouble_add (s t : Module.End ℝ (Matrix n n ℝ × Matrix n n ℝ)) :
    onDouble (s + t) = onDouble s + onDouble t := by
  ext z
  rfl

/-- The same doubled boundary, on the carrier with its positive product metric. -/
def differential (u : Matrix n n ℝ) :
    Module.End ℝ (WithLp 2 (Matrix n n ℝ × Matrix n n ℝ)) :=
  onDouble (boundary (R := ℝ) u)

/-- The positive adjoint exchanges the blocks and transposes the coefficient. -/
theorem differential_adjoint (u : Matrix n n ℝ) :
    (differential u).adjoint = onDouble (coboundary (R := ℝ) uᴴ) := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).2
  intro x y
  simp only [WithLp.prod_inner_apply]
  change inner ℝ (jordanLeft (R := ℝ) uᴴ x.ofLp.2) y.ofLp.1 +
      inner ℝ (LieAlgebra.ad ℝ (Matrix n n ℝ) uᴴ x.ofLp.1) y.ofLp.2 =
    inner ℝ x.ofLp.1 (LieAlgebra.ad ℝ (Matrix n n ℝ) u y.ofLp.2) +
      inner ℝ x.ofLp.2 (jordanLeft (R := ℝ) u y.ofLp.1)
  rw [jordan_inner, ad_inner, Matrix.conjTranspose_conjTranspose, add_comm]

/-- The actual adjoint anticommutator is the doubled Jordan Gram action. -/
theorem hodge_eq_jordan (u : Matrix n n ℝ) :
    differential u * (differential u).adjoint +
      (differential u).adjoint * differential u =
        onDouble (liftOp (jordanLeft (R := ℝ) (u * uᴴ + uᴴ * u))) := by
  rw [differential_adjoint]
  change onDouble (boundary (R := ℝ) u) * onDouble (coboundary (R := ℝ) uᴴ) +
      onDouble (coboundary (R := ℝ) uᴴ) * onDouble (boundary (R := ℝ) u) = _
  rw [← onDouble_mul, ← onDouble_mul, ← onDouble_add, boundary_coboundary]

/-- Positive Hodge energy, with no nilpotence or symmetry premise. -/
theorem hodge_energy (u : Matrix n n ℝ)
    (z : WithLp 2 (Matrix n n ℝ × Matrix n n ℝ)) :
    inner ℝ z ((differential u * (differential u).adjoint +
      (differential u).adjoint * differential u) z) =
      ‖(differential u).adjoint z‖ ^ 2 + ‖differential u z‖ ^ 2 := by
  let d := differential u
  change inner ℝ z (d (d.adjoint z) + d.adjoint (d z)) = _
  rw [inner_add_right, ← LinearMap.adjoint_inner_left d (d.adjoint z) z,
    LinearMap.adjoint_inner_right d z (d z)]
  simp only [real_inner_self_eq_norm_sq, d]

theorem hodge_isPositive (u : Matrix n n ℝ) :
    (differential u * (differential u).adjoint +
      (differential u).adjoint * differential u).IsPositive :=
  (LinearMap.isPositive_self_comp_adjoint (differential u)).add
    (LinearMap.isPositive_adjoint_comp_self (differential u))

/-- The harmonic subspace is specified by the actual positive adjoint. -/
theorem hodge_apply_eq_zero_iff (u : Matrix n n ℝ)
    (z : WithLp 2 (Matrix n n ℝ × Matrix n n ℝ)) :
    (differential u * (differential u).adjoint +
      (differential u).adjoint * differential u) z = 0 ↔
        differential u z = 0 ∧ (differential u).adjoint z = 0 := by
  constructor
  · intro hz
    have he := hodge_energy u z
    rw [hz, inner_zero_right] at he
    have h₁ : ‖differential u z‖ ^ 2 = 0 := by
      nlinarith only [he, sq_nonneg ‖differential u z‖,
        sq_nonneg ‖(differential u).adjoint z‖]
    have h₂ : ‖(differential u).adjoint z‖ ^ 2 = 0 := by
      nlinarith only [he, sq_nonneg ‖differential u z‖,
        sq_nonneg ‖(differential u).adjoint z‖]
    simpa only [sq_eq_zero_iff, norm_eq_zero] using And.intro h₁ h₂
  · rintro ⟨hd, ha⟩
    change differential u ((differential u).adjoint z) +
      (differential u).adjoint (differential u z) = 0
    simp only [hd, ha, map_zero, add_zero]

theorem hodge_ker (u : Matrix n n ℝ) :
    (differential u * (differential u).adjoint +
      (differential u).adjoint * differential u).ker =
        (differential u).ker ⊓ (differential u).adjoint.ker := by
  ext z
  simpa only [Submodule.mem_inf, LinearMap.mem_ker] using hodge_apply_eq_zero_iff u z

theorem differential_square_zero {u : Matrix n n ℝ} (hu : u * u = 0) :
    differential u * differential u = 0 := by
  change onDouble (boundary (R := ℝ) u) * onDouble (boundary (R := ℝ) u) = 0
  rw [← onDouble_mul, boundary_square_zero hu]
  ext z
  rfl

/-- Every nonzero real matrix gives a nonzero doubled boundary. -/
theorem differential_ne_zero {u : Matrix n n ℝ} (hu : u ≠ 0) :
    differential u ≠ 0 := by
  intro h
  have hx := congrArg
    (fun t : Module.End ℝ (WithLp 2 (Matrix n n ℝ × Matrix n n ℝ)) =>
      (t (WithLp.toLp 2 (1, 0))).ofLp.2) h
  change u * 1 + 1 * u = 0 at hx
  simp only [mul_one, one_mul] at hx
  apply hu
  ext i j
  change u i j = 0
  have hij := congrArg (fun m : Matrix n n ℝ => m i j) hx
  change u i j + u i j = 0 at hij
  linarith

/-- For nonzero coefficients the positive adjoint is never the unexchanged
boundary of the transposed coefficient. This excludes the false identification. -/
theorem adjoint_ne_unexchanged {u : Matrix n n ℝ} (hu : u ≠ 0) :
    (differential u).adjoint ≠ differential uᴴ := by
  intro h
  rw [differential_adjoint] at h
  have hx := congrArg
    (fun t : Module.End ℝ (WithLp 2 (Matrix n n ℝ × Matrix n n ℝ)) =>
      (t (WithLp.toLp 2 (1, 0))).ofLp.2) h
  change uᴴ * 1 - 1 * uᴴ = uᴴ * 1 + 1 * uᴴ at hx
  simp only [mul_one, one_mul, sub_self] at hx
  have hz : uᴴ = 0 := by
    ext i j
    change uᴴ i j = 0
    have hij := congrArg (fun m : Matrix n n ℝ => m i j) hx
    change 0 = uᴴ i j + uᴴ i j at hij
    linarith
  apply hu
  simpa only [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero] using
    congrArg (fun m : Matrix n n ℝ => mᴴ) hz

/-- The finite-space bound is stated pointwise on the actual homotopy; this
is equivalent to an operator-norm bound and avoids changing the matrix norm. -/
theorem hodge_coercive_of_homotopy (u : Matrix n n ℝ)
    (h P : Module.End ℝ (WithLp 2 (Matrix n n ℝ × Matrix n n ℝ)))
    (C : ℝ) (hC : 0 < C)
    (hbound : ∀ z : WithLp 2 (Matrix n n ℝ × Matrix n n ℝ), ‖h z‖ ≤ C * ‖z‖)
    (hhom : differential u * h + h * differential u = 1 - P)
    (z : WithLp 2 (Matrix n n ℝ × Matrix n n ℝ)) (hz : P z = 0) :
    (1 / (2 * C ^ 2)) * ‖z‖ ^ 2 ≤
      inner ℝ z (onDouble (liftOp (jordanLeft (R := ℝ) (u * uᴴ + uᴴ * u))) z) := by
  have he := LieJordanHodgeCoercivity.linear_energy_ge_of_homotopy
    (differential u) h P C hC hbound hhom z hz
  rw [hodge_eq_jordan] at he
  exact he

end InfoGeometry.OperatorAlgebra.LieJordanHodgeReal
