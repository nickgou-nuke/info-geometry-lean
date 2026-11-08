/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.LieJordanGenerators
import InfoGeometry.HodgeCohomology.HodgeDirac
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-!
# Real Frobenius geometry of paired adjoint actions

Mathlib's matrix inner-product structures are installed on the full real
matrix algebra. The transpose identifies the actual adjoint of the native
Lie action. The existing real adjoint-pair owner then supplies the energy
and common-kernel identities, without a nilpotency assumption.

The scoped instances are available through
InfoGeometry.Canonical.RealLieJordanGeometry. Positive semidefinite
preservation of the paired sandwich is kept distinct from positivity of
an endomorphism's Frobenius quadratic form.
-/

noncomputable section

namespace InfoGeometry.Canonical.RealLieJordanGeometry

open scoped InnerProductSpace Matrix

open Core.LieJordanGenerators

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Mathlib's native Frobenius norm on the full real matrix algebra. -/
@[instance_reducible]
def frobeniusNormedAddCommGroup : NormedAddCommGroup (Matrix n n ℝ) :=
  Matrix.toMatrixNormedAddCommGroup (1 : Matrix n n ℝ) Matrix.PosDef.one

attribute [local instance] frobeniusNormedAddCommGroup

/-- Mathlib's native matrix inner product, specialized to identity weight. -/
@[instance_reducible]
def frobeniusInnerProductSpace : InnerProductSpace ℝ (Matrix n n ℝ) :=
  Matrix.toMatrixInnerProductSpace (1 : Matrix n n ℝ) Matrix.PosDef.one.posSemidef

attribute [local instance] frobeniusInnerProductSpace

scoped[InfoGeometry.Canonical.RealLieJordanGeometry] attribute [instance]
  frobeniusNormedAddCommGroup frobeniusInnerProductSpace

/-- The selected native inner product is the real Frobenius trace pairing. -/
@[simp]
theorem inner_eq_trace_transpose_mul (x y : Matrix n n ℝ) :
    inner ℝ x y = Matrix.trace (xᵀ * y) := by
  change Matrix.trace (y * (1 : Matrix n n ℝ) * xᴴ) = Matrix.trace (xᵀ * y)
  rw [mul_one, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.trace_mul_comm]

theorem transpose_ad (u x : Matrix n n ℝ) :
    (LieAlgebra.ad ℝ (Matrix n n ℝ) u x)ᵀ =
      -(LieAlgebra.ad ℝ (Matrix n n ℝ) uᵀ xᵀ) := by
  change (u * x - x * u)ᵀ = -(uᵀ * xᵀ - xᵀ * uᵀ)
  simp only [Matrix.transpose_sub, Matrix.transpose_mul]
  abel

/-- Transpose adjunction for arbitrary real matrix coefficients and inputs. -/
theorem inner_ad (u x y : Matrix n n ℝ) :
    inner ℝ (LieAlgebra.ad ℝ (Matrix n n ℝ) u x) y =
      inner ℝ x (LieAlgebra.ad ℝ (Matrix n n ℝ) uᵀ y) := by
  rw [inner_eq_trace_transpose_mul, inner_eq_trace_transpose_mul,
    transpose_ad, neg_mul, Matrix.trace_neg]
  have hz := Core.LieJordanComposition.trace_ad_skew (R := ℝ)
    (Matrix.traceAddMonoidHom n ℝ) Matrix.trace_mul_comm uᵀ xᵀ y
  change Matrix.trace (LieAlgebra.ad ℝ (Matrix n n ℝ) uᵀ xᵀ * y) +
    Matrix.trace (xᵀ * LieAlgebra.ad ℝ (Matrix n n ℝ) uᵀ y) = 0 at hz
  apply neg_eq_of_add_eq_zero_left
  simpa only [add_comm] using hz

/-- The adjoint is Mathlib's finite-dimensional linear-map adjoint. -/
@[simp]
theorem adjoint_ad (u : Matrix n n ℝ) :
    (LieAlgebra.ad ℝ (Matrix n n ℝ) u).adjoint =
      LieAlgebra.ad ℝ (Matrix n n ℝ) uᵀ := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simpa only [Matrix.transpose_transpose] using inner_ad uᵀ x y

/-- The paired generator is the negative sum of the two native Gram operators. -/
theorem symmetricGenerator_eq_negative_gram (u : Matrix n n ℝ) :
    symmetricGenerator (R := ℝ) u uᵀ =
      -((LieAlgebra.ad ℝ (Matrix n n ℝ) u) *
          (LieAlgebra.ad ℝ (Matrix n n ℝ) u).adjoint +
        (LieAlgebra.ad ℝ (Matrix n n ℝ) u).adjoint *
          LieAlgebra.ad ℝ (Matrix n n ℝ) u) := by
  simp only [symmetricGenerator, adjoint_ad]

/-- Positivity here is positivity of the operator on the Frobenius space. -/
theorem neg_symmetricGenerator_isPositive (u : Matrix n n ℝ) :
    (-symmetricGenerator (R := ℝ) u uᵀ).IsPositive := by
  rw [symmetricGenerator_eq_negative_gram, neg_neg]
  exact (LinearMap.isPositive_self_comp_adjoint
    (LieAlgebra.ad ℝ (Matrix n n ℝ) u)).add
      (LinearMap.isPositive_adjoint_comp_self (LieAlgebra.ad ℝ (Matrix n n ℝ) u))

theorem symmetricGenerator_isSymmetric (u : Matrix n n ℝ) :
    (symmetricGenerator (R := ℝ) u uᵀ).IsSymmetric := by
  have h := (neg_symmetricGenerator_isPositive u).isSymmetric
  intro x y
  simpa only [LinearMap.neg_apply, inner_neg_left, inner_neg_right, neg_inj] using h x y

theorem symmetricGenerator_isSelfAdjoint (u : Matrix n n ℝ) :
    IsSelfAdjoint (symmetricGenerator (R := ℝ) u uᵀ) :=
  (LinearMap.isSymmetric_iff_isSelfAdjoint _).mp (symmetricGenerator_isSymmetric u)

@[simp]
theorem adjoint_symmetricGenerator (u : Matrix n n ℝ) :
    (symmetricGenerator (R := ℝ) u uᵀ).adjoint =
      symmetricGenerator (R := ℝ) u uᵀ :=
  (symmetricGenerator_isSymmetric u).adjoint_eq

/-- The exact energy identity consumes the existing real adjoint-pair theorem. -/
theorem inner_symmetricGenerator (u x : Matrix n n ℝ) :
    inner ℝ x (symmetricGenerator (R := ℝ) u uᵀ x) =
      -(‖LieAlgebra.ad ℝ (Matrix n n ℝ) u x‖ ^ 2 +
        ‖LieAlgebra.ad ℝ (Matrix n n ℝ) uᵀ x‖ ^ 2) := by
  have h := HodgeCohomology.HodgeDirac.laplacian_energy
    (LieAlgebra.ad ℝ (Matrix n n ℝ) u)
    (LieAlgebra.ad ℝ (Matrix n n ℝ) uᵀ) (inner_ad u) x
  change inner ℝ x (-((LieAlgebra.ad ℝ (Matrix n n ℝ) u *
    LieAlgebra.ad ℝ (Matrix n n ℝ) uᵀ +
    LieAlgebra.ad ℝ (Matrix n n ℝ) uᵀ *
    LieAlgebra.ad ℝ (Matrix n n ℝ) u) x)) = _
  rw [inner_neg_right, real_inner_comm, h]

theorem inner_symmetricGenerator_nonpos (u x : Matrix n n ℝ) :
    inner ℝ x (symmetricGenerator (R := ℝ) u uᵀ x) ≤ 0 := by
  rw [inner_symmetricGenerator]
  exact neg_nonpos.mpr (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- Vanishing of the generator is exactly the simultaneous vanishing of both actions. -/
theorem symmetricGenerator_apply_eq_zero_iff (u x : Matrix n n ℝ) :
    symmetricGenerator (R := ℝ) u uᵀ x = 0 ↔
      LieAlgebra.ad ℝ (Matrix n n ℝ) u x = 0 ∧
        LieAlgebra.ad ℝ (Matrix n n ℝ) uᵀ x = 0 := by
  change -((LieAlgebra.ad ℝ (Matrix n n ℝ) u *
    LieAlgebra.ad ℝ (Matrix n n ℝ) uᵀ +
    LieAlgebra.ad ℝ (Matrix n n ℝ) uᵀ *
    LieAlgebra.ad ℝ (Matrix n n ℝ) u) x) = 0 ↔ _
  rw [neg_eq_zero]
  exact HodgeCohomology.HodgeDirac.harmonic_iff_closed_and_coclosed
    (LieAlgebra.ad ℝ (Matrix n n ℝ) u)
    (LieAlgebra.ad ℝ (Matrix n n ℝ) uᵀ) (inner_ad u) x

theorem ker_symmetricGenerator (u : Matrix n n ℝ) :
    (symmetricGenerator (R := ℝ) u uᵀ).ker =
      (LieAlgebra.ad ℝ (Matrix n n ℝ) u).ker ⊓
        (LieAlgebra.ad ℝ (Matrix n n ℝ) uᵀ).ker := by
  ext x
  simp only [LinearMap.mem_ker, Submodule.mem_inf]
  exact symmetricGenerator_apply_eq_zero_iff u x

/-- The common centralizer is the existing native subalgebra. -/
theorem ker_symmetricGenerator_eq_centralizer (u : Matrix n n ℝ) :
    (symmetricGenerator (R := ℝ) u uᵀ).ker =
      (Subalgebra.centralizer ℝ ({u, uᵀ} : Set (Matrix n n ℝ))).toSubmodule := by
  ext x
  change symmetricGenerator (R := ℝ) u uᵀ x = 0 ↔
    x ∈ Subalgebra.centralizer ℝ ({u, uᵀ} : Set (Matrix n n ℝ))
  rw [symmetricGenerator_apply_eq_zero_iff, Subalgebra.mem_centralizer_iff]
  change (u * x - x * u = 0 ∧ uᵀ * x - x * uᵀ = 0) ↔
    ∀ a ∈ ({u, uᵀ} : Set (Matrix n n ℝ)), a * x = x * a
  simp [sub_eq_zero]

theorem range_symmetricGenerator (u : Matrix n n ℝ) :
    (symmetricGenerator (R := ℝ) u uᵀ).range =
      ((LieAlgebra.ad ℝ (Matrix n n ℝ) u).ker ⊓
        (LieAlgebra.ad ℝ (Matrix n n ℝ) uᵀ).ker)ᗮ := by
  have h := LinearMap.orthogonal_ker (symmetricGenerator (R := ℝ) u uᵀ)
  rw [adjoint_symmetricGenerator, ker_symmetricGenerator] at h
  exact h.symm

theorem range_symmetricGenerator_eq_centralizer_orthogonal (u : Matrix n n ℝ) :
    (symmetricGenerator (R := ℝ) u uᵀ).range =
      (Subalgebra.centralizer ℝ ({u, uᵀ} : Set (Matrix n n ℝ))).toSubmoduleᗮ := by
  have h := LinearMap.orthogonal_ker (symmetricGenerator (R := ℝ) u uᵀ)
  rw [adjoint_symmetricGenerator, ker_symmetricGenerator_eq_centralizer] at h
  exact h.symm

/-- The paired sandwich preserves the matrix positive cone on every real input in that cone. -/
theorem paired_sandwich_posSemidef (u : Matrix n n ℝ)
    {x : Matrix n n ℝ} (hx : x.PosSemidef) :
    ((LinearMap.mulLeftRight ℝ (u, uᵀ) +
      LinearMap.mulLeftRight ℝ (uᵀ, u)) x).PosSemidef := by
  change (u * x * uᵀ + uᵀ * x * u).PosSemidef
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (hx.mul_mul_conjTranspose_same u).add (hx.conjTranspose_mul_mul_same u)

end InfoGeometry.Canonical.RealLieJordanGeometry
