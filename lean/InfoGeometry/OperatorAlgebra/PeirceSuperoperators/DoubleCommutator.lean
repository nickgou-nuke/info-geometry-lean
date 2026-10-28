/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSuperoperators.HodgeKernel
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Lie.OfAssociative

/-!
# Paired inner commutators on the full matrix Hilbert–Schmidt space

At the identity algebra automorphism the existing intrinsic graded action
is the native inner Lie action. Its previously established Hodge laws give
the energy and common kernel of the negative paired double commutator.
No nilpotence, projection, or commutativity assumption is imposed.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceSuperoperators

open Matrix
open scoped ComplexOrder
open InfoGeometry.OperatorAlgebra.IntrinsicGradedAdjoint

attribute [local instance] LieRing.ofAssociativeRing

variable {n : Type*} [Fintype n] [DecidableEq n]

local instance doubleCommutatorNormedAddCommGroup : NormedAddCommGroup (Matrix n n ℂ) :=
  Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one

local instance doubleCommutatorInnerProductSpace : InnerProductSpace ℂ (Matrix n n ℂ) :=
  Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

local notation "adM" => LieAlgebra.ad ℂ (Matrix n n ℂ)

/-- Identity parity recovers the native inner Lie action on full matrices. -/
theorem gradedAdjoint_refl_eq_ad (N : Matrix n n ℂ) :
    gradedAdjoint (AlgEquiv.refl : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ) N = adM N := by
  apply LinearMap.ext
  intro X
  change N * X - X * N = N * X - X * N
  rfl

/-- Conjugate transpose of the charge gives the Hilbert–Schmidt adjoint of its inner action. -/
theorem hs_adjoint_ad (N : Matrix n n ℂ) :
    (adM N).adjoint = adM Nᴴ := by
  have had (A : Matrix n n ℂ) :
      adM A = LinearMap.mulLeft ℂ A - LinearMap.mulRight ℂ A :=
    congrFun (LieAlgebra.ad_eq_lmul_left_sub_lmul_right (R := ℂ) (Matrix n n ℂ)) A
  rw [had N, map_sub, hs_adjoint_mulLeft, hs_adjoint_mulRight, had Nᴴ]

/-- The negative paired double commutator is self-adjoint as a native endomorphism. -/
theorem doubleCommutator_adjoint (N : Matrix n n ℂ) :
    (-(adM N * adM Nᴴ + adM Nᴴ * adM N)).adjoint =
      -(adM N * adM Nᴴ + adM Nᴴ * adM N) := by
  simp only [map_neg, map_add, Module.End.mul_eq_comp, LinearMap.adjoint_comp,
    hs_adjoint_ad, Matrix.conjTranspose_conjTranspose]

/-- The negative of the paired double-commutator generator is positive. -/
theorem neg_doubleCommutator_isPositive (N : Matrix n n ℂ) :
    (adM N * adM Nᴴ + adM Nᴴ * adM N).IsPositive := by
  simpa only [gradedAdjoint_refl_eq_ad, hs_adjoint_ad] using
    gradedAdjoint_hodge_isPositive (AlgEquiv.refl : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ) N

/-- The negative paired action has the sum of two commutator energies with a minus sign. -/
theorem doubleCommutator_energy (N X : Matrix n n ℂ) :
    RCLike.re (inner ℂ X
      ((-(adM N * adM Nᴴ + adM Nᴴ * adM N)) X)) =
        -(‖⁅N, X⁆‖ ^ 2 + ‖⁅Nᴴ, X⁆‖ ^ 2) := by
  have h := gradedAdjoint_hodge_energy (AlgEquiv.refl : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ) N X
  rw [gradedAdjoint_refl_eq_ad, hs_adjoint_ad] at h
  rw [LinearMap.neg_apply, inner_neg_right, map_neg, h]
  simp only [LieAlgebra.ad_apply]
  rw [add_comm]

/-- Zero paired double commutator is exactly simultaneous commutation with both charges. -/
theorem doubleCommutator_apply_eq_zero_iff (N X : Matrix n n ℂ) :
    (-(adM N * adM Nᴴ + adM Nᴴ * adM N)) X = 0 ↔
      ⁅N, X⁆ = 0 ∧ ⁅Nᴴ, X⁆ = 0 := by
  rw [LinearMap.neg_apply, neg_eq_zero]
  simpa only [gradedAdjoint_refl_eq_ad, hs_adjoint_ad, LieAlgebra.ad_apply] using
    gradedAdjoint_hodge_apply_eq_zero_iff (AlgEquiv.refl : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ) N X

/-- The paired double-commutator kernel is the intersection of native inner-action kernels. -/
theorem doubleCommutator_ker (N : Matrix n n ℂ) :
    (-(adM N * adM Nᴴ + adM Nᴴ * adM N)).ker =
      (adM N).ker ⊓ (adM Nᴴ).ker := by
  rw [LinearMap.ker_neg]
  simpa only [gradedAdjoint_refl_eq_ad, hs_adjoint_ad] using
    gradedAdjoint_hodge_ker_eq_inf (AlgEquiv.refl : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ) N

/-- The same kernel is the underlying complex submodule of the actual joint centralizer. -/
theorem doubleCommutator_ker_eq_centralizer (N : Matrix n n ℂ) :
    (-(adM N * adM Nᴴ + adM Nᴴ * adM N)).ker =
      (Subalgebra.centralizer ℂ ({N, Nᴴ} : Set (Matrix n n ℂ))).toSubmodule := by
  apply Submodule.ext
  intro X
  simp only [LinearMap.mem_ker, doubleCommutator_apply_eq_zero_iff,
    Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff,
    Set.forall_mem_insert, Set.forall_mem_singleton, Ring.lie_def, sub_eq_zero]

end InfoGeometry.OperatorAlgebra.PeirceSuperoperators
