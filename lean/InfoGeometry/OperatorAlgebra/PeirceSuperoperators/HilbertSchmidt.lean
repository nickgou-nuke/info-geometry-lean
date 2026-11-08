/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.JordanMultiplicationClosure
import InfoGeometry.OperatorAlgebra.IntrinsicGradedAdjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Order

/-!
# Hilbert–Schmidt adjoints of intrinsic graded matrix actions

The carrier is the full complex matrix algebra with Mathlib's native matrix
inner product at weight one. The Hilbert–Schmidt adjoint of the intrinsic
graded action has a plus sign. Its adjoint anticommutator is the existing
Jordan multiplication operator for the sum of the two matrix Gram products.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceSuperoperators

open Matrix
open scoped ComplexOrder

open InfoGeometry.Core.JordanMultiplicationClosure
open InfoGeometry.OperatorAlgebra.IntrinsicGradedAdjoint

variable {n : Type*} [Fintype n] [DecidableEq n]

local instance : NormedAddCommGroup (Matrix n n ℂ) :=
  Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one

local instance : InnerProductSpace ℂ (Matrix n n ℂ) :=
  Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

/-- The native weight-one matrix inner product is the Hilbert–Schmidt pairing. -/
theorem hs_inner_eq_trace (X Y : Matrix n n ℂ) :
    inner ℂ X Y = Matrix.trace (Y * Xᴴ) := by
  change Matrix.trace (Y * (1 : Matrix n n ℂ) * Xᴴ) = _
  rw [Matrix.mul_one]

/-- Left multiplication has conjugate-transposed left multiplication as its adjoint. -/
theorem hs_adjoint_mulLeft (A : Matrix n n ℂ) :
    (LinearMap.mulLeft ℂ A).adjoint = LinearMap.mulLeft ℂ Aᴴ := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).2
  intro X Y
  simp only [LinearMap.mulLeft_apply, hs_inner_eq_trace,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle Y Xᴴ A

/-- Right multiplication has conjugate-transposed right multiplication as its adjoint. -/
theorem hs_adjoint_mulRight (A : Matrix n n ℂ) :
    (LinearMap.mulRight ℂ A).adjoint = LinearMap.mulRight ℂ Aᴴ := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).2
  intro X Y
  simp only [LinearMap.mulRight_apply, hs_inner_eq_trace,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- An involutive trace-preserving star-compatible algebra automorphism is self-adjoint. -/
theorem hs_adjoint_parity
    (θ : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ)
    (hθ : Function.Involutive θ)
    (hstar : ∀ X, θ Xᴴ = (θ X)ᴴ)
    (htrace : ∀ X, Matrix.trace (θ X) = Matrix.trace X) :
    θ.toLinearMap.adjoint = θ.toLinearMap := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).2
  intro X Y
  change inner ℂ (θ X) Y = inner ℂ X (θ Y)
  rw [hs_inner_eq_trace, hs_inner_eq_trace]
  calc
    Matrix.trace (Y * (θ X)ᴴ) = Matrix.trace (θ (θ Y * Xᴴ)) := by
      rw [map_mul, hθ Y, hstar X]
    _ = Matrix.trace (θ Y * Xᴴ) := htrace _

/-- The metric adjoint generally differs from the intrinsic graded action of `Nᴴ`. -/
theorem gradedAdjoint_adjoint
    (θ : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ)
    (hθ : Function.Involutive θ)
    (hstar : ∀ X, θ Xᴴ = (θ X)ᴴ)
    (htrace : ∀ X, Matrix.trace (θ X) = Matrix.trace X)
    (N : Matrix n n ℂ) (hN : θ N = -N) :
    (gradedAdjoint θ N).adjoint =
      LinearMap.mulLeft ℂ Nᴴ + (LinearMap.mulRight ℂ Nᴴ).comp θ.toLinearMap := by
  have hNH : θ Nᴴ = -Nᴴ := by
    rw [hstar N, hN, Matrix.conjTranspose_neg]
  rw [gradedAdjoint, map_sub, LinearMap.adjoint_comp, hs_adjoint_mulLeft,
    hs_adjoint_mulRight, hs_adjoint_parity θ hθ hstar htrace]
  apply LinearMap.ext
  intro X
  change Nᴴ * X - θ (X * Nᴴ) = Nᴴ * X + θ X * Nᴴ
  rw [map_mul, hNH]
  noncomm_ring

/-- The actual adjoint anticommutator is a Jordan action, with no square-zero premise. -/
theorem gradedAdjoint_hodge
    (θ : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ)
    (hθ : Function.Involutive θ)
    (hstar : ∀ X, θ Xᴴ = (θ X)ᴴ)
    (htrace : ∀ X, Matrix.trace (θ X) = Matrix.trace X)
    (N : Matrix n n ℂ) (hN : θ N = -N) :
    gradedAdjoint θ N * (gradedAdjoint θ N).adjoint +
      (gradedAdjoint θ N).adjoint * gradedAdjoint θ N =
        jordanLeft (R := ℂ) (N * Nᴴ + Nᴴ * N) := by
  have hNH : θ Nᴴ = -Nᴴ := by
    rw [hstar N, hN, Matrix.conjTranspose_neg]
  rw [gradedAdjoint_adjoint θ hθ hstar htrace N hN]
  apply LinearMap.ext
  intro X
  change N * (Nᴴ * X + θ X * Nᴴ) - θ (Nᴴ * X + θ X * Nᴴ) * N +
      (Nᴴ * (N * X - θ X * N) + θ (N * X - θ X * N) * Nᴴ) =
        (N * Nᴴ + Nᴴ * N) * X + X * (N * Nᴴ + Nᴴ * N)
  simp only [map_add, map_sub, map_mul, hN, hNH, hθ X]
  noncomm_ring

/-- The Jordan action of the two matrix Gram products is a sum of four adjoint squares. -/
theorem hs_jordan_gram_eq (N : Matrix n n ℂ) :
    jordanLeft (R := ℂ) (N * Nᴴ + Nᴴ * N) =
      (LinearMap.mulLeft ℂ N).adjoint * LinearMap.mulLeft ℂ N +
      LinearMap.mulLeft ℂ N * (LinearMap.mulLeft ℂ N).adjoint +
      (LinearMap.mulRight ℂ N).adjoint * LinearMap.mulRight ℂ N +
      LinearMap.mulRight ℂ N * (LinearMap.mulRight ℂ N).adjoint := by
  rw [hs_adjoint_mulLeft, hs_adjoint_mulRight]
  apply LinearMap.ext
  intro X
  change (N * Nᴴ + Nᴴ * N) * X + X * (N * Nᴴ + Nᴴ * N) =
    Nᴴ * (N * X) + N * (Nᴴ * X) + (X * N) * Nᴴ + (X * Nᴴ) * N
  noncomm_ring

/-- Positivity of the Gram Jordan action requires neither parity nor nilpotence. -/
theorem hs_jordan_gram_isPositive (N : Matrix n n ℂ) :
    (jordanLeft (R := ℂ) (N * Nᴴ + Nᴴ * N)).IsPositive := by
  rw [hs_jordan_gram_eq]
  exact (((LinearMap.isPositive_adjoint_comp_self (LinearMap.mulLeft ℂ N)).add
    (LinearMap.isPositive_self_comp_adjoint (LinearMap.mulLeft ℂ N))).add
    (LinearMap.isPositive_adjoint_comp_self (LinearMap.mulRight ℂ N))).add
    (LinearMap.isPositive_self_comp_adjoint (LinearMap.mulRight ℂ N))

/-- The native metric adjoint anticommutator is positive for every intrinsic graded action. -/
theorem gradedAdjoint_hodge_isPositive
    (θ : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ) (N : Matrix n n ℂ) :
    (gradedAdjoint θ N * (gradedAdjoint θ N).adjoint +
      (gradedAdjoint θ N).adjoint * gradedAdjoint θ N).IsPositive :=
  (LinearMap.isPositive_self_comp_adjoint (gradedAdjoint θ N)).add
    (LinearMap.isPositive_adjoint_comp_self (gradedAdjoint θ N))

end InfoGeometry.OperatorAlgebra.PeirceSuperoperators
