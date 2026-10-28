/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.PeirceSuperoperators.HilbertSchmidt
import Mathlib.Tactic.Linarith

/-!
# The kernel of the full-matrix Jordan Gram action

The Hilbert–Schmidt energy of `X ↦ HX + XH`, for `H = NNᴴ + NᴴN`, is the sum
of four squared matrix norms. Its kernel is exactly the simultaneous left
and right annihilator of `N` and `Nᴴ`. No parity or nilpotence is needed for
this statement; the graded Hodge specialization uses the actual adjoint law.
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

/-- The full-matrix Jordan Gram action has four nonnegative energy terms. -/
theorem hs_jordan_gram_energy (N X : Matrix n n ℂ) :
    RCLike.re (inner ℂ X (jordanLeft (R := ℂ) (N * Nᴴ + Nᴴ * N) X)) =
      ‖N * X‖ ^ 2 + ‖Nᴴ * X‖ ^ 2 + ‖X * N‖ ^ 2 + ‖X * Nᴴ‖ ^ 2 := by
  have hinner : inner ℂ X (jordanLeft (R := ℂ) (N * Nᴴ + Nᴴ * N) X) =
      inner ℂ (N * X) (N * X) + inner ℂ (Nᴴ * X) (Nᴴ * X) +
      inner ℂ (X * N) (X * N) + inner ℂ (X * Nᴴ) (X * Nᴴ) := by
    rw [hs_jordan_gram_eq]
    simp only [LinearMap.add_apply, Module.End.mul_apply, inner_add_right]
    rw [LinearMap.adjoint_inner_right (LinearMap.mulLeft ℂ N) X
        (LinearMap.mulLeft ℂ N X),
      ← LinearMap.adjoint_inner_left (LinearMap.mulLeft ℂ N)
        ((LinearMap.mulLeft ℂ N).adjoint X) X,
      LinearMap.adjoint_inner_right (LinearMap.mulRight ℂ N) X
        (LinearMap.mulRight ℂ N X),
      ← LinearMap.adjoint_inner_left (LinearMap.mulRight ℂ N)
        ((LinearMap.mulRight ℂ N).adjoint X) X]
    simp only [hs_adjoint_mulLeft, hs_adjoint_mulRight, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply]
  rw [hinner]
  simp only [map_add, inner_self_eq_norm_sq]

/-- Zero Jordan Gram action is exactly simultaneous left and right annihilation. -/
theorem hs_jordan_gram_apply_eq_zero_iff (N X : Matrix n n ℂ) :
    jordanLeft (R := ℂ) (N * Nᴴ + Nᴴ * N) X = 0 ↔
      N * X = 0 ∧ Nᴴ * X = 0 ∧ X * N = 0 ∧ X * Nᴴ = 0 := by
  constructor
  · intro hX
    have hE := hs_jordan_gram_energy N X
    rw [hX, inner_zero_right, map_zero] at hE
    have h₁ : 0 ≤ ‖N * X‖ ^ 2 := sq_nonneg _
    have h₂ : 0 ≤ ‖Nᴴ * X‖ ^ 2 := sq_nonneg _
    have h₃ : 0 ≤ ‖X * N‖ ^ 2 := sq_nonneg _
    have h₄ : 0 ≤ ‖X * Nᴴ‖ ^ 2 := sq_nonneg _
    have hz₁ : ‖N * X‖ ^ 2 = 0 := by linarith only [hE, h₁, h₂, h₃, h₄]
    have hz₂ : ‖Nᴴ * X‖ ^ 2 = 0 := by linarith only [hE, h₁, h₂, h₃, h₄]
    have hz₃ : ‖X * N‖ ^ 2 = 0 := by linarith only [hE, h₁, h₂, h₃, h₄]
    have hz₄ : ‖X * Nᴴ‖ ^ 2 = 0 := by linarith only [hE, h₁, h₂, h₃, h₄]
    simpa only [sq_eq_zero_iff, norm_eq_zero] using
      And.intro hz₁ (And.intro hz₂ (And.intro hz₃ hz₄))
  · rintro ⟨hNX, hNHX, hXN, hXNH⟩
    change (N * Nᴴ + Nᴴ * N) * X + X * (N * Nᴴ + Nᴴ * N) = 0
    calc
      _ = N * (Nᴴ * X) + Nᴴ * (N * X) + (X * N) * Nᴴ + (X * Nᴴ) * N := by
        noncomm_ring
      _ = 0 := by simp only [hNHX, hNX, hXN, hXNH, mul_zero, zero_mul, zero_add]

/-- The kernel criterion as an equality of native complex submodules. -/
theorem hs_jordan_gram_ker (N : Matrix n n ℂ) :
    (jordanLeft (R := ℂ) (N * Nᴴ + Nᴴ * N)).ker =
      (LinearMap.mulLeft ℂ N).ker ⊓
        ((LinearMap.mulLeft ℂ Nᴴ).ker ⊓
          ((LinearMap.mulRight ℂ N).ker ⊓ (LinearMap.mulRight ℂ Nᴴ).ker)) := by
  apply Submodule.ext
  intro X
  simpa only [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply] using hs_jordan_gram_apply_eq_zero_iff N X

/-- The actual graded Hodge operator has the same four-annihilator kernel. -/
theorem gradedAdjoint_hodge_ker
    (θ : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ)
    (hθ : Function.Involutive θ)
    (hstar : ∀ X, θ Xᴴ = (θ X)ᴴ)
    (htrace : ∀ X, Matrix.trace (θ X) = Matrix.trace X)
    (N : Matrix n n ℂ) (hN : θ N = -N) :
    (gradedAdjoint θ N * (gradedAdjoint θ N).adjoint +
      (gradedAdjoint θ N).adjoint * gradedAdjoint θ N).ker =
      (LinearMap.mulLeft ℂ N).ker ⊓
        ((LinearMap.mulLeft ℂ Nᴴ).ker ⊓
          ((LinearMap.mulRight ℂ N).ker ⊓ (LinearMap.mulRight ℂ Nᴴ).ker)) := by
  rw [gradedAdjoint_hodge θ hθ hstar htrace N hN]
  exact hs_jordan_gram_ker N

/-- The Hodge energy is the sum of the two native action energies. -/
theorem gradedAdjoint_hodge_energy
    (θ : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ) (N X : Matrix n n ℂ) :
    RCLike.re (inner ℂ X
      ((gradedAdjoint θ N * (gradedAdjoint θ N).adjoint +
        (gradedAdjoint θ N).adjoint * gradedAdjoint θ N) X)) =
      ‖(gradedAdjoint θ N).adjoint X‖ ^ 2 + ‖gradedAdjoint θ N X‖ ^ 2 := by
  let D := gradedAdjoint θ N
  change RCLike.re (inner ℂ X (D (D.adjoint X) + D.adjoint (D X))) =
    ‖D.adjoint X‖ ^ 2 + ‖D X‖ ^ 2
  rw [inner_add_right, map_add,
    ← LinearMap.adjoint_inner_left D (D.adjoint X) X,
    LinearMap.adjoint_inner_right D X (D X)]
  simp only [inner_self_eq_norm_sq]

/-- Vanishing Hodge action is equivalent to vanishing action and metric adjoint. -/
theorem gradedAdjoint_hodge_apply_eq_zero_iff
    (θ : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ) (N X : Matrix n n ℂ) :
    (gradedAdjoint θ N * (gradedAdjoint θ N).adjoint +
      (gradedAdjoint θ N).adjoint * gradedAdjoint θ N) X = 0 ↔
        gradedAdjoint θ N X = 0 ∧ (gradedAdjoint θ N).adjoint X = 0 := by
  constructor
  · intro hX
    have hE := gradedAdjoint_hodge_energy θ N X
    rw [hX, inner_zero_right, map_zero] at hE
    have hD : 0 ≤ ‖gradedAdjoint θ N X‖ ^ 2 := sq_nonneg _
    have hA : 0 ≤ ‖(gradedAdjoint θ N).adjoint X‖ ^ 2 := sq_nonneg _
    have hzD : ‖gradedAdjoint θ N X‖ ^ 2 = 0 := by linarith only [hE, hD, hA]
    have hzA : ‖(gradedAdjoint θ N).adjoint X‖ ^ 2 = 0 := by
      linarith only [hE, hD, hA]
    simpa only [sq_eq_zero_iff, norm_eq_zero] using And.intro hzD hzA
  · rintro ⟨hD, hA⟩
    change gradedAdjoint θ N ((gradedAdjoint θ N).adjoint X) +
      (gradedAdjoint θ N).adjoint (gradedAdjoint θ N X) = 0
    simp only [hD, hA, map_zero, add_zero]

/-- Harmonic matrices form the intersection of the two native action kernels. -/
theorem gradedAdjoint_hodge_ker_eq_inf
    (θ : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ) (N : Matrix n n ℂ) :
    (gradedAdjoint θ N * (gradedAdjoint θ N).adjoint +
      (gradedAdjoint θ N).adjoint * gradedAdjoint θ N).ker =
        (gradedAdjoint θ N).ker ⊓ (gradedAdjoint θ N).adjoint.ker := by
  apply Submodule.ext
  intro X
  simpa only [Submodule.mem_inf, LinearMap.mem_ker] using
    gradedAdjoint_hodge_apply_eq_zero_iff θ N X

/-- The positive Gram Jordan action vanishes exactly when both Gram actions vanish. -/
theorem hs_jordan_gram_eq_zero_iff_left_right (N X : Matrix n n ℂ) :
    jordanLeft (R := ℂ) (N * Nᴴ + Nᴴ * N) X = 0 ↔
      (N * Nᴴ + Nᴴ * N) * X = 0 ∧ X * (N * Nᴴ + Nᴴ * N) = 0 := by
  constructor
  · intro hX
    obtain ⟨hNX, hNHX, hXN, hXNH⟩ :=
      (hs_jordan_gram_apply_eq_zero_iff N X).mp hX
    constructor
    · calc
        (N * Nᴴ + Nᴴ * N) * X = N * (Nᴴ * X) + Nᴴ * (N * X) := by
          noncomm_ring
        _ = 0 := by simp only [hNHX, hNX, mul_zero, zero_add]
    · calc
        X * (N * Nᴴ + Nᴴ * N) = (X * N) * Nᴴ + (X * Nᴴ) * N := by
          noncomm_ring
        _ = 0 := by simp only [hXN, hXNH, zero_mul, zero_add]
  · rintro ⟨hL, hR⟩
    change (N * Nᴴ + Nᴴ * N) * X + X * (N * Nᴴ + Nᴴ * N) = 0
    rw [hL, hR, zero_add]

/-- The Jordan Gram kernel is the intersection of its left and right multiplication kernels. -/
theorem hs_jordan_gram_ker_eq_inf (N : Matrix n n ℂ) :
    (jordanLeft (R := ℂ) (N * Nᴴ + Nᴴ * N)).ker =
      (LinearMap.mulLeft ℂ (N * Nᴴ + Nᴴ * N)).ker ⊓
        (LinearMap.mulRight ℂ (N * Nᴴ + Nᴴ * N)).ker := by
  apply Submodule.ext
  intro X
  simpa only [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply] using hs_jordan_gram_eq_zero_iff_left_right N X

end InfoGeometry.OperatorAlgebra.PeirceSuperoperators
