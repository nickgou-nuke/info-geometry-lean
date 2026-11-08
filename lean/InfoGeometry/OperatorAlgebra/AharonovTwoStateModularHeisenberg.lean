/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing

/-!
# Two-boundary sandwiches and modular shift identities

The first section is valid in any unital associative ring.  The matrix results
are finite algebraic readouts; no measurement instrument, probability model,
or analytic weak-value limit is constructed here.
-/

namespace InfoGeometry.OperatorAlgebra.AharonovTwoStateModularHeisenberg

section RingLevel

variable {A : Type*} [Ring A]

def IsSpine (S : A) : Prop := S * S = S

def SpinePresence (S X : A) : A := S * X * S

def TwoStateSandwich (S₂ X S₁ : A) : A := S₂ * X * S₁

@[simp] theorem twoStateSandwich_same (S X : A) :
    TwoStateSandwich S X S = SpinePresence S X := rfl

theorem twoStateSandwich_boundary_absorption {S₁ S₂ : A} (X : A)
    (hS₁ : IsSpine S₁) (hS₂ : IsSpine S₂) :
    S₂ * TwoStateSandwich S₂ X S₁ = TwoStateSandwich S₂ X S₁ ∧
    TwoStateSandwich S₂ X S₁ * S₁ = TwoStateSandwich S₂ X S₁ := by
  constructor
  · unfold TwoStateSandwich
    calc
      S₂ * (S₂ * X * S₁) = (S₂ * S₂) * X * S₁ := by noncomm_ring
      _ = S₂ * X * S₁ := by rw [hS₂]
  · unfold TwoStateSandwich
    rw [mul_assoc _ _ S₁, hS₁]

theorem twoStateSandwich_self_left_and_right {S₁ S₂ : A}
    (hS₁ : IsSpine S₁) (hS₂ : IsSpine S₂) :
    TwoStateSandwich S₂ S₁ S₁ = S₂ * S₁ ∧
    TwoStateSandwich S₂ S₂ S₁ = S₂ * S₁ := by
  constructor
  · unfold TwoStateSandwich
    rw [mul_assoc, hS₁]
  · unfold TwoStateSandwich
    rw [hS₂]

theorem twoStateSandwich_sum_amplification {S₁ S₂ : A}
    (hS₁ : IsSpine S₁) (hS₂ : IsSpine S₂) :
    TwoStateSandwich S₂ (S₁ + S₂) S₁ = (2 : ℕ) • (S₂ * S₁) := by
  have h := twoStateSandwich_self_left_and_right hS₁ hS₂
  unfold TwoStateSandwich
  calc
    S₂ * (S₁ + S₂) * S₁ = S₂ * S₁ * S₁ + S₂ * S₂ * S₁ := by
      rw [mul_add, add_mul]
    _ = S₂ * S₁ + S₂ * S₁ := by
      rw [mul_assoc S₂ S₁ S₁, hS₁, hS₂]
    _ = (2 : ℕ) • (S₂ * S₁) := by abel

theorem twoStateSandwich_square_disturbance {S₁ S₂ : A}
    (hS₁ : IsSpine S₁) (hS₂ : IsSpine S₂) :
    TwoStateSandwich S₂ ((S₁ + S₂) ^ 2) S₁ =
      (3 : ℕ) • (S₂ * S₁) + (S₂ * S₁) * (S₂ * S₁) := by
  have h₁ : S₂ * (S₁ * S₁) * S₁ = S₂ * S₁ := by
    rw [hS₁, mul_assoc S₂ S₁ S₁, hS₁]
  have h₂ : S₂ * (S₁ * S₂) * S₁ = (S₂ * S₁) * (S₂ * S₁) := by
    noncomm_ring
  have h₃ : S₂ * (S₂ * S₁) * S₁ = S₂ * S₁ := by
    calc
      S₂ * (S₂ * S₁) * S₁ = (S₂ * S₂) * (S₁ * S₁) := by noncomm_ring
      _ = S₂ * S₁ := by rw [hS₂, hS₁]
  have h₄ : S₂ * (S₂ * S₂) * S₁ = S₂ * S₁ := by
    rw [hS₂, hS₂]
  have hexp :
      (S₁ + S₂) ^ 2 =
        (S₁ * S₁ + S₁ * S₂) + (S₂ * S₁ + S₂ * S₂) := by
    simp only [pow_two]
    noncomm_ring
  unfold TwoStateSandwich
  rw [hexp]
  rw [mul_add, mul_add, mul_add, add_mul, add_mul, add_mul]
  rw [h₁, h₂, h₃, h₄]
  abel

theorem one_sub_spine_idempotent {S : A} (hS : IsSpine S) :
    (1 - S) * (1 - S) = 1 - S := by
  have hmul : (1 - S) * (1 - S) = 1 - S - S + S * S := by noncomm_ring
  rw [hmul, hS]
  abel

theorem twoStateSandwich_intermediate_decomposition
    (S₂ X Y S₁ S : A) (hS : IsSpine S) :
    TwoStateSandwich S₂ (X * Y) S₁ =
      TwoStateSandwich S₂ X S * TwoStateSandwich S Y S₁ +
        (S₂ * X * (1 - S)) * ((1 - S) * Y * S₁) := by
  have hcomp := one_sub_spine_idempotent hS
  have hsplit : S + (1 - S) = (1 : A) := by abel
  have hproj : ∀ z : A, S * (S * z) = S * z := by
    intro z
    rw [← mul_assoc, hS]
  have hcompProj : ∀ z : A, (1 - S) * ((1 - S) * z) = (1 - S) * z := by
    intro z
    rw [← mul_assoc, hcomp]
  change S₂ * (X * Y) * S₁ =
    (S₂ * X * S) * (S * Y * S₁) +
      (S₂ * X * (1 - S)) * ((1 - S) * Y * S₁)
  calc
    S₂ * (X * Y) * S₁ = S₂ * X * (Y * S₁) := by noncomm_ring
    _ = S₂ * X * ((S + (1 - S)) * (Y * S₁)) := by rw [hsplit, one_mul]
    _ = S₂ * X * (S * (Y * S₁)) + S₂ * X * ((1 - S) * (Y * S₁)) := by
      rw [add_mul, mul_add]
    _ = (S₂ * X * S) * (S * Y * S₁) +
        (S₂ * X * (1 - S)) * ((1 - S) * Y * S₁) := by
      simp only [mul_assoc, hproj, hcompProj]

def opComm (X Y : A) : A := X * Y - Y * X

structure ModularShiftPair (A : Type*) [Ring A] where
  T : A
  σ : A →+* A
  intertwine : ∀ V : A, T * V = σ V * T

namespace ModularShiftPair

theorem heisenberg_modular_difference_law (M : ModularShiftPair A) (V : A) :
    opComm M.T V = (M.σ V - V) * M.T := by
  unfold opComm
  rw [M.intertwine V, sub_mul]

def comp (M₁ M₂ : ModularShiftPair A) : ModularShiftPair A where
  T := M₁.T * M₂.T
  σ := M₁.σ.comp M₂.σ
  intertwine V := by
    calc
      (M₁.T * M₂.T) * V = M₁.T * (M₂.T * V) := mul_assoc _ _ _
      _ = M₁.T * (M₂.σ V * M₂.T) := by rw [M₂.intertwine]
      _ = (M₁.T * M₂.σ V) * M₂.T := (mul_assoc _ _ _).symm
      _ = (M₁.σ (M₂.σ V) * M₁.T) * M₂.T := by rw [M₁.intertwine]
      _ = M₁.σ (M₂.σ V) * (M₁.T * M₂.T) := mul_assoc _ _ _

theorem comp_shift_cocycle (M₁ M₂ : ModularShiftPair A) (V : A) :
    opComm (M₁.T * M₂.T) V =
      ((M₁.σ (M₂.σ V) - M₁.σ V) + (M₁.σ V - V)) * (M₁.T * M₂.T) := by
  have h := heisenberg_modular_difference_law (comp M₁ M₂) V
  change opComm (M₁.T * M₂.T) V =
    ((M₁.σ.comp M₂.σ) V - V) * (M₁.T * M₂.T) at h
  rw [h]
  congr 1
  simp only [RingHom.comp_apply]
  abel

theorem gauge_dressed_shift_commutator (M : ModularShiftPair A) (W V : A) :
    opComm (W * M.T) V =
      W * (M.σ V - V) * M.T + opComm W V * M.T := by
  unfold opComm
  calc
    (W * M.T) * V - V * (W * M.T) =
        W * (M.σ V * M.T) - (V * W) * M.T := by
          rw [mul_assoc W M.T V, mul_assoc V W M.T, M.intertwine V]
    _ = W * (M.σ V - V) * M.T + (W * V - V * W) * M.T := by
          noncomm_ring

end ModularShiftPair

end RingLevel

section MatrixReadout

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : Type*} [CommRing R]

/-- The permutation shift whose `(i,j)` entry is one when `j = π i`. -/
def sylvesterShiftMatrix (π : ι ≃ ι) : Matrix ι ι R :=
  fun i j => if j = π i then 1 else 0

theorem sylvesterShift_intertwines_diagonal (π : ι ≃ ι) (v : ι → R) :
    sylvesterShiftMatrix π * Matrix.diagonal v =
      Matrix.diagonal (v ∘ π) * sylvesterShiftMatrix π := by
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, sylvesterShiftMatrix,
    Function.comp_apply]
  by_cases h : j = π i
  · subst j
    simp
  · simp [h]

theorem sylvesterShift_commutator_diagonal (π : ι ≃ ι) (v : ι → R) :
    sylvesterShiftMatrix π * Matrix.diagonal v -
        Matrix.diagonal v * sylvesterShiftMatrix π =
      Matrix.diagonal (fun i => v (π i) - v i) * sylvesterShiftMatrix π := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    sylvesterShiftMatrix]
  by_cases h : j = π i
  · subst j
    simp
  · simp [h]

theorem matrix_trace_two_state_sum_and_square
    {S₁ S₂ : Matrix ι ι R}
    (hS₁ : IsSpine S₁) (hS₂ : IsSpine S₂) :
    Matrix.trace (TwoStateSandwich S₂ (S₁ + S₂) S₁) =
        (2 : ℕ) • Matrix.trace (S₂ * S₁) ∧
    Matrix.trace (TwoStateSandwich S₂ ((S₁ + S₂) ^ 2) S₁) =
        (3 : ℕ) • Matrix.trace (S₂ * S₁) +
          Matrix.trace ((S₂ * S₁) * (S₂ * S₁)) := by
  constructor
  · rw [twoStateSandwich_sum_amplification hS₁ hS₂, Matrix.trace_smul]
  · rw [twoStateSandwich_square_disturbance hS₁ hS₂,
      Matrix.trace_add, Matrix.trace_smul]

end MatrixReadout

end InfoGeometry.OperatorAlgebra.AharonovTwoStateModularHeisenberg
