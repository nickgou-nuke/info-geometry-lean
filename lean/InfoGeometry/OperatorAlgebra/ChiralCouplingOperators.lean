/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.MassAsCommutantCoupling
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic

/-!
# Operator-valued chiral coupling and parity averaging

Arbitrary rectangular blocks, with no scalar-square or commuting-block
assumption. The even square is an operator Gramian in the adjoint case.
Parity restoration is proved for the explicitly defined averaging map,
not asserted for arbitrary mixed states or for a physical mass mechanism.
-/

noncomputable section
namespace InfoGeometry.OperatorAlgebra.ChiralCouplingOperators

open Matrix
open InfoGeometry.Core.PeirceDecomposition
open InfoGeometry.QuantumContext.MassAsCommutantCoupling

section Blocks
variable {R m n : Type*} [Ring R]
variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def chiral (B : Matrix m n R) (C : Matrix n m R) : Matrix (m ⊕ n) (m ⊕ n) R :=
  fromBlocks 0 B C 0

def leftProjection : Matrix (m ⊕ n) (m ⊕ n) R := fromBlocks 1 0 0 0

theorem leftProjection_idempotent :
    IsIdempotentElem (leftProjection (R := R) (m := m) (n := n)) := by
  change leftProjection * leftProjection = leftProjection
  simp [leftProjection, fromBlocks_multiply]

theorem upper_square_zero (B : Matrix m n R) :
    chiral B 0 * chiral B 0 = 0 := by
  ext i j
  cases i <;> cases j <;> simp [chiral, fromBlocks_multiply]

theorem lower_square_zero (C : Matrix n m R) :
    chiral 0 C * chiral 0 C = 0 := by
  ext i j
  cases i <;> cases j <;> simp [chiral, fromBlocks_multiply]

theorem coupling_square (B : Matrix m n R) (C : Matrix n m R) :
    chiral B C * chiral B C = fromBlocks (B * C) 0 0 (C * B) := by
  simp [chiral, fromBlocks_multiply]

theorem coupling_swaps (B : Matrix m n R) (C : Matrix n m R) :
    leftProjection * chiral B C =
      chiral B C * complementIdempotent leftProjection := by
  unfold complementIdempotent
  rw [mul_sub, mul_one]
  ext i j
  cases i <;> cases j <;> simp [leftProjection, chiral, fromBlocks_multiply]

/-- Reuse the existing Peirce grading instead of a new chirality carrier. -/
theorem coupling_odd (B : Matrix m n R) (C : Matrix n m R) :
    grading leftProjection * chiral B C + chiral B C * grading leftProjection = 0 :=
  grading_anticommutes _ _ (coupling_swaps B C)

theorem coupling_square_commutes (B : Matrix m n R) (C : Matrix n m R) :
    Commute leftProjection (chiral B C * chiral B C) := by
  change leftProjection * (chiral B C * chiral B C) =
    (chiral B C * chiral B C) * leftProjection
  rw [coupling_square]
  simp [leftProjection, fromBlocks_multiply]

/-- Without an intertwining law the kinetic-coupling cross terms remain. -/
theorem kinetic_coupling_defect
    (L : Matrix m m R) (R' : Matrix n n R)
    (B : Matrix m n R) (C : Matrix n m R) :
    fromBlocks L 0 0 (-R') * chiral B C +
      chiral B C * fromBlocks L 0 0 (-R') =
        fromBlocks 0 (L * B - B * R') (C * L - R' * C) 0 := by
  ext i j
  cases i <;> cases j <;>
    simp [chiral, fromBlocks_multiply, sub_eq_add_neg, add_comm]

end Blocks

section StarBlocks
variable {R m n : Type*} [Ring R] [StarRing R]
variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem adjoint_coupling_hermitian (B : Matrix m n R) :
    (chiral B Bᴴ)ᴴ = chiral B Bᴴ := by
  ext i j
  cases i <;> cases j <;> simp [chiral, Matrix.conjTranspose_apply]

/-- The two Gramian products retain their order. -/
theorem adjoint_coupling_square (B : Matrix m n R) :
    chiral B Bᴴ * chiral B Bᴴ = fromBlocks (B * Bᴴ) 0 0 (Bᴴ * B) :=
  coupling_square B Bᴴ

end StarBlocks

section GradedDerivation
variable {A : Type*} [Ring A]

/-- Odd inner superderivation, squared on an even input. -/
theorem superderivation_square_even (D a : A) :
    D * (D * a - a * D) + (D * a - a * D) * D =
      (D * D) * a - a * (D * D) := by noncomm_ring

/-- The same square on an odd input, with the other bracket order. -/
theorem superderivation_square_odd (D a : A) :
    D * (D * a + a * D) - (D * a + a * D) * D =
      (D * D) * a - a * (D * D) := by noncomm_ring

/-- Centrality on a selected observable is a condition, not inferred globally. -/
theorem superderivation_square_zero_of_commute (D a : A)
    (ha : Commute (D * D) a) :
    D * (D * a - a * D) + (D * a - a * D) * D = 0 := by
  rw [superderivation_square_even, ha.eq, sub_self]

end GradedDerivation

section Parity
variable {A : Type*} [Ring A] [Algebra ℝ A]

def parityAverage (γ a : A) : A := (1 / 2 : ℝ) • (a + γ * a * γ)

theorem conjugate_parityAverage (γ a : A) (hγ : γ * γ = 1) :
    γ * parityAverage γ a * γ = parityAverage γ a := by
  unfold parityAverage
  simp only [mul_smul_comm, smul_mul_assoc]
  congr 1
  calc γ * (a + γ * a * γ) * γ = γ * a * γ + (γ * γ) * a * (γ * γ) := by
         noncomm_ring
       _ = a + γ * a * γ := by rw [hγ]; simp [add_comm]

theorem parityAverage_eq_self (γ a : A) (ha : γ * a * γ = a) :
    parityAverage γ a = a := by
  rw [parityAverage, ha]
  module

theorem parityAverage_idempotent (γ a : A) (hγ : γ * γ = 1) :
    parityAverage γ (parityAverage γ a) = parityAverage γ a :=
  parityAverage_eq_self _ _ (conjugate_parityAverage γ a hγ)

theorem parityAverage_eq_self_iff (γ a : A) (hγ : γ * γ = 1) :
    parityAverage γ a = a ↔ Commute γ a := by
  constructor
  · intro h
    have hc : γ * a * γ = a := by
      rw [← h]
      exact conjugate_parityAverage γ a hγ
    have hh := congrArg (fun z : A => z * γ) hc
    change γ * a = a * γ
    simpa [mul_assoc, hγ] using hh
  · intro h
    apply parityAverage_eq_self
    calc γ * a * γ = a * (γ * γ) := by rw [h.eq, mul_assoc]
         _ = a := by rw [hγ, mul_one]

theorem parityAverage_odd_zero (γ a : A) (ha : γ * a * γ = -a) :
    parityAverage γ a = 0 := by simp [parityAverage, ha]

/-- Symmetric averaging removes odd coupling but preserves its even square. -/
theorem parityAverage_preserves_square_of_odd
    (γ a : A) (hγ : γ * γ = 1) (ha : γ * a * γ = -a) :
    parityAverage γ (a * a) = a * a := by
  apply parityAverage_eq_self
  have h : (γ * a * γ) * (γ * a * γ) = γ * (a * a) * γ := by
    calc (γ * a * γ) * (γ * a * γ) = γ * a * (γ * γ) * a * γ := by noncomm_ring
      _ = γ * (a * a) * γ := by rw [hγ]; noncomm_ring
  rw [← h, ha]
  simp

end Parity

theorem square_zero_not_isUnit {A : Type*} [Ring A] [Nontrivial A]
    (a : A) (ha : a * a = 0) : ¬ IsUnit a := by
  rintro ⟨u, rfl⟩
  exact (u * u).ne_zero (by simpa using ha)

end InfoGeometry.OperatorAlgebra.ChiralCouplingOperators
