import Mathlib.Tactic

import InfoGeometry.Canonical.Cl11BipartiteDiracBridge
import InfoGeometry.Canonical.Cl11LeftRightDoubleBridge

/-!
# Bipartite Cl(1,1) order-one condition

This module formalizes the finite algebraic double-commutator identity for the
native bipartite composite operator

  D_tot = D_L ⊗ β_R + I_L ⊗ D_R

on the repository-owned stage-two carrier.

For a left observable a and right observable b,

  [[D_tot, a ⊗ I], I ⊗ b]
    = [D_L,a] ⊗ [β_R,b].

Consequently the double commutator vanishes whenever b commutes with β_R.

The opposite ordering has the same obstruction:

  [[D_tot, I ⊗ b], a ⊗ I] = [D_L,a] ⊗ [β_R,b].

It vanishes under the same right-evenness hypothesis, not for arbitrary a,b.

These are finite matrix identities. They are not, by themselves, a proof of
the full analytic order-one axiom for an unbounded real spectral triple, nor
of AQFT microcausality or gauge-anomaly cancellation.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11BipartiteOrderOneCondition

open scoped Matrix Kronecker
open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Canonical.Cl11LeftRightDoubleBridge
open InfoGeometry.Canonical.Cl11BipartiteDiracBridge

abbrev Atom := Mat2
abbrev StageOne := MatStage 1
abbrev StageTwo := MatStage 2

/-- Associative commutator on the native stage-two matrix algebra. -/
def commutator (X Y : StageTwo) : StageTwo :=
  X * Y - Y * X

/-- Associative commutator on the native stage-one matrix algebra. -/
def commutatorL (X Y : StageOne) : StageOne :=
  X * Y - Y * X

/-- Associative commutator on the executable Cl(1,1) atom. -/
def commutatorR (X Y : Atom) : Atom :=
  X * Y - Y * X

/-- Left embedding a ↦ a ⊗ I. -/
def embedLeft (a : StageOne) : StageTwo :=
  a ⊗ₖ (1 : Atom)

/-- Right embedding b ↦ I ⊗ b. -/
def embedRight (b : Atom) : StageTwo :=
  (1 : StageOne) ⊗ₖ b

/-- Order-zero: the left and right embedded observables commute. -/
theorem orderZero (a : StageOne) (b : Atom) :
    commutator (embedLeft a) (embedRight b) = 0 := by
  change (a ⊗ₖ (1 : Atom)) * ((1 : StageOne) ⊗ₖ b) -
      ((1 : StageOne) ⊗ₖ b) * (a ⊗ₖ (1 : Atom)) = 0
  have h1 := Matrix.mul_kronecker_mul a (1 : StageOne) (1 : Atom) b
  have h2 := Matrix.mul_kronecker_mul (1 : StageOne) a b (1 : Atom)
  rw [mul_one, one_mul] at h1 h2
  rw [← h1, ← h2, sub_self]

/-- First commutator with a left observable:
the right-Dirac term drops out and only [D_L,a] ⊗ β_R remains. -/
theorem commutator_compositeDirac_embedLeft
    (DL a : StageOne) (betaR DR : Atom) :
    commutator (compositeDirac DL betaR DR) (embedLeft a) =
      commutatorL DL a ⊗ₖ betaR := by
  change (DL ⊗ₖ betaR + (1 : StageOne) ⊗ₖ DR) * (a ⊗ₖ (1 : Atom)) -
      (a ⊗ₖ (1 : Atom)) * (DL ⊗ₖ betaR + (1 : StageOne) ⊗ₖ DR) =
    (DL * a - a * DL) ⊗ₖ betaR
  rw [Matrix.add_mul, Matrix.mul_add]
  rw [← Matrix.mul_kronecker_mul DL a betaR (1 : Atom),
      ← Matrix.mul_kronecker_mul (1 : StageOne) a DR (1 : Atom),
      ← Matrix.mul_kronecker_mul a DL (1 : Atom) betaR,
      ← Matrix.mul_kronecker_mul a (1 : StageOne) (1 : Atom) DR]
  simp only [Matrix.one_mul, Matrix.mul_one]
  ext x y
  simp [Matrix.kroneckerMap_apply]
  ring

/-- First commutator with a right observable:
the left Dirac term retains [β_R,b], and the right Dirac term contributes
I ⊗ [D_R,b]. -/
theorem commutator_compositeDirac_embedRight
    (DL : StageOne) (betaR DR b : Atom) :
    commutator (compositeDirac DL betaR DR) (embedRight b) =
      DL ⊗ₖ commutatorR betaR b +
      (1 : StageOne) ⊗ₖ commutatorR DR b := by
  change (DL ⊗ₖ betaR + (1 : StageOne) ⊗ₖ DR) * ((1 : StageOne) ⊗ₖ b) -
      ((1 : StageOne) ⊗ₖ b) * (DL ⊗ₖ betaR + (1 : StageOne) ⊗ₖ DR) =
    DL ⊗ₖ (betaR * b - b * betaR) + (1 : StageOne) ⊗ₖ (DR * b - b * DR)
  rw [Matrix.add_mul, Matrix.mul_add]
  rw [← Matrix.mul_kronecker_mul DL (1 : StageOne) betaR b,
      ← Matrix.mul_kronecker_mul (1 : StageOne) (1 : StageOne) DR b,
      ← Matrix.mul_kronecker_mul (1 : StageOne) DL b betaR,
      ← Matrix.mul_kronecker_mul (1 : StageOne) (1 : StageOne) b DR]
  simp only [Matrix.one_mul, Matrix.mul_one]
  ext x y
  simp [Matrix.kroneckerMap_apply]
  ring

/-- Exact factorization of the left-right double commutator:
  [[D_tot, a⊗I], I⊗b] = [D_L,a] ⊗ [β_R,b]. -/
theorem orderOne_factorization
    (DL a : StageOne) (betaR DR b : Atom) :
    commutator
        (commutator (compositeDirac DL betaR DR) (embedLeft a))
        (embedRight b) =
      commutatorL DL a ⊗ₖ commutatorR betaR b := by
  rw [commutator_compositeDirac_embedLeft]
  change (commutatorL DL a ⊗ₖ betaR) * ((1 : StageOne) ⊗ₖ b) -
      ((1 : StageOne) ⊗ₖ b) * (commutatorL DL a ⊗ₖ betaR) =
    commutatorL DL a ⊗ₖ (betaR * b - b * betaR)
  rw [← Matrix.mul_kronecker_mul (commutatorL DL a) (1 : StageOne) betaR b,
      ← Matrix.mul_kronecker_mul (1 : StageOne) (commutatorL DL a) b betaR]
  simp only [Matrix.mul_one, Matrix.one_mul]
  ext x y
  simp [Matrix.kroneckerMap_apply]
  ring

/-- Finite order-one condition under the exact evenness hypothesis
[β_R,b]=0. -/
theorem orderOne_of_right_even
    (DL a : StageOne) (betaR DR b : Atom)
    (heven : commutatorR betaR b = 0) :
    commutator
        (commutator (compositeDirac DL betaR DR) (embedLeft a))
        (embedRight b) = 0 := by
  rw [orderOne_factorization, heven]
  ext i j
  simp [Matrix.kroneckerMap_apply]
  rfl

/-- Equivalent hypothesis written directly as β_R b = b β_R. -/
theorem orderOne_of_right_commutes
    (DL a : StageOne) (betaR DR b : Atom)
    (heven : betaR * b = b * betaR) :
    commutator
        (commutator (compositeDirac DL betaR DR) (embedLeft a))
        (embedRight b) = 0 := by
  apply orderOne_of_right_even
  unfold commutatorR
  rw [heven]
  simp

/-- Diagonal 2×2 observables commute with the standard split grading β. -/
theorem diagonal_commutes_kreinBeta (d0 d1 : ℝ) :
    commutatorR kreinBeta !![d0, 0; 0, d1] = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [commutatorR, kreinBeta, Eplus]

/-- Hence every diagonal right observable satisfies the finite order-one
condition for arbitrary left observable and arbitrary left/right Dirac data. -/
theorem orderOne_diagonal_right
    (DL a : StageOne) (DR : Atom) (d0 d1 : ℝ) :
    commutator
        (commutator
          (compositeDirac DL kreinBeta DR)
          (embedLeft a))
        (embedRight !![d0, 0; 0, d1]) = 0 := by
  apply orderOne_of_right_even
  exact diagonal_commutes_kreinBeta d0 d1

/-- Reversing the two commuting observables preserves the obstruction. -/
theorem dual_orderOne_factorization
    (DL a : StageOne) (betaR DR b : Atom) :
    commutator
        (commutator (compositeDirac DL betaR DR) (embedRight b))
        (embedLeft a) = commutatorL DL a ⊗ₖ commutatorR betaR b := by
  rw [commutator_compositeDirac_embedRight]
  change (DL ⊗ₖ commutatorR betaR b + (1 : StageOne) ⊗ₖ commutatorR DR b) * (a ⊗ₖ (1 : Atom)) -
      (a ⊗ₖ (1 : Atom)) * (DL ⊗ₖ commutatorR betaR b + (1 : StageOne) ⊗ₖ commutatorR DR b) =
    (DL * a - a * DL) ⊗ₖ commutatorR betaR b
  rw [Matrix.add_mul, Matrix.mul_add]
  rw [← Matrix.mul_kronecker_mul DL a (commutatorR betaR b) (1 : Atom),
      ← Matrix.mul_kronecker_mul (1 : StageOne) a (commutatorR DR b) (1 : Atom),
      ← Matrix.mul_kronecker_mul a DL (1 : Atom) (commutatorR betaR b),
      ← Matrix.mul_kronecker_mul a (1 : StageOne) (1 : Atom) (commutatorR DR b)]
  simp only [Matrix.one_mul, Matrix.mul_one]
  ext x y
  simp [Matrix.kroneckerMap_apply]
  ring

/-- Right evenness also kills the reversed double commutator. -/
theorem dual_orderOne_of_right_commutes
    (DL a : StageOne) (betaR DR b : Atom)
    (heven : betaR * b = b * betaR) :
    commutator
        (commutator (compositeDirac DL betaR DR) (embedRight b))
        (embedLeft a) = 0 := by
  rw [dual_orderOne_factorization]
  have hcomm : commutatorR betaR b = 0 := by
    dsimp [commutatorR]
    rw [heven, sub_self]
  rw [hcomm]
  ext i j
  simp [Matrix.kroneckerMap_apply]
  rfl

/-- Consolidated finite bipartite order-zero/order-one packet. -/
theorem bipartite_order_packet
    (DL a : StageOne) (betaR DR b : Atom)
    (heven : betaR * b = b * betaR) :
    commutator (embedLeft a) (embedRight b) = 0 ∧
    commutator
        (commutator (compositeDirac DL betaR DR) (embedLeft a))
        (embedRight b) = 0 ∧
    commutator
        (commutator (compositeDirac DL betaR DR) (embedRight b))
        (embedLeft a) = 0 := by
  exact ⟨orderZero a b,
    orderOne_of_right_commutes DL a betaR DR b heven,
    dual_orderOne_of_right_commutes DL a betaR DR b heven⟩

end InfoGeometry.Canonical.Cl11BipartiteOrderOneCondition
