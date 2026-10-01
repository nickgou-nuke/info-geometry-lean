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

The opposite ordering is even simpler:

  [[D_tot, I ⊗ b], a ⊗ I] = 0

for all a,b, because the surviving commutator lives purely in the right tensor
factor.

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
  unfold commutator embedLeft embedRight
  rw [Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul]
  simp

/-- First commutator with a left observable:
the right-Dirac term drops out and only [D_L,a] ⊗ β_R remains. -/
theorem commutator_compositeDirac_embedLeft
    (DL a : StageOne) (betaR DR : Atom) :
    commutator (compositeDirac DL betaR DR) (embedLeft a) =
      commutatorL DL a ⊗ₖ betaR := by
  unfold commutator compositeDirac embedLeft commutatorL
  rw [Matrix.add_mul, Matrix.mul_add]
  repeat rw [Matrix.mul_kronecker_mul]
  simp only [Matrix.one_mul, Matrix.mul_one]
  ext x y
  simp [Matrix.kroneckerMap_apply, commutatorL]
  ring

/-- First commutator with a right observable:
the left Dirac term retains [β_R,b], and the right Dirac term contributes
I ⊗ [D_R,b]. -/
theorem commutator_compositeDirac_embedRight
    (DL : StageOne) (betaR DR b : Atom) :
    commutator (compositeDirac DL betaR DR) (embedRight b) =
      DL ⊗ₖ commutatorR betaR b +
      (1 : StageOne) ⊗ₖ commutatorR DR b := by
  unfold commutator compositeDirac embedRight commutatorR
  rw [Matrix.add_mul, Matrix.mul_add]
  repeat rw [Matrix.mul_kronecker_mul]
  simp only [Matrix.one_mul, Matrix.mul_one]
  ext x y
  simp [Matrix.kroneckerMap_apply, commutatorR]
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
  unfold commutator embedRight commutatorR
  rw [Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul]
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
  simp

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
    simp [commutatorR, kreinBeta, Eplus,
      Matrix.mul_apply, Fin.sum_univ_two]

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

/-- Dual double commutator:
after commuting D_tot with a right observable, commuting with any left
observable vanishes identically. -/
theorem dual_orderOne
    (DL a : StageOne) (betaR DR b : Atom) :
    commutator
        (commutator (compositeDirac DL betaR DR) (embedRight b))
        (embedLeft a) = 0 := by
  rw [commutator_compositeDirac_embedRight]
  unfold commutator embedLeft
  rw [Matrix.add_mul, Matrix.mul_add]
  repeat rw [Matrix.mul_kronecker_mul]
  simp only [Matrix.one_mul, Matrix.mul_one]
  abel

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
    dual_orderOne DL a betaR DR b⟩

end InfoGeometry.Canonical.Cl11BipartiteOrderOneCondition
