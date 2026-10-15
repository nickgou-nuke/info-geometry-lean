import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.ColeFuryQuadrantMatrixUnits

/-!
# Cole-Fury 32-dimensional ideal quadrant laws

This module is the Lean twin of `tools/sympy/cole_fury_ideals.py`.
It formalizes exact `32 × 32` integer block matrices for the `16+16` spinor
quadrant decomposition used by the finite Pin(5,5) glide/projective-center lane.

#### BUCKET 1: CLOSED FINITE THEOREMS
The concrete matrices below prove:

* upper-left and lower-right diagonal quadrant projectors are idempotent;
* the upper-right horizon `horizonUp` and lower-left horizon `horizonDown` are nilpotent;
* `horizonUp * horizonDown = upperLeft` and `horizonDown * horizonUp = lowerRight`;
* the commutator `[horizonDown, horizonUp]` closes to `diag(-I₁₆,+I₁₆)`;
* the diagonal grading core squares to identity and acts on the horizons by
  weights `-2` and `+2`.

#### BUCKET 3: OPEN CLOSURE DEBT
This is a finite quadrant-block law surface.  It does not prove a physical
Cole-Fury/electron-positron classification theorem or a Cuntz quasilattice
boundary theorem.
-/


namespace InfoGeometry.OperatorAlgebra.ColeFury

open Matrix

abbrev Spin32Matrix := InfoGeometry.Algebra.FiniteSpin.Mat32Z

/-- Upper-left `16 × 16` diagonal block. -/
def upperLeft : Spin32Matrix :=
  fun i j => if i.val < 16 ∧ j = i then 1 else 0

/-- Lower-right `16 × 16` diagonal block. -/
def lowerRight : Spin32Matrix :=
  fun i j => if 16 ≤ i.val ∧ j = i then 1 else 0

/-- Upper-right nilpotent horizon block. -/
def horizonUp : Spin32Matrix :=
  fun i j => if i.val < 16 ∧ j.val = i.val + 16 then 1 else 0

/-- Lower-left conjugate nilpotent horizon block. -/
def horizonDown : Spin32Matrix :=
  fun i j => if 16 ≤ i.val ∧ j.val + 16 = i.val then 1 else 0

/-- Diagonal grading core obtained as `[g₋₁,g₊₁] = horizonDown*horizonUp - horizonUp*horizonDown`. -/
def g0Core : Spin32Matrix := horizonDown * horizonUp - horizonUp * horizonDown

/-- Explicit diagonal `diag(-I₁₆,+I₁₆)` target for the commutator closure. -/
def expectedG0Core : Spin32Matrix := -upperLeft + lowerRight

private def splitIndex : Fin 32 ≃ Fin 16 ⊕ Fin 16 :=
  (finSumFinEquiv (m := 16) (n := 16)).symm

private abbrev blockReindex :
    Spin32Matrix ≃ₐ[ℤ]
      Matrix (Fin 16 ⊕ Fin 16) (Fin 16 ⊕ Fin 16) ℤ :=
  Matrix.reindexAlgEquiv ℤ ℤ splitIndex

private theorem upperLeft_reindex :
    blockReindex upperLeft =
      InfoGeometry.Algebra.ColeFury.upperLeft (R := ℤ) (n := 16) := by
  ext i j
  cases i <;> cases j <;>
    simp [blockReindex, splitIndex, upperLeft,
      InfoGeometry.Algebra.ColeFury.upperLeft, Matrix.fromBlocks,
      finSumFinEquiv, Fin.ext_iff, Fin.val_castAdd,
      Matrix.one_apply] <;> omega

private theorem lowerRight_reindex :
    blockReindex lowerRight =
      InfoGeometry.Algebra.ColeFury.lowerRight (R := ℤ) (n := 16) := by
  ext i j
  cases i <;> cases j <;>
    simp [blockReindex, splitIndex, lowerRight,
      InfoGeometry.Algebra.ColeFury.lowerRight, Matrix.fromBlocks,
      finSumFinEquiv, Fin.ext_iff, Fin.val_castAdd,
      Matrix.one_apply] <;> omega

private theorem horizonUp_reindex :
    blockReindex horizonUp =
      InfoGeometry.Algebra.ColeFury.horizonUp (R := ℤ) (n := 16) := by
  ext i j
  cases i <;> cases j <;>
    simp [blockReindex, splitIndex, horizonUp,
      InfoGeometry.Algebra.ColeFury.horizonUp, Matrix.fromBlocks,
      finSumFinEquiv, Fin.ext_iff, Fin.val_castAdd,
      Matrix.one_apply] <;> omega

private theorem horizonDown_reindex :
    blockReindex horizonDown =
      InfoGeometry.Algebra.ColeFury.horizonDown (R := ℤ) (n := 16) := by
  ext i j
  cases i <;> cases j <;>
    simp [blockReindex, splitIndex, horizonDown,
      InfoGeometry.Algebra.ColeFury.horizonDown, Matrix.fromBlocks,
      finSumFinEquiv, Fin.ext_iff, Fin.val_castAdd,
      Matrix.one_apply] <;> omega

private theorem expectedG0Core_reindex :
    blockReindex expectedG0Core =
      -InfoGeometry.Algebra.ColeFury.upperLeft (R := ℤ) (n := 16) +
        InfoGeometry.Algebra.ColeFury.lowerRight (R := ℤ) (n := 16) := by
  simp only [expectedG0Core, map_add, map_neg, lowerRight_reindex,
    upperLeft_reindex]

private theorem blockCore_horizonUp_weight :
    (InfoGeometry.Algebra.ColeFury.lowerRight (R := ℤ) (n := 16) -
        InfoGeometry.Algebra.ColeFury.upperLeft (R := ℤ) (n := 16)) *
        InfoGeometry.Algebra.ColeFury.horizonUp (R := ℤ) (n := 16) -
      InfoGeometry.Algebra.ColeFury.horizonUp (R := ℤ) (n := 16) *
        (InfoGeometry.Algebra.ColeFury.lowerRight (R := ℤ) (n := 16) -
          InfoGeometry.Algebra.ColeFury.upperLeft (R := ℤ) (n := 16)) =
      (-2 : ℤ) • InfoGeometry.Algebra.ColeFury.horizonUp (R := ℤ) (n := 16) := by
  have hcore :
      InfoGeometry.Algebra.ColeFury.lowerRight (R := ℤ) (n := 16) -
          InfoGeometry.Algebra.ColeFury.upperLeft (R := ℤ) (n := 16) =
        Matrix.fromBlocks (-1 : Matrix (Fin 16) (Fin 16) ℤ) 0 0 1 := by
    simp only [InfoGeometry.Algebra.ColeFury.lowerRight,
      InfoGeometry.Algebra.ColeFury.upperLeft, sub_eq_add_neg,
      Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
    simp
  rw [hcore, InfoGeometry.Algebra.ColeFury.horizonUp,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_smul]
  ext i j
  cases i <;> cases j
  all_goals simp [Matrix.fromBlocks, Matrix.one_apply]
  all_goals split_ifs <;> norm_num [Matrix.ofNat_apply, Matrix.neg_apply] <;> assumption

private theorem blockCore_horizonDown_weight :
    (InfoGeometry.Algebra.ColeFury.lowerRight (R := ℤ) (n := 16) -
        InfoGeometry.Algebra.ColeFury.upperLeft (R := ℤ) (n := 16)) *
        InfoGeometry.Algebra.ColeFury.horizonDown (R := ℤ) (n := 16) -
      InfoGeometry.Algebra.ColeFury.horizonDown (R := ℤ) (n := 16) *
        (InfoGeometry.Algebra.ColeFury.lowerRight (R := ℤ) (n := 16) -
          InfoGeometry.Algebra.ColeFury.upperLeft (R := ℤ) (n := 16)) =
      (2 : ℤ) • InfoGeometry.Algebra.ColeFury.horizonDown (R := ℤ) (n := 16) := by
  have hcore :
      InfoGeometry.Algebra.ColeFury.lowerRight (R := ℤ) (n := 16) -
          InfoGeometry.Algebra.ColeFury.upperLeft (R := ℤ) (n := 16) =
        Matrix.fromBlocks (-1 : Matrix (Fin 16) (Fin 16) ℤ) 0 0 1 := by
    simp only [InfoGeometry.Algebra.ColeFury.lowerRight,
      InfoGeometry.Algebra.ColeFury.upperLeft, sub_eq_add_neg,
      Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
    simp
  rw [hcore, InfoGeometry.Algebra.ColeFury.horizonDown,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_smul]
  ext i j
  cases i <;> cases j
  all_goals simp [Matrix.fromBlocks, Matrix.one_apply]
  all_goals split_ifs <;> norm_num [Matrix.ofNat_apply, Matrix.neg_apply] <;> assumption

/-- Structure packaging the quadrant splitting laws. -/
structure ColeFurySplit where
  horizonUp : Spin32Matrix
  horizonDown : Spin32Matrix
  h_nilpotent : horizonUp * horizonUp = 0
  h_dag_nilpotent : horizonDown * horizonDown = 0
  h_commutator : horizonDown * horizonUp - horizonUp * horizonDown = expectedG0Core

/-- Concrete quadrant split. -/
def concreteSplit : ColeFurySplit where
  horizonUp := horizonUp
  horizonDown := horizonDown
  h_nilpotent := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.zero_apply]
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hi : i.val < 16
    · by_cases hki : k.val = i.val + 16
      · simp [horizonUp, hi, hki]
      · simp [horizonUp, hi, hki]
    · simp [horizonUp, hi]
  h_dag_nilpotent := by
    unfold horizonDown
    decide
  h_commutator := by
    apply blockReindex.injective
    calc
      blockReindex (horizonDown * horizonUp - horizonUp * horizonDown) =
          InfoGeometry.Algebra.ColeFury.horizonDown (R := ℤ) (n := 16) *
              InfoGeometry.Algebra.ColeFury.horizonUp (R := ℤ) (n := 16) -
            InfoGeometry.Algebra.ColeFury.horizonUp (R := ℤ) (n := 16) *
              InfoGeometry.Algebra.ColeFury.horizonDown (R := ℤ) (n := 16) := by
        simp only [map_sub, map_mul, horizonDown_reindex, horizonUp_reindex]
      _ = InfoGeometry.Algebra.ColeFury.lowerRight (R := ℤ) (n := 16) -
            InfoGeometry.Algebra.ColeFury.upperLeft (R := ℤ) (n := 16) :=
        InfoGeometry.Algebra.ColeFury.quadrant_commutator
      _ = blockReindex expectedG0Core := by
        simp only [expectedG0Core, map_add, map_neg, lowerRight_reindex,
          upperLeft_reindex]
        abel

/-- Upper-left quadrant is an idempotent projector. -/
theorem upperLeft_idempotent : upperLeft * upperLeft = upperLeft := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · by_cases hi : i.val < 16 <;> simp [upperLeft, hi]
  · intro x _ hxi
    simp [upperLeft, hxi]
  · simp

/-- Lower-right quadrant is an idempotent projector. -/
theorem lowerRight_idempotent : lowerRight * lowerRight = lowerRight := by
  apply blockReindex.injective
  simp only [map_mul, lowerRight_reindex, InfoGeometry.Algebra.ColeFury.lowerRight_sq]

/-- Diagonal quadrants are orthogonal in this block decomposition. -/
theorem upperLeft_lowerRight_zero : upperLeft * lowerRight = 0 := by
  unfold upperLeft lowerRight
  decide

/-- Diagonal quadrants are orthogonal in the reverse order. -/
theorem lowerRight_upperLeft_zero : lowerRight * upperLeft = 0 := by
  unfold upperLeft lowerRight
  decide

/-- The two diagonal quadrants partition the full spinor identity. -/
theorem diagonal_quadrants_sum : upperLeft + lowerRight = 1 := by
  unfold upperLeft lowerRight
  decide

/-- The upper-right horizon block is nilpotent. -/
theorem horizonUp_nilpotent : horizonUp * horizonUp = 0 :=
  concreteSplit.h_nilpotent

/-- The lower-left horizon block is nilpotent. -/
theorem horizonDown_nilpotent : horizonDown * horizonDown = 0 :=
  concreteSplit.h_dag_nilpotent

/-- Upper-right followed by lower-left closes to the upper-left diagonal block. -/
theorem horizonUp_horizonDown : horizonUp * horizonDown = upperLeft := by
  apply blockReindex.injective
  simp only [map_mul, horizonUp_reindex, horizonDown_reindex, upperLeft_reindex,
    InfoGeometry.Algebra.ColeFury.horizonUp_mul_horizonDown]

/-- Lower-left followed by upper-right closes to the lower-right diagonal block. -/
theorem horizonDown_horizonUp : horizonDown * horizonUp = lowerRight := by
  apply blockReindex.injective
  simp only [map_mul, horizonDown_reindex, horizonUp_reindex, lowerRight_reindex,
    InfoGeometry.Algebra.ColeFury.horizonDown_mul_horizonUp]

/-- Anticommutator of the two horizon blocks is the full identity. -/
theorem horizon_anticomm_identity : horizonUp * horizonDown + horizonDown * horizonUp = 1 := by
  rw [horizonUp_horizonDown, horizonDown_horizonUp, diagonal_quadrants_sum]

/-- The horizon commutator closes into the diagonal grading core. -/
theorem horizon_commutator_expected :
    horizonDown * horizonUp - horizonUp * horizonDown = expectedG0Core :=
  concreteSplit.h_commutator

/-- The named grading core equals the explicit diagonal target. -/
theorem g0Core_eq_expected : g0Core = expectedG0Core := by
  unfold g0Core
  exact horizon_commutator_expected

/-- The diagonal grading core is an involution. -/
theorem g0Core_sq : g0Core * g0Core = 1 := by
  rw [g0Core_eq_expected]
  have hcore : expectedG0Core = lowerRight - upperLeft := by
    dsimp [expectedG0Core]
    abel
  rw [hcore]
  simp only [sub_mul, mul_sub, lowerRight_idempotent,
    lowerRight_upperLeft_zero, upperLeft_lowerRight_zero, upperLeft_idempotent]
  simpa [add_comm] using diagonal_quadrants_sum

/-- The diagonal grading core acts on the upper-right horizon with weight `-2`. -/
theorem g0Core_horizonUp_weight : g0Core * horizonUp - horizonUp * g0Core = (-2 : ℤ) • horizonUp := by
  rw [g0Core_eq_expected]
  apply blockReindex.injective
  calc
    blockReindex (expectedG0Core * horizonUp - horizonUp * expectedG0Core) =
        (-InfoGeometry.Algebra.ColeFury.upperLeft (R := ℤ) (n := 16) +
          InfoGeometry.Algebra.ColeFury.lowerRight (R := ℤ) (n := 16)) *
          InfoGeometry.Algebra.ColeFury.horizonUp (R := ℤ) (n := 16) -
        InfoGeometry.Algebra.ColeFury.horizonUp (R := ℤ) (n := 16) *
          (-InfoGeometry.Algebra.ColeFury.upperLeft (R := ℤ) (n := 16) +
            InfoGeometry.Algebra.ColeFury.lowerRight (R := ℤ) (n := 16)) := by
      simp only [map_sub, map_mul, expectedG0Core_reindex, horizonUp_reindex]
    _ = (-2 : ℤ) • InfoGeometry.Algebra.ColeFury.horizonUp (R := ℤ) (n := 16) := by
      have horder :
          -InfoGeometry.Algebra.ColeFury.upperLeft (R := ℤ) (n := 16) +
              InfoGeometry.Algebra.ColeFury.lowerRight (R := ℤ) (n := 16) =
            InfoGeometry.Algebra.ColeFury.lowerRight (R := ℤ) (n := 16) -
              InfoGeometry.Algebra.ColeFury.upperLeft (R := ℤ) (n := 16) := by
        abel
      rw [horder]
      exact blockCore_horizonUp_weight
    _ = blockReindex ((-2 : ℤ) • horizonUp) := by
      simp only [map_smul, horizonUp_reindex]

/-- The diagonal grading core acts on the lower-left horizon with weight `+2`. -/
theorem g0Core_horizonDown_weight : g0Core * horizonDown - horizonDown * g0Core = (2 : ℤ) • horizonDown := by
  rw [g0Core_eq_expected]
  apply blockReindex.injective
  calc
    blockReindex (expectedG0Core * horizonDown - horizonDown * expectedG0Core) =
        (-InfoGeometry.Algebra.ColeFury.upperLeft (R := ℤ) (n := 16) +
          InfoGeometry.Algebra.ColeFury.lowerRight (R := ℤ) (n := 16)) *
          InfoGeometry.Algebra.ColeFury.horizonDown (R := ℤ) (n := 16) -
        InfoGeometry.Algebra.ColeFury.horizonDown (R := ℤ) (n := 16) *
          (-InfoGeometry.Algebra.ColeFury.upperLeft (R := ℤ) (n := 16) +
            InfoGeometry.Algebra.ColeFury.lowerRight (R := ℤ) (n := 16)) := by
      simp only [map_sub, map_mul, expectedG0Core_reindex, horizonDown_reindex]
    _ = (2 : ℤ) • InfoGeometry.Algebra.ColeFury.horizonDown (R := ℤ) (n := 16) := by
      have horder :
          -InfoGeometry.Algebra.ColeFury.upperLeft (R := ℤ) (n := 16) +
              InfoGeometry.Algebra.ColeFury.lowerRight (R := ℤ) (n := 16) =
            InfoGeometry.Algebra.ColeFury.lowerRight (R := ℤ) (n := 16) -
              InfoGeometry.Algebra.ColeFury.upperLeft (R := ℤ) (n := 16) := by
        abel
      rw [horder]
      exact blockCore_horizonDown_weight
    _ = blockReindex ((2 : ℤ) • horizonDown) := by
      simp only [map_smul, horizonDown_reindex]

/-- Finite kernel-checked packet for the 32-dimensional quadrant ideal laws. -/
theorem coleFury_ideal_packet :
    upperLeft * upperLeft = upperLeft ∧
      lowerRight * lowerRight = lowerRight ∧
      horizonUp * horizonUp = 0 ∧
      horizonDown * horizonDown = 0 ∧
      horizonUp * horizonDown = upperLeft ∧
      horizonDown * horizonUp = lowerRight ∧
      horizonDown * horizonUp - horizonUp * horizonDown = expectedG0Core ∧
      g0Core * g0Core = 1 ∧
      g0Core * horizonUp - horizonUp * g0Core = (-2 : ℤ) • horizonUp ∧
      g0Core * horizonDown - horizonDown * g0Core = (2 : ℤ) • horizonDown := by
  exact ⟨upperLeft_idempotent, lowerRight_idempotent, horizonUp_nilpotent,
    horizonDown_nilpotent, horizonUp_horizonDown, horizonDown_horizonUp,
    horizon_commutator_expected, g0Core_sq, g0Core_horizonUp_weight,
    g0Core_horizonDown_weight⟩

end InfoGeometry.OperatorAlgebra.ColeFury
