/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.Cl11TensorTower
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.RingTheory.Morita.Matrix

namespace InfoGeometry.Canonical.Cl11MoritaNeutralStabilization

open InfoGeometry.Clifford

/-!
# Finite-stage Clifford matrix and Morita readout

This owner records the associative matrix readout supplied by `TowerMatrix`
and proves that each finite real matrix stage is Morita equivalent to `ℝ`.
It does not identify the stage with a composition algebra, assert split Bott
periodicity, or pass the equivalence to a colimit or completion.
-/

abbrev StageThree := TowerMatrix.Mat 3

theorem stageThree_finPowTwo_eq_eight :
    (2 : ℕ) ^ 3 = 8 := by
  norm_num

theorem stageThree_index_card :
    Fintype.card (TowerMatrix.Idx 3) = 8 := by
  simpa using TowerMatrix.idx_card_pow_two 3

noncomputable def stageThreeMatrix8 :
    StageThree ≃ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℝ :=
  TowerMatrix.matEquivFinPowTwo 3

@[simp] theorem stageThreeMatrix8_apply (A : StageThree) :
    stageThreeMatrix8 A = TowerMatrix.matEquivFinPowTwo 3 A :=
  rfl

theorem stageThreeMatrix8_mul (A B : StageThree) :
    stageThreeMatrix8 (A * B) =
      stageThreeMatrix8 A * stageThreeMatrix8 B := by
  exact stageThreeMatrix8.map_mul A B

theorem stageThreeMatrix8_one :
    stageThreeMatrix8 (1 : StageThree) = 1 := by
  exact stageThreeMatrix8.map_one

noncomputable def standardMatrixStageEmbed (n : ℕ) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ →ₐ[ℝ]
      Matrix (Fin (2 ^ (n + 1))) (Fin (2 ^ (n + 1))) ℝ :=
  (TowerMatrix.matEquivFinPowTwo (n + 1)).toAlgHom.comp
    ((Cl11TensorTower.stageEmbed n).comp
      (TowerMatrix.matEquivFinPowTwo n).symm.toAlgHom)

theorem standardMatrixStageEmbed_compatibility
    (n : ℕ) (A : TowerMatrix.Mat n) :
    standardMatrixStageEmbed n
        (TowerMatrix.matEquivFinPowTwo n A) =
      TowerMatrix.matEquivFinPowTwo (n + 1)
        (Cl11TensorTower.stageEmbed n A) := by
  simp [standardMatrixStageEmbed]

theorem stageTwo_to_stageThree_matrix_compatibility
    (A : TowerMatrix.Mat 2) :
    standardMatrixStageEmbed 2
        (TowerMatrix.matEquivFinPowTwo 2 A) =
      stageThreeMatrix8 (Cl11TensorTower.stageEmbed 2 A) := by
  exact standardMatrixStageEmbed_compatibility 2 A

/-- Each finite real Clifford-tower stage is Morita equivalent to `ℝ`.
The equivalence is built by composing the tower's actual algebra equivalence
with Mathlib's matrix-module Morita equivalence; it concerns this finite stage
and makes no assertion about a colimit or a completion. -/
noncomputable def stageMoritaEquivalence (n : ℕ) :
    MoritaEquivalence ℝ (TowerMatrix.Mat n) ℝ :=
  (MoritaEquivalence.ofAlgEquiv (TowerMatrix.matEquivFinPowTwo n)).trans ℝ
    ((moritaEquivalenceMatrix ℝ ℝ (0 : Fin (2 ^ n))).symm ℝ)

/-- For an arbitrary, possibly noncommutative coefficient ring, left modules
over the full `n × n` matrix operator algebra are equivalent to left modules
over the coefficient ring. This is the module-category equivalence itself,
not only an assertion that two rings have the same finite-dimensional
representations. -/
noncomputable def arbitraryMatrixModuleEquivalence (A : Type*) [Ring A]
    {n : ℕ} (hn : 0 < n) : ModuleCat A ≌ ModuleCat (Matrix (Fin n) (Fin n) A) :=
  ModuleCat.matrixEquivalence A ⟨0, hn⟩

/-- The arbitrary-ring matrix-module equivalence supplies an explicit Morita
equivalence over the canonical central `ℤ`-algebra structures. -/
noncomputable def arbitraryMatrixMoritaEquivalence (A : Type*) [Ring A]
    [Algebra ℤ A] {n : ℕ} (hn : 0 < n) :
    MoritaEquivalence ℤ A (Matrix (Fin n) (Fin n) A) :=
  moritaEquivalenceMatrix A ℤ ⟨0, hn⟩

noncomputable def stageTwoMatrix4Unit
    (u : (TowerMatrix.Mat 2)ˣ) :
    (Matrix (Fin 4) (Fin 4) ℝ)ˣ :=
  Units.map (TowerMatrix.matEquivFinPowTwo 2).toMonoidHom u

@[simp] theorem stageTwoMatrix4Unit_val
    (u : (TowerMatrix.Mat 2)ˣ) :
    (stageTwoMatrix4Unit u : Matrix (Fin 4) (Fin 4) ℝ) =
      TowerMatrix.matEquivFinPowTwo 2 (u : TowerMatrix.Mat 2) := by
  simp [stageTwoMatrix4Unit]

@[simp] theorem stageTwoMatrix4Unit_one :
    stageTwoMatrix4Unit (1 : (TowerMatrix.Mat 2)ˣ) = 1 := by
  simp [stageTwoMatrix4Unit]

@[simp] theorem stageTwoMatrix4Unit_mul
    (u v : (TowerMatrix.Mat 2)ˣ) :
    stageTwoMatrix4Unit (u * v) =
      stageTwoMatrix4Unit u * stageTwoMatrix4Unit v := by
  simp [stageTwoMatrix4Unit]

/- The matrix algebra remains genuinely noncommutative even over a general
nontrivial coefficient ring: these two matrix units multiply in opposite
orders to different diagonal corners. -/
theorem matrixUnits_noncommute (A : Type*) [Ring A] [Nontrivial A]
    {n : ℕ} (hn : 2 ≤ n) :
    ∃ matI matJ : Matrix (Fin n) (Fin n) A,
      matI * matJ ≠ matJ * matI := by
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 2) hn
  refine ⟨Matrix.single ⟨0, hn0⟩ ⟨1, hn1⟩ 1,
    Matrix.single ⟨1, hn1⟩ ⟨0, hn0⟩ 1, ?_⟩
  intro h
  have h00 := congrFun (congrFun h ⟨0, hn0⟩) ⟨0, hn0⟩
  simp [Matrix.mul_apply, Matrix.single_apply] at h00

theorem matrixUnits4_noncommute :
    ∃ matI matJ : Matrix (Fin 4) (Fin 4) ℝ,
      matI * matJ ≠ matJ * matI :=
  matrixUnits_noncommute ℝ (by decide : 2 ≤ 4)

theorem matrixUnits8_noncommute :
    ∃ matI matJ : Matrix (Fin 8) (Fin 8) ℝ,
      matI * matJ ≠ matJ * matI :=
  matrixUnits_noncommute ℝ (by decide : 2 ≤ 8)

end InfoGeometry.Canonical.Cl11MoritaNeutralStabilization
