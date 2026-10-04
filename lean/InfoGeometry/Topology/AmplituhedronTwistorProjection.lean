
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

open Matrix
open scoped BigOperators

namespace AmplituhedronTwistorProjection

variable {R : Type*} [CommRing R]

def minor2 (C : Matrix (Fin 2) (Fin 4) R) (a b : Fin 4) : R :=
  C 0 a * C 1 b - C 1 a * C 0 b

def det4 (M : Matrix (Fin 4) (Fin 4) R) : R :=
  M 0 0 * (M 1 1 * (M 2 2 * M 3 3 - M 2 3 * M 3 2) -
           M 1 2 * (M 2 1 * M 3 3 - M 2 3 * M 3 1) +
           M 1 3 * (M 2 1 * M 3 2 - M 2 2 * M 3 1)) -
  M 0 1 * (M 1 0 * (M 2 2 * M 3 3 - M 2 3 * M 3 2) -
           M 1 2 * (M 2 0 * M 3 3 - M 2 3 * M 3 0) +
           M 1 3 * (M 2 0 * M 3 2 - M 2 2 * M 3 0)) +
  M 0 2 * (M 1 0 * (M 2 1 * M 3 3 - M 2 3 * M 3 1) -
           M 1 1 * (M 2 0 * M 3 3 - M 2 3 * M 3 0) +
           M 1 3 * (M 2 0 * M 3 1 - M 2 1 * M 3 0)) -
  M 0 3 * (M 1 0 * (M 2 1 * M 3 2 - M 2 2 * M 3 1) -
           M 1 1 * (M 2 0 * M 3 2 - M 2 2 * M 3 0) +
           M 1 2 * (M 2 0 * M 3 1 - M 2 1 * M 3 0))

def twistorProj (C : Matrix (Fin 2) (Fin 4) R) (Z : Matrix (Fin 4) (Fin 4) R) :
    Matrix (Fin 2) (Fin 4) R :=
  C * Z

lemma twistorProj_apply (C : Matrix (Fin 2) (Fin 4) R) (Z : Matrix (Fin 4) (Fin 4) R)
    (r : Fin 2) (c : Fin 4) :
    twistorProj C Z r c = C r 0 * Z 0 c + C r 1 * Z 1 c + C r 2 * Z 2 c + C r 3 * Z 3 c := by
  dsimp [twistorProj, Matrix.mul_apply]
  rw [Fin.sum_univ_four]

def twistorMatrix (Y : Matrix (Fin 2) (Fin 4) R) (Z : Matrix (Fin 4) (Fin 4) R) (a b : Fin 4) :
    Matrix (Fin 4) (Fin 4) R :=
  fun r c =>
    if r = 0 then Y 0 c
    else if r = 1 then Y 1 c
    else if r = 2 then Z a c
    else Z b c

@[simp] lemma twistorMatrix_row0 (Y : Matrix (Fin 2) (Fin 4) R) (Z : Matrix (Fin 4) (Fin 4) R)
    (a b : Fin 4) (c : Fin 4) :
    twistorMatrix Y Z a b 0 c = Y 0 c := rfl

@[simp] lemma twistorMatrix_row1 (Y : Matrix (Fin 2) (Fin 4) R) (Z : Matrix (Fin 4) (Fin 4) R)
    (a b : Fin 4) (c : Fin 4) :
    twistorMatrix Y Z a b 1 c = Y 1 c := rfl

@[simp] lemma twistorMatrix_row2 (Y : Matrix (Fin 2) (Fin 4) R) (Z : Matrix (Fin 4) (Fin 4) R)
    (a b : Fin 4) (c : Fin 4) :
    twistorMatrix Y Z a b 2 c = Z a c := rfl

@[simp] lemma twistorMatrix_row3 (Y : Matrix (Fin 2) (Fin 4) R) (Z : Matrix (Fin 4) (Fin 4) R)
    (a b : Fin 4) (c : Fin 4) :
    twistorMatrix Y Z a b 3 c = Z b c := rfl

def twistorBracket (Y : Matrix (Fin 2) (Fin 4) R) (Z : Matrix (Fin 4) (Fin 4) R) (a b : Fin 4) : R :=
  det4 (twistorMatrix Y Z a b)

theorem twistorBracket_skew (Y : Matrix (Fin 2) (Fin 4) R) (Z : Matrix (Fin 4) (Fin 4) R) (a b : Fin 4) :
    twistorBracket Y Z b a = - twistorBracket Y Z a b := by
  dsimp [twistorBracket, det4]
  simp [twistorMatrix_row0, twistorMatrix_row1, twistorMatrix_row2, twistorMatrix_row3]
  ring

theorem twistorBracket_01 (C : Matrix (Fin 2) (Fin 4) R) (Z : Matrix (Fin 4) (Fin 4) R) :
    twistorBracket (twistorProj C Z) Z 0 1 = minor2 C 2 3 * det4 Z := by
  dsimp [twistorBracket, det4, minor2]
  simp [twistorMatrix_row0, twistorMatrix_row1, twistorMatrix_row2, twistorMatrix_row3, twistorProj_apply]
  ring

theorem twistorBracket_02 (C : Matrix (Fin 2) (Fin 4) R) (Z : Matrix (Fin 4) (Fin 4) R) :
    twistorBracket (twistorProj C Z) Z 0 2 = - (minor2 C 1 3 * det4 Z) := by
  dsimp [twistorBracket, det4, minor2]
  simp [twistorMatrix_row0, twistorMatrix_row1, twistorMatrix_row2, twistorMatrix_row3, twistorProj_apply]
  ring

theorem twistorBracket_03 (C : Matrix (Fin 2) (Fin 4) R) (Z : Matrix (Fin 4) (Fin 4) R) :
    twistorBracket (twistorProj C Z) Z 0 3 = minor2 C 1 2 * det4 Z := by
  dsimp [twistorBracket, det4, minor2]
  simp [twistorMatrix_row0, twistorMatrix_row1, twistorMatrix_row2, twistorMatrix_row3, twistorProj_apply]
  ring

theorem twistorBracket_12 (C : Matrix (Fin 2) (Fin 4) R) (Z : Matrix (Fin 4) (Fin 4) R) :
    twistorBracket (twistorProj C Z) Z 1 2 = minor2 C 0 3 * det4 Z := by
  dsimp [twistorBracket, det4, minor2]
  simp [twistorMatrix_row0, twistorMatrix_row1, twistorMatrix_row2, twistorMatrix_row3, twistorProj_apply]
  ring

theorem twistorBracket_13 (C : Matrix (Fin 2) (Fin 4) R) (Z : Matrix (Fin 4) (Fin 4) R) :
    twistorBracket (twistorProj C Z) Z 1 3 = - (minor2 C 0 2 * det4 Z) := by
  dsimp [twistorBracket, det4, minor2]
  simp [twistorMatrix_row0, twistorMatrix_row1, twistorMatrix_row2, twistorMatrix_row3, twistorProj_apply]
  ring

theorem twistorBracket_23 (C : Matrix (Fin 2) (Fin 4) R) (Z : Matrix (Fin 4) (Fin 4) R) :
    twistorBracket (twistorProj C Z) Z 2 3 = minor2 C 0 1 * det4 Z := by
  dsimp [twistorBracket, det4, minor2]
  simp [twistorMatrix_row0, twistorMatrix_row1, twistorMatrix_row2, twistorMatrix_row3, twistorProj_apply]
  ring

def IsTotallyPositive24 (C : Matrix (Fin 2) (Fin 4) ℝ) : Prop :=
  0 < minor2 C 0 1 ∧
  0 < minor2 C 0 2 ∧
  0 < minor2 C 0 3 ∧
  0 < minor2 C 1 2 ∧
  0 < minor2 C 1 3 ∧
  0 < minor2 C 2 3

theorem twistorBracket_boundary_01_pos {C : Matrix (Fin 2) (Fin 4) ℝ} {Z : Matrix (Fin 4) (Fin 4) ℝ}
    (hC : IsTotallyPositive24 C) (hZ : 0 < det4 Z) :
    0 < twistorBracket (twistorProj C Z) Z 0 1 := by
  rw [twistorBracket_01]
  exact mul_pos hC.2.2.2.2.2 hZ

theorem twistorBracket_boundary_12_pos {C : Matrix (Fin 2) (Fin 4) ℝ} {Z : Matrix (Fin 4) (Fin 4) ℝ}
    (hC : IsTotallyPositive24 C) (hZ : 0 < det4 Z) :
    0 < twistorBracket (twistorProj C Z) Z 1 2 := by
  rw [twistorBracket_12]
  exact mul_pos hC.2.2.1 hZ

theorem twistorBracket_boundary_23_pos {C : Matrix (Fin 2) (Fin 4) ℝ} {Z : Matrix (Fin 4) (Fin 4) ℝ}
    (hC : IsTotallyPositive24 C) (hZ : 0 < det4 Z) :
    0 < twistorBracket (twistorProj C Z) Z 2 3 := by
  rw [twistorBracket_23]
  exact mul_pos hC.1 hZ

theorem twistorBracket_boundary_03_pos {C : Matrix (Fin 2) (Fin 4) ℝ} {Z : Matrix (Fin 4) (Fin 4) ℝ}
    (hC : IsTotallyPositive24 C) (hZ : 0 < det4 Z) :
    0 < twistorBracket (twistorProj C Z) Z 0 3 := by
  rw [twistorBracket_03]
  exact mul_pos hC.2.2.2.1 hZ

theorem amplituhedron_boundary_facets_pos
    {C : Matrix (Fin 2) (Fin 4) ℝ} {Z : Matrix (Fin 4) (Fin 4) ℝ}
    (hC : IsTotallyPositive24 C) (hZ : 0 < det4 Z) :
    0 < twistorBracket (twistorProj C Z) Z 0 1 ∧
    0 < twistorBracket (twistorProj C Z) Z 1 2 ∧
    0 < twistorBracket (twistorProj C Z) Z 2 3 ∧
    0 < twistorBracket (twistorProj C Z) Z 0 3 :=
  ⟨twistorBracket_boundary_01_pos hC hZ,
   twistorBracket_boundary_12_pos hC hZ,
   twistorBracket_boundary_23_pos hC hZ,
   twistorBracket_boundary_03_pos hC hZ⟩

theorem twistorBracket_chord_02_neg
    {C : Matrix (Fin 2) (Fin 4) ℝ} {Z : Matrix (Fin 4) (Fin 4) ℝ}
    (hC : IsTotallyPositive24 C) (hZ : 0 < det4 Z) :
    twistorBracket (twistorProj C Z) Z 0 2 < 0 := by
  rw [twistorBracket_02]
  have : 0 < minor2 C 1 3 * det4 Z := mul_pos hC.2.2.2.2.1 hZ
  linarith

theorem twistorBracket_chord_13_neg
    {C : Matrix (Fin 2) (Fin 4) ℝ} {Z : Matrix (Fin 4) (Fin 4) ℝ}
    (hC : IsTotallyPositive24 C) (hZ : 0 < det4 Z) :
    twistorBracket (twistorProj C Z) Z 1 3 < 0 := by
  rw [twistorBracket_13]
  have : 0 < minor2 C 0 2 * det4 Z := mul_pos hC.2.1 hZ
  linarith

def boundaryMeasurementMatrix (t₁ t₂ t₃ t₄ : ℝ) : Matrix (Fin 2) (Fin 4) ℝ :=
  !![1, t₁, 0, -t₄;
     0, t₂, 1,  t₃]

theorem boundaryMeasurement_plucker_pos {t₁ t₂ t₃ t₄ : ℝ}
    (h1 : 0 < t₁) (h2 : 0 < t₂) (h3 : 0 < t₃) (h4 : 0 < t₄) :
    IsTotallyPositive24 (boundaryMeasurementMatrix t₁ t₂ t₃ t₄) := by
  dsimp [IsTotallyPositive24, minor2, boundaryMeasurementMatrix]
  refine ⟨by linarith, by linarith, by linarith, by linarith, ?_, by linarith⟩
  have h13 : 0 < t₁ * t₃ := mul_pos h1 h3
  have h24 : 0 < t₂ * t₄ := mul_pos h2 h4
  linarith

theorem amplituhedron_from_plabic_weights
    {t₁ t₂ t₃ t₄ : ℝ} (h1 : 0 < t₁) (h2 : 0 < t₂) (h3 : 0 < t₃) (h4 : 0 < t₄)
    {Z : Matrix (Fin 4) (Fin 4) ℝ} (hZ : 0 < det4 Z) :
    let C := boundaryMeasurementMatrix t₁ t₂ t₃ t₄
    0 < twistorBracket (twistorProj C Z) Z 0 1 ∧
    0 < twistorBracket (twistorProj C Z) Z 1 2 ∧
    0 < twistorBracket (twistorProj C Z) Z 2 3 ∧
    0 < twistorBracket (twistorProj C Z) Z 0 3 :=
  amplituhedron_boundary_facets_pos (boundaryMeasurement_plucker_pos h1 h2 h3 h4) hZ

end AmplituhedronTwistorProjection
