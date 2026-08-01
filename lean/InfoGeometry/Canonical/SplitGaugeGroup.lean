import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Algebra.Group.Basic

namespace InfoGeometry.Canonical

/-- 1. Канонична Сплит Метрика η_{(5,5)} = [[0, I₅], [I₅, 0]] в 10D -/
def splitMetric10D (R : Type*) [CommRing R] : Matrix (Sum (Fin 5) (Fin 5)) (Sum (Fin 5) (Fin 5)) R :=
  Matrix.fromBlocks 0 1 1 0

/-- 2. Предикат за O(5,5) Изометрична Калибровочна Група: G * η * Gᵀ = η -/
def isO55Isometric (R : Type*) [CommRing R]
    (G : Matrix (Sum (Fin 5) (Fin 5)) (Sum (Fin 5) (Fin 5)) R) : Prop :=
  G * (splitMetric10D R) * G.transpose = splitMetric10D R

/-- Теорема 1: Идентитетната 10x10 Матрица е O(5,5) Изометрия -/
theorem id_is_o55_isometric (R : Type*) [CommRing R] :
    isO55Isometric R 1 := by
  dsimp [isO55Isometric]
  rw [Matrix.transpose_one, mul_one, one_mul]

/-- Теорема 2: Сплит Метриката η_{(5,5)} е Симетрична -/
theorem splitMetric10D_symmetric (R : Type*) [CommRing R] :
    (splitMetric10D R).transpose = splitMetric10D R := by
  dsimp [splitMetric10D]
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · simp [Matrix.fromBlocks, Matrix.transpose_apply]
  · simp [Matrix.fromBlocks, Matrix.transpose_apply, Matrix.one_apply]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  · simp [Matrix.fromBlocks, Matrix.transpose_apply, Matrix.one_apply]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  · simp [Matrix.fromBlocks, Matrix.transpose_apply]

end InfoGeometry.Canonical