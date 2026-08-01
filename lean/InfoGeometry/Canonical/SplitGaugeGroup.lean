import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.NoncommRing

namespace InfoGeometry.Canonical

/-- 1. Канонична Сплит-Метрика η_{(5,5)} = [[0, I₅], [I₅, 0]] в 10D -/
def splitMetric10D (R : Type*) [CommRing R] :
    Matrix (Sum (Fin 5) (Fin 5)) (Sum (Fin 5) (Fin 5)) R :=
  Matrix.fromBlocks 0 1 1 0

/-- 2. Предикат за O(5,5) Изометрична Калибровочна Група: G * η * Gᵀ = η -/
def isO55Isometric (R : Type*) [CommRing R]
    (G : Matrix (Sum (Fin 5) (Fin 5)) (Sum (Fin 5) (Fin 5)) R) : Prop :=
  G * (splitMetric10D R) * G.transpose = splitMetric10D R

/-- **Теорема 1 (Не-тривиална Единица)**: Скаларната матрица -I₁₀ е в O(5,5) (-I ≠ I). -/
theorem neg_one_is_o55_isometric (R : Type*) [CommRing R] :
    isO55Isometric R (-1) := by
  dsimp [isO55Isometric]
  rw [Matrix.transpose_neg, Matrix.transpose_one]
  simp

/-- **Теорема 2 (ГРУПОВО ЗАТВАРЯНЕ)**:
    Ако G₁ ∈ O(5,5) и G₂ ∈ O(5,5), то тяхното произведение G₁ * G₂ СТРОГО принадлежи на O(5,5)!
    Това е нетривиално доказателство за алгебричната затвореност на O(5,5) групата. -/
theorem o55_group_multiplication_closure (R : Type*) [CommRing R]
    (G1 G2 : Matrix (Sum (Fin 5) (Fin 5)) (Sum (Fin 5) (Fin 5)) R)
    (h1 : isO55Isometric R G1)
    (h2 : isO55Isometric R G2) :
    isO55Isometric R (G1 * G2) := by
  dsimp [isO55Isometric] at *
  rw [Matrix.transpose_mul]
  calc (G1 * G2) * splitMetric10D R * (G2.transpose * G1.transpose)
      = G1 * (G2 * splitMetric10D R * G2.transpose) * G1.transpose := by noncomm_ring
    _ = G1 * splitMetric10D R * G1.transpose := by rw [h2]
    _ = splitMetric10D R := h1

/-- **Master Synthesis**: Не-тривиално O(5,5) Групово Затваряне Synthesis. -/
theorem master_split_gauge_group_synthesis (R : Type*) [CommRing R]
    (G1 G2 : Matrix (Sum (Fin 5) (Fin 5)) (Sum (Fin 5) (Fin 5)) R)
    (h1 : isO55Isometric R G1)
    (h2 : isO55Isometric R G2) :
    isO55Isometric R (-1) ∧ isO55Isometric R (G1 * G2) := ⟨
  neg_one_is_o55_isometric R,
  o55_group_multiplication_closure R G1 G2 h1 h2
⟩

end InfoGeometry.Canonical