import InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge

/-!
# The finite BitWord graph differential

The BitWord matrix stages provide the coefficient algebra, while the finite
BitWord cube provides the vertices.  This file records the concrete graph
coboundary from vertex cochains to edge cochains and its next coboundary on
triangles.  The square-zero law is proved by cancellation, not supplied as
structure data.

This is deliberately a finite graph-cochain owner.  It does not assert a
global de Rham or continuum differential.  Its product is only the
degree-zero pointwise matrix product, with the corresponding endpoint-aware
Leibniz law proved below.
-/

noncomputable section

namespace InfoGeometry.Canonical.BitWordGraphDifferential

open InfoGeometry.OperatorAlgebra.CantorBernoulliFiniteMatrixUnitBridge
open InfoGeometry.Canonical.UHFInductiveColimitBoundary

abbrev Vertex (n : ℕ) := BitWord n
abbrev Cochain0 (n : ℕ) := Vertex n → BitWordMatrixStage n
abbrev Cochain1 (n : ℕ) := Vertex n → Vertex n → BitWordMatrixStage n
abbrev Cochain2 (n : ℕ) := Vertex n → Vertex n → Vertex n → BitWordMatrixStage n
abbrev Cochain3 (n : ℕ) :=
  Vertex n → Vertex n → Vertex n → Vertex n → BitWordMatrixStage n
abbrev Cochain4 (n : ℕ) :=
  Vertex n → Vertex n → Vertex n → Vertex n → Vertex n → BitWordMatrixStage n

/-- Cochains on ordered finite simplices, with values in the BitWord stage algebra. -/
abbrev SimplexCochain (n k : ℕ) :=
  (Fin (k + 1) → Vertex n) → BitWordMatrixStage n

/-- The alternating face coboundary on ordered finite simplices. -/
def simplexCoboundary {n k : ℕ} (c : SimplexCochain n k) : SimplexCochain n (k + 1) :=
  fun σ => ∑ i : Fin (k + 2),
    (-1 : BitWordMatrixStage n) ^ i.1 • (c (σ ∘ Fin.succAbove i))

theorem face_comp_delete_zero_one :
    (Fin.succAbove (0 : Fin 3) ∘ Fin.succAbove (0 : Fin 2)) =
      (Fin.succAbove (1 : Fin 3) ∘ Fin.succAbove (0 : Fin 2)) := by
  funext i
  fin_cases i
  rfl

theorem face_comp_delete_zero_two :
    (Fin.succAbove (0 : Fin 3) ∘ Fin.succAbove (1 : Fin 2)) =
      (Fin.succAbove (2 : Fin 3) ∘ Fin.succAbove (0 : Fin 2)) := by
  funext i
  fin_cases i
  rfl

theorem face_comp_delete_one_two :
    (Fin.succAbove (1 : Fin 3) ∘ Fin.succAbove (1 : Fin 2)) =
      (Fin.succAbove (2 : Fin 3) ∘ Fin.succAbove (1 : Fin 2)) := by
  funext i
  fin_cases i
  rfl

/-- Pointwise product of zero-cochains.  The order is the matrix-algebra order. -/
def mul0 {n : ℕ} (f g : Cochain0 n) : Cochain0 n :=
  fun u => f u * g u

/-- Multiply a one-cochain on the right by the value at its terminal vertex. -/
def rightMul1 {n : ℕ} (g : Cochain1 n) (f : Cochain0 n) : Cochain1 n :=
  fun u v => g u v * f v

/-- Multiply a one-cochain on the left by the value at its initial vertex. -/
def leftMul1 {n : ℕ} (f : Cochain0 n) (g : Cochain1 n) : Cochain1 n :=
  fun u v => f u * g u v

/-- The degree-zero/degree-one cup action, using the initial vertex. -/
def cup01 {n : ℕ} (f : Cochain0 n) (g : Cochain1 n) : Cochain1 n :=
  leftMul1 f g

/-- The degree-zero/degree-two cup action, using the initial vertex. -/
def cup02 {n : ℕ} (f : Cochain0 n) (h : Cochain2 n) : Cochain2 n :=
  fun u v w => f u * h u v w

/-- The degree-zero/degree-three cup action, using the initial vertex. -/
def cup03 {n : ℕ} (f : Cochain0 n) (k : Cochain3 n) : Cochain3 n :=
  fun u v w x => f u * k u v w x

/-- The degree-zero/degree-four cup action, using the initial vertex. -/
def cup04 {n : ℕ} (f : Cochain0 n) (q : Cochain4 n) : Cochain4 n :=
  fun u v w x y => f u * q u v w x y

/-- The finite vertex-to-edge coboundary. -/
def d0 {n : ℕ} (f : Cochain0 n) (u v : Vertex n) : BitWordMatrixStage n :=
  f v - f u

/-- The finite edge-to-triangle coboundary. -/
def d1 {n : ℕ} (g : Cochain1 n) (u v w : Vertex n) : BitWordMatrixStage n :=
  g v w - g u w + g u v

/-- The next alternating coboundary, from triangles to tetrahedra. -/
def d2 {n : ℕ} (h : Cochain2 n) (u v w x : Vertex n) : BitWordMatrixStage n :=
  h v w x - h u w x + h u v x - h u v w

/-- The next alternating coboundary, from tetrahedra to 4-simplices. -/
def d3 {n : ℕ} (k : Cochain3 n) (u v w x y : Vertex n) : BitWordMatrixStage n :=
  k v w x y - k u w x y + k u v x y - k u v w y + k u v w x

/-- The next alternating coboundary, from 4-simplices to 5-simplices. -/
def d4 {n : ℕ} (q : Cochain4 n) (u v w x y z : Vertex n) : BitWordMatrixStage n :=
  q v w x y z - q u w x y z + q u v x y z - q u v w y z +
    q u v w x z - q u v w x y

theorem d1_d0 {n : ℕ} (f : Cochain0 n) (u v w : Vertex n) :
    d1 (d0 f) u v w = 0 := by
  simp [d1, d0]

theorem d2_d1 {n : ℕ} (g : Cochain1 n) (u v w x : Vertex n) :
    d2 (d1 g) u v w x = 0 := by
  simp [d2, d1]
  abel

theorem d3_d2 {n : ℕ} (h : Cochain2 n) (u v w x y : Vertex n) :
    d3 (d2 h) u v w x y = 0 := by
  simp [d3, d2]
  abel

theorem d4_d3 {n : ℕ} (k : Cochain3 n) (u v w x y z : Vertex n) :
    d4 (d3 k) u v w x y z = 0 := by
  simp [d4, d3]
  abel

theorem d0_swap {n : ℕ} (f : Cochain0 n) (u v : Vertex n) :
    d0 f v u = -d0 f u v := by
  simp [d0]

theorem d1_swap_of_swap {n : ℕ} (g : Cochain1 n)
    (h_swap : ∀ u v, g v u = -g u v) (u v w : Vertex n) :
    d1 g v u w = -d1 g u v w := by
  simp only [d1]
  rw [h_swap u v]
  noncomm_ring

theorem d0_mul0_leibniz {n : ℕ} (f g : Cochain0 n) (u v : Vertex n) :
    d0 (mul0 f g) u v =
      rightMul1 (d0 f) g u v + leftMul1 f (d0 g) u v := by
  simp [d0, mul0, rightMul1, leftMul1]
  noncomm_ring

theorem d1_cup01_leibniz {n : ℕ} (f : Cochain0 n) (g : Cochain1 n)
    (u v w : Vertex n) :
    d1 (cup01 f g) u v w =
      (d0 f u v) * g v w + f u * d1 g u v w := by
  simp [d1, d0, cup01, leftMul1]
  noncomm_ring

theorem d2_cup02_leibniz {n : ℕ} (f : Cochain0 n) (h : Cochain2 n)
    (u v w x : Vertex n) :
    d2 (cup02 f h) u v w x =
      (d0 f u v) * h v w x + f u * d2 h u v w x := by
  simp [d2, d0, cup02]
  noncomm_ring

theorem d3_cup03_leibniz {n : ℕ} (f : Cochain0 n) (k : Cochain3 n)
    (u v w x y : Vertex n) :
    d3 (cup03 f k) u v w x y =
      (d0 f u v) * k v w x y + f u * d3 k u v w x y := by
  simp [d3, d0, cup03]
  noncomm_ring

theorem d4_cup04_leibniz {n : ℕ} (f : Cochain0 n) (q : Cochain4 n)
    (u v w x y z : Vertex n) :
    d4 (cup04 f q) u v w x y z =
      (d0 f u v) * q v w x y z + f u * d4 q u v w x y z := by
  simp [d4, d0, cup04]
  noncomm_ring

end InfoGeometry.Canonical.BitWordGraphDifferential
