import InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinHadamard
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Graph sections of a doubled null frame

This is the finite coefficient-level form of the graph-section construction.
The two copies of `Fin 4 → ℝ` are null sheets, paired by the off-diagonal
bilinear form.  A matrix `H` selects the graph

`E_a = e_a⁺ + Σ_b H a b e_b⁻`.

The induced form is exactly `H + Hᵀ`.  No spacetime, analytic boundary, or
Tomita claim is hidden in this finite statement.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinGraphSection

open scoped BigOperators

abbrev Index := Fin 4
abbrev Sheet := Index → ℝ
abbrev Doubled := Sheet × Sheet
abbrev CoefficientMatrix := Matrix Index Index ℝ

def dot (x y : Sheet) : ℝ := ∑ i, x i * y i

def unit (a : Index) : Sheet := Pi.single a 1

/-- Cross-sheet Witt pairing on the two coefficient sheets. -/
def crossPair (x y : Doubled) : ℝ :=
  dot x.1 y.2 + dot x.2 y.1

/-- Graph section `e_a⁺ + H a b e_b⁻`. -/
def graphSection (H : CoefficientMatrix) (a : Index) : Doubled :=
  (unit a, fun b => H a b)

def inducedMetric (H : CoefficientMatrix) : CoefficientMatrix :=
  fun a b => crossPair (graphSection H a) (graphSection H b)

@[simp] theorem dot_unit_left (a : Index) (y : Sheet) :
    dot (unit a) y = y a := by
  classical
  rw [dot, Finset.sum_eq_single a]
  · simp [unit]
  · intro b hb hba
    simp [unit, hba]
  · simp

@[simp] theorem dot_right_unit (x : Sheet) (a : Index) :
    dot x (unit a) = x a := by
  classical
  rw [dot, Finset.sum_eq_single a]
  · simp [unit]
  · intro b hb hba
    simp [unit, hba]
  · simp

theorem inducedMetric_eq_symmetricPart (H : CoefficientMatrix) :
    inducedMetric H = fun a b => H a b + H b a := by
  funext a b
  simp [inducedMetric, graphSection, crossPair]
  ring

theorem inducedMetric_eq_add_transpose (H : CoefficientMatrix) :
    inducedMetric H = H + H.transpose := by
  funext a b
  simp [inducedMetric_eq_symmetricPart, add_comm]

theorem inducedMetric_symmetric (H : CoefficientMatrix) :
    (inducedMetric H).transpose = inducedMetric H := by
  rw [inducedMetric_eq_add_transpose]
  simp [Matrix.transpose_add, Matrix.transpose_transpose, add_comm]

theorem inducedQuadratic_eq_twice_symmetricPart (H : CoefficientMatrix)
    (a : Index) :
    inducedMetric H a a = 2 * H a a := by
  simp [inducedMetric_eq_symmetricPart]
  ring

theorem crossPair_left_isotropic (x y : Sheet) :
    crossPair (x, 0) (y, 0) = 0 := by
  simp [crossPair, dot]

theorem crossPair_right_isotropic (x y : Sheet) :
    crossPair (0, x) (0, y) = 0 := by
  simp [crossPair, dot]

theorem crossPair_graph_formula (H : CoefficientMatrix) (a b : Index) :
    crossPair (graphSection H a) (graphSection H b) =
      H a b + H b a := by
  exact congrFun (congrFun (inducedMetric_eq_symmetricPart H) a) b

end InfoGeometry.OperatorAlgebra.RealDoubledChiralKreinGraphSection
