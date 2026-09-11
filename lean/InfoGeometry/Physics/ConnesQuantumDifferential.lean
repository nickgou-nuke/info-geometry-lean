import InfoGeometry.Physics.BdGChiralBlockMatrix
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Tactic

namespace InfoGeometry.Physics

variable {A : Type*} [Ring A] [StarRing A]

/-- A diagonal observable on the doubled block carrier. -/
def diagonalObservable (alpha beta : A) : BdGBlock A :=
  !![alpha, 0; 0, beta]

@[simp] theorem connesDifferential_diagonalObservable
    (Delta alpha beta : A) :
    connesDifferential (diracOperator Delta) (diagonalObservable alpha beta) =
      !![0, Delta * beta - alpha * Delta;
         star Delta * alpha - beta * star Delta, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [connesDifferential, diracOperator, diagonalObservable,
      Matrix.mul_apply, Fin.sum_univ_two]

end InfoGeometry.Physics
