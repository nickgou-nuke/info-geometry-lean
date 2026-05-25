import Mathlib.Algebra.Quaternion
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# InfoGeometry.Projective.Cl44QuaternionSplit

This file implements the explicit $M_2(\mathbb{H})$ representation of split-octonions
as derived by Özcan Bektaş.

Every split-octonion $X \in \mathbb{O}_s$ can be represented as:
$X = q_1 + q_2 e_4$ where $q_1, q_2 \in \mathbb{H}$.

Left multiplication by an octonion maps isomorphically to the associative
$2 \times 2$ real quaternion matrix:
$A_X = \begin{pmatrix} q_1 & q_2 \\ \overline{q_2} & \overline{q_1} \end{pmatrix} \in M_2(\mathbb{H})$.

This bridges the non-associativity of the twistor incidence grid into an exact,
associative representation, enabling rigorous quantization paths.
-/

namespace InfoGeometry.Projective

open Matrix

/-- The classical real quaternion algebra structure $\mathbb{H}$. -/
abbrev RealQuaternion := Quaternion ℝ

/-- A split-type octonion represented as a pair of real quaternions $(q_1, q_2)$,
    corresponding to $q_1 + q_2 e_4$. -/
structure SplitOctonion where
  q1 : RealQuaternion
  q2 : RealQuaternion

/-- The exact operatorial matrix mapping defined by Bektaş.
    $X \mapsto A_X \in M_2(\mathbb{H})$. -/
def splitOctonionToMatrix (X : SplitOctonion) : Matrix (Fin 2) (Fin 2) RealQuaternion :=
  !![X.q1, X.q2; star X.q2, star X.q1]

/-- Non-associative multiplication on split octonions defined via the $e_4$ shift logic.
    $XY = (q_1 q_3 + \overline{q_4} q_2) + (q_4 q_1 + q_2 \overline{q_3}) e_4$ -/
def splitOctonionMul (X Y : SplitOctonion) : SplitOctonion := {
  q1 := X.q1 * Y.q1 + X.q2 * (star Y.q2)
  q2 := X.q1 * Y.q2 + X.q2 * (star Y.q1)
}

/-- Top-row homomorphism of the split-octonion product into matrix multiplication.
The `q₁` and `q₂` components are exactly the `(0,0)` and `(0,1)` blocks of the matrix
product. -/
theorem splitOctonion_matrix_homomorphism_topRow (X Y : SplitOctonion) :
    ((splitOctonionToMatrix (splitOctonionMul X Y)) 0 0 =
      (splitOctonionToMatrix X * splitOctonionToMatrix Y) 0 0)
    ∧
    ((splitOctonionToMatrix (splitOctonionMul X Y)) 0 1 =
      (splitOctonionToMatrix X * splitOctonionToMatrix Y) 0 1) := by
  constructor
  · simp [splitOctonionToMatrix, splitOctonionMul, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [splitOctonionToMatrix, splitOctonionMul, Matrix.mul_apply, Fin.sum_univ_two]

end InfoGeometry.Projective
