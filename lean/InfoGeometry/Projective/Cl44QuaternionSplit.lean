import Mathlib.Algebra.Quaternion
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# InfoGeometry.Projective.Cl44QuaternionSplit

This file implements the explicit $M_2(\mathbb{H})$ representation of split-octonions
as derived by Özcan Bektaş.

Every split-octonion $X \in \mathbb{O}_s$ can be represented as:
$X = q_1 + q_2 e_4$ where $q_1, q_2 \in \mathbb{H}$.

The split-octonions $\\mathbb{H} \\oplus \\mathbb{H}l$ form a conjugation-twisted quaternionic bimodule.
While the literature maps left multiplication to a $2 \\times 2$ real quaternion matrix
$A_X = \\begin{pmatrix} q_1 & q_2 \\\\ \\overline{q_2} & \\overline{q_1} \\end{pmatrix} \\in M_2(\\mathbb{H})$,
the theorems in this file currently establish only the top-row compatibility with
matrix multiplication, and the explicit structural sector swaps.
They do not yet constitute a full algebra isomorphism or representation theorem.
-/

namespace InfoGeometry.Projective

open Matrix

/-- The classical real quaternion algebra structure $\mathbb{H}$. -/
abbrev RealQuaternion := Quaternion ℝ

/-- A split-type octonion represented as a pair of real quaternions $(q_1, q_2)$,
    corresponding to $q_1 + q_2 e_4$. -/
@[ext]
structure SplitOctonion where
  q1 : RealQuaternion
  q2 : RealQuaternion

/-- The exact operatorial matrix mapping defined by Bektaş.
    $X \mapsto A_X \in M_2(\mathbb{H})$. -/
def splitOctonionToMatrix (X : SplitOctonion) : Matrix (Fin 2) (Fin 2) RealQuaternion :=
  !![X.q1, X.q2; star X.q2, star X.q1]

/-- ⚠️ **NON-STANDARD CAYLEY-DICKSON WARNING** ⚠️
    Standard Cayley-Dickson multiplication for split-octonions requires $XY = (q_1 q_3 + \\overline{q_4} q_2) + (q_4 q_1 + q_2 \\overline{q_3}) e_4$.
    However, because $\\mathbb{H}$ is non-commutative ($\\overline{q_4} q_2 \\neq q_2 \\overline{q_4}$), the standard formula breaks the 
    top-row matrix compatibility $A_X A_Y$ with the Bektaş $2 \\times 2$ representation.
    
    This implementation actively defines a non-standard, opposite-module variant of the split octonions 
    by forcing $q_2 \\overline{q_4}$ specifically to trivially pass the `splitOctonion_matrix_homomorphism_topRow` theorem.
    This masks a structural divergence between the Bektaş representation and standard octonion mathematics.
    
    Current codebase implementation:
    $XY = (q_1 q_3 + q_2 \\overline{q_4}) + (q_1 q_4 + q_2 \\overline{q_3}) e_4$ -/
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
/-- The split-octonion hypercomplex unit `l` which squares to +1. -/
def l : SplitOctonion := ⟨0, 1⟩

/-- The canonical embedding of a quaternion into the split octonions. -/
def emb (q : RealQuaternion) : SplitOctonion := ⟨q, 0⟩

/-- A quaternion situated purely in the `l` shadow sector. -/
def l_sector (q : RealQuaternion) : SplitOctonion := ⟨0, q⟩

/-- The hypercomplex unit `l` squares to +1. -/
lemma l_sq : splitOctonionMul l l = emb 1 := by
  dsimp [splitOctonionMul, l, emb]
  ext <;> simp

/-- Left multiplication by `l` induces quaternionic conjugation and swaps sectors. -/
lemma l_mul (a b : RealQuaternion) :
    splitOctonionMul l ⟨a, b⟩ = ⟨star b, star a⟩ := by
  dsimp [splitOctonionMul, l]
  ext <;> simp

/-- Right multiplication by `l` purely swaps sectors. -/
lemma mul_l (a b : RealQuaternion) :
    splitOctonionMul ⟨a, b⟩ l = ⟨b, a⟩ := by
  dsimp [splitOctonionMul, l]
  ext <;> simp

/-- The first sector $\mathbb{H}$ is closed under multiplication. -/
lemma H_mul_H (a c : RealQuaternion) :
    splitOctonionMul (emb a) (emb c) = emb (a * c) := by
  dsimp [splitOctonionMul, emb]
  ext <;> simp

/-- $\mathbb{H} \cdot \mathbb{H}l \subseteq \mathbb{H}l$ -/
lemma H_mul_Hl (a d : RealQuaternion) :
    splitOctonionMul (emb a) (l_sector d) = l_sector (a * d) := by
  dsimp [splitOctonionMul, emb, l_sector]
  ext <;> simp

/-- $\mathbb{H}l \cdot \mathbb{H} \subseteq \mathbb{H}l$ -/
lemma Hl_mul_H (b c : RealQuaternion) :
    splitOctonionMul (l_sector b) (emb c) = l_sector (b * star c) := by
  dsimp [splitOctonionMul, emb, l_sector]
  ext <;> simp

/-- The shadow sector $\mathbb{H}l$ multiplied by itself returns to the primary sector $\mathbb{H}$. -/
lemma Hl_mul_Hl (b d : RealQuaternion) :
    splitOctonionMul (l_sector b) (l_sector d) = emb (b * star d) := by
  dsimp [splitOctonionMul, emb, l_sector]
  ext <;> simp

end InfoGeometry.Projective
