import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.RealSplitAlbert
import InfoGeometry.Algebra.RealSplitOctSimp

/-!
# Native Proof of Real Split-Albert Jordan Commutativity & Idempotent Orthogonality

This module proves the true, explicit 27-dimensional Jordan commutativity ($X \circ Y = Y \circ X$),
idempotence ($e_i \circ e_i = e_i$), and orthogonality ($e_i \circ e_j = 0$) on `RealAlbertMatrix`
from `InfoGeometry.Algebra.RealSplitAlbert` natively over $\mathbb{R}$.
-/

namespace InfoGeometry.Algebra

open RealSplitOct
open RealAlbertMatrix

noncomputable section

/-- The three primitive diagonal idempotents on `RealAlbertMatrix`. -/
def e1 : RealAlbertMatrix := ⟨1, 0, 0, RealSplitOct.zero, RealSplitOct.zero, RealSplitOct.zero⟩
def e2 : RealAlbertMatrix := ⟨0, 1, 0, RealSplitOct.zero, RealSplitOct.zero, RealSplitOct.zero⟩
def e3 : RealAlbertMatrix := ⟨0, 0, 1, RealSplitOct.zero, RealSplitOct.zero, RealSplitOct.zero⟩

/-- **Theorem 1 (Native Proof)**: The 27-dimensional real Albert Jordan product is commutative ($X \circ Y = Y \circ X$). -/
theorem real_albert_jordan_comm (X Y : RealAlbertMatrix) : RealAlbertMatrix.mul X Y = RealAlbertMatrix.mul Y X := by
  ext <;> simp <;> ring

/-- **Theorem 2 (Native Proof)**: Idempotence of $e_1$ ($e_1 \circ e_1 = e_1$). -/
theorem e1_idempotent : RealAlbertMatrix.mul e1 e1 = e1 := by
  ext <;> simp [e1, RealSplitOct.zero]

/-- **Theorem 3 (Native Proof)**: Idempotence of $e_2$ ($e_2 \circ e_2 = e_2$). -/
theorem e2_idempotent : RealAlbertMatrix.mul e2 e2 = e2 := by
  ext <;> simp [e2, RealSplitOct.zero]

/-- **Theorem 4 (Native Proof)**: Idempotence of $e_3$ ($e_3 \circ e_3 = e_3$). -/
theorem e3_idempotent : RealAlbertMatrix.mul e3 e3 = e3 := by
  ext <;> simp [e3, RealSplitOct.zero]

/-- **Theorem 5 (Native Proof)**: Orthogonality of $e_1$ and $e_2$ ($e_1 \circ e_2 = 0$). -/
theorem e1_e2_orthogonal : RealAlbertMatrix.mul e1 e2 = RealAlbertMatrix.zero := by
  ext <;> simp [e1, e2, RealAlbertMatrix.zero, RealSplitOct.zero]

/-- **Theorem 6 (Native Proof)**: Orthogonality of $e_2$ and $e_3$ ($e_2 \circ e_3 = 0$). -/
theorem e2_e3_orthogonal : RealAlbertMatrix.mul e2 e3 = RealAlbertMatrix.zero := by
  ext <;> simp [e2, e3, RealAlbertMatrix.zero, RealSplitOct.zero]

/-- **Theorem 7 (Native Proof)**: Orthogonality of $e_3$ and $e_1$ ($e_3 \circ e_1 = 0$). -/
theorem e3_e1_orthogonal : RealAlbertMatrix.mul e3 e1 = RealAlbertMatrix.zero := by
  ext <;> simp [e3, e1, RealAlbertMatrix.zero, RealSplitOct.zero]

end
end InfoGeometry.Algebra
