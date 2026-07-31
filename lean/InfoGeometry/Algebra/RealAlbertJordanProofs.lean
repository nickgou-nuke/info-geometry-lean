import Mathlib.Tactic
import InfoGeometry.Algebra.RealSplitAlbert

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

@[ext] theorem realAlbertMatrix_ext (X Y : RealAlbertMatrix)
    (h1 : X.α₁ = Y.α₁) (h2 : X.α₂ = Y.α₂) (h3 : X.α₃ = Y.α₃)
    (hz1 : X.z₁ = Y.z₁) (hz2 : X.z₂ = Y.z₁) (hz3 : X.z₃ = Y.z₃) : X = Y := by
  cases X; cases Y; congr

@[ext] theorem realSplitOct_ext (X Y : RealSplitOct)
    (ha : X.a = Y.a) (hb : X.b = Y.b) (hx0 : X.x0 = Y.x0) (hx1 : X.x1 = Y.x1) (hx2 : X.x2 = Y.x2)
    (hy0 : X.y0 = Y.y0) (hy1 : X.y1 = Y.y1) (hy2 : X.y2 = Y.y2) : X = Y := by
  cases X; cases Y; congr

/-- **Theorem 1 (Native Proof)**: The 27-dimensional real Albert Jordan product is commutative ($X \circ Y = Y \circ X$). -/
theorem real_albert_jordan_comm (X Y : RealAlbertMatrix) : RealAlbertMatrix.mul X Y = RealAlbertMatrix.mul Y X := by
  apply realAlbertMatrix_ext
  · dsimp [RealAlbertMatrix.mul]; ring
  · dsimp [RealAlbertMatrix.mul]; ring
  · dsimp [RealAlbertMatrix.mul]; ring
  · apply realSplitOct_ext <;> (dsimp [RealAlbertMatrix.mul, RealSplitOct.smul, RealSplitOct.add, RealSplitOct.mul, RealSplitOct.conj, RealSplitOct.zero]; ring)
  · apply realSplitOct_ext <;> (dsimp [RealAlbertMatrix.mul, RealSplitOct.smul, RealSplitOct.add, RealSplitOct.mul, RealSplitOct.conj, RealSplitOct.zero]; ring)
  · apply realSplitOct_ext <;> (dsimp [RealAlbertMatrix.mul, RealSplitOct.smul, RealSplitOct.add, RealSplitOct.mul, RealSplitOct.conj, RealSplitOct.zero]; ring)

/-- **Theorem 2 (Native Proof)**: Idempotence of $e_1$ ($e_1 \circ e_1 = e_1$). -/
theorem e1_idempotent : RealAlbertMatrix.mul e1 e1 = e1 := by
  apply realAlbertMatrix_ext
  · dsimp [RealAlbertMatrix.mul, e1, RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul]; ring
  · dsimp [RealAlbertMatrix.mul, e1, RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul]; ring
  · dsimp [RealAlbertMatrix.mul, e1, RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul]; ring
  · dsimp [RealAlbertMatrix.mul, e1, RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul, RealSplitOct.smul, RealSplitOct.add]; apply realSplitOct_ext <;> (dsimp [RealSplitOct.smul, RealSplitOct.add, RealSplitOct.mul, RealSplitOct.conj, RealSplitOct.zero]; ring)
  · dsimp [RealAlbertMatrix.mul, e1, RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul, RealSplitOct.smul, RealSplitOct.add]; apply realSplitOct_ext <;> (dsimp [RealSplitOct.smul, RealSplitOct.add, RealSplitOct.mul, RealSplitOct.conj, RealSplitOct.zero]; ring)
  · dsimp [RealAlbertMatrix.mul, e1, RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul, RealSplitOct.smul, RealSplitOct.add]; apply realSplitOct_ext <;> (dsimp [RealSplitOct.smul, RealSplitOct.add, RealSplitOct.mul, RealSplitOct.conj, RealSplitOct.zero]; ring)

/-- **Theorem 3 (Native Proof)**: Idempotence of $e_2$ ($e_2 \circ e_2 = e_2$). -/
theorem e2_idempotent : RealAlbertMatrix.mul e2 e2 = e2 := by
  apply realAlbertMatrix_ext
  · dsimp [RealAlbertMatrix.mul, e2, RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul]; ring
  · dsimp [RealAlbertMatrix.mul, e2, RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul]; ring
  · dsimp [RealAlbertMatrix.mul, e2, RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul]; ring
  · dsimp [RealAlbertMatrix.mul, e2, RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul, RealSplitOct.smul, RealSplitOct.add]; apply realSplitOct_ext <;> (dsimp [RealSplitOct.smul, RealSplitOct.add, RealSplitOct.mul, RealSplitOct.conj, RealSplitOct.zero]; ring)
  · dsimp [RealAlbertMatrix.mul, e2, RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul, RealSplitOct.smul, RealSplitOct.add]; apply realSplitOct_ext <;> (dsimp [RealSplitOct.smul, RealSplitOct.add, RealSplitOct.mul, RealSplitOct.conj, RealSplitOct.zero]; ring)
  · dsimp [RealAlbertMatrix.mul, e2, RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul, RealSplitOct.smul, RealSplitOct.add]; apply realSplitOct_ext <;> (dsimp [RealSplitOct.smul, RealSplitOct.add, RealSplitOct.mul, RealSplitOct.conj, RealSplitOct.zero]; ring)

/-- **Theorem 4 (Native Proof)**: Idempotence of $e_3$ ($e_3 \circ e_3 = e_3$). -/
theorem e3_idempotent : RealAlbertMatrix.mul e3 e3 = e3 := by
  apply realAlbertMatrix_ext
  · dsimp [RealAlbertMatrix.mul, e3, RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul]; ring
  · dsimp [RealAlbertMatrix.mul, e3, RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul]; ring
  · dsimp [RealAlbertMatrix.mul, e3, RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul]; ring
  · dsimp [RealAlbertMatrix.mul, e3, RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul, RealSplitOct.smul, RealSplitOct.add]; apply realSplitOct_ext <;> (dsimp [RealSplitOct.smul, RealSplitOct.add, RealSplitOct.mul, RealSplitOct.conj, RealSplitOct.zero]; ring)
  · dsimp [RealAlbertMatrix.mul, e3, RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul, RealSplitOct.smul, RealSplitOct.add]; apply realSplitOct_ext <;> (dsimp [RealSplitOct.smul, RealSplitOct.add, RealSplitOct.mul, RealSplitOct.conj, RealSplitOct.zero]; ring)
  · dsimp [RealAlbertMatrix.mul, e3, RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul, RealSplitOct.smul, RealSplitOct.add]; apply realSplitOct_ext <;> (dsimp [RealSplitOct.smul, RealSplitOct.add, RealSplitOct.mul, RealSplitOct.conj, RealSplitOct.zero]; ring)

/-- **Theorem 5 (Native Proof)**: Orthogonality of $e_1$ and $e_2$ ($e_1 \circ e_2 = 0$). -/
theorem e1_e2_orthogonal : RealAlbertMatrix.mul e1 e2 = RealAlbertMatrix.zero := by
  apply realAlbertMatrix_ext
  · dsimp [RealAlbertMatrix.mul, e1, e2, RealAlbertMatrix.zero, RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul]; ring
  · dsimp [RealAlbertMatrix.mul, e1, e2, RealAlbertMatrix.zero, RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul]; ring
  · dsimp [RealAlbertMatrix.mul, e1, e2, RealAlbertMatrix.zero, RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul]; ring
  · dsimp [RealAlbertMatrix.mul, e1, e2, RealAlbertMatrix.zero, RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul, RealSplitOct.smul, RealSplitOct.add]; apply realSplitOct_ext <;> (dsimp [RealSplitOct.smul, RealSplitOct.add, RealSplitOct.mul, RealSplitOct.conj, RealSplitOct.zero]; ring)
  · dsimp [RealAlbertMatrix.mul, e1, e2, RealAlbertMatrix.zero, RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul, RealSplitOct.smul, RealSplitOct.add]; apply realSplitOct_ext <;> (dsimp [RealSplitOct.smul, RealSplitOct.add, RealSplitOct.mul, RealSplitOct.conj, RealSplitOct.zero]; ring)
  · dsimp [RealAlbertMatrix.mul, e1, e2, RealAlbertMatrix.zero, RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul, RealSplitOct.smul, RealSplitOct.add]; apply realSplitOct_ext <;> (dsimp [RealSplitOct.smul, RealSplitOct.add, RealSplitOct.mul, RealSplitOct.conj, RealSplitOct.zero]; ring)

/-- **Theorem 6 (Native Proof)**: Orthogonality of $e_2$ and $e_3$ ($e_2 \circ e_3 = 0$). -/
theorem e2_e3_orthogonal : RealAlbertMatrix.mul e2 e3 = RealAlbertMatrix.zero := by
  apply realAlbertMatrix_ext
  · dsimp [RealAlbertMatrix.mul, e2, e3, RealAlbertMatrix.zero, RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul]; ring
  · dsimp [RealAlbertMatrix.mul, e2, e3, RealAlbertMatrix.zero, RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul]; ring
  · dsimp [RealAlbertMatrix.mul, e2, e3, RealAlbertMatrix.zero, RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul]; ring
  · dsimp [RealAlbertMatrix.mul, e2, e3, RealAlbertMatrix.zero, RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul, RealSplitOct.smul, RealSplitOct.add]; apply realSplitOct_ext <;> (dsimp [RealSplitOct.smul, RealSplitOct.add, RealSplitOct.mul, RealSplitOct.conj, RealSplitOct.zero]; ring)
  · dsimp [RealAlbertMatrix.mul, e2, e3, RealAlbertMatrix.zero, RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul, RealSplitOct.smul, RealSplitOct.add]; apply realSplitOct_ext <;> (dsimp [RealSplitOct.smul, RealSplitOct.add, RealSplitOct.mul, RealSplitOct.conj, RealSplitOct.zero]; ring)
  · dsimp [RealAlbertMatrix.mul, e2, e3, RealAlbertMatrix.zero, RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul, RealSplitOct.smul, RealSplitOct.add]; apply realSplitOct_ext <;> (dsimp [RealSplitOct.smul, RealSplitOct.add, RealSplitOct.mul, RealSplitOct.conj, RealSplitOct.zero]; ring)

/-- **Theorem 7 (Native Proof)**: Orthogonality of $e_3$ and $e_1$ ($e_3 \circ e_1 = 0$). -/
theorem e3_e1_orthogonal : RealAlbertMatrix.mul e3 e1 = RealAlbertMatrix.zero := by
  apply realAlbertMatrix_ext
  · dsimp [RealAlbertMatrix.mul, e3, e1, RealAlbertMatrix.zero, RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul]; ring
  · dsimp [RealAlbertMatrix.mul, e3, e1, RealAlbertMatrix.zero, RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul]; ring
  · dsimp [RealAlbertMatrix.mul, e3, e1, RealAlbertMatrix.zero, RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul]; ring
  · dsimp [RealAlbertMatrix.mul, e3, e1, RealAlbertMatrix.zero, RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul, RealSplitOct.smul, RealSplitOct.add]; apply realSplitOct_ext <;> (dsimp [RealSplitOct.smul, RealSplitOct.add, RealSplitOct.mul, RealSplitOct.conj, RealSplitOct.zero]; ring)
  · dsimp [RealAlbertMatrix.mul, e3, e1, RealAlbertMatrix.zero, RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul, RealSplitOct.smul, RealSplitOct.add]; apply realSplitOct_ext <;> (dsimp [RealSplitOct.smul, RealSplitOct.add, RealSplitOct.mul, RealSplitOct.conj, RealSplitOct.zero]; ring)
  · dsimp [RealAlbertMatrix.mul, e3, e1, RealAlbertMatrix.zero, RealSplitOct.zero, RealSplitOct.conj, RealSplitOct.mul, RealSplitOct.smul, RealSplitOct.add]; apply realSplitOct_ext <;> (dsimp [RealSplitOct.smul, RealSplitOct.add, RealSplitOct.mul, RealSplitOct.conj, RealSplitOct.zero]; ring)

end InfoGeometry.Algebra
