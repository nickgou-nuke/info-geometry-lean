import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Algebra.Star.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian

namespace InfoGeometry.Canonical.PlabicDiracKrein

variable {R : Type*} [CommRing R] [StarRing R]
variable {VB VW : Type*} [Fintype VB] [Fintype VW] [DecidableEq VB] [DecidableEq VW]

/-! ### 1. Krein Signature and Chiral Substrate -/

/-- The Krein signature / Chiral grading operator η = γ.
    It assigns +1 to Black vertices and -1 to White vertices. -/
def kreinSignature : Matrix (VB ⊕ VW) (VB ⊕ VW) R :=
  Matrix.fromBlocks 1 0 0 (-1)

/-- The Krein adjoint of an operator T is defined as T^# = η T^† η. -/
def kreinAdjoint (M : Matrix (VB ⊕ VW) (VB ⊕ VW) R) : Matrix (VB ⊕ VW) (VB ⊕ VW) R :=
  kreinSignature * M.conjTranspose * kreinSignature

/-! ### 2. The Chiral Dirac-Hodge-Krein Operator -/

/-- Given a bipartite Kasteleyn transition matrix K : VW → VB,
    the Dirac-Hodge-Krein operator is the full block off-diagonal matrix. -/
def diracDHK (K : Matrix VW VB R) : Matrix (VB ⊕ VW) (VB ⊕ VW) R :=
  Matrix.fromBlocks 0 K.conjTranspose K 0

/-! ### 3. Chiral Symmetry and Krein Anti-Self-Adjointness -/

/-- Theorem: The Dirac-Hodge-Krein operator strictly anti-commutes with chirality.
    {D, γ} = D γ + γ D = 0 -/
theorem diracDHK_anticommutes_chirality (K : Matrix VW VB R) :
    diracDHK K * kreinSignature + kreinSignature * diracDHK K = 0 := by
  ext (i | i) (j | j) <;>
    simp [diracDHK, kreinSignature, Matrix.fromBlocks_multiply]

/-- Theorem: The Dirac-Hodge-Krein operator is Krein-skew-adjoint.
    D^# = -D. (This implies iD is Krein-self-adjoint). -/
theorem diracDHK_krein_skew (K : Matrix VW VB R) :
    kreinAdjoint (diracDHK K) = - diracDHK K := by
  ext (i | i) (j | j) <;>
    simp [kreinAdjoint, diracDHK, kreinSignature, Matrix.fromBlocks_conjTranspose,
          Matrix.fromBlocks_multiply, Matrix.mul_apply, Matrix.one_apply,
          Finset.sum_ite_eq', Matrix.conjTranspose_apply]

/-! ### 4. Sylvester Matrix Deformations (Quantum Torus) -/

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- A Sylvester pair (X, Z) encoding the quantum torus boundary conditions.
    Z X = ω X Z, where ω is a root of unity. -/
structure SylvesterPair (R : Type*) [CommRing R] (N : Type*) [Fintype N] [DecidableEq N] where
  ω : R
  X : Matrix N N R
  Z : Matrix N N R
  weyl_heisenberg : Z * X = ω • (X * Z)
  nilpotent_X : X ^ (Fintype.card N) = 1
  nilpotent_Z : Z ^ (Fintype.card N) = 1

end InfoGeometry.Canonical.PlabicDiracKrein
