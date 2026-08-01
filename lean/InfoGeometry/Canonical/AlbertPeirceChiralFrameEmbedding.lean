import Mathlib.Tactic
import InfoGeometry.Algebra.RealSplitAlbert
import InfoGeometry.Algebra.RealAlbertJordanProofs
import Mathlib.Data.Matrix.Basic

/-!
# Real Peirce Embeddings of the Chiral Spin Frame

This module provides the structural bridge mapping the local $Cl(1,1)$ chiral 
spin frame (modeled via $M_2(\mathbb{R})$) into the 27-dimensional real Albert algebra $J_3(\mathbb{O}')$.

By construction, these embeddings populate the purely off-diagonal blocks $J_{23}, J_{31}, J_{12}$, 
known conceptually as the three color channels (Red, Green, Blue) of the Amplituhedron kinematics.

The eigenvalues of the diagonal primitive idempotents ($e_1, e_2, e_3$) verify the standard 
Peirce algebraic properties:
- $e_1 \circ \iota_{23}(M) = 0$
- $e_2 \circ \iota_{23}(M) = \frac{1}{2}\iota_{23}(M)$
- $e_3 \circ \iota_{23}(M) = \frac{1}{2}\iota_{23}(M)$
-/

namespace InfoGeometry.Canonical

open InfoGeometry.Algebra

/-- Maps a real $2 \times 2$ matrix to the scalar subset of a real split octonion. -/
noncomputable def embedRealSplit (M : Matrix (Fin 2) (Fin 2) ℝ) : RealSplitOct :=
  ⟨M 0 0, M 1 1, M 0 1, 0, 0, M 1 0, 0, 0⟩

/-- The Red color channel embedding $\iota_{23}: M_2(\mathbb{R}) \to J_3(\mathbb{O}')$. -/
noncomputable def peirce23_chiralFrame_embedding (M : Matrix (Fin 2) (Fin 2) ℝ) : RealAlbertMatrix :=
  ⟨0, 0, 0, embedRealSplit M, RealSplitOct.zero, RealSplitOct.zero⟩

/-- The Green color channel embedding $\iota_{31}: M_2(\mathbb{R}) \to J_3(\mathbb{O}')$. -/
noncomputable def peirce31_chiralFrame_embedding (M : Matrix (Fin 2) (Fin 2) ℝ) : RealAlbertMatrix :=
  ⟨0, 0, 0, RealSplitOct.zero, embedRealSplit M, RealSplitOct.zero⟩

/-- The Blue color channel embedding $\iota_{12}: M_2(\mathbb{R}) \to J_3(\mathbb{O}')$. -/
noncomputable def peirce12_chiralFrame_embedding (M : Matrix (Fin 2) (Fin 2) ℝ) : RealAlbertMatrix :=
  ⟨0, 0, 0, RealSplitOct.zero, RealSplitOct.zero, embedRealSplit M⟩

section PeirceEigenvalues

-- # Red Channel (23)

/-- $e_1$ acts by $0$ on the 23-component. -/
lemma e1_circ_peirce23 (M : Matrix (Fin 2) (Fin 2) ℝ) :
    RealAlbertMatrix.mul e1 (peirce23_chiralFrame_embedding M) = RealAlbertMatrix.zero := by
  ext <;> simp [RealAlbertMatrix.mul, e1, peirce23_chiralFrame_embedding, embedRealSplit, RealSplitOct.zero, RealSplitOct.smul, RealSplitOct.conj, RealSplitOct.mul, RealAlbertMatrix.zero]

/-- $e_2$ acts by $1/2$ on the 23-component. -/
lemma e2_circ_peirce23 (M : Matrix (Fin 2) (Fin 2) ℝ) :
    RealAlbertMatrix.mul e2 (peirce23_chiralFrame_embedding M) = RealAlbertMatrix.smul (1/2) (peirce23_chiralFrame_embedding M) := by
  ext <;> simp [RealAlbertMatrix.mul, e2, peirce23_chiralFrame_embedding, embedRealSplit, RealSplitOct.zero, RealSplitOct.smul, RealSplitOct.conj, RealSplitOct.mul, RealAlbertMatrix.smul]

/-- $e_3$ acts by $1/2$ on the 23-component. -/
lemma e3_circ_peirce23 (M : Matrix (Fin 2) (Fin 2) ℝ) :
    RealAlbertMatrix.mul e3 (peirce23_chiralFrame_embedding M) = RealAlbertMatrix.smul (1/2) (peirce23_chiralFrame_embedding M) := by
  ext <;> simp [RealAlbertMatrix.mul, e3, peirce23_chiralFrame_embedding, embedRealSplit, RealSplitOct.zero, RealSplitOct.smul, RealSplitOct.conj, RealSplitOct.mul, RealAlbertMatrix.smul]

-- # Green Channel (31)

/-- $e_1$ acts by $1/2$ on the 31-component. -/
lemma e1_circ_peirce31 (M : Matrix (Fin 2) (Fin 2) ℝ) :
    RealAlbertMatrix.mul e1 (peirce31_chiralFrame_embedding M) = RealAlbertMatrix.smul (1/2) (peirce31_chiralFrame_embedding M) := by
  ext <;> simp [RealAlbertMatrix.mul, e1, peirce31_chiralFrame_embedding, embedRealSplit, RealSplitOct.zero, RealSplitOct.smul, RealSplitOct.conj, RealSplitOct.mul, RealAlbertMatrix.smul]

/-- $e_2$ acts by $0$ on the 31-component. -/
lemma e2_circ_peirce31 (M : Matrix (Fin 2) (Fin 2) ℝ) :
    RealAlbertMatrix.mul e2 (peirce31_chiralFrame_embedding M) = RealAlbertMatrix.zero := by
  ext <;> simp [RealAlbertMatrix.mul, e2, peirce31_chiralFrame_embedding, embedRealSplit, RealSplitOct.zero, RealSplitOct.smul, RealSplitOct.conj, RealSplitOct.mul, RealAlbertMatrix.zero]

/-- $e_3$ acts by $1/2$ on the 31-component. -/
lemma e3_circ_peirce31 (M : Matrix (Fin 2) (Fin 2) ℝ) :
    RealAlbertMatrix.mul e3 (peirce31_chiralFrame_embedding M) = RealAlbertMatrix.smul (1/2) (peirce31_chiralFrame_embedding M) := by
  ext <;> simp [RealAlbertMatrix.mul, e3, peirce31_chiralFrame_embedding, embedRealSplit, RealSplitOct.zero, RealSplitOct.smul, RealSplitOct.conj, RealSplitOct.mul, RealAlbertMatrix.smul]

-- # Blue Channel (12)

/-- $e_1$ acts by $1/2$ on the 12-component. -/
lemma e1_circ_peirce12 (M : Matrix (Fin 2) (Fin 2) ℝ) :
    RealAlbertMatrix.mul e1 (peirce12_chiralFrame_embedding M) = RealAlbertMatrix.smul (1/2) (peirce12_chiralFrame_embedding M) := by
  ext <;> simp [RealAlbertMatrix.mul, e1, peirce12_chiralFrame_embedding, embedRealSplit, RealSplitOct.zero, RealSplitOct.smul, RealSplitOct.conj, RealSplitOct.mul, RealAlbertMatrix.smul]

/-- $e_2$ acts by $1/2$ on the 12-component. -/
lemma e2_circ_peirce12 (M : Matrix (Fin 2) (Fin 2) ℝ) :
    RealAlbertMatrix.mul e2 (peirce12_chiralFrame_embedding M) = RealAlbertMatrix.smul (1/2) (peirce12_chiralFrame_embedding M) := by
  ext <;> simp [RealAlbertMatrix.mul, e2, peirce12_chiralFrame_embedding, embedRealSplit, RealSplitOct.zero, RealSplitOct.smul, RealSplitOct.conj, RealSplitOct.mul, RealAlbertMatrix.smul]

/-- $e_3$ acts by $0$ on the 12-component. -/
lemma e3_circ_peirce12 (M : Matrix (Fin 2) (Fin 2) ℝ) :
    RealAlbertMatrix.mul e3 (peirce12_chiralFrame_embedding M) = RealAlbertMatrix.zero := by
  ext <;> simp [RealAlbertMatrix.mul, e3, peirce12_chiralFrame_embedding, embedRealSplit, RealSplitOct.zero, RealSplitOct.smul, RealSplitOct.conj, RealSplitOct.mul, RealAlbertMatrix.zero]

end PeirceEigenvalues

end InfoGeometry.Canonical
