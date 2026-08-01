import Mathlib.Tactic
import InfoGeometry.Algebra.RealSplitAlbert
import InfoGeometry.Algebra.RealAlbertJordanProofs
import Mathlib.Data.Matrix.Basic

/-!
# Real Peirce Embeddings of the Chiral Spin Frame

This module provides the structural bridge mapping the local $Cl(1,1)$ chiral
spin frame (modeled via $M_2(\mathbb{R})$) into the 27-dimensional real Albert
carrier equipped with the split-Albert Jordan product from
`InfoGeometry.Algebra.RealSplitAlbert`.

By construction, these embeddings populate the purely off-diagonal blocks
$J_{23}, J_{31}, J_{12}$ of that carrier.

The eigenvalues of the diagonal primitive idempotents ($e_1, e_2, e_3$) verify
the standard Peirce algebraic properties:
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

/-- Thin API aliases for the three Peirce embeddings. -/
noncomputable abbrev peirce23Embedding := peirce23_chiralFrame_embedding
noncomputable abbrev peirce31Embedding := peirce31_chiralFrame_embedding
noncomputable abbrev peirce12Embedding := peirce12_chiralFrame_embedding

theorem peirce23Embedding_injective : Function.Injective peirce23Embedding := by
  intro M N h
  have h00 : M 0 0 = N 0 0 := by
    have h' := congrArg (fun X => X.z₁.a) h
    simpa [peirce23Embedding, peirce23_chiralFrame_embedding, embedRealSplit] using h'
  have h11 : M 1 1 = N 1 1 := by
    have h' := congrArg (fun X => X.z₁.b) h
    simpa [peirce23Embedding, peirce23_chiralFrame_embedding, embedRealSplit] using h'
  have h01 : M 0 1 = N 0 1 := by
    have h' := congrArg (fun X => X.z₁.x0) h
    simpa [peirce23Embedding, peirce23_chiralFrame_embedding, embedRealSplit] using h'
  have h10 : M 1 0 = N 1 0 := by
    have h' := congrArg (fun X => X.z₁.y0) h
    simpa [peirce23Embedding, peirce23_chiralFrame_embedding, embedRealSplit] using h'
  ext i j <;> fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

theorem peirce31Embedding_injective : Function.Injective peirce31Embedding := by
  intro M N h
  have h00 : M 0 0 = N 0 0 := by
    have h' := congrArg (fun X => X.z₂.a) h
    simpa [peirce31Embedding, peirce31_chiralFrame_embedding, embedRealSplit] using h'
  have h11 : M 1 1 = N 1 1 := by
    have h' := congrArg (fun X => X.z₂.b) h
    simpa [peirce31Embedding, peirce31_chiralFrame_embedding, embedRealSplit] using h'
  have h01 : M 0 1 = N 0 1 := by
    have h' := congrArg (fun X => X.z₂.x0) h
    simpa [peirce31Embedding, peirce31_chiralFrame_embedding, embedRealSplit] using h'
  have h10 : M 1 0 = N 1 0 := by
    have h' := congrArg (fun X => X.z₂.y0) h
    simpa [peirce31Embedding, peirce31_chiralFrame_embedding, embedRealSplit] using h'
  ext i j <;> fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

theorem peirce12Embedding_injective : Function.Injective peirce12Embedding := by
  intro M N h
  have h00 : M 0 0 = N 0 0 := by
    have h' := congrArg (fun X => X.z₃.a) h
    simpa [peirce12Embedding, peirce12_chiralFrame_embedding, embedRealSplit] using h'
  have h11 : M 1 1 = N 1 1 := by
    have h' := congrArg (fun X => X.z₃.b) h
    simpa [peirce12Embedding, peirce12_chiralFrame_embedding, embedRealSplit] using h'
  have h01 : M 0 1 = N 0 1 := by
    have h' := congrArg (fun X => X.z₃.x0) h
    simpa [peirce12Embedding, peirce12_chiralFrame_embedding, embedRealSplit] using h'
  have h10 : M 1 0 = N 1 0 := by
    have h' := congrArg (fun X => X.z₃.y0) h
    simpa [peirce12Embedding, peirce12_chiralFrame_embedding, embedRealSplit] using h'
  ext i j <;> fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

theorem peirce23_chiralFrame_spectrum (M : Matrix (Fin 2) (Fin 2) ℝ) :
    RealAlbertMatrix.mul e1 (peirce23Embedding M) = RealAlbertMatrix.zero ∧
    RealAlbertMatrix.mul e2 (peirce23Embedding M) = RealAlbertMatrix.smul (1 / 2) (peirce23Embedding M) ∧
    RealAlbertMatrix.mul e3 (peirce23Embedding M) = RealAlbertMatrix.smul (1 / 2) (peirce23Embedding M) := by
  exact ⟨e1_circ_peirce23 M, ⟨e2_circ_peirce23 M, e3_circ_peirce23 M⟩⟩

theorem peirce31_chiralFrame_spectrum (M : Matrix (Fin 2) (Fin 2) ℝ) :
    RealAlbertMatrix.mul e1 (peirce31Embedding M) = RealAlbertMatrix.smul (1 / 2) (peirce31Embedding M) ∧
    RealAlbertMatrix.mul e2 (peirce31Embedding M) = RealAlbertMatrix.zero ∧
    RealAlbertMatrix.mul e3 (peirce31Embedding M) = RealAlbertMatrix.smul (1 / 2) (peirce31Embedding M) := by
  exact ⟨e1_circ_peirce31 M, ⟨e2_circ_peirce31 M, e3_circ_peirce31 M⟩⟩

theorem peirce12_chiralFrame_spectrum (M : Matrix (Fin 2) (Fin 2) ℝ) :
    RealAlbertMatrix.mul e1 (peirce12Embedding M) = RealAlbertMatrix.smul (1 / 2) (peirce12Embedding M) ∧
    RealAlbertMatrix.mul e2 (peirce12Embedding M) = RealAlbertMatrix.smul (1 / 2) (peirce12Embedding M) ∧
    RealAlbertMatrix.mul e3 (peirce12Embedding M) = RealAlbertMatrix.zero := by
  exact ⟨e1_circ_peirce12 M, ⟨e2_circ_peirce12 M, e3_circ_peirce12 M⟩⟩

end InfoGeometry.Canonical
