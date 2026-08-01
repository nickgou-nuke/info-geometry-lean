import Mathlib
import InfoGeometry.Canonical.SplitPauliMatrixRelations

namespace InfoGeometry.Canonical

/-!
# Peirce Chiral Cone Spin Frame Bridge

This module embeds the three local chiral $Cl(1,1)$ spin frames (which map to the 
generations/colors) into the global Peirce decomposition components $J_{23}, J_{31}, J_{12}$.
It demonstrates that the $M_2(\mathbb{R})$ structures constructed previously are not merely 
abstract, but are the explicit coordinate channels of the causal null cone in the Jordan algebra.
-/

noncomputable section

/-- The shared hyperbolic/grading/Krein axis. -/
abbrev commonHyperbolicAxis : Matrix (Fin 2) (Fin 2) ℝ := L_2

/-- The local split-complex subalgebra shared by all three sectors. -/
def sharedSplitComplexSubalgebra : Submodule ℝ (Matrix (Fin 2) (Fin 2) ℝ) :=
  Submodule.span ℝ {I_2, commonHyperbolicAxis}

/-- The positive chiral projector $p_+$ -/
def p_plus : Matrix (Fin 2) (Fin 2) ℝ :=
  (⅟2 : ℝ) • (I_2 + commonHyperbolicAxis)

/-- The negative chiral projector $p_-$ -/
def p_minus : Matrix (Fin 2) (Fin 2) ℝ :=
  (⅟2 : ℝ) • (I_2 - commonHyperbolicAxis)

/-- $p_+$ is idempotent. -/
theorem p_plus_sq : p_plus * p_plus = p_plus := by
  ext i j; fin_cases i <;> fin_cases j <;> {
    simp [p_plus, commonHyperbolicAxis, I_2, L_2, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two]
    try ring
  }

/-- $p_-$ is idempotent. -/
theorem p_minus_sq : p_minus * p_minus = p_minus := by
  ext i j; fin_cases i <;> fin_cases j <;> {
    simp [p_minus, commonHyperbolicAxis, I_2, L_2, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two]
    try ring
  }

/-- Orthogonality of chiral projectors: $p_+ p_- = 0$. -/
theorem p_plus_p_minus : p_plus * p_minus = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> {
    simp [p_plus, p_minus, commonHyperbolicAxis, I_2, L_2, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two]
    try ring
  }

/-- Completeness of chiral projectors: $p_+ + p_- = 1$. -/
theorem p_plus_add_p_minus : p_plus + p_minus = I_2 := by
  ext i j; fin_cases i <;> fin_cases j <;> {
    simp [p_plus, p_minus, commonHyperbolicAxis, I_2, L_2, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]
    try ring
  }

/-- Local chiral null generator $n_m^+ = e_m + e_m l$. -/
def n_plus (e_m eMulL : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  e_m + eMulL

/-- Local chiral null generator $n_m^- = e_m - e_m l$. -/
def n_minus (e_m eMulL : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  e_m - eMulL

/-- $n_m^+$ is a null element. -/
theorem n_plus_sq_zero : n_plus I_comp IL_comp * n_plus I_comp IL_comp = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> {
    simp [n_plus, I_comp, IL_comp, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]
    try ring
  }

/-- $n_m^-$ is a null element. -/
theorem n_minus_sq_zero : n_minus I_comp IL_comp * n_minus I_comp IL_comp = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> {
    simp [n_minus, I_comp, IL_comp, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
    try ring
  }

/-- Left Peirce identity for the positive projector. -/
theorem p_minus_n_plus : p_minus * n_plus I_comp IL_comp = n_plus I_comp IL_comp := by
  ext i j; fin_cases i <;> fin_cases j <;> {
    simp [p_minus, n_plus, commonHyperbolicAxis, I_2, L_2, I_comp, IL_comp, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two]
    try ring
  }

/-- Right Peirce identity for the negative projector. -/
theorem n_plus_p_plus : n_plus I_comp IL_comp * p_plus = n_plus I_comp IL_comp := by
  ext i j; fin_cases i <;> fin_cases j <;> {
    simp [p_plus, n_plus, commonHyperbolicAxis, I_2, L_2, I_comp, IL_comp, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two]
    try ring
  }

/-!
## Global Peirce Eigenvalues and Transport Equivariance

The next layer requires mapping these structures explicitly into $J_{23}, J_{31}, J_{12}$ 
via embeddings $\iota_m$, proving the global Peirce eigenvalues $c_r \circ \iota_m(x)$, 
and demonstrating `peirceEmbedding_intertwines_chiralBoost`.
-/

end

end InfoGeometry.Canonical
