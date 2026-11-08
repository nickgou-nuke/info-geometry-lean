import InfoGeometry.Canonical.Cl11WittBasis
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.CausalDiracMatrixBasisChange

noncomputable section

namespace SplitOctonion

/--
A generic Dirac operator connection over the Cl(1,1) spectral algebra.
Parameterized by chiral (gamma), sheet (k), and circular/phase (j) fields.
-/
def DiracConnection (A_gamma A_k A_j : ℝ) (x : SplitOctonion) : SplitOctonion :=
  A_gamma • Gamma_sheet x + A_k • K_sheet x + A_j • J_sheet x

/--
The same Dirac connection formulated in the null Witt basis.
A_plus  = A_gamma + A_k
A_minus = A_gamma - A_k
-/
def DiracConnectionWitt (A_plus A_minus A_j : ℝ) (x : SplitOctonion) : SplitOctonion :=
  A_plus • Witt_e_plus x + A_minus • Witt_e_minus x + A_j • J_sheet x

/--
Integration of the causal Witt coordinates into the operator spectrum.
-/
theorem DiracConnection_eq_Witt (A_gamma A_k A_j : ℝ) (x : SplitOctonion) :
    DiracConnection A_gamma A_k A_j x =
    DiracConnectionWitt (A_gamma + A_k) (A_gamma - A_k) A_j x := by
  dsimp [DiracConnection, DiracConnectionWitt]
  rw [Gamma_sheet_eq_Witt_e_plus_add_minus, K_sheet_eq_Witt_e_plus_sub_minus]
  ext <;> simp <;> ring

end SplitOctonion
