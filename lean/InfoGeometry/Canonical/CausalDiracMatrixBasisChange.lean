import InfoGeometry.Canonical.Cl11WittBasis
import InfoGeometry.Algebra.FiniteSpinAlgebra

open scoped Quaternion
namespace SplitOctonion

-- Witt basis inversion
lemma Gamma_sheet_eq_Witt_e_plus_add_minus (x : SplitOctonion) :
    Gamma_sheet x = Witt_e_plus x + Witt_e_minus x := by
  ext <;> simp [Witt_e_plus, Witt_e_minus] <;> ring

lemma K_sheet_eq_Witt_e_plus_sub_minus (x : SplitOctonion) :
    K_sheet x = Witt_e_plus x - Witt_e_minus x := by
  ext <;> simp [Witt_e_plus, Witt_e_minus] <;> ring

lemma J_sheet_eq_Witt_e_commutator (x : SplitOctonion) :
    J_sheet x = Witt_e_plus (Witt_e_minus x) - Witt_e_minus (Witt_e_plus x) := by
  rw [Witt_e_plus_minus_eq_proj_plus, Witt_e_minus_plus_eq_proj_minus]
  ext <;> simp <;> ring

end SplitOctonion
