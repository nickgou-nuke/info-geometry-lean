import InfoGeometry.Canonical.Cl11SheetDiracMatrices

open scoped Quaternion
namespace SplitOctonion
noncomputable section

/-- The Witt creation/annihilation basis for the Cl(1,1) sheet atom. -/
def Witt_e_plus (x : SplitOctonion) : SplitOctonion :=
  (1 / 2 : ℝ) • (Gamma_sheet x + K_sheet x)

def Witt_e_minus (x : SplitOctonion) : SplitOctonion :=
  (1 / 2 : ℝ) • (Gamma_sheet x - K_sheet x)

lemma Witt_e_plus_sq (x : SplitOctonion) :
    Witt_e_plus (Witt_e_plus x) = 0 := by
  ext <;> simp [Witt_e_plus, Gamma_sheet, K_sheet, J_sheet, smul_add] <;> try ring

lemma Witt_e_minus_sq (x : SplitOctonion) :
    Witt_e_minus (Witt_e_minus x) = 0 := by
  ext <;> simp [Witt_e_minus, Gamma_sheet, K_sheet, J_sheet, smul_add] <;> try ring

lemma Witt_e_anticomm (x : SplitOctonion) :
    Witt_e_plus (Witt_e_minus x) + Witt_e_minus (Witt_e_plus x) = x := by
  ext <;> simp [Witt_e_plus, Witt_e_minus, Gamma_sheet, K_sheet, J_sheet, smul_add] <;> try ring

lemma Witt_e_plus_minus_eq_proj_plus (x : SplitOctonion) :
    Witt_e_plus (Witt_e_minus x) = (1 / 2 : ℝ) • (x + J_sheet x) := by
  ext <;> simp [Witt_e_plus, Witt_e_minus, Gamma_sheet, K_sheet, J_sheet, smul_add] <;> try ring

lemma Witt_e_minus_plus_eq_proj_minus (x : SplitOctonion) :
    Witt_e_minus (Witt_e_plus x) = (1 / 2 : ℝ) • (x - J_sheet x) := by
  ext <;> simp [Witt_e_plus, Witt_e_minus, Gamma_sheet, K_sheet, J_sheet, smul_add] <;> try ring

end
end SplitOctonion
