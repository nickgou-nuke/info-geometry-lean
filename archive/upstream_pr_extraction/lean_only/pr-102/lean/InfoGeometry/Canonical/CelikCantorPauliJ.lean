import InfoGeometry.Canonical.CelikCantorClifford

/-!
# Rank-one Pauli coupling readout

This owner closes the concrete `J`-matrix packet attached to the rank-one
Pauli base.  It proves matrix identities only; no tensor recursion,
Clifford-algebra equivalence, or Bott-periodicity statement is asserted.
-/

noncomputable section

namespace InfoGeometry.Canonical.CelikCantorPauliJ

open InfoGeometry.Canonical.CelikCantorClifford

@[simp] theorem J_sq :
    J * J = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

theorem UJ_anticomm : U * J = -(J * U) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [U, J, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

theorem VJ_anticomm : V * J = -(J * V) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [V, J, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

theorem J_eq_I_smul_UV :
    J = Complex.I • (U * V) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J, U, V, Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two]

theorem celik_rank_one_pauli_J_packet :
    J * J = (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
      U * J = -(J * U) ∧
      V * J = -(J * V) ∧
      J = Complex.I • (U * V) := by
  exact ⟨J_sq, UJ_anticomm, VJ_anticomm, J_eq_I_smul_UV⟩

end InfoGeometry.Canonical.CelikCantorPauliJ
