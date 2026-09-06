import InfoGeometry.Clifford.Cl11TensorTower

set_option autoImplicit false

namespace InfoGeometry.Canonical.Cl11TensorTowerLocalParity

open Matrix
open InfoGeometry.Clifford.Cl11TensorTower

theorem gamma_chiral_base_anticomm_wittCreation :
    gamma_chiral_base * wittCreationBase +
      wittCreationBase * gamma_chiral_base = 0 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    norm_num [gamma_chiral_base, gamma_0_base, gamma_1_base,
      InfoGeometry.Clifford.Cl11Matrix.J1,
      InfoGeometry.Clifford.Cl11Matrix.Eminus,
      wittCreationBase, Matrix.mul_apply, Matrix.add_apply,
      Fin.sum_univ_two]

theorem gamma_chiral_base_anticomm_wittAnnihilation :
    gamma_chiral_base * wittAnnihilationBase +
      wittAnnihilationBase * gamma_chiral_base = 0 := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    norm_num [gamma_chiral_base, gamma_0_base, gamma_1_base,
      InfoGeometry.Clifford.Cl11Matrix.J1,
      InfoGeometry.Clifford.Cl11Matrix.Eminus,
      wittAnnihilationBase, Matrix.mul_apply, Matrix.add_apply,
      Fin.sum_univ_two]

end InfoGeometry.Canonical.Cl11TensorTowerLocalParity
