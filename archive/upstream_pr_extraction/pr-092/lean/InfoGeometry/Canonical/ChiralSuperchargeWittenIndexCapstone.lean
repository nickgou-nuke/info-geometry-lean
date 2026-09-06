/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Quantum.ChiralSuperchargeWittenIndex

namespace InfoGeometry.Canonical

open InfoGeometry.Quantum.ChiralSuperchargeWittenIndex

/-- Canonical projection capstone for Chiral Supercharge & Witten Index module. -/
theorem chiral_supercharge_witten_index_canonical_capstone {R : Type*} [CommRing R]
    (a_L_dag a_L f_L_dag f_L : R)
    (h_car : f_L * f_L_dag = 1 - f_L_dag * f_L)
    (h_ccr : a_L * a_L_dag = 1 + a_L_dag * a_L)
    (E_vac : R)
    (σ : ℝ) (h_bps : chiralHamiltonian 0 0 (1 / 2 : ℝ) = σ) :
    (a_L_dag * a_L * (f_L * f_L_dag) + (a_L * a_L_dag) * (f_L_dag * f_L) =
     a_L_dag * a_L + f_L_dag * f_L) ∧
    (chiralHamiltonian 0 0 E_vac = E_vac) ∧
    (σ = 1 / 2) :=
  grand_chiral_supercharge_synthesis a_L_dag a_L f_L_dag f_L h_car h_ccr E_vac σ h_bps

end InfoGeometry.Canonical
