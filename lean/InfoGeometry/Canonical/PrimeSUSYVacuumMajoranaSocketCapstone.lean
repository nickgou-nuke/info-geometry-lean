/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic
import InfoGeometry.Quantum.PrimeSUSYVacuumMajoranaSocket
import InfoGeometry.Canonical.YangBaxterProof

namespace InfoGeometry.Canonical.PrimeSUSYVacuumMajoranaSocket

open InfoGeometry.Quantum.PrimeSUSYVacuum
open InfoGeometry.Canonical.YangBaxterProof

theorem grand_canonical_prime_susy_vacuum_majorana_synthesis
    (omega : ℝ) (S : Finset ℕ) (p : ℕ) (hp_in : p ∈ S) (hp_prime : 2 ≤ p) :
    (cAnnihilate * cAnnihilate = 0) ∧
    (cCreate * cCreate = 0) ∧
    (cAnnihilate * cCreate + cCreate * cAnnihilate = 1) ∧
    (parityOp * cAnnihilate + cAnnihilate * parityOp = 0) ∧
    (majoranaGamma1 * majoranaGamma1 = 1) ∧
    ((omega • majoranaGamma1) * (omega • majoranaGamma1) =
      (omega ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (subsystemThermalWittenIndex S 0 = 0) ∧
    (F * F = (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    (F * B * F = R) :=
  ⟨c_annihilate_nilpotent,
   c_create_nilpotent,
   car_anticommutation,
   parity_anticomm_annihilate,
   majorana1_sq,
   susy_dirac_sq omega,
   subsystem_witten_index_zero_of_nonempty S p hp_in hp_prime,
   F_sq,
   F_B_F_eq_R⟩

end InfoGeometry.Canonical.PrimeSUSYVacuumMajoranaSocket
