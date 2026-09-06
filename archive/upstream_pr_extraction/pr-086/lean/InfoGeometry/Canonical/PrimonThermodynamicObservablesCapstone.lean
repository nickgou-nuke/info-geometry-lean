/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic
import InfoGeometry.Quantum.PrimonColimitFiltration
import InfoGeometry.Quantum.PrimonThermodynamics
import InfoGeometry.Canonical.YangBaxterProof

/-!
# Primon Thermodynamic Observables Capstone (Canonical Export)

Canonical umbrella export of the differential thermodynamic observables, mean mode energies,
and negative potential gradient relations for the primon gas.
-/

namespace InfoGeometry.Canonical.PrimonThermodynamics

open InfoGeometry.Quantum.PrimonColimit
open InfoGeometry.Quantum.PrimonThermodynamics
open InfoGeometry.Canonical.YangBaxterProof

/-- 🏆 Canonical Grand Synthesis of Primon Thermodynamic Observables & Yang-Baxter Integrability -/
theorem grand_canonical_primon_thermodynamics_synthesis
    (p : ℕ) (hp : 2 ≤ p) (beta : ℝ) (h_beta : 0 < beta) :
    (HasDerivAt (fun b : ℝ => (p : ℝ) ^ (-b)) (-Real.log (p : ℝ) * (p : ℝ) ^ (-beta)) beta) ∧
    (HasDerivAt (fun b : ℝ => primeSurprisalPotential p b) (-primeMeanEnergy p beta) beta) ∧
    (deriv (fun b : ℝ => primeSurprisalPotential p b) beta = -primeMeanEnergy p beta) ∧
    (0 < primeMeanEnergy p beta) ∧
    (F * F = (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    (F * B * F = R) :=
  ⟨hasDerivAt_prime_boltzmann p hp beta,
   hasDerivAt_prime_surprisal_potential p hp beta h_beta,
   prime_mean_energy_eq_neg_deriv p hp beta h_beta,
   prime_mean_energy_pos p hp beta h_beta,
   F_sq,
   F_B_F_eq_R⟩

end InfoGeometry.Canonical.PrimonThermodynamics
