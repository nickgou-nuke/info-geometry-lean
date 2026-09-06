/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib.Tactic
import InfoGeometry.Quantum.ApolloniusLieBracket
import InfoGeometry.Canonical.YangBaxterProof

/-!
# Apollonius Lie Bracket & Symplectic Decoupling Capstone

Canonical umbrella export connecting the differential Lie bracket, Cauchy-Riemann
conformal orthogonality, symplectic non-degeneracy, and topological Yang-Baxter integrability.
-/

namespace InfoGeometry.Canonical.ApolloniusLieBracket

open InfoGeometry.Quantum.ApolloniusLieBracket
open InfoGeometry.Canonical.YangBaxterProof

/-- 🏆 Canonical Grand Synthesis of Apollonius Lie Bracket & Yang-Baxter Integrability -/
theorem grand_canonical_apollonius_lie_bracket_synthesis
    (d_sigma_Phi d_t_Phi d_sigma_H d_t_H : ℝ → ℝ → ℝ)
    (h_cr : HarmonicConjugateData d_sigma_Phi d_t_Phi d_sigma_H d_t_H)
    (σ t : ℝ) :
    (innerProduct (souriauGradient d_sigma_Phi d_t_Phi) (hamiltonianGradient d_sigma_H d_t_H) σ t = 0) ∧
    (innerProduct (hamiltonianFlow d_sigma_H d_t_H) (hamiltonianGradient d_sigma_H d_t_H) σ t = 0) ∧
    (symplecticForm (hamiltonianGradient d_sigma_H d_t_H) (souriauGradient d_sigma_Phi d_t_Phi) σ t =
      (d_sigma_Phi σ t)^2 + (d_t_Phi σ t)^2) ∧
    (F * F = (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    (F * B * F = R) :=
  ⟨souriau_hamiltonian_gradients_orthogonal d_sigma_Phi d_t_Phi d_sigma_H d_t_H h_cr σ t,
   hamiltonian_flow_hamiltonian_grad_orthogonal d_sigma_H d_t_H σ t,
   souriau_hamiltonian_symplectic_pairing d_sigma_Phi d_t_Phi d_sigma_H d_t_H h_cr σ t,
   F_sq,
   F_B_F_eq_R⟩

end InfoGeometry.Canonical.ApolloniusLieBracket
