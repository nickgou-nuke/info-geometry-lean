/-
Copyright (c) 2026 nickgou-nuke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: nickgou-nuke contributors
-/
import InfoGeometry.Physics.SimplexPrincipalBundleIwasawa

/-!
# Audit Module: SimplexPrincipalBundleIwasawaAudit

Automated kernel verification of Section 5.89:
- Zero debt: 0 sorry, 0 admit.
- Verifies Principal $\mathbb{R}_{>0}$-bundle structure $\mathbb{R}_{>0}^D \to \Delta^{D-1}$.
- Checks Linear / Probability Section normalization $\sum \sigma_{\mathrm{lin}} = 1$ and gauge invariance.
- Checks Geometric / Unimodular Section Cartan projection $\sum \ln \sigma_{\mathrm{geom}} = 0$ and gauge invariance.
- Checks Softmax bridge relating unimodular geometric section to linear probability section.
- Checks Amari Inönü-Wigner curvature contraction $K(0) = 1/4$ and $K(\pm 1) = 0$.
- Checks symplectic Poisson bracket $\{s_k, \phi_j\} = -\delta_{kj}/p_k$ and surprisal commutativity.
- Checks Bayesian conditional surprisal chain rule $s(A \cap B) = s(A) + s(B \mid A)$.
- Checks Iwasawa unimodular factorization $\det(K)\det(A)\det(N) = 1$.
- Certified Axiom Footprint: standard foundational axioms only [propext, Classical.choice, Quot.sound].
-/

namespace InfoGeometry.Physics.SimplexPrincipalBundleIwasawaAudit

open InfoGeometry.Physics.SimplexPrincipalBundleIwasawa

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

-- 1. Signature and Type-Level Verification
#check (PositiveMeasure.totalMass_pos :
  ∀ {D : ℕ} (m : PositiveMeasure D) (hD : 0 < D), 0 < m.totalMass)

#check (PositiveMeasure.linearSection_pos :
  ∀ {D : ℕ} (m : PositiveMeasure D) (hD : 0 < D) (i : Fin D), 0 < m.linearSection hD i)

#check (PositiveMeasure.sum_linearSection_eq_one :
  ∀ {D : ℕ} (m : PositiveMeasure D) (hD : 0 < D), ∑ i, m.linearSection hD i = 1)

#check (PositiveMeasure.linearSection_scale :
  ∀ {D : ℕ} (m : PositiveMeasure D) (c : ℝ) (hc : 0 < c) (hD : 0 < D) (i : Fin D),
    (m.scale c hc).linearSection hD i = m.linearSection hD i)

#check (PositiveMeasure.linearSection_reconstruction :
  ∀ {D : ℕ} (m : PositiveMeasure D) (hD : 0 < D) (i : Fin D),
    m.x i = m.totalMass * m.linearSection hD i)

#check (PositiveMeasure.geometricScale_pos :
  ∀ {D : ℕ} (m : PositiveMeasure D) (hD : 0 < D), 0 < m.geometricScale hD)

#check (PositiveMeasure.geomSection_pos :
  ∀ {D : ℕ} (m : PositiveMeasure D) (hD : 0 < D) (i : Fin D), 0 < m.geomSection hD i)

#check (PositiveMeasure.sum_log_geomSection_zero :
  ∀ {D : ℕ} (m : PositiveMeasure D) (hD : 0 < D), ∑ i, Real.log (m.geomSection hD i) = 0)

#check (PositiveMeasure.geomSection_scale :
  ∀ {D : ℕ} (m : PositiveMeasure D) (c : ℝ) (hc : 0 < c) (hD : 0 < D) (i : Fin D),
    (m.scale c hc).geomSection hD i = m.geomSection hD i)

#check (PositiveMeasure.linear_from_geom_section :
  ∀ {D : ℕ} (m : PositiveMeasure D) (hD : 0 < D) (i : Fin D),
    m.linearSection hD i = m.geomSection hD i / ∑ k, m.geomSection hD k)

#check (inonu_wigner_curvature_zero :
  inonuWignerCurvature 0 = 1 / 4)

#check (inonu_wigner_curvature_flat :
  inonuWignerCurvature 1 = 0 ∧ inonuWignerCurvature (-1) = 0)

#check (inonu_wigner_curvature_parity :
  ∀ (alpha : ℝ), inonuWignerCurvature (-alpha) = inonuWignerCurvature alpha)

#check (inonu_wigner_curvature_le_quarter :
  ∀ (alpha : ℝ), inonuWignerCurvature alpha ≤ 1 / 4)

#check (inonu_wigner_curvature_nonneg :
  ∀ {alpha : ℝ}, -1 ≤ alpha → alpha ≤ 1 → 0 ≤ inonuWignerCurvature alpha)

#check (surprisal_phase_poisson_bracket :
  ∀ {D : ℕ} (p : Fin D → ℝ) (k j : Fin D),
    poissonBracket (surprisalGradP p k) (fun _ => 0) (fun _ => 0) (phaseGradPhi j) =
      if k = j then - (1 / p k) else 0)

#check (surprisal_surprisal_poisson_bracket :
  ∀ {D : ℕ} (p : Fin D → ℝ) (k j : Fin D),
    poissonBracket (surprisalGradP p k) (fun _ => 0) (surprisalGradP p j) (fun _ => 0) = 0)

#check (hamiltonian_phase_velocity_eval :
  ∀ {D : ℕ} (p : Fin D → ℝ) (k : Fin D),
    hamiltonianPhaseVelocity p k k = - (1 / p k))

#check (bayesian_surprisal_chain_rule :
  ∀ (p_A p_B_given_A : ℝ) (hA : 0 < p_A) (hB : 0 < p_B_given_A),
    -Real.log (p_A * p_B_given_A) = (-Real.log p_A) + (-Real.log p_B_given_A))

#check (unipotent_det_one :
  ∀ {D : ℕ} (N : UnipotentData D), N.det_val = 1)

#check (unimodular_iwasawa_det :
  ∀ (kan : IwasawaKANFullData), kan.det_K * kan.det_A * kan.det_N = 1)

#check (simplex_principal_bundle_iwasawa_synthesis :
  ∀ {D : ℕ} (m : PositiveMeasure D) (hD : 0 < D) (c : ℝ) (hc : 0 < c) (k j : Fin D)
    (p_A p_B : ℝ) (hA : 0 < p_A) (hB : 0 < p_B) (kan : IwasawaKANFullData),
    (∑ i, m.linearSection hD i = 1) ∧
    ((m.scale c hc).linearSection hD k = m.linearSection hD k) ∧
    (∑ i, Real.log (m.geomSection hD i) = 0) ∧
    ((m.scale c hc).geomSection hD k = m.geomSection hD k) ∧
    (inonuWignerCurvature 0 = 1 / 4) ∧
    (inonuWignerCurvature 1 = 0 ∧ inonuWignerCurvature (-1) = 0) ∧
    (poissonBracket (surprisalGradP m.x k) (fun _ => 0) (fun _ => 0) (phaseGradPhi j) =
      if k = j then - (1 / m.x k) else 0) ∧
    (-Real.log (p_A * p_B) = (-Real.log p_A) + (-Real.log p_B)) ∧
    (kan.det_K * kan.det_A * kan.det_N = 1))

-- 2. Axiom Footprint Verification
#print axioms PositiveMeasure.totalMass_pos
#print axioms PositiveMeasure.sum_linearSection_eq_one
#print axioms PositiveMeasure.linearSection_scale
#print axioms PositiveMeasure.sum_log_geomSection_zero
#print axioms PositiveMeasure.geomSection_scale
#print axioms PositiveMeasure.linear_from_geom_section
#print axioms inonu_wigner_curvature_zero
#print axioms inonu_wigner_curvature_flat
#print axioms inonu_wigner_curvature_parity
#print axioms surprisal_phase_poisson_bracket
#print axioms surprisal_surprisal_poisson_bracket
#print axioms bayesian_surprisal_chain_rule
#print axioms unimodular_iwasawa_det
#print axioms simplex_principal_bundle_iwasawa_synthesis

end InfoGeometry.Physics.SimplexPrincipalBundleIwasawaAudit
