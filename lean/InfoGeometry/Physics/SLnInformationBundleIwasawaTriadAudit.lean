/-
Copyright (c) 2026 nickgou-nuke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: nickgou-nuke contributors
-/
import InfoGeometry.Physics.SLnInformationBundleIwasawaTriad

/-!
# Audit Module: SLnInformationBundleIwasawaTriadAudit

Automated kernel verification of Section 5.89:
- Zero debt: 0 sorry, 0 admit.
- Checks Principal ℝ_{>0}-bundle structure and simplex normalization.
- Checks scale invariance of bundle projection π(λ · x) = π(x).
- Checks linear gauge consistency π(σ_prob(p)) = p.
- Checks centered log-ratio trace condition ∑ clr_i = 0 in Cartan subalgebra 𝔞.
- Checks unimodular geometric gauge determinant condition.
- Checks Inönü–Wigner contraction K(0) = 1/4 and flat limits K(±1) = 0.
- Checks complex quadric hypersurface constraint ∑ ‖z_k‖² = 1 on T* S^{D-1}.
- Checks canonical Poisson bracket { s_k, φ_j } = δ_{kj} / p_k.
- Checks strictly upper-triangular nilpotent generator trace Tr(M) = 0 in 𝔰𝔩(3, ℝ).
- Checks unipotent group determinant det(N) = 1.
- Verifies master Iwasawa triad product det(K) · det(A) · det(N) = 1 on SL(3, ℝ).
- Verifies master composite synthesis theorem.
- Certified Axiom Footprint: standard foundational axioms only [propext, Classical.choice, Quot.sound].
-/

namespace InfoGeometry.Physics.SLnInformationBundleIwasawaTriadAudit

open InfoGeometry.Physics.SLnInformationBundleIwasawaTriad

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

-- 1. Signature and Type-Level Verification
#check (@PositiveRay.project_sum_eq_one)
#check (@PositiveRay.project_scale_invariance)
#check (@SimplexPoint.linearSection_projection)

#check (SimplexPoint.sum_clr_zero :
  ∀ {D : ℕ} (P : SimplexPoint D) (hD : 0 < D), ∑ i, P.clr hD i = 0)

#check (SimplexPoint.unimodular_log_det_zero :
  ∀ {D : ℕ} (P : SimplexPoint D) (hD : 0 < D),
    ∑ i, Real.log ((P.unimodularSection hD).x i) = 0)

#check (amari_curvature_round_sphere :
  amariSectionalCurvature 0 = 1 / 4)

#check (amari_curvature_flat_limits :
  amariSectionalCurvature 1 = 0 ∧ amariSectionalCurvature (-1) = 0)

#check (amari_curvature_le_quarter :
  ∀ (alpha : ℝ), amariSectionalCurvature alpha ≤ 1 / 4)

#check (amari_curvature_parity :
  ∀ (alpha : ℝ), amariSectionalCurvature (-alpha) = amariSectionalCurvature alpha)

#check (ComplexAmplitude.quadric_sum :
  ∀ {D : ℕ} (Z : ComplexAmplitude D), ∑ i, ‖Z.z i‖ ^ 2 = 1)

#check (ComplexAmplitude.canonicalBracket_diag :
  ∀ {D : ℕ} (Z : ComplexAmplitude D) (i : Fin D),
    Z.canonicalBracket i i = 1 / ((Z.xi i) ^ 2))

#check (ComplexAmplitude.canonicalBracket_offdiag :
  ∀ {D : ℕ} (Z : ComplexAmplitude D) (i j : Fin D) (h : i ≠ j),
    Z.canonicalBracket i j = 0)

#check (StrictlyUpperTriangular3.trace_zero :
  ∀ (M : StrictlyUpperTriangular3),
    (M.toMatrix 0 0 + M.toMatrix 1 1 + M.toMatrix 2 2) = 0)

#check (UnipotentUpperTriangular3.unipotent_det_one :
  ∀ (U : UnipotentUpperTriangular3), U.det = 1)

#check (sl3_unimodular_product :
  ∀ (I : IwasawaFactorization3), I.det_K * I.det_A * I.det_N = 1)

#check (sl_information_bundle_iwasawa_synthesis :
  ∀ {D : ℕ} (hD : 0 < D) [NeZero D]
    (X : PositiveRay D)
    (P : SimplexPoint D)
    (Z : ComplexAmplitude D)
    (I : IwasawaFactorization3),
    (∑ i, X.project i = 1) ∧
    (∑ i, P.clr hD i = 0) ∧
    (amariSectionalCurvature 0 = 1 / 4) ∧
    (amariSectionalCurvature 1 = 0) ∧
    (amariSectionalCurvature (-1) = 0) ∧
    (∑ i, ‖Z.z i‖ ^ 2 = 1) ∧
    (I.det_K * I.det_A * I.det_N = 1))

-- 2. Axiom Footprint Verification
#print axioms PositiveRay.project_sum_eq_one
#print axioms PositiveRay.project_scale_invariance
#print axioms SimplexPoint.linearSection_projection
#print axioms SimplexPoint.sum_clr_zero
#print axioms SimplexPoint.unimodular_log_det_zero
#print axioms amari_curvature_round_sphere
#print axioms amari_curvature_flat_limits
#print axioms ComplexAmplitude.quadric_sum
#print axioms ComplexAmplitude.canonicalBracket_diag
#print axioms StrictlyUpperTriangular3.trace_zero
#print axioms sl3_unimodular_product
#print axioms sl_information_bundle_iwasawa_synthesis

end InfoGeometry.Physics.SLnInformationBundleIwasawaTriadAudit
