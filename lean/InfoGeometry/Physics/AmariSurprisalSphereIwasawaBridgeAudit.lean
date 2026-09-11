/-
Copyright (c) 2026 nickgou-nuke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: nickgou-nuke contributors
-/
import InfoGeometry.Physics.AmariSurprisalSphereIwasawaBridge

/-!
# Audit Module: AmariSurprisalSphereIwasawaBridgeAudit

Automated kernel verification of Section 5.86:
- Zero debt: 0 sorry, 0 admit.
- Checks Shannon entropy as expected surprisal.
- Verifies CLR as negative centered surprisal.
- Verifies ALR as log-ratio against reference pole.
- Verifies free energy cumulant potential equals reference state surprisal.
- Verifies square-root amplitude map to the unit sphere (Born rule spinorization).
- Verifies spherical inner product normalization and symmetry.
- Verifies Amari curvature contraction factor K(alpha) = (1 - alpha^2)/4:
  - K(0) = 1/4 (Fisher-Rao / round sphere Levi-Civita).
  - K(1) = 0 (e-flat exponential surprisal connection).
  - K(-1) = 0 (m-flat mixture connection).
  - Parity symmetry K(-alpha) = K(alpha).
  - Bound K(alpha) <= 1/4.
- Certified Axiom Footprint: standard foundational axioms only [propext, Classical.choice, Quot.sound].
-/

namespace InfoGeometry.Physics.AmariSurprisalSphereIwasawaBridgeAudit

open InfoGeometry.Physics.AmariSurprisalSphereIwasawa
open InfoGeometry.Physics.AitchisonTraceDeterminant
open InfoGeometry.Physics.AitchisonCartanDuallyFlat

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {D : ℕ}

-- 1. Signature and Type-Level Verification
#check (entropy_eq_expected_surprisal :
  ∀ (P : PositiveDistribution D), shannonEntropy P = ∑ i, P.p i * surprisal P i)

#check (clr_eq_neg_centered_surprisal :
  ∀ (P : PositiveDistribution D) (hD : 0 < D) (i : Fin D),
    clr P hD i = - surprisal P i + (1 / (D : ℝ)) * ∑ k, surprisal P k)

#check (alr_eq_log_ratio :
  ∀ (P : PositiveDistribution D) (d_ref : Fin D) (i : Fin D),
    alr P d_ref i = Real.log (P.p i / P.p d_ref))

#check (log_sum_exp_alr_eq_ref_surprisal :
  ∀ (P : PositiveDistribution D) (d_ref : Fin D),
    Real.log (∑ i, Real.exp (alr P d_ref i)) = surprisal P d_ref)

#check (sum_amplitude_sq_one :
  ∀ (P : PositiveDistribution D), ∑ i, (amplitude P i) ^ 2 = 1)

#check (bhattacharyyaInner_self :
  ∀ (P : PositiveDistribution D), bhattacharyyaInner P P = 1)

#check (curvatureFactor_zero : curvatureFactor 0 = 1 / 4)
#check (curvatureFactor_one : curvatureFactor 1 = 0)
#check (curvatureFactor_neg_one : curvatureFactor (-1) = 0)
#check (curvatureFactor_symm : ∀ (alpha : ℝ), curvatureFactor (-alpha) = curvatureFactor alpha)
#check (curvatureFactor_le_quarter : ∀ (alpha : ℝ), curvatureFactor alpha ≤ 1 / 4)

#check (certified_amari_surprisal_sphere_iwasawa_synthesis :
  CertifiedAmariSurprisalSphereIwasawaSynthesis (D := D))

-- 2. Certified Axiom Footprint Verification
#print axioms certified_amari_surprisal_sphere_iwasawa_synthesis

end InfoGeometry.Physics.AmariSurprisalSphereIwasawaBridgeAudit
