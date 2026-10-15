/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.ChevalleyKreinDirac

/-!
# Audit: ChevalleyKreinDiracAudit

Automated kernel verification of the Chevalley–Krein–Dirac geometry:
- Zero debt: 0 sorry, 0 admit, 0 custom axioms.
- Verifies the CAR grading identity $\eta = 2P - \mathbb{1}$.
- Verifies the algebraic grading involution $\eta^2 = \mathbb{1}_X$; no adjoint or positivity data are assumed.
- Verifies Dirac conjugation involution $(A^\ddagger)^\ddagger = A$.
- Verifies off-diagonal flip on transition dyads: $E_{01}^\ddagger = -E_{01}$, $E_{10}^\ddagger = -E_{10}$.
- Verifies preservation of the vacuum idempotent: $E_{00}^\ddagger = E_{00}$.
- Verifies Master Krein–Dirac soundness theorem.
- Axiom footprint check: standard foundational axioms only [propext, Classical.choice, Quot.sound].
-/

namespace InfoGeometry.Physics.ChevalleyKreinDiracAudit

open CategoryTheory
open InfoGeometry.Physics.Chevalley
open InfoGeometry.Physics.ChevalleyDyads
open InfoGeometry.Physics.ChevalleyKreinDirac

set_option linter.unusedVariables false

-- 1. Signature and Type-Level Verification
#check @kreinMetric_eq_two_P_minus_one
#check @kreinMetric_sq
#check @diracConj_involutive
#check @diracConj_negates_n
#check @diracConj_negates_p
#check @diracConj_flips_transition_dyads
#check @diracConj_preserves_vacuum
#check @master_krein_dirac_soundness

-- 2. Axiom Footprint Verification
#print axioms kreinMetric_eq_two_P_minus_one
#print axioms kreinMetric_sq
#print axioms diracConj_involutive
#print axioms diracConj_negates_n
#print axioms diracConj_negates_p
#print axioms diracConj_flips_transition_dyads
#print axioms diracConj_preserves_vacuum
#print axioms master_krein_dirac_soundness

end InfoGeometry.Physics.ChevalleyKreinDiracAudit
