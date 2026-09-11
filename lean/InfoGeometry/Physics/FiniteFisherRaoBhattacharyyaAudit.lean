/-
Copyright (c) 2026 nickgou-nuke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: nickgou-nuke contributors
-/
import InfoGeometry.Physics.FiniteFisherRaoBhattacharyya

/-!
# Audit Module: FiniteFisherRaoBhattacharyyaAudit

Automated kernel verification:
- Zero debt: 0 sorry, 0 admit.
- Verifies Bhattacharyya overlap symmetry, self-overlap, positivity, and upper bound.
- Verifies overlap unity uniqueness: BC(P, Q) = 1 ↔ P = Q.
- Verifies Fisher-Rao distance symmetry, self-distance, non-negativity, and kernel characterization.
- Certified Axiom Footprint: standard foundational axioms only [propext, Classical.choice, Quot.sound].
-/

namespace InfoGeometry.Physics.FiniteFisherRaoBhattacharyyaAudit

open InfoGeometry.Physics.AmariSurprisalIwasawa

set_option linter.unusedVariables false

variable {D : ℕ}

-- 1. Signature and Type-Level Verification
#check (@bhattacharyyaOverlap_comm :
  ∀ {D : ℕ} (P Q : PositiveDist D), bhattacharyyaOverlap P Q = bhattacharyyaOverlap Q P)

#check (@bhattacharyyaOverlap_self :
  ∀ {D : ℕ} (P : PositiveDist D), bhattacharyyaOverlap P P = 1)

#check (@bhattacharyyaOverlap_pos :
  ∀ {D : ℕ} (P Q : PositiveDist D) (hD : 0 < D), 0 < bhattacharyyaOverlap P Q)

#check (@bhattacharyyaOverlap_le_one :
  ∀ {D : ℕ} (P Q : PositiveDist D), bhattacharyyaOverlap P Q ≤ 1)

#check (@bhattacharyyaOverlap_eq_one_imp_prob_eq :
  ∀ {D : ℕ} (P Q : PositiveDist D), bhattacharyyaOverlap P Q = 1 → P.p = Q.p)

#check (@fisherRaoDistance_comm :
  ∀ {D : ℕ} (P Q : PositiveDist D), fisherRaoDistance P Q = fisherRaoDistance Q P)

#check (@fisherRaoDistance_self :
  ∀ {D : ℕ} (P : PositiveDist D), fisherRaoDistance P P = 0)

#check (@fisherRaoDistance_nonneg :
  ∀ {D : ℕ} (P Q : PositiveDist D), 0 ≤ fisherRaoDistance P Q)

#check (@fisherRaoDistance_eq_zero_iff_overlap_eq_one :
  ∀ {D : ℕ} (P Q : PositiveDist D), fisherRaoDistance P Q = 0 ↔ bhattacharyyaOverlap P Q = 1)

#check (@fisherRaoDistance_eq_zero_of_amplitude_eq :
  ∀ {D : ℕ} (P Q : PositiveDist D), (∀ i, amplitude P i = amplitude Q i) → fisherRaoDistance P Q = 0)

-- 2. Axiom Footprint Verification
#print axioms bhattacharyyaOverlap_comm
#print axioms bhattacharyyaOverlap_self
#print axioms bhattacharyyaOverlap_pos
#print axioms bhattacharyyaOverlap_le_one
#print axioms bhattacharyyaOverlap_eq_one_imp_prob_eq
#print axioms fisherRaoDistance_comm
#print axioms fisherRaoDistance_self
#print axioms fisherRaoDistance_nonneg
#print axioms fisherRaoDistance_eq_zero_iff_overlap_eq_one
#print axioms fisherRaoDistance_eq_zero_of_amplitude_eq

end InfoGeometry.Physics.FiniteFisherRaoBhattacharyyaAudit
