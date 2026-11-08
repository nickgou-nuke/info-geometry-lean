/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.KitaevSYKHolographyScramblonPoset
import InfoGeometry.Quantum.ThermofieldDouble

/-!
# Axiom audit for the finite Kitaev/SYK Peirce identities

## i. Overview

Ask Lean to report the transitive axiom dependencies of each theorem in the
Kitaev/SYK archetype owner. These reports do not certify its physical
interpretations, which are explicitly outside that owner's formal scope.

## ii. Key results

- Axiom reports for the integer and real scalar scaling results, Peirce commutator identities,
  corner-defect/shear identities, and finite master synthesis.

## iii. Table of contents

1. Transitive axiom reports for the focused owner declarations.

## iv. References

- `InfoGeometry.Canonical.KitaevSYKHolographyScramblonPoset`
- `InfoGeometry.OperatorAlgebra.PeirceSpine.Basic`
-/

#print axioms InfoGeometry.Canonical.KitaevSYKHolographyScramblonPoset.syk_probe_bath_conformal_dimension_lock
#print axioms InfoGeometry.Canonical.KitaevSYKHolographyScramblonPoset.syk_probe_bath_integer_dimension_lock
#print axioms InfoGeometry.Canonical.KitaevSYKHolographyScramblonPoset.finite_matrix_vectorized_commutant_iff
#print axioms InfoGeometry.Canonical.KitaevSYKHolographyScramblonPoset.finite_matrix_vectorize_norm_sq_eq_trace
#print axioms InfoGeometry.Canonical.KitaevSYKHolographyScramblonPoset.finite_gibbs_half_weight_posSemidef
#print axioms InfoGeometry.Canonical.KitaevSYKHolographyScramblonPoset.finite_gibbs_half_weight_mul_self_eq_density
#print axioms InfoGeometry.Canonical.KitaevSYKHolographyScramblonPoset.finite_gibbs_half_weight_commutes
#print axioms InfoGeometry.Canonical.KitaevSYKHolographyScramblonPoset.finite_gibbs_half_weight_vectorized_equilibrium
#print axioms InfoGeometry.Canonical.KitaevSYKHolographyScramblonPoset.finite_gibbs_half_weight_vectorized_norm_eq_partition
#print axioms InfoGeometry.Canonical.KitaevSYKHolographyScramblonPoset.sl2_rindler_wedge_and_tfd_scramblon_excitation
#print axioms InfoGeometry.Canonical.KitaevSYKHolographyScramblonPoset.peirce_horizon_bracket_matches_boost_iff_unit_foam
#print axioms InfoGeometry.Canonical.KitaevSYKHolographyScramblonPoset.wick_scramblon_ladder_and_shockwave_entanglement_action
#print axioms InfoGeometry.Canonical.KitaevSYKHolographyScramblonPoset.two_corner_shockwave_sheet_transfer_round_trip
#print axioms InfoGeometry.Canonical.KitaevSYKHolographyScramblonPoset.kitaev_syk_holography_and_elementary_expansion_master_synthesis
#print axioms InfoGeometry.Quantum.ThermofieldDouble.FiniteQuantumSpectrum.tfdCoeff_zero_time_normSq
#print axioms InfoGeometry.Quantum.ThermofieldDouble.FiniteQuantumSpectrum.tfdCoeff_zero_time_normSq_sum_eq_one
#print axioms InfoGeometry.Quantum.ThermofieldDouble.FiniteQuantumSpectrum.tfdCoeff_normSq
#print axioms InfoGeometry.Quantum.ThermofieldDouble.FiniteQuantumSpectrum.tfdCoeff_normSq_sum_eq_one
