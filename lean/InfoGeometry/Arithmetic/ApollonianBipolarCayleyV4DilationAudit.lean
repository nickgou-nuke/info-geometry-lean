/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Arithmetic.ApollonianBipolarCayleyV4Dilation

/-!
# Axiom Audit for ApollonianBipolarCayleyV4Dilation

Verifies via `#print axioms` that all exported theorems in
`InfoGeometry.Arithmetic.ApollonianBipolarCayleyV4Dilation` depend exclusively
on Lean 4's foundational axioms (`propext`, `Quot.sound`, `Classical.choice`),
with zero `sorry`, `admit`, `native_decide`, or custom axioms.
-/

open InfoGeometry.Arithmetic.ApollonianBipolarCayleyV4Dilation

#print axioms matE01_mul_E10_ne_mul_E10_E01_C
#print axioms mat2C_j_plus_j_minus_ne
#print axioms mat2C_starRing_selfAdjoint_noncomm_witness
#print axioms mat2C_ccr_trace_obstruction
#print axioms dilationGen_star_adjoint_anomaly
#print axioms berryKeatingHam_eq_berryKeatingH
#print axioms berryKeatingH_selfAdjoint_from_dilation
#print axioms physicalHamiltonian_unit_hbar_eq_euler_shift
#print axioms sToCentered_centeredToS
#print axioms centeredToS_sToCentered
#print axioms bostConnes_centered_strip_alignment
#print axioms bostConnes_highTemp_centered_iff
#print axioms bostConnes_lowTemp_centered_iff
#print axioms bostConnes_centered_strip_alignment_centeredToS
#print axioms bostConnes_centered_phases_disjoint
#print axioms v4_critical_line_orbit_collapse
#print axioms v4_off_line_orbit_four_distinct
#print axioms v4GroupApply_involutive
#print axioms v4GroupApply_mul
#print axioms v4CenteredPerm_id
#print axioms v4CenteredPerm_P
#print axioms v4CenteredPerm_T
#print axioms v4CenteredPerm_PT
#print axioms v4CenteredPerm_abs_re
#print axioms v4CenteredPerm_orbit_dichotomy_and_strip_invariance
#print axioms normSq_bipolar_diff
#print axioms apollonianCayleyW_unit_circle_iff
#print axioms apollonianCayleyW_leeYang_iff
#print axioms apollonianCayleyW_leeYang_iff_unconditional
#print axioms apollonian_bipolar_equidistance_iff
#print axioms apollonianCayleyW_disk_iff
#print axioms apollonianCayleyW_exterior_iff
#print axioms apollonianCayleyW_pole_counterexample
#print axioms apollonianCayleyW_sToCentered
#print axioms apollonianCayleyW_centeredToS
#print axioms apollonianCayleyW_neg
#print axioms apollonianCayleyW_neg_star
#print axioms apollonianCayleyW_bipolar_circle_and_halfplane
#print axioms apollonianCayleyW_antiholomorphic_and_fn26_link
#print axioms finite_li_kernel_circle_nonneg
#print axioms finite_li_kernel_circle_nonneg_and_offCircle_neg_witness
