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
#print axioms dilationGen_star_adjoint_anomaly
#print axioms bostConnes_centered_strip_alignment
#print axioms v4_critical_line_orbit_collapse
#print axioms v4_off_line_orbit_four_distinct
#print axioms normSq_bipolar_diff
#print axioms apollonianCayleyW_unit_circle_iff
#print axioms apollonianCayleyW_neg
#print axioms apollonianCayleyW_neg_star
#print axioms finite_li_kernel_circle_nonneg
