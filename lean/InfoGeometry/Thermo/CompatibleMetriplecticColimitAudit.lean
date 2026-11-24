/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Thermo.CompatibleMetriplecticColimit

/-!
# Axiom inventory for compatible metriplectic colimit laws

The eleven declarations are new to the thermodynamic continuation. Existing
compatible-colimit declarations remain in `CompatibleColimitAudit`; the
inventories are disjoint and the focused checker requires every record.
-/

#print axioms InfoGeometry.LinearAlgebra.CompatibleBilinearColimit.form_isAdjointPair_iff
#print axioms InfoGeometry.LinearAlgebra.CompatibleBilinearColimit.form_isSelfAdjoint_iff
#print axioms InfoGeometry.LinearAlgebra.CompatibleBilinearColimit.form_isSkewAdjoint_iff
#print axioms InfoGeometry.LinearAlgebra.CompatibleBilinearColimit.form_apply_liftEnd_nonneg_iff
#print axioms InfoGeometry.Thermo.CompatibleMetriplecticColimit.velocity_of
#print axioms InfoGeometry.Thermo.CompatibleMetriplecticColimit.energy_rate
#print axioms InfoGeometry.Thermo.CompatibleMetriplecticColimit.entropy_rate_eq_dissipative
#print axioms InfoGeometry.Thermo.CompatibleMetriplecticColimit.entropy_rate_nonneg
#print axioms InfoGeometry.Thermo.CompatibleMetriplecticColimit.energy_rate_of
#print axioms InfoGeometry.Thermo.CompatibleMetriplecticColimit.entropy_rate_of_eq
#print axioms InfoGeometry.Thermo.CompatibleMetriplecticColimit.entropy_rate_of_nonneg
