import InfoGeometry.Hydrodynamics.GrassmannianGaugeZornTriality

/-!
# Audit Companion for Grassmannian Gauge Connection & Zorn Triality Automorphisms

Module: `InfoGeometry.Hydrodynamics.GrassmannianGaugeZornTrialityAudit`

This module audits the axiomatic footprint of all theorems in
`GrassmannianGaugeZornTriality.lean`.
-/

namespace InfoGeometry.Hydrodynamics.GrassmannianGauge.Audit

open InfoGeometry.Hydrodynamics.GrassmannianGauge

-- Section 1: Incompressibility & Traceless Shear
#print axioms Matrix2.incompressible_diagonal_opposite

-- Section 2: Abelian Trace Curvature Vanishing
#print axioms GaugePacket.abelian_curvature_zero

-- Section 3: Supergauge Automorphisms & Determinant Preservation
#print axioms ZornAutomorphism.zorn_potential_supergauge_split
#print axioms ZornAutomorphism.zorn_supergauge_kinetic_fisher_balance

-- Section 4: Associator Defect
#print axioms associator_of_associative

-- Section 5: Master Verification Certificate
#print axioms compile_grassmannian_gauge_zorn_triality

end InfoGeometry.Hydrodynamics.GrassmannianGauge.Audit
