import InfoGeometry.QuantumContext.ArakiPetzEntropyMonotonicity

/-!
# Audit Companion for Section 91: Araki Relative Modular Entropy Monotonicity & Petz Saturation

Module: `InfoGeometry.QuantumContext.ArakiPetzEntropyMonotonicityAudit`

This module audits the axiomatic footprint of all theorems in
`ArakiPetzEntropyMonotonicity.lean` to verify 0 sorry, 0 admit, and 0 custom axioms.
-/

namespace InfoGeometry.QuantumContext.Audit

open InfoGeometry.QuantumContext

-- Section 1 & 2: Stiefel 2-Block Defect Matrix & Trace Preservation
#print axioms defectMatrix_explicit
#print axioms defect_trace_zero

-- Section 3: Frobenius Norm Squared and Quadratic Leakage Loss
#print axioms defect_frobenius_norm_sq
#print axioms defect_frobenius_zero_iff

-- Section 4: Algebraic Pinsker–Petz Saturation
#print axioms algebraic_pinsker_relation
#print axioms araki_petz_saturation_iff_zero_leakage
#print axioms algebraic_pinsker_petz_relation
#print axioms petz_entropy_saturation_iff_zero_future

-- Section 5: Relative Modular Intertwining & Sufficiency
#print axioms relative_modular_intertwining

-- Section 6: Master Compilation Target
#print axioms compile_araki_petz_entropy_monotonicity

end InfoGeometry.QuantumContext.Audit
