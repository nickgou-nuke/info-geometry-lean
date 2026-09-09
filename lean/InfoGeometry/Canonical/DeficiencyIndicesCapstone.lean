import InfoGeometry.Quantum.DeficiencyIndices

namespace InfoGeometry.Canonical.DeficiencyIndicesCapstone

open InfoGeometry.Quantum.DeficiencyIndices

/-! Self-adjoint deficiency indices at the finite zero model. -/
theorem capstone_deficiency_indices_synthesis :
    deficiencyIndicesSelfAdjoint 0 0 := by
  exact apollonius_self_adjoint_indices

end InfoGeometry.Canonical.DeficiencyIndicesCapstone
