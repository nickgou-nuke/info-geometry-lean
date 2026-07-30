import InfoGeometry.External.Auto.BuresMetricClosedCartography

noncomputable section

namespace InfoGeometry.Canonical.BuresMetricClosedCartography

/-- Maintained packet exposing the finite canonical Bures/Bloch owner surface. -/
theorem canonical_bures_cartography_packet
    (x y z dx dy dz : ℝ)
    (hball : x^2 + y^2 + z^2 < 1)
    (hvec : dx^2 + dy^2 + dz^2 > 0) :
    Matrix.trace (densityMatrix x y z) = 1 ∧
    Matrix.det (densityMatrix x y z) = ((1 - (x^2 + y^2 + z^2)) / 4 : ℝ) ∧
    0 < buresMetric x y z dx dy dz hball := by
  exact ⟨trace_densityMatrix x y z, det_densityMatrix x y z,
    buresMetric_pos x y z dx dy dz hball hvec⟩

end InfoGeometry.Canonical.BuresMetricClosedCartography

end noncomputable section
