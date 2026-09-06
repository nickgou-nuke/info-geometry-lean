import InfoGeometry.Canonical.WheelerBoundaryHomologyBridge

namespace InfoGeometry.Canonical.WheelerBoundaryHomologyCapstone

open InfoGeometry.Canonical.WheelerHomology

/-- Canonical boundary/homology packet assembled from the local chain owner. -/
theorem wheeler_boundary_homology_canonical_capstone
    {C2 C1 C0 : Type*} [AddCommGroup C2] [AddCommGroup C1] [AddCommGroup C0]
    (C : ChainThreeStage C2 C1 C0)
    (h_exact : IsExactAtNode C)
    (x : C2) (z : C1) (hz : C.d1 z = 0) :
    (C.d1 (C.d2 x) = 0) ∧
    (C.d2 x ∈ AddMonoidHom.ker C.d1) ∧
    (∃ y : C2, C.d2 y = z) ∧
    ((∀ r : ℝ, 0 + r = r) ∧ (∀ r : ℝ, 1 * r = r)) := by
  exact ⟨boundary_squared_zero C x,
    image_subset_kernel C x,
    exact_node_cycle_resolved C h_exact z hz,
    zero_one_neutral_duality⟩

end InfoGeometry.Canonical.WheelerBoundaryHomologyCapstone
