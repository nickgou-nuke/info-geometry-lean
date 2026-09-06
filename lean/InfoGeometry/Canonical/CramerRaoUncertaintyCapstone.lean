import InfoGeometry.Quantum.CramerRaoUncertainty

namespace InfoGeometry.Canonical.CramerRaoUncertaintyCapstone

open InfoGeometry.Quantum.CramerRaoUncertainty

/-! Direct finite Cramér--Rao packet; the duplicated conclusion records the
same bound in both slots of the upstream interface. -/
theorem capstone_cramer_rao_uncertainty_synthesis (v F : ℝ)
    (hF : 0 < F) (hCR : cramerRaoBound v F) :
    (v * F ≥ 1) ∧ (v * F ≥ 1) := by
  exact ⟨cramer_rao_variance_product v F hF hCR,
    cramer_rao_variance_product v F hF hCR⟩

end InfoGeometry.Canonical.CramerRaoUncertaintyCapstone
