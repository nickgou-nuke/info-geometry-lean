import InfoGeometry.Quantum.CramerRaoUncertainty

namespace InfoGeometry.Canonical.CramerRaoUncertaintyCapstone

open InfoGeometry.Quantum.CramerRaoUncertainty

theorem capstone_cramer_rao_uncertainty_synthesis (v F : ℝ) (hF : 0 < F) (hCR : cramerRaoBound v F) :
    (v * F ≥ 1) ∧ (v * F ≥ 1) :=
  grand_cramer_rao_uncertainty_synthesis v F hF hCR

end InfoGeometry.Canonical.CramerRaoUncertaintyCapstone
