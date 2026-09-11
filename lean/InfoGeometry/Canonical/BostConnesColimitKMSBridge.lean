import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.BostConnesKMS

open scoped BigOperators
open InfoGeometry.Canonical.BostConnesKMS

namespace InfoGeometry.Canonical.BostConnesColimitKMSBridge

/-- The finite theorem package needed for the Bost--Connes colimit readout. -/
theorem colimit_kms_state_exists {β : ℝ} (hβ : 1 < β) :
    1 < β ∧
      bostConnesPartition β = (riemannZeta (β : ℂ)).re ∧
      (∑' n : ℕ+, normalizedBostConnesWeight β n) = 1 ∧
      ∀ n : ℕ+, 0 < normalizedBostConnesWeight β n := by
  exact ⟨hβ, bostConnesPartition_eq_riemannZeta_re β hβ,
    tsum_normalizedBostConnesWeight β hβ,
    fun n => normalizedBostConnesWeight_pos β hβ n⟩

end InfoGeometry.Canonical.BostConnesColimitKMSBridge
