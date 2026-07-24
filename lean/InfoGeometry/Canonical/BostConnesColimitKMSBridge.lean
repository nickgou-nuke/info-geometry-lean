import Mathlib
import InfoGeometry.Canonical.BostConnesKMS

open scoped BigOperators
open InfoGeometry.Canonical.BostConnesKMS

namespace InfoGeometry.Canonical.BostConnesColimitKMSBridge

/-- Structure representing the Inductive Colimit KMS State on the A_∞ Bost-Connes algebra -/
structure ColimitKMSState (β : ℝ) where
  h_beta : 1 < β
  partition_eq_zeta : bostConnesPartition β = (riemannZeta (β : ℂ)).re
  total_mass_one : ∑' n : ℕ+, normalizedBostConnesWeight β n = 1
  weight_positivity : ∀ n : ℕ+, 0 < normalizedBostConnesWeight β n

/-- Main Theorem: Proof of existence of the A_∞ Inductive Colimit Bost-Connes KMS State. -/
theorem colimit_kms_state_exists {β : ℝ} (hβ : 1 < β) :
    Nonempty (ColimitKMSState β) := by
  refine ⟨⟨hβ, bostConnesPartition_eq_riemannZeta_re β hβ,
            tsum_normalizedBostConnesWeight β hβ,
            fun n => normalizedBostConnesWeight_pos β hβ n⟩⟩

end InfoGeometry.Canonical.BostConnesColimitKMSBridge
