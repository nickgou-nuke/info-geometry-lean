import InfoGeometry.Canonical.RenyiFromModularPowers
import InfoGeometry.Canonical.BayesianMoebius

namespace InfoGeometry.Canonical

open Real

/-- Binary relative surprisal eigenvalues (spectral gap). -/
theorem binary_moebius_spectral_gap (α r : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hr0 : 0 < r) (hr1 : r < 1) :
    let Δ_plus := r / α
    let Δ_minus := (1 - r) / (1 - α)
    Real.log (Δ_plus / Δ_minus) = logit r - logit α := by
  intros Δ_plus Δ_minus
  dsimp [logit]
  have hd_plus : Δ_plus = r / α := rfl
  have hd_minus : Δ_minus = (1 - r) / (1 - α) := rfl
  rw [hd_plus, hd_minus]
  have h1 : (r / α) / ((1 - r) / (1 - α)) = (r / (1 - r)) / (α / (1 - α)) := by ring
  rw [h1]
  have hr_div_pos : 0 < r / (1 - r) := div_pos hr0 (sub_pos.mpr hr1)
  have hα_div_pos : 0 < α / (1 - α) := div_pos hα0 (sub_pos.mpr hα1)
  rw [Real.log_div hr_div_pos.ne' hα_div_pos.ne']

end InfoGeometry.Canonical
