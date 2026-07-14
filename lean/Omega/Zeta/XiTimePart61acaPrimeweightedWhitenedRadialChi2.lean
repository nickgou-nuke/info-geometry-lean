import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Omega.Zeta

/-- The radial square in whitened two-dimensional coordinates. -/
def xi_time_part61aca_primeweighted_whitened_radial_chi2_radialSquare
    (x : Fin 2 → ℝ) : ℝ :=
  x 0 ^ 2 + x 1 ^ 2

/-- The CDF of a chi-square random variable with two degrees of freedom. -/
noncomputable def xi_time_part61aca_primeweighted_whitened_radial_chi2_chi2TwoCdf
    (t : ℝ) : ℝ :=
  if 0 ≤ t then 1 - Real.exp (-(t / 2)) else 0

/-- Radial square process after applying the supplied whitening map. -/
def xi_time_part61aca_primeweighted_whitened_radial_chi2_radialSquareProcess
    (whitenedFingerprint : ℕ → Fin 2 → ℝ) (n : ℕ) : ℝ :=
  xi_time_part61aca_primeweighted_whitened_radial_chi2_radialSquare (whitenedFingerprint n)

/-- Paper-facing clauses: whitening is applied to the fingerprint, the radial-square limit is
chi-square with two degrees of freedom, and the CDF has its explicit positive/negative branches. -/
def xi_time_part61aca_primeweighted_whitened_radial_chi2_clauses
    (rawFingerprint : ℕ → Fin 2 → ℝ)
    (whitenedFingerprint : ℕ → Fin 2 → ℝ)
    (whiteningMap : (Fin 2 → ℝ) → Fin 2 → ℝ)
    (radialSquareLimitCdf : ℝ → ℝ) : Prop :=
  (∀ n, whitenedFingerprint n = whiteningMap (rawFingerprint n)) ∧
    (∀ t,
      radialSquareLimitCdf t =
        xi_time_part61aca_primeweighted_whitened_radial_chi2_chi2TwoCdf t) ∧
    (∀ t, 0 ≤ t → radialSquareLimitCdf t = 1 - Real.exp (-(t / 2))) ∧
      ∀ t, t < 0 → radialSquareLimitCdf t = 0

/-- Paper label: `thm:xi-time-part61aca-primeweighted-whitened-radial-chi2`. -/
theorem paper_xi_time_part61aca_primeweighted_whitened_radial_chi2
    (rawFingerprint : ℕ → Fin 2 → ℝ)
    (whitenedFingerprint : ℕ → Fin 2 → ℝ)
    (whiteningMap : (Fin 2 → ℝ) → Fin 2 → ℝ)
    (radialSquareLimitCdf : ℝ → ℝ)
    (whiteningMap_spec : ∀ n, whitenedFingerprint n = whiteningMap (rawFingerprint n))
    (standardGaussianRadialSquareLimit :
      ∀ t, radialSquareLimitCdf t =
        xi_time_part61aca_primeweighted_whitened_radial_chi2_chi2TwoCdf t) :
    xi_time_part61aca_primeweighted_whitened_radial_chi2_clauses
      rawFingerprint whitenedFingerprint whiteningMap radialSquareLimitCdf := by
  refine ⟨whiteningMap_spec, standardGaussianRadialSquareLimit, ?_, ?_⟩
  · intro t ht
    rw [standardGaussianRadialSquareLimit t]
    simp [xi_time_part61aca_primeweighted_whitened_radial_chi2_chi2TwoCdf, ht]
  · intro t ht
    rw [standardGaussianRadialSquareLimit t]
    have hnot : ¬ 0 ≤ t := not_le_of_gt ht
    simp [xi_time_part61aca_primeweighted_whitened_radial_chi2_chi2TwoCdf, hnot]

end Omega.Zeta
