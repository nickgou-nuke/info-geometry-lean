import InfoGeometry.Geometry.ParaHessianMixedPotential
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Probability.BinaryAitchisonMoments

/-!
# Binary Legendre graph and entropy-gradient evolution

The Bernoulli Legendre graph sits in the existing doubled para-Hessian carrier.
Its tangent pulls the neutral metric back to twice the Fisher variance.
This is a concrete one-dimensional graph calculation, not a claim that the
one-simplex itself is a nondegenerate symplectic manifold.

The explicit relaxation below is a model choice: log odds decay exponentially.
The Shannon entropy production is obtained by differentiation, not assumed.
-/

noncomputable section
namespace InfoGeometry.Geometry.BinaryLegendreEntropyFlow

open InfoGeometry.Geometry.ParaHessianMixedPotential
open InfoGeometry.Canonical.AmariBinarySimplexBridge
open InfoGeometry.Analysis.LogOddsSimplexGeometry
open InfoGeometry.Probability.BinaryAitchisonMoments

def legendreCurve (θ : ℝ) : ℝ × ℝ := (θ, logistic θ)

theorem hasDerivAt_legendreCurve (θ : ℝ) :
    HasDerivAt legendreCurve (1, fisherExp θ) θ := by
  exact (hasDerivAt_id θ).prodMk (hasDerivAt_logistic θ)

/-- The mixed metric induces the Hessian metric on the actual Legendre tangent. -/
theorem legendre_metric_pullback (θ u v : ℝ) :
    metric (u • deriv legendreCurve θ) (v • deriv legendreCurve θ) =
      2 * u * v * fisherExp θ := by
  rw [(hasDerivAt_legendreCurve θ).deriv]
  simp [metric]
  ring

/-- The graph tangent is isotropic for the existing skew form. -/
theorem legendre_symplectic_pullback (θ u v : ℝ) :
    symplectic (u • deriv legendreCurve θ) (v • deriv legendreCurve θ) = 0 := by
  rw [(hasDerivAt_legendreCurve θ).deriv, symplectic_apply]
  simp
  ring

theorem legendre_metric_positive (θ : ℝ) :
    0 < metric (deriv legendreCurve θ) (deriv legendreCurve θ) := by
  have h := legendre_metric_pullback θ 1 1
  simp only [one_smul, mul_one] at h
  rw [h]
  exact mul_pos (by norm_num) (fisherExp_pos θ)

/-- An explicit, globally interior binary evolution. -/
def entropyRelaxation (θ₀ t : ℝ) : ℝ := logistic (θ₀ * Real.exp (-t))

theorem entropyRelaxation_mem_Ioo (θ₀ t : ℝ) :
    entropyRelaxation θ₀ t ∈ Set.Ioo (0 : ℝ) 1 := logistic_mem_Ioo _

/-- Actual derivative of the proposed trajectory realizes the Fisher-gradient field. -/
theorem hasDerivAt_entropyRelaxation (θ₀ t : ℝ) :
    HasDerivAt (entropyRelaxation θ₀)
      (entropyGradientField (entropyRelaxation θ₀ t)) t := by
  have he := ((hasDerivAt_id t).neg.exp).const_mul θ₀
  have h := (hasDerivAt_logistic (θ₀ * Real.exp (-t))).comp t he
  convert h using 1
  unfold entropyGradientField entropyRelaxation
  rw [logit_logistic]
  dsimp
  ring

/-- The second law for this explicit trajectory, expressed as a native derivative. -/
theorem entropyRelaxation_entropy_derivative (θ₀ t : ℝ) :
    deriv (fun s => -negativeEntropy (entropyRelaxation θ₀ s)) t =
      entropyRelaxation θ₀ t * (1 - entropyRelaxation θ₀ t) *
        logit (entropyRelaxation θ₀ t) ^ 2 := by
  have hd := ((hasDerivAt_negativeEntropy (entropyRelaxation_mem_Ioo θ₀ t)).neg).comp t
    (hasDerivAt_entropyRelaxation θ₀ t)
  convert hd.deriv using 1
  unfold entropyGradientField
  ring

theorem entropyRelaxation_entropy_nondecreasing (θ₀ : ℝ) :
    Monotone (fun t => -negativeEntropy (entropyRelaxation θ₀ t)) := by
  apply monotone_of_deriv_nonneg
  · intro t
    exact (((hasDerivAt_negativeEntropy (entropyRelaxation_mem_Ioo θ₀ t)).neg).comp t
      (hasDerivAt_entropyRelaxation θ₀ t)).differentiableAt
  · intro t
    rw [entropyRelaxation_entropy_derivative]
    have hp := entropyRelaxation_mem_Ioo θ₀ t
    exact mul_nonneg (mul_pos hp.1 (sub_pos.mpr hp.2)).le (sq_nonneg _)

end InfoGeometry.Geometry.BinaryLegendreEntropyFlow
