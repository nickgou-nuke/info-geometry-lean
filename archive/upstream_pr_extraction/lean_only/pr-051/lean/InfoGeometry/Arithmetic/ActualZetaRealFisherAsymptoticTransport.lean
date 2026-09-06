import InfoGeometry.Arithmetic.ActualZetaRealPartitionDerivativeBridge

/-!
# Conditional transport of the actual real Fisher asymptotic

The actual Fisher readout is already identified on `1 < beta` with the real
part of the von Mangoldt `logMul` L-series.  This owner transports a future
derivative-level pole asymptotic through that equality.  It deliberately does
not assert that asymptotic: Mathlib currently supplies the function-level
zeta pole asymptotic, not the required derivative-level statement.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.ActualZetaRealFisherAsymptoticTransport

open Filter
open scoped Topology
open InfoGeometry.Arithmetic.ActualZetaRealPartitionDerivativeBridge
open ArithmeticFunction
open scoped LSeries.notation

theorem actualZetaRealFisherInformation_rescaled_tendsto_of_logMul_rescaled
    (hlog : Tendsto
      (fun beta : ℝ => ((beta - 1 : ℝ) : ℂ) ^ 2 *
        LSeries (LSeries.logMul (↗ArithmeticFunction.vonMangoldt))
          (beta : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ))) :
    Tendsto
      (fun beta : ℝ => (beta - 1) ^ 2 *
        actualZetaRealFisherInformation beta)
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℝ)) := by
  have hreal : Tendsto
      (fun beta : ℝ =>
        ((((beta - 1 : ℝ) : ℂ) ^ 2 *
          LSeries (LSeries.logMul (↗ArithmeticFunction.vonMangoldt))
            (beta : ℂ)).re))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa using Complex.continuous_re.continuousAt.tendsto.comp hlog
  apply hreal.congr'
  filter_upwards [self_mem_nhdsWithin] with beta hbeta
  rw [actualZetaRealFisherInformation_eq_vonMangoldt_logMul_re hbeta]
  simp [Complex.mul_re, pow_two]

theorem actualZetaRealFisherInformation_rescaled_eventually_pos_of_logMul_rescaled
    (hlog : Tendsto
      (fun beta : ℝ => ((beta - 1 : ℝ) : ℂ) ^ 2 *
        LSeries (LSeries.logMul (↗ArithmeticFunction.vonMangoldt))
          (beta : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ))) :
    ∀ᶠ beta in 𝓝[>] (1 : ℝ),
      0 < (beta - 1) ^ 2 * actualZetaRealFisherInformation beta := by
  have hlim :=
    actualZetaRealFisherInformation_rescaled_tendsto_of_logMul_rescaled hlog
  have hpos : {x : ℝ | 0 < x} ∈ 𝓝 (1 : ℝ) := by
    exact IsOpen.mem_nhds
      (isOpen_lt continuous_const continuous_id) (by norm_num)
  simpa only [Set.mem_setOf_eq] using hlim.eventually hpos

theorem actualZetaRealFisherInformation_rescaled_pos
    {beta : ℝ} (hbeta : 1 < beta) :
    0 < (beta - 1) ^ 2 * actualZetaRealFisherInformation beta := by
  exact mul_pos (sq_pos_of_pos (sub_pos.mpr hbeta))
    (actualZetaRealFisherInformation_pos hbeta)

theorem actualZetaRealFisherInformation_rescaled_eventually_pos_of_one_lt :
    ∀ᶠ beta in 𝓝[>] (1 : ℝ),
      0 < (beta - 1) ^ 2 * actualZetaRealFisherInformation beta := by
  filter_upwards [self_mem_nhdsWithin] with beta hbeta
  exact actualZetaRealFisherInformation_rescaled_pos hbeta

end InfoGeometry.Arithmetic.ActualZetaRealFisherAsymptoticTransport
