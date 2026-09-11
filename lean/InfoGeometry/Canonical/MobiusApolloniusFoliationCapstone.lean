import InfoGeometry.Canonical.YangBaxterProof
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Complex.MobiusApolloniusFoliation

open scoped BigOperators Real Complex Matrix
open Complex Matrix
open InfoGeometry.Canonical.YangBaxterProof
open InfoGeometry.Complex.MobiusApollonius

namespace InfoGeometry.Canonical.MobiusApolloniusFoliation

/-- Canonical packaging of the Möbius--Apollonius and Yang--Baxter identities. -/
theorem grand_mobius_apollonius_foliation_synthesis
    (σ t : ℝ) (h_half : σ = 1/2)
    (σ_disk : ℝ) (h_disk : 1/2 < σ_disk)
    (σ_ext : ℝ) (h_ext : σ_ext < 1/2)
    (lam : ℝ) (h_lam : lam ≠ 1) (s : ℂ) :
    (mobiusNumerator σ t - mobiusDenominator σ t = -4 * σ + 2) ∧
    (mobiusNumerator σ t = mobiusDenominator σ t) ∧
    (mobiusNumerator (1/2) t = 1 + t ^ 2 ∧ mobiusDenominator (1/2) t = 1 + t ^ 2) ∧
    (mobiusNumerator σ_disk t < mobiusDenominator σ_disk t) ∧
    (mobiusNumerator σ_ext t > mobiusDenominator σ_ext t) ∧
    (mobiusNumerator σ t - lam * mobiusDenominator σ t =
      (1 - lam) * ((σ - apolloniusCenter lam) ^ 2 + t ^ 2 - apolloniusRadiusSq lam)) ∧
    (mobiusMap (1 - s) = (mobiusMap s)⁻¹) ∧
    (F * F = (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    (F * B * F = R) := by
  exact ⟨mobius_norm_diff σ t,
    (mobius_unitary_iff σ t).mpr h_half,
    mobius_critical_line_vertical_flow t,
    (mobius_disk_foliation_iff σ_disk t).mpr h_disk,
    (mobius_exterior_foliation_iff σ_ext t).mpr h_ext,
    apollonius_circle_identity σ t lam h_lam,
    mobius_functional_equation_dual s,
    F_sq,
    F_B_F_eq_R⟩

end InfoGeometry.Canonical.MobiusApolloniusFoliation
