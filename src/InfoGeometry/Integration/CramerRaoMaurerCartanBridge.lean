import InfoGeometry.Canonical.CramerRaoUncertaintyCapstone
import InfoGeometry.Information.ModularCocycleKMSBridge
import InfoGeometry.ParaKahler.UnifiedPotential
import InfoGeometry.Quantum.CramerRaoUncertainty

namespace InfoGeometry.Integration.CramerRaoMaurerCartanBridge

open InfoGeometry.Canonical.CramerRaoUncertaintyCapstone
open InfoGeometry.Information.ModularCocycleKMSBridge
open InfoGeometry.ParaKahler.UnifiedPotential
open InfoGeometry.Quantum.CramerRaoUncertainty

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

structure CramerRaoMaurerCartanData (v F dξ dθ : ℝ) (K : A) (u : Aˣ) where
  hF : 0 < F
  hCR : cramerRaoBound v F

theorem bridge_synthesis (v F dξ dθ : ℝ) (K : A) (u : Aˣ)
  (data : CramerRaoMaurerCartanData v F dξ dθ K u) :
  (v * F ≥ 1) ∧
  (dlogL (adOp K) (u * u) = (↑u⁻¹ : A) * dlogL (adOp K) u * (u : A) + dlogL (adOp K) u) ∧
  (let ω := maurerCartanForm dξ dθ; ω * ω - ω * ω = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (capstone_cramer_rao_uncertainty_synthesis v F data.hF data.hCR).1
  · exact dlogL_ad_mul_cocycle K u u
  · exact maurer_cartan_self_bracket_zero dξ dθ

end InfoGeometry.Integration.CramerRaoMaurerCartanBridge
