import InfoGeometry.Analytic.ZetaRegVolume
import InfoGeometry.Canonical.ChiralRadiationCones
import InfoGeometry.Canonical.TopologicalGapShadow

/-!
# Chiral Null-Space Bridge

This bridge packages the zero-mode subtraction used by the analytic
zeta-volume layer together with the existing chiral radiation and Drazin-core
owner surfaces.

It does not claim a generalized inverse theorem or a spectral theorem.
-/

namespace InfoGeometry.Canonical.ChiralNullSpaceBridge

open TopologicalGapShadow
open ChiralRadiationCones

section Core

variable {E : Type 0}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "EndH" => E →L[ℝ] E

/-- Witness that the heat kernel has a vacuum mode that is subtracted out. -/
structure ZeroModeSubtractionData where
  heatKernel : ℝ → ℂ
  vacuumMode : ℂ
  vacuum_eq_one : vacuumMode = 1
  regulatedHeatKernel : ℝ → ℂ
  regulated_eq_subtract :
    ∀ t : ℝ, regulatedHeatKernel t = heatKernel t - vacuumMode

omit [CompleteSpace E] in
/-- The Drazin core is definitionally the kernel of the hopping operator. -/
theorem drazinCore_eq_kernel (Q : EndH) :
    DrazinCore Q = (susyHoppingOperator Q).ker := rfl

omit [CompleteSpace E] in
/-- The excited state sector is definitionally the orthogonal complement. -/
theorem excitedStateSector_eq_orthogonal (Q : EndH) :
    ExcitedStateSector Q = (DrazinCore Q)ᗮ := rfl

/-- The regulated heat kernel is exactly the vacuum-subtracted kernel property. -/
theorem regulatedHeatKernel_eq_subtract_one
    (W : ZeroModeSubtractionData) (t : ℝ) :
    W.regulatedHeatKernel t = W.heatKernel t - W.vacuumMode := by
  simpa using W.regulated_eq_subtract t

/-- The vacuum mode is explicitly normalized to one in the prime-gas boundary package. -/
theorem vacuumMode_eq_one (W : ZeroModeSubtractionData) :
    W.vacuumMode = 1 := W.vacuum_eq_one

end Core

end InfoGeometry.Canonical.ChiralNullSpaceBridge
