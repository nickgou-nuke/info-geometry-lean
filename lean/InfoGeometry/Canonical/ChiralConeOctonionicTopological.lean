import Mathlib
import InfoGeometry.Canonical.ChiralConeOctonionicBridge

namespace InfoGeometry.Canonical

def hyperbolicInvolutionLocus : Set ℝ :=
  {u : ℝ | u * u = 1}

theorem continuous_lightconePlus :
    Continuous (fun u : ℝ => lightconePlus u) := by
  fun_prop

theorem continuous_lightconeMinus :
    Continuous (fun u : ℝ => lightconeMinus u) := by
  fun_prop

theorem hyperbolicInvolutionLocus_isClosed :
    IsClosed (hyperbolicInvolutionLocus) := by
  change IsClosed ((fun u : ℝ => u * u) ⁻¹' ({1} : Set ℝ))
  exact isClosed_singleton.preimage (continuous_id.mul continuous_id)

theorem lightconePlusOnInvolutionLocus_idempotent
    (u : hyperbolicInvolutionLocus) :
    lightconePlus (R := ℝ) u.val * lightconePlus (R := ℝ) u.val =
      lightconePlus (R := ℝ) u.val := by
  have hu : u.val * u.val = 1 := u.property
  exact lightconePlus_idempotent (R := ℝ) u.val hu

theorem lightconeMinusOnInvolutionLocus_idempotent
    (u : hyperbolicInvolutionLocus) :
    lightconeMinus (R := ℝ) u.val * lightconeMinus (R := ℝ) u.val =
      lightconeMinus (R := ℝ) u.val := by
  have hu : u.val * u.val = 1 := u.property
  exact lightconeMinus_idempotent (R := ℝ) u.val hu

end InfoGeometry.Canonical
