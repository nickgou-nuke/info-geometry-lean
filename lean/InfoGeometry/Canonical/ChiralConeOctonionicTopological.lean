import Mathlib
import InfoGeometry.Canonical.ChiralConeOctonionicBridge

namespace InfoGeometry.Canonical

def realHyperbolicInvolutionLocus : Set ℝ :=
  {u : ℝ | u * u = 1}

theorem continuous_lightconePlus :
    Continuous (fun u : ℝ => lightconePlus u) := by
  unfold lightconePlus
  fun_prop

theorem continuous_lightconeMinus :
    Continuous (fun u : ℝ => lightconeMinus u) := by
  unfold lightconeMinus
  fun_prop

theorem realHyperbolicInvolutionLocus_closed :
    IsClosed (realHyperbolicInvolutionLocus) := by
  change IsClosed ((fun u : ℝ => u * u) ⁻¹' ({1} : Set ℝ))
  exact isClosed_singleton.preimage (continuous_id.mul continuous_id)

theorem lightconePlusOnInvolutionLocus_idempotent
    (u : realHyperbolicInvolutionLocus) :
    lightconePlus (R := ℝ) u.val * lightconePlus (R := ℝ) u.val =
      lightconePlus (R := ℝ) u.val := by
  have hu : u.val * u.val = 1 := u.property
  exact lightconePlus_idempotent (R := ℝ) u.val hu

theorem lightconeMinusOnInvolutionLocus_idempotent
    (u : realHyperbolicInvolutionLocus) :
    lightconeMinus (R := ℝ) u.val * lightconeMinus (R := ℝ) u.val =
      lightconeMinus (R := ℝ) u.val := by
  have hu : u.val * u.val = 1 := u.property
  exact lightconeMinus_idempotent (R := ℝ) u.val hu

end InfoGeometry.Canonical
