import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

noncomputable section

def schurChannelPressure (q c theta : ℝ) : ℝ :=
  c + q * theta / 2

def schurChannelRate (q c alpha : ℝ) : ℝ :=
  (alpha - q / 2) ^ 2 + c

def schurChannelCenteredRate (c s : ℝ) : ℝ :=
  s ^ 2 + c

def schurChannelAffineCenteredRate (q c s : ℝ) : ℝ :=
  s ^ 2 - q * s / 2 + c

/-- Gallavotti--Cohen symmetry for the concrete Schur-channel package: the pressure satisfies the
affine reflection law, the rate is symmetric under `α ↦ q - α`, the centered rate is even, and
the affine-centered antisymmetry closes with slope `-q`.
    thm:sync-kernel-schur-channel-pressure-gc -/
theorem paper_sync_kernel_schur_channel_pressure_gc (q c : ℝ) :
    (∀ theta : ℝ, schurChannelPressure q c theta = q * theta +
      schurChannelPressure q c (-theta)) ∧
      (∀ alpha : ℝ, schurChannelRate q c alpha = schurChannelRate q c (q - alpha)) ∧
      (∀ s : ℝ, schurChannelCenteredRate c s = schurChannelCenteredRate c (-s)) ∧
      (∀ s : ℝ,
        schurChannelAffineCenteredRate q c s -
          schurChannelAffineCenteredRate q c (-s) = -q * s) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro theta
    unfold schurChannelPressure
    ring
  · intro alpha
    unfold schurChannelRate
    ring
  · intro s
    unfold schurChannelCenteredRate
    ring
  · intro s
    unfold schurChannelAffineCenteredRate
    ring

end

end Omega.SyncKernelWeighted
