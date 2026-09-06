import InfoGeometry.Analysis.LogVolumeEntropyRate

noncomputable section

namespace InfoGeometry.Analysis.LogVolumeExactDifferential

open InfoGeometry.Analysis.LogVolumeEntropyRate

/-- Global logarithmic potential of a nonzero scalar volume path. -/
def logVolumePotential
    (Q : ℝ → ℝ)
    (t : ℝ) : ℝ :=
  Real.log (Q t)

/-- One-dimensional logarithmic-volume differential. -/
def logVolumeDifferential
    (Q : ℝ → ℝ)
    (t : ℝ) : ℝ :=
  logVolumeRate Q t

/-- Chain rule for the global logarithmic-volume potential. -/
theorem hasDerivAt_logVolumePotential
    {Q : ℝ → ℝ}
    {t Q' : ℝ}
    (hQ : HasDerivAt Q Q' t)
    (hQt : Q t ≠ 0) :
    HasDerivAt
      (logVolumePotential Q)
      (Q' / Q t)
      t := by
  simpa [logVolumePotential] using hQ.log hQt

/--
The derivative of the global logarithmic potential is the logarithmic-volume
rate.
-/
theorem deriv_logVolumePotential_eq_logVolumeRate
    {Q : ℝ → ℝ}
    {t : ℝ}
    (hQ : DifferentiableAt ℝ Q t)
    (hQt : Q t ≠ 0) :
    deriv (logVolumePotential Q) t =
      logVolumeRate Q t := by
  have h :=
    hasDerivAt_logVolumePotential hQ.hasDerivAt hQt
  rw [h.deriv]
  rfl

/-- The compression potential is the negative logarithmic-volume potential. -/
theorem compressionPotential_eq_neg_logVolumePotential
    (Q : ℝ → ℝ) :
    compressionPotential Q =
      -logVolumePotential Q := by
  funext t
  rfl

/--
At every differentiable nonzero point, entropy rate and logarithmic-volume
rate cancel exactly.
-/
theorem entropyRate_add_logVolumeRate_eq_zero
    {Q : ℝ → ℝ}
    {t : ℝ}
    (hQ : DifferentiableAt ℝ Q t)
    (hQt : Q t ≠ 0) :
    deriv (compressionPotential Q) t +
        deriv (logVolumePotential Q) t =
      0 := by
  rw [deriv_compressionPotential hQ hQt,
    deriv_logVolumePotential_eq_logVolumeRate hQ hQt]
  ring

/-- The logarithmic-volume differential is exact along a differentiable path. -/
theorem logVolumeDifferential_eq_deriv_logVolumePotential
    {Q : ℝ → ℝ}
    {t : ℝ}
    (hQ : DifferentiableAt ℝ Q t)
    (hQt : Q t ≠ 0) :
    logVolumeDifferential Q t =
      deriv (logVolumePotential Q) t := by
  rw [logVolumeDifferential,
    deriv_logVolumePotential_eq_logVolumeRate hQ hQt]

end InfoGeometry.Analysis.LogVolumeExactDifferential
