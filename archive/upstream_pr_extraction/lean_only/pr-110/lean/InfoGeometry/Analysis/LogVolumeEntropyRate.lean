import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section

namespace InfoGeometry.Analysis.LogVolumeEntropyRate

/-- Logarithmic derivative of a scalar volume path. -/
def logVolumeRate
    (Q : ℝ → ℝ)
    (t : ℝ) : ℝ :=
  deriv Q t / Q t

/-- Negative logarithmic compression potential of a scalar volume path. -/
def compressionPotential
    (Q : ℝ → ℝ)
    (t : ℝ) : ℝ :=
  -Real.log (Q t)

/--
The derivative of negative log-volume is the negative logarithmic derivative.
-/
theorem hasDerivAt_compressionPotential
    {Q : ℝ → ℝ}
    {t Q' : ℝ}
    (hQ : HasDerivAt Q Q' t)
    (hQt : Q t ≠ 0) :
    HasDerivAt
      (compressionPotential Q)
      (-Q' / Q t)
      t := by
  have h := (hQ.log hQt).neg
  change HasDerivAt (-fun y => Real.log (Q y)) (-Q' / Q t) t
  convert h using 1
  ring

/-- Derivative-level form of the negative logarithmic-volume law. -/
theorem deriv_compressionPotential
    {Q : ℝ → ℝ}
    {t : ℝ}
    (hQ : DifferentiableAt ℝ Q t)
    (hQt : Q t ≠ 0) :
    deriv (compressionPotential Q) t =
      -logVolumeRate Q t := by
  have h :=
    hasDerivAt_compressionPotential hQ.hasDerivAt hQt
  rw [h.deriv]
  unfold logVolumeRate
  ring

/-- Exponential scalar volume has affine negative-log compression potential. -/
theorem compressionPotential_exp
    (a t : ℝ) :
    compressionPotential (fun u : ℝ => Real.exp (u * a)) t =
      -(t * a) := by
  simp [compressionPotential]

/-- The logarithmic rate of `exp (t a)` is the constant generator `a`. -/
theorem logVolumeRate_exp
    (a t : ℝ) :
    logVolumeRate (fun u : ℝ => Real.exp (u * a)) t = a := by
  have h :
      HasDerivAt
        (fun u : ℝ => Real.exp (u * a))
        (Real.exp (t * a) * a)
        t := by
    simpa using ((hasDerivAt_id t).mul_const a).exp
  unfold logVolumeRate
  rw [h.deriv]
  field_simp [Real.exp_ne_zero]

/-- The entropy-production rate of exponential scalar volume is `-a`. -/
theorem deriv_compressionPotential_exp
    (a t : ℝ) :
    deriv
        (compressionPotential (fun u : ℝ => Real.exp (u * a)))
        t =
      -a := by
  have h :
      DifferentiableAt ℝ (fun u : ℝ => Real.exp (u * a)) t :=
    (((hasDerivAt_id t).mul_const a).exp).differentiableAt
  rw [deriv_compressionPotential h (Real.exp_ne_zero (t * a))]
  rw [logVolumeRate_exp]

end InfoGeometry.Analysis.LogVolumeEntropyRate
