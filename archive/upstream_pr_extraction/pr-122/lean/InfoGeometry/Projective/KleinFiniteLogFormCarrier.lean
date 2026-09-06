import InfoGeometry.Projective.KleinQuadricLogDeRhamClass
import InfoGeometry.Projective.KleinQuadricDeRhamComplex

/-!
# Finite local logarithmic-form carrier

This owner supplies a concrete finite local `Ω¹` witness for the Klein
logarithmic coefficient.  It uses a chosen slit-plane branch, so it makes no
global de Rham or global logarithm claim.
-/

namespace InfoGeometry.Projective.KleinFiniteLogFormCarrier

noncomputable section

open InfoGeometry.Projective.KleinQuadric.LogDeRhamClass
open InfoGeometry.Projective.KleinQuadric.DeRhamComplex
open InfoGeometry.Clifford.UniversalCoverLog
open InfoGeometry.Projective.KleinQuadric.DeRhamMotive

structure LocalLogForm where
  point : ℂ
  branch : point ∈ Complex.slitPlane

abbrev SlitPlanePoint := {z : ℂ // z ∈ Complex.slitPlane}

def globalCoefficient (z : SlitPlanePoint) : ℂ := 1 / z.1

def globalPrimitive (z : SlitPlanePoint) : ℂ := Complex.log z.1

theorem globalPrimitive_derivative (z : SlitPlanePoint) :
    HasDerivAt (fun w : ℂ => Complex.log w) (globalCoefficient z) z.1 := by
  simpa [globalCoefficient] using Complex.hasDerivAt_log z.2

theorem globalPrimitive_derivative_in_owner (z : SlitPlanePoint) :
    HasDerivAt grothendieckLog (globalCoefficient z) z.1 := by
  simpa only [grothendieckLog] using globalPrimitive_derivative z

theorem globalCoefficient_eq_dlog (z : SlitPlanePoint) :
    globalCoefficient z = grothendieck_dlog z.1 := by
  rfl

theorem globalCoefficient_nonzero (z : SlitPlanePoint)
    (hz : z.1 ≠ 0) : globalCoefficient z ≠ 0 := by
  exact one_div_ne_zero hz

theorem universalCover_sheet_add (z : ℂ) (n k : ℤ) :
    uLog (z, n + k) = uLog (z, n) +
      (2 * Real.pi * Complex.I : ℂ) * (k : ℂ) := by
  unfold uLog
  push_cast
  ring

theorem universalCoverLog_derivative
    (z : SlitPlanePoint) (n : ℤ) :
    HasDerivAt (fun w : ℂ => uLog (w, n))
      (globalCoefficient z) z.1 := by
  simpa [uLog, globalCoefficient, mul_assoc, mul_left_comm, mul_comm] using
    (Complex.hasDerivAt_log z.2).add_const
      ((2 * Real.pi * Complex.I : ℂ) * (n : ℂ))

def coefficient (ω : LocalLogForm) : ℂ := 1 / ω.point

def primitive (ω : LocalLogForm) : ℂ := Complex.log ω.point

theorem primitive_derivative (ω : LocalLogForm) :
    HasDerivAt (fun z : ℂ => Complex.log z) (coefficient ω) ω.point := by
  simpa [coefficient] using Complex.hasDerivAt_log ω.branch

theorem primitive_derivative_in_owner (ω : LocalLogForm) :
    HasDerivAt grothendieckLog (coefficient ω) ω.point := by
  simpa only [grothendieckLog] using primitive_derivative ω

theorem coefficient_eq_grothendieck_dlog (ω : LocalLogForm) :
    coefficient ω = grothendieck_dlog ω.point := by
  rfl

theorem coefficient_nonzero (ω : LocalLogForm)
    (hpoint : ω.point ≠ 0) : coefficient ω ≠ 0 := by
  exact one_div_ne_zero hpoint

/-! ## A finite circular cycle stage -/

structure CirclePeriodStage where
  radius : ℝ
  positive : 0 < radius

def circlePeriod (C : CirclePeriodStage) : ℂ :=
  logarithmicPeriod C.radius

theorem circlePeriod_eq_residue (C : CirclePeriodStage) :
    circlePeriod C = (2 * Real.pi * Complex.I : ℂ) := by
  exact logarithmicPeriod_eq_residue C.radius C.positive

def circleWindingPeriod (C : CirclePeriodStage) (n : ℤ) : ℂ :=
  (n : ℂ) * circlePeriod C

theorem circleWindingPeriod_add (C : CirclePeriodStage) (m n : ℤ) :
    circleWindingPeriod C (m + n) =
      circleWindingPeriod C m + circleWindingPeriod C n := by
  unfold circleWindingPeriod
  rw [Int.cast_add]
  ring

theorem circlePeriod_ne_zero (C : CirclePeriodStage) :
    circlePeriod C ≠ 0 := by
  exact logarithmicPeriod_ne_zero C.radius C.positive

theorem circleWindingPeriod_one (C : CirclePeriodStage) :
    circleWindingPeriod C 1 = circlePeriod C := by
  simp [circleWindingPeriod]

def circleReadoutClass (C : CirclePeriodStage) :
    cohomologyModule kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex :=
  closedClass kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
    (circlePeriod C) (by simp [kleinZeroD₁])

def circleReadoutPeriodClass :
    cohomologyModule kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex →ₗ[ℂ] ℂ :=
  periodClassFactor kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
    (LinearMap.id : ℂ →ₗ[ℂ] ℂ) (by simp [kleinZeroD₀])

theorem circleReadoutPeriodClass_apply (C : CirclePeriodStage) :
    circleReadoutPeriodClass (circleReadoutClass C) = circlePeriod C := by
  exact periodClassFactor_apply kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
    (LinearMap.id : ℂ →ₗ[ℂ] ℂ) (by simp [kleinZeroD₀])
    (circlePeriod C) (by simp [kleinZeroD₁])

theorem circleReadoutClass_ne_zero (C : CirclePeriodStage) :
    circleReadoutClass C ≠ 0 := by
  apply closedClass_ne_zero_of_period_ne_zero
    kleinZeroD₀ kleinZeroD₁ kleinZeroD_complex
    (circlePeriod C) (by simp [kleinZeroD₁])
    (LinearMap.id : ℂ →ₗ[ℂ] ℂ)
  · simp [kleinZeroD₀]
  · exact circlePeriod_ne_zero C

end
end InfoGeometry.Projective.KleinFiniteLogFormCarrier
