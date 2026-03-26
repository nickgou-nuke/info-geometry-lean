import InfoGeometry.Canonical.RelativePotentialCore

/-!
# InfoGeometry.Canonical.RelativePotentialScalarBridge

Scalar representation layer for the projective/affine relative-potential spine.

A strictly positive scalar is realized as a positive measure on the singleton
carrier. This makes plain `-log` potentials instances of the existing
representative-level modular-potential language rather than a separate ontology.
-/

namespace InfoGeometry.Canonical.RelativePotentialScalarBridge

open InfoGeometry.Canonical.RelativePotentialCore

/-- Realize a strictly positive scalar as a positive measure on the singleton carrier. -/
def scalarPositiveMeasure (r : ℝ) (hr : 0 < r) : InfoGeometry.PositiveMeasure Unit ℝ where
  mass _ := r
  pos _ := hr

@[simp] theorem scalarPositiveMeasure_apply
    (r : ℝ) (hr : 0 < r) :
    scalarPositiveMeasure r hr () = r := rfl

@[simp] theorem representativeRelativeDensity_scalar
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    representativeRelativeDensity
        (scalarPositiveMeasure r hr)
        (scalarPositiveMeasure s hs) ()
      = r / s := rfl

@[simp] theorem representativeRelativeLogDensity_scalar
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    representativeRelativeLogDensity
        (scalarPositiveMeasure r hr)
        (scalarPositiveMeasure s hs) ()
      = Real.log (r / s) := rfl

@[simp] theorem representativeModularPotential_scalar
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    representativeModularPotential
        (scalarPositiveMeasure r hr)
        (scalarPositiveMeasure s hs) ()
      = -Real.log (r / s) := rfl

/-- Log-density of a scalar relative to the unit reference. -/
noncomputable def scalarLogDensity (r : ℝ) (hr : 0 < r) : ℝ :=
  representativeRelativeLogDensity
    (scalarPositiveMeasure r hr)
    (scalarPositiveMeasure 1 zero_lt_one) ()

/-- Modular potential of a scalar relative to the unit reference. -/
noncomputable def scalarModularPotential (r : ℝ) (hr : 0 < r) : ℝ :=
  representativeModularPotential
    (scalarPositiveMeasure r hr)
    (scalarPositiveMeasure 1 zero_lt_one) ()

@[simp] theorem scalarLogDensity_eq_log
    (r : ℝ) (hr : 0 < r) :
    scalarLogDensity r hr = Real.log r := by
  unfold scalarLogDensity
  rw [representativeRelativeLogDensity_eq_log_sub_log]
  simp

@[simp] theorem scalarModularPotential_eq_neg_log
    (r : ℝ) (hr : 0 < r) :
    scalarModularPotential r hr = -Real.log r := by
  unfold scalarModularPotential
  rw [representativeModularPotential_scalar]
  simp

@[simp] theorem exp_neg_scalarModularPotential_eq
    (r : ℝ) (hr : 0 < r) :
    Real.exp (-(scalarModularPotential r hr)) = r := by
  rw [scalarModularPotential_eq_neg_log]
  simp [Real.exp_log hr]

/--
Positive Weyl rescaling changes the scalar modular potential only by an
additive constant. The rescaling mode `-log c` is the gauge term coming from
changing the normalization section, not new dynamics.
-/
theorem scalarModularPotential_weylRescale_eq_sub_log
    (c r : ℝ) (hc : 0 < c) (hr : 0 < r) :
    scalarModularPotential (c * r) (mul_pos hc hr)
      = scalarModularPotential r hr - Real.log c := by
  rw [scalarModularPotential_eq_neg_log, scalarModularPotential_eq_neg_log,
    Real.log_mul hc.ne' hr.ne']
  ring

end InfoGeometry.Canonical.RelativePotentialScalarBridge
