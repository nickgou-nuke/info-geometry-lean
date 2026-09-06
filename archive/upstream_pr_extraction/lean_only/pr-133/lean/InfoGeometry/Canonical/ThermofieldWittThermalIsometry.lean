import Mathlib.Tactic
import InfoGeometry.Canonical.ThermofieldWittSoldering

/-!
# Thermal Witt isometry for the thermofield soldering map

The thermofield/Witt soldering owner already constructs the reciprocal thermal
scaling

`(x, ξ) ↦ (exp r • x, exp (-r) • ξ)`

and proves that soldering intertwines it with the corresponding scaling of the
two complementary isotropic Witt sectors.  This file closes the missing metric
statement: the reciprocal scaling preserves the explicit split `(4,4)` polar
form exactly.

This is the finite orthogonal-isometry statement.  We deliberately do not call
the transformation an element of a bundled `SO(4,4)` object here, because that
would additionally require a chosen matrix/basis realization and a proved
`det = 1` statement in that owner.
-/

noncomputable section

namespace InfoGeometry.Canonical.ThermofieldWittThermalIsometry

open InfoGeometry.Krein
open InfoGeometry.Lie.SplitOctonionCircularWittForm
open InfoGeometry.Canonical.ThermofieldWittSoldering

/-- Reciprocal thermal dilation preserves the split `(4,4)` Witt polar form. -/
theorem wittThermalDilation_preserves_polar
    (r : ℝ) (x y : WittCoord) :
    circularPeircePolar (wittThermalDilation r x)
        (wittThermalDilation r y) =
      circularPeircePolar x y := by
  simp [wittThermalDilation, circularPeircePolar, Real.exp_neg]
  field_simp [Real.exp_ne_zero]
  ring

/-- The inverse reciprocal dilation is obtained by reversing the thermal
parameter. -/
theorem wittThermalDilation_neg_comp
    (r : ℝ) :
    (wittThermalDilation (-r)).comp (wittThermalDilation r) =
      LinearMap.id := by
  ext z i
  fin_cases i <;>
    simp [wittThermalDilation, ← Real.exp_add]

/-- The opposite composition is also the identity. -/
theorem wittThermalDilation_comp_neg
    (r : ℝ) :
    (wittThermalDilation r).comp (wittThermalDilation (-r)) =
      LinearMap.id := by
  ext z i
  fin_cases i <;>
    simp [wittThermalDilation, ← Real.exp_add]

/-- Hence the Witt thermal dilation is injective. -/
theorem wittThermalDilation_injective (r : ℝ) :
    Function.Injective (wittThermalDilation r) := by
  intro x y hxy
  have h := congrArg (wittThermalDilation (-r)) hxy
  have hcomp := congrArg (fun T : WittCoord →ₗ[ℝ] WittCoord => T x)
    (wittThermalDilation_neg_comp r)
  have hcomp' := congrArg (fun T : WittCoord →ₗ[ℝ] WittCoord => T y)
    (wittThermalDilation_neg_comp r)
  simpa [LinearMap.comp_apply] using hcomp.symm.trans (h.trans hcomp')

/-- Hence the Witt thermal dilation is surjective. -/
theorem wittThermalDilation_surjective (r : ℝ) :
    Function.Surjective (wittThermalDilation r) := by
  intro y
  refine ⟨wittThermalDilation (-r) y, ?_⟩
  have h := congrArg (fun T : WittCoord →ₗ[ℝ] WittCoord => T y)
    (wittThermalDilation_comp_neg r)
  simpa [LinearMap.comp_apply] using h

/-- The metric statement transported back through the soldering map: thermal
forward expansion and backward contraction cancel exactly in the cross pairing. -/
theorem thermalDilation_preserves_soldered_polar
    (r : ℝ) (u v : DoubledSpace V4) :
    circularPeircePolar
        (wittSoldering (thermalDilation r u))
        (wittSoldering (thermalDilation r v)) =
      circularPeircePolar (wittSoldering u) (wittSoldering v) := by
  rw [wittSoldering_intertwines_thermalDilation,
    wittSoldering_intertwines_thermalDilation]
  exact wittThermalDilation_preserves_polar r (wittSoldering u) (wittSoldering v)

/-- On explicit doubled coordinates, the preserved form is the Lorentzian
forward/backward cross pairing. -/
theorem thermalDilation_cross_pairing
    (r : ℝ) (x ξ y η : V4) :
    circularPeircePolar
        (wittSoldering
          (thermalDilation r (to_doubled x ξ : DoubledSpace V4)))
        (wittSoldering
          (thermalDilation r (to_doubled y η : DoubledSpace V4))) =
      minkowskiPair x η + minkowskiPair y ξ := by
  rw [thermalDilation_preserves_soldered_polar]
  exact circularPeircePolar_wittSoldering x ξ y η

/-- The diagonal real section remains exactly twice the physical `(1,3)`
Minkowski pairing after thermal dilation. -/
theorem thermalDilation_diagonal_metric
    (r : ℝ) (x y : V4) :
    circularPeircePolar
        (wittSoldering
          (thermalDilation r (to_doubled x x : DoubledSpace V4)))
        (wittSoldering
          (thermalDilation r (to_doubled y y : DoubledSpace V4))) =
      2 * minkowskiPair x y := by
  rw [thermalDilation_preserves_soldered_polar]
  exact diagonal_soldering_metric x y

/-- Compact finite theorem packet for the reciprocal thermofield/Witt isometry. -/
theorem thermal_witt_isometry_packet (r : ℝ) :
    Function.Bijective (wittThermalDilation r) ∧
      (∀ x y : WittCoord,
        circularPeircePolar (wittThermalDilation r x)
            (wittThermalDilation r y) =
          circularPeircePolar x y) := by
  exact ⟨⟨wittThermalDilation_injective r,
      wittThermalDilation_surjective r⟩,
    wittThermalDilation_preserves_polar r⟩

end InfoGeometry.Canonical.ThermofieldWittThermalIsometry
