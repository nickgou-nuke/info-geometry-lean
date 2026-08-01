import InfoGeometry.Dynamics.RapiditySpace
import Mathlib.Tactic

noncomputable section

/-!
# RindlerWedge

Finite real light-cone coordinate algebra for the hyperbolic `A` component.

The module records the elementary Rindler-coordinate facts available from the
verified `2 × 2` boost matrix:

* `A(λ)` translates Rindler time;
* the light-cone product `x₊ * x₋` is invariant along the flow.

No Bisognano--Wichmann, KMS, Unruh temperature, or analytic modular theorem is
claimed here.
-/

namespace InfoGeometry.Dynamics.RindlerWedge

open Matrix
open InfoGeometry.Dynamics.HyperbolicComponent
open InfoGeometry.Dynamics.RapiditySpace

/-- Rindler coordinates with positive radius. -/
def RindlerCoordinatePredicate (p : ℝ × ℝ) : Prop := 0 < p.1

/-- Positive-radius Rindler coordinates. -/
abbrev RindlerCoordinates := {p : ℝ × ℝ // RindlerCoordinatePredicate p}

namespace RindlerCoordinates

abbrev radius (coords : RindlerCoordinates) : ℝ := coords.1.1

abbrev time (coords : RindlerCoordinates) : ℝ := coords.1.2

lemma radius_pos (coords : RindlerCoordinates) : 0 < coords.radius := coords.2

end RindlerCoordinates

/-- Right-wedge condition in light-cone coordinates. -/
def IsInRightRindlerWedge (xplus xminus : ℝ) : Prop :=
  0 < xplus ∧ 0 < xminus

/-- Rindler embedding into light-cone coordinates. -/
def rindlerToMinkowski (coords : RindlerCoordinates) : LightConeColumn :=
  !![coords.radius * Real.exp coords.time;
     coords.radius * Real.exp (-coords.time)]

/-- The Rindler embedding lands in the positive right wedge. -/
theorem rindlerToMinkowski_mem_right_wedge (coords : RindlerCoordinates) :
    IsInRightRindlerWedge
      (rindlerToMinkowski coords 0 0)
      (rindlerToMinkowski coords 1 0) := by
  constructor <;> simp [rindlerToMinkowski, coords.radius_pos] <;> positivity

/--
Applying the hyperbolic boost translates Rindler time by `λ`.
-/
theorem rindler_flow_is_time_translation (coords : RindlerCoordinates) (lam : ℝ) :
    componentAReal lam * rindlerToMinkowski coords =
      rindlerToMinkowski
        ⟨(coords.radius, coords.time + lam), coords.radius_pos⟩ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [componentAReal, rindlerToMinkowski, RindlerCoordinates.radius,
      RindlerCoordinates.time, Matrix.mul_apply, Real.exp_add,
      add_comm, add_left_comm, add_assoc] <;>
      ring_nf <;>
      rw [← Real.exp_add] <;>
      simp <;>
      ring

/-- The light-cone product of a Rindler point is the squared radius. -/
theorem rindler_lightcone_product (coords : RindlerCoordinates) :
    rindlerToMinkowski coords 0 0 * rindlerToMinkowski coords 1 0 =
      coords.radius ^ 2 := by
  simp [rindlerToMinkowski, pow_two]
  calc
    coords.radius * Real.exp coords.time *
        (coords.radius * Real.exp (-coords.time))
        = coords.radius * coords.radius *
            (Real.exp coords.time * Real.exp (-coords.time)) := by
            ring
    _ = coords.radius * coords.radius *
            Real.exp (coords.time + -coords.time) := by
            rw [Real.exp_add]
    _ = coords.radius * coords.radius := by
            simp

/--
The hyperbolic flow preserves the light-cone product, hence the finite
proper-distance readout `radius²`.
-/
theorem rindler_flow_preserves_proper_distance (coords : RindlerCoordinates) (lam : ℝ) :
    let flowed := componentAReal lam * rindlerToMinkowski coords
    flowed 0 0 * flowed 1 0 = coords.radius ^ 2 := by
  intro flowed
  rw [show flowed = componentAReal lam * rindlerToMinkowski coords by rfl]
  rw [rindler_flow_is_time_translation]
  exact rindler_lightcone_product
    ⟨(coords.radius, coords.time + lam), coords.radius_pos⟩

end InfoGeometry.Dynamics.RindlerWedge
