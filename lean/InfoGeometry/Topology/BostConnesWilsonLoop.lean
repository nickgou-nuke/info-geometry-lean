import Mathlib.Tactic
import InfoGeometry.Topology.ThermodynamicGauge
import InfoGeometry.Topology.WilsonLoopThermodynamics

/-!
# Finite Wilson-loop readouts

This owner contains only the finite ring-level mathematics available in the
repository. A Wilson word is an ordered finite product, and a curvature
readout is the linear image of the thermodynamic commutator. External zeta
values, analytic partition functions, and physical constitutive laws are not
encoded here.
-/

namespace InfoGeometry.Topology.BostConnesWilsonLoop

open InfoGeometry.Topology.ThermodynamicGauge
open InfoGeometry.Topology.WilsonLoopThermodynamics

variable {Op : Type*} [Ring Op] [Algebra ℝ Op]

/-- The trace readout of a finite Wilson word. -/
def wilsonReadout (trace : Op →ₗ[ℝ] ℝ) (path : List Op) : ℝ :=
  trace (finite_wilson_loop path)

/-- The trace readout of the thermodynamic curvature commutator. -/
def curvatureReadout
    (flow : CausalNonequilibriumFlow Op) (trace : Op →ₗ[ℝ] ℝ) : ℝ :=
  trace (thermodynamic_curvature flow)

@[simp] theorem wilsonReadout_nil (trace : Op →ₗ[ℝ] ℝ) :
    wilsonReadout trace [] = trace 1 := by
  rfl

@[simp] theorem wilsonReadout_append_singleton
    (trace : Op →ₗ[ℝ] ℝ) (path : List Op) (step : Op) :
    wilsonReadout trace (path ++ [step]) =
      trace (finite_wilson_loop path * (1 + step)) := by
  rw [wilsonReadout, finite_wilson_loop_append_singleton]

@[simp] theorem flowWilsonReadout_append_singleton
    (flow : CausalNonequilibriumFlow Op) (trace : Op →ₗ[ℝ] ℝ)
    (path : List Op) (step : Op) :
    trace (finite_flow_wilson_loop flow (path ++ [step])) =
      trace (finite_flow_wilson_loop flow path *
        (1 + flowed_connection_step flow step)) := by
  rw [finite_flow_wilson_loop_append_singleton]

/-- Detailed balance annihilates the curvature readout. -/
theorem curvatureReadout_eq_zero_of_detailed_balance
    (flow : CausalNonequilibriumFlow Op)
    (trace : Op →ₗ[ℝ] ℝ)
    (hdb : entropy_production flow = 0) :
    curvatureReadout flow trace = 0 := by
  rw [curvatureReadout, curvature_vanishes_under_detailed_balance flow hdb]
  exact map_zero trace

/-- The curvature readout is linear in the chosen trace. -/
theorem curvatureReadout_smul
    (flow : CausalNonequilibriumFlow Op)
    (trace : Op →ₗ[ℝ] ℝ) (a : ℝ) :
    curvatureReadout flow (a • trace) = a * curvatureReadout flow trace := by
  rfl

end InfoGeometry.Topology.BostConnesWilsonLoop
