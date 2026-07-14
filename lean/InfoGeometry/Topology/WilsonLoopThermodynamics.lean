import Mathlib
import InfoGeometry.Topology.ThermodynamicGauge

/-!
# Wilson-Loop Thermodynamics

Conservative first-level scaffold for finite non-abelian Wilson-loop style
transport over a finite thermodynamic flow packet.

This module deliberately avoids analytic content. It records finite-word
algebra for transported loop words and the detailed-balance curvature
collapse used by downstream files.
-/

namespace WilsonLoopThermodynamics

open InfoGeometry.Topology.ThermodynamicGauge

variable {Op : Type*} [Ring Op]

/-- A finite loop word is represented only by its ordered list of steps. -/
abbrev LoopWord (Op : Type*) := List Op

/-- Flow-displaced local connection step: `a ↦ P_forward * a * P_backward`. -/
def flowed_connection_step (flow : CausalNonequilibriumFlow Op) (step : Op) : Op :=
  flow.P_forward * step * flow.P_backward

/-- Flow-word transport: ordered product of flow-displaced steps. -/
def finite_flow_connection_word (flow : CausalNonequilibriumFlow Op) (path : List Op) : Op :=
  path.foldl (fun acc step => acc * flowed_connection_step flow step) 1

/-- Flow Wilson-loop holonomy: path-ordered finite product of a finite list
of infinitesimal factors `(1 + transported_step)`. -/
def finite_flow_wilson_loop (flow : CausalNonequilibriumFlow Op) (path : List Op) : Op :=
  path.foldl (fun acc step => acc * (1 + flowed_connection_step flow step)) 1

namespace LoopWord

/-- Static finite Wilson-loop holonomy attached to a loop word. -/
def holonomy (word : LoopWord Op) : Op :=
  finite_wilson_loop word

/-- Flow-transported finite Wilson-loop holonomy attached to a loop word. -/
def flowHolonomy (flow : CausalNonequilibriumFlow Op) (word : LoopWord Op) : Op :=
  finite_flow_wilson_loop flow word

@[simp] theorem holonomy_nil :
    holonomy ([] : LoopWord Op) = 1 := by
  rfl

@[simp] theorem flowHolonomy_nil (flow : CausalNonequilibriumFlow Op) :
    flowHolonomy flow ([] : LoopWord Op) = 1 := by
  rfl

@[simp] theorem holonomy_singleton (step : Op) :
    holonomy ([step] : LoopWord Op) = 1 + step := by
  simp [holonomy, finite_wilson_loop]

@[simp] theorem flowHolonomy_singleton (flow : CausalNonequilibriumFlow Op) (step : Op) :
    flowHolonomy flow ([step] : LoopWord Op) = 1 + flowed_connection_step flow step := by
  simp [flowHolonomy, finite_flow_wilson_loop]

end LoopWord

/-- Empty flow-transport word is unit. -/
theorem finite_flow_connection_word_nil (flow : CausalNonequilibriumFlow Op) :
    finite_flow_connection_word flow ([] : List Op) = 1 := by
  rfl

/-- Empty finite flow Wilson loop is unit. -/
theorem finite_flow_wilson_loop_nil (flow : CausalNonequilibriumFlow Op) :
    finite_flow_wilson_loop flow ([] : List Op) = 1 := by
  rfl

/-- Appending one transported step multiplies the flow connection word. -/
theorem finite_flow_connection_word_append_singleton
    (flow : CausalNonequilibriumFlow Op) (path : List Op) (step : Op) :
    finite_flow_connection_word flow (path ++ [step]) =
      finite_flow_connection_word flow path * flowed_connection_step flow step := by
  simp [finite_flow_connection_word]

/-- Appending one loop step multiplies finite Wilson-loop transport by
`(1 + transported_step)`. -/
theorem finite_flow_wilson_loop_append_singleton
    (flow : CausalNonequilibriumFlow Op) (path : List Op) (step : Op) :
    finite_flow_wilson_loop flow (path ++ [step]) =
      finite_flow_wilson_loop flow path * (1 + flowed_connection_step flow step) := by
  simp [finite_flow_wilson_loop]

/-- One-step specializations. -/
theorem finite_flow_connection_word_singleton
    (flow : CausalNonequilibriumFlow Op) (step : Op) :
    finite_flow_connection_word flow [step] = flowed_connection_step flow step := by
  simp [finite_flow_connection_word]

theorem finite_flow_wilson_loop_singleton
    (flow : CausalNonequilibriumFlow Op) (step : Op) :
    finite_flow_wilson_loop flow [step] = 1 + flowed_connection_step flow step := by
  simp [finite_flow_wilson_loop]

/-- Curvature vanishes under detailed balance of the thermodynamic flow. -/
theorem curvature_vanishes_under_detailed_balance
    (flow : CausalNonequilibriumFlow Op)
    (hdb : entropy_production flow = 0) :
    thermodynamic_curvature flow = 0 := by
  rw [thermodynamic_curvature, hdb]
  simp

end WilsonLoopThermodynamics
