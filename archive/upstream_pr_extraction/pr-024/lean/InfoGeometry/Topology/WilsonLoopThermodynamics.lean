import Mathlib
import InfoGeometry.Topology.ThermodynamicGauge

/-!
# Wilson-Loop Thermodynamics

Conservative first-level scaffold for finite non-abelian Wilson-loop style
transport over a finite thermodynamic flow packet.

This module deliberately avoids analytic content. It only records
finite-word algebra and explicit trace/curvature hypotheses that can be
consumed by downstream files.
-/

namespace InfoGeometry.Topology.WilsonLoopThermodynamics

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

/-- Explicit compatibility hypothesis comparing transported and static loop-word
trace readouts. This keeps the Wilson/Bost-Connes bridge assumption-driven. -/
structure FlowStaticHolonomyAgreement (flow : CausalNonequilibriumFlow Op)
    [Algebra ℝ Op] (trace : Op →ₗ[ℝ] ℝ) where
  agrees : ∀ word : LoopWord Op,
    trace (LoopWord.flowHolonomy flow word) = trace (LoopWord.holonomy word)

/-- Read back a supplied transported/static trace comparison on one finite word. -/
theorem flow_static_holonomy_agreement_readout
    [Algebra ℝ Op]
    (flow : CausalNonequilibriumFlow Op)
    (trace : Op →ₗ[ℝ] ℝ)
    (agreement : FlowStaticHolonomyAgreement flow trace)
    (word : LoopWord Op) :
    trace (LoopWord.flowHolonomy flow word) = trace (LoopWord.holonomy word) :=
  agreement.agrees word

/-- Certificate carrying compatible finite flow-holonomy and curvature trace
evaluations. The scalar is named `partitionZeta` because downstream
Bost-Connes interfaces use it as a supplied partition readout; no analytic
partition identity is asserted here. -/
structure WilsonCurvatureTraceCertificate (flow : CausalNonequilibriumFlow Op)
    [Algebra ℝ Op] (trace : Op →ₗ[ℝ] ℝ) where
  partitionZeta : ℝ
  path : LoopWord Op
  holonomy_trace_eval : trace (LoopWord.flowHolonomy flow path) = partitionZeta
  curvature_trace_eval : trace (thermodynamic_curvature flow) = partitionZeta

/-- Readout schema from an explicit finite flow Wilson-loop trace premise. -/
theorem reads_holonomy_of_premise
    [Algebra ℝ Op] (flow : CausalNonequilibriumFlow Op)
    (trace : Op →ₗ[ℝ] ℝ)
    (path : LoopWord Op)
    (partitionZeta : ℝ)
    (holonomy_trace_eval : trace (LoopWord.flowHolonomy flow path) = partitionZeta) :
    trace (LoopWord.flowHolonomy flow path) = partitionZeta :=
  holonomy_trace_eval

/-- Readout schema from an explicit finite curvature trace premise. -/
theorem reads_curvature_of_premise
    [Algebra ℝ Op] (flow : CausalNonequilibriumFlow Op)
    (trace : Op →ₗ[ℝ] ℝ)
    (partitionZeta : ℝ)
    (curvature_trace_eval : trace (thermodynamic_curvature flow) = partitionZeta) :
    trace (thermodynamic_curvature flow) = partitionZeta :=
  curvature_trace_eval

/-- Readout schema from a finite certificate packet carrying holonomy data. -/
theorem reads_holonomy_of_certificate
    [Algebra ℝ Op] (flow : CausalNonequilibriumFlow Op)
    (trace : Op →ₗ[ℝ] ℝ)
    (certificate : WilsonCurvatureTraceCertificate flow trace) :
    trace (LoopWord.flowHolonomy flow certificate.path) = certificate.partitionZeta :=
  certificate.holonomy_trace_eval

/-- Readout schema from a finite certificate packet carrying curvature data. -/
theorem reads_curvature_of_certificate
    [Algebra ℝ Op] (flow : CausalNonequilibriumFlow Op)
    (trace : Op →ₗ[ℝ] ℝ)
    (certificate : WilsonCurvatureTraceCertificate flow trace) :
    trace (thermodynamic_curvature flow) = certificate.partitionZeta :=
  certificate.curvature_trace_eval

/-- Curvature and holonomy traces match the same scalar under explicit premises. -/
theorem reads_both_from_premises
    [Algebra ℝ Op] (flow : CausalNonequilibriumFlow Op)
    (trace : Op →ₗ[ℝ] ℝ)
    (path : LoopWord Op)
    (partitionZeta : ℝ)
    (holonomy_trace_eval : trace (LoopWord.flowHolonomy flow path) = partitionZeta)
    (curvature_trace_eval : trace (thermodynamic_curvature flow) = partitionZeta) :
    trace (LoopWord.flowHolonomy flow path) =
      trace (thermodynamic_curvature flow) := by
  rw [holonomy_trace_eval, curvature_trace_eval]

/-- Curvature vanishes under detailed balance of the thermodynamic flow. -/
theorem curvature_vanishes_under_detailed_balance
    (flow : CausalNonequilibriumFlow Op)
    (hdb : entropy_production flow = 0) :
    thermodynamic_curvature flow = 0 := by
  rw [thermodynamic_curvature, hdb]
  simp

end InfoGeometry.Topology.WilsonLoopThermodynamics
