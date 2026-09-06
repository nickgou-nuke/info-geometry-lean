import Mathlib
import InfoGeometry.Topology.ThermodynamicGauge
import InfoGeometry.Topology.WilsonLoopThermodynamics

/-!
# Bost-Connes Wilson Loop Expansion

Assumption-driven scaffolding for the finite Wilson-loop/Bost-Cones interface.
This file does not assert analytic partition-function identities. It only
exposes explicit readout assumptions.
-/

namespace InfoGeometry.Topology.BostConnesWilsonLoop

open InfoGeometry.Topology.ThermodynamicGauge

variable {Op : Type*} [Ring Op] [Algebra ℝ Op]

/-- Curvature trace hypothesis: trace of the thermodynamic curvature equals
`zetaValue`. -/
structure BostConnesZetaHypothesis (flow : CausalNonequilibriumFlow Op)
    (trace : Op →ₗ[ℝ] ℝ) where
  zetaValue : ℝ
  curvature_evals_to_zeta : trace (thermodynamic_curvature flow) = zetaValue

/-- Canonical finite Bost-Connes certificate for static words. -/
structure BostConnesWilsonCertificate (flow : CausalNonequilibriumFlow Op)
    (trace : Op →ₗ[ℝ] ℝ) where
  beta : ℝ
  partitionZeta : ℝ
  path : List Op
  holonomy_trace_eval : trace (finite_wilson_loop path) = partitionZeta
  curvature_trace_eval : trace (thermodynamic_curvature flow) = partitionZeta

/-- Flow-aware Wilson certificate for transported loops. -/
structure BostConnesFlowCertificate (flow : CausalNonequilibriumFlow Op)
    (trace : Op →ₗ[ℝ] ℝ) where
  partitionZeta : ℝ
  path : List Op
  holonomy_trace_eval :
    trace (_root_.InfoGeometry.Topology.WilsonLoopThermodynamics.LoopWord.flowHolonomy flow path) =
    partitionZeta
  curvature_trace_eval : trace (thermodynamic_curvature flow) = partitionZeta

/-- Read out a supplied holonomy trace value. -/
theorem evaluate_bost_connes_holonomy
    (trace : Op →ₗ[ℝ] ℝ)
    (path : List Op)
    (zetaValue : ℝ)
    (h_holonomy : trace (finite_wilson_loop path) = zetaValue) :
    trace (finite_wilson_loop path) = zetaValue := h_holonomy

/-- Read out a supplied curvature trace value. -/
theorem evaluate_bost_connes_curvature
    (flow : CausalNonequilibriumFlow Op)
    (trace : Op →ₗ[ℝ] ℝ)
    (zetaValue : ℝ)
    (h_curvature : trace (thermodynamic_curvature flow) = zetaValue) :
    trace (thermodynamic_curvature flow) = zetaValue := h_curvature

/-- Read out from a finite Bost-Connes certificate. -/
theorem evaluate_bost_connes_certificate_holonomy
    (flow : CausalNonequilibriumFlow Op)
    (trace : Op →ₗ[ℝ] ℝ)
    (certificate : BostConnesWilsonCertificate flow trace) :
    trace (finite_wilson_loop certificate.path) = certificate.partitionZeta :=
  certificate.holonomy_trace_eval

/-- Read out curvature from a finite Bost-Connes certificate. -/
theorem evaluate_bost_connes_certificate_curvature
    (flow : CausalNonequilibriumFlow Op)
    (trace : Op →ₗ[ℝ] ℝ)
    (certificate : BostConnesWilsonCertificate flow trace) :
    trace (thermodynamic_curvature flow) = certificate.partitionZeta :=
  certificate.curvature_trace_eval

/-- Build a finite Bost-Connes certificate from explicit premises. -/
def finite_wilson_certificate
    (flow : CausalNonequilibriumFlow Op)
    (trace : Op →ₗ[ℝ] ℝ)
    (path : List Op)
    (zetaValue : ℝ)
    (h_holonomy : trace (finite_wilson_loop path) = zetaValue)
    (h_curvature : trace (thermodynamic_curvature flow) = zetaValue) :
    BostConnesWilsonCertificate flow trace :=
  { beta := 0
    partitionZeta := zetaValue
    path := path
    holonomy_trace_eval := h_holonomy
    curvature_trace_eval := h_curvature }

/-- Legacy hypothesis readout for thermodynamic curvature. -/
theorem evaluate_bost_connes_curvature_from_hypothesis
    (flow : CausalNonequilibriumFlow Op)
    (trace : Op →ₗ[ℝ] ℝ)
    (hypothesis : BostConnesZetaHypothesis flow trace) :
    trace (thermodynamic_curvature flow) = hypothesis.zetaValue := by
  exact hypothesis.curvature_evals_to_zeta

/-- If both finite readout premises are available, both reduce to the same
partition scalar. -/
theorem explicit_premises_resolve_both_readouts
    (flow : CausalNonequilibriumFlow Op)
    (trace : Op →ₗ[ℝ] ℝ)
    (path : List Op)
    (zetaValue : ℝ)
    (h_holonomy : trace (finite_wilson_loop path) = zetaValue)
    (h_curvature : trace (thermodynamic_curvature flow) = zetaValue) :
    trace (finite_wilson_loop path) = zetaValue ∧
      trace (thermodynamic_curvature flow) = zetaValue := by
  exact ⟨h_holonomy, h_curvature⟩

/-- Under explicit matching scalar premises, holonomy and curvature traces agree. -/
theorem holonomy_trace_eq_curvature_trace_of_explicit_premises
    (flow : CausalNonequilibriumFlow Op)
    (trace : Op →ₗ[ℝ] ℝ)
    (path : List Op)
    (zetaValue : ℝ)
    (h_holonomy : trace (finite_wilson_loop path) = zetaValue)
    (h_curvature : trace (thermodynamic_curvature flow) = zetaValue) :
    trace (finite_wilson_loop path) =
      trace (thermodynamic_curvature flow) := by
  rw [h_holonomy, h_curvature]

/-- Flow-aware evaluation through transported-loop certificates. -/
theorem evaluate_bost_connes_flow_holonomy
    (flow : CausalNonequilibriumFlow Op)
    (trace : Op →ₗ[ℝ] ℝ)
    (certificate : BostConnesFlowCertificate flow trace) :
    trace
      (_root_.InfoGeometry.Topology.WilsonLoopThermodynamics.LoopWord.flowHolonomy
        flow certificate.path) =
      certificate.partitionZeta :=
  certificate.holonomy_trace_eval

/-- Flow-aware curvature readout through transported-loop certificate. -/
theorem evaluate_bost_connes_flow_curvature
    (flow : CausalNonequilibriumFlow Op)
    (trace : Op →ₗ[ℝ] ℝ)
    (certificate : BostConnesFlowCertificate flow trace) :
    trace (thermodynamic_curvature flow) = certificate.partitionZeta :=
  certificate.curvature_trace_eval

/-- Lift a static finite certificate into a transported-loop certificate under
an explicit compatibility hypothesis. -/
def flowify_static_certificate
    (flow : CausalNonequilibriumFlow Op)
    (trace : Op →ₗ[ℝ] ℝ)
    (certificate : BostConnesWilsonCertificate flow trace)
    (agreement :
      _root_.InfoGeometry.Topology.WilsonLoopThermodynamics.FlowStaticHolonomyAgreement
        flow trace) :
    BostConnesFlowCertificate flow trace :=
  { partitionZeta := certificate.partitionZeta
    path := certificate.path
    holonomy_trace_eval := by
      rw [
        _root_.InfoGeometry.Topology.WilsonLoopThermodynamics.flow_static_holonomy_agreement_readout
          flow trace agreement]
      exact certificate.holonomy_trace_eval
    curvature_trace_eval := certificate.curvature_trace_eval }

end InfoGeometry.Topology.BostConnesWilsonLoop
