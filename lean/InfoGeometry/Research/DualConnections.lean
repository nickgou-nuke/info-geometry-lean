import InfoGeometry.Assumptions.DualConnections
import InfoGeometry.Information.MultiLogPotential

/-!
# Research.DualConnections

Domain module for dual-connection geometry draft APIs extracted from
historical `InfoGeometry/New.lean`.

Import boundary:
- explicit scaffold interface from `InfoGeometry.Assumptions.DualConnections`
- constructive information-geometry context from `InfoGeometry.Information.MultiLogPotential`

This module is intentionally noncanonical and kept outside `InfoGeometry.Library`.
-/

namespace InfoGeometry.Research.DualConnections

variable {Θ α : Type*} [Fintype α]

@[deprecated InfoGeometry.Assumptions.DualConnections.fisherMetric (since := "2026-02-25")]
abbrev fisherMetric (p : Θ → InfoGeometry.FinProb α) : Prop :=
  InfoGeometry.Assumptions.DualConnections.fisherMetric p

@[deprecated InfoGeometry.Assumptions.DualConnections.amariChentsovTensor (since := "2026-02-25")]
abbrev amariChentsovTensor (p : Θ → InfoGeometry.FinProb α) : Prop :=
  InfoGeometry.Assumptions.DualConnections.amariChentsovTensor p

@[deprecated InfoGeometry.Assumptions.DualConnections.alphaConnection (since := "2026-02-25")]
abbrev alphaConnection (p : Θ → InfoGeometry.FinProb α) (αc : ℝ) : Prop :=
  InfoGeometry.Assumptions.DualConnections.alphaConnection p αc

@[deprecated InfoGeometry.Assumptions.DualConnections.alpha_duality (since := "2026-02-25")]
theorem alpha_duality (p : Θ → InfoGeometry.FinProb α) (αc : ℝ) :
    InfoGeometry.Assumptions.DualConnections.alphaConnection p αc ↔
      InfoGeometry.Assumptions.DualConnections.alphaConnection p (-αc) :=
  InfoGeometry.Assumptions.DualConnections.alpha_duality p αc

@[deprecated InfoGeometry.Assumptions.DualConnections.fisher_metric_eq_hessian_KL (since := "2026-02-25")]
theorem fisher_metric_eq_hessian_KL (p : Θ → InfoGeometry.FinProb α) :
    InfoGeometry.Assumptions.DualConnections.fisherMetric p →
      InfoGeometry.Assumptions.DualConnections.amariChentsovTensor p :=
  InfoGeometry.Assumptions.DualConnections.fisher_metric_eq_hessian_KL p

end InfoGeometry.Research.DualConnections
