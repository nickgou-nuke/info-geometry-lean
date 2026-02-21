import InfoGeometry.Basic

/-!
# Assumptions.DualConnections

Assumption-backed interface for dual-connection geometry drafts extracted from
the historical `InfoGeometry/New.lean`.
-/

namespace InfoGeometry.Assumptions.DualConnections

variable {Θ α : Type*} [Fintype α]

/-- Draft Fisher metric placeholder. -/
def fisherMetric (p : Θ → InfoGeometry.FinProb α) : Prop := p = p

/-- Draft Amari–Chentsov tensor placeholder. -/
def amariChentsovTensor (p : Θ → InfoGeometry.FinProb α) : Prop := fisherMetric p

/-- Draft α-connection placeholder. -/
def alphaConnection (p : Θ → InfoGeometry.FinProb α) (αc : ℝ) : Prop :=
  fisherMetric p ∧ amariChentsovTensor p ∧ αc = αc

/-- Draft duality characterization placeholder for α-connections. -/
def alpha_duality (p : Θ → InfoGeometry.FinProb α) (αc : ℝ) : Prop :=
  alphaConnection p αc ↔ alphaConnection p (-αc)

/-- Draft Hessian/Fisher identification placeholder. -/
def fisher_metric_eq_hessian_KL (p : Θ → InfoGeometry.FinProb α) : Prop :=
  fisherMetric p → amariChentsovTensor p

end InfoGeometry.Assumptions.DualConnections
