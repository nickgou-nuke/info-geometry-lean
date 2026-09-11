import InfoGeometry.Inference.PoissonUnbalancedSinkhorn
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.ContinuousMap.Basic

/-!
# Topological finite objective for unbalanced Poisson transport

The transport property and its row/column data are finite.  This file adds
the native topological readout in the three scalar penalty parameters.  It
does not assert convergence of Sinkhorn iteration or a continuum transport
theorem.
-/

namespace InfoGeometry.Inference

open scoped BigOperators

variable {Row Col : Type*}
  [Fintype Row] [Nonempty Row] [Fintype Col] [Nonempty Col]

noncomputable def fullUnbalancedTransportObjectiveContinuousMap
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col))
    (cost reference : Row → Col → ℝ) :
    C(((ℝ × ℝ) × ℝ), ℝ) :=
  ContinuousMap.mk
    (fun p => fullUnbalancedTransportObjective T cost reference p.1.1 p.1.2 p.2)
    (by
      unfold fullUnbalancedTransportObjective
      unfold unbalancedTransportObjective
      fun_prop)

@[simp] theorem fullUnbalancedTransportObjectiveContinuousMap_apply
    (T : UnbalancedTransportCertificate (Row := Row) (Col := Col))
    (cost reference : Row → Col → ℝ)
    (p : (ℝ × ℝ) × ℝ) :
    fullUnbalancedTransportObjectiveContinuousMap T cost reference p =
      fullUnbalancedTransportObjective T cost reference p.1.1 p.1.2 p.2 :=
  rfl

instance : TopologicalSpace (UnbalancedTransportCertificate (Row := Row) (Col := Col)) :=
  inferInstanceAs (TopologicalSpace {p : (Row → Col → ℝ) × (Row → ℝ) × (Col → ℝ) // _})

end InfoGeometry.Inference
