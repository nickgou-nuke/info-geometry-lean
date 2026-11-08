import Mathlib.Topology.Algebra.Module.FiniteDimension
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Algebra.Group.Basic
import InfoGeometry.Canonical.AffinePin55Cover
import InfoGeometry.Topology.Pin55TopologicalGroups
import InfoGeometry.Topology.Pin55ContinuityLemmas
import InfoGeometry.Topology.AffinePin55Topology

/-!
# The topological affine split-Pin group

The algebraic carrier `AffinePin55Native` is the native Mathlib semidirect
product.  Its topology is transported from the product of the translation and
split-Pin factors.  The action is proved jointly continuous from the actual
Clifford conjugation formula; it is not declared continuous by a typeclass
placeholder.
-/

noncomputable section

namespace InfoGeometry.Topology.AffinePin55TopologicalGroup

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Topology.Pin55TopologicalGroups
open InfoGeometry.Canonical.AffinePin55Cover

abbrev AffinePin55 := AffinePin55Native

theorem realSplitPinAction_continuous :
    Continuous (fun p : realSplitPin55 × Multiplicative V55 =>
      realSplitPinAction p.1 p.2) := by
  change Continuous (fun p : realSplitPin55 × V55 =>
    realSplitPinTwistedAction p.1 p.2)
  exact InfoGeometry.Topology.AffinePin55Topology.continuous_realSplitPin_action

instance affinePin55_topologicalSpace : TopologicalSpace AffinePin55 :=
  InfoGeometry.Topology.AffinePin55Topology.affinePin55Topology

instance instIsTopologicalGroupAffinePin55 : IsTopologicalGroup AffinePin55 :=
  InfoGeometry.Topology.AffinePin55Topology.affinePin55_isTopologicalGroup

end InfoGeometry.Topology.AffinePin55TopologicalGroup
