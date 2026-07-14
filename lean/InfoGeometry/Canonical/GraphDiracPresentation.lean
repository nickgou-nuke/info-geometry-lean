import InfoGeometry.Canonical.QuantumPresentation
import InfoGeometry.Meta.Architecture
import Mathlib.Data.Real.Basic

/-!
# InfoGeometry.Canonical.GraphDiracPresentation

Translator surface for graph-metric / discrete-Dirac presentations.

This file is intentionally interface-level. It does not claim a full discrete
spectral triple implementation; it packages the data needed to embed a
graph-defined Dirac lane into `QuantumPresentation`.
-/

namespace GraphDiracPresentation

open InfoGeometry.Canonical.QuantumPresentation

/--
Graph-metric Dirac presentation package.

- `vertexOf` maps a state to graph position.
- `distance` is the graph-defined metric readout source.
- `diracGenerator` is the discrete transport/generator lane.
- `referenceVertex` anchors scalar metric readout.
-/
@[rep_depth operator]
structure GraphMetricDirac where
  Vertex : Type
  State : Type
  Observable : Type
  act : Observable → State → State
  support : State → Prop
  diracGenerator : State → State
  vertexOf : State → Vertex
  distance : Vertex → Vertex → Real
  phaseReadout : State → Real
  referenceVertex : Vertex
  distance_nonneg : ∀ x y : Vertex, 0 ≤ distance x y

namespace GraphMetricDirac

/-- Scalar metric readout induced by distance-to-reference vertex. -/
@[rep_depth operator]
def metricReadout (G : GraphMetricDirac) (ψ : G.State) : Real :=
  G.distance (G.vertexOf ψ) G.referenceVertex

/-- Graph metric readout is nonnegative under the package contract. -/
@[rep_depth operator]
theorem metricReadout_nonneg (G : GraphMetricDirac) (ψ : G.State) :
    0 ≤ G.metricReadout ψ := by
  unfold metricReadout
  exact G.distance_nonneg (G.vertexOf ψ) G.referenceVertex

/--
Translator map to the generic representation interface.

This is the canonical way to plug graph-Dirac lanes into intertwiners.
-/
@[rep_depth operator]
def toQuantumPresentation (G : GraphMetricDirac) : Presentation where
  Scalar := Real
  State := G.State
  Observable := G.Observable
  act := G.act
  support := G.support
  generator := G.diracGenerator
  metricReadout := G.metricReadout
  phaseReadout := G.phaseReadout

@[rep_depth operator]
theorem toQuantumPresentation_generator_eq_dirac
    (G : GraphMetricDirac) (ψ : G.State) :
    (G.toQuantumPresentation.generator ψ) = G.diracGenerator ψ := by
  rfl

/-- Tagged presentation witness for this graph-Dirac lane. -/
@[rep_depth operator]
def taggedPresentation (G : GraphMetricDirac) : TaggedPresentation where
  lane := PresentationLane.graphDirac
  data := G.toQuantumPresentation

end GraphMetricDirac

end GraphDiracPresentation
