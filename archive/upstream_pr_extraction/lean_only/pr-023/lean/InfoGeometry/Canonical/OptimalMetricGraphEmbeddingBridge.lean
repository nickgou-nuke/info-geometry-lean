import InfoGeometry.Canonical.CantorTiltSwitchCliffordBridge

/-!
# InfoGeometry.Canonical.OptimalMetricGraphEmbeddingBridge

Finite endpoint metric-compression lane:

`V_n metric -> weighted graph realization -> finite Erlangen/Birkhoff skeleton`.

This is not a Clifford owner.  It is the finite metric/geometric layer attached
to Cantor endpoint and cylinder geometries.
-/

noncomputable section

namespace InfoGeometry.Canonical.OptimalMetricGraphEmbeddingBridge

open InfoGeometry.Canonical.CantorTiltSwitchCliffordBridge

/-- Public finite metric graph embedding bridge alias. -/
abbrev OptimalMetricGraphEmbeddingBridge (n : ℕ) :=
  FiniteMetricGraphEmbeddingBridge n

namespace OptimalMetricGraphEmbeddingBridge

variable {n : ℕ}
variable (B : OptimalMetricGraphEmbeddingBridge n)

/-- Re-export the Cantor address associated to an endpoint. -/
@[rep_depth operator]
def endpointAddress (x : B.Endpoint) : CantorAddress n :=
  B.endpointAddressWitness x

/-- Re-export the endpoint embedding into the weighted graph carrier. -/
@[rep_depth operator]
def graphEmbedding (x : B.Endpoint) : B.WeightedGraph :=
  B.embedding x

/-- The graph realization's supplied optimality/compression proposition. -/
@[rep_depth operator]
def optimality_or_compression_statement : Prop :=
  B.optimalityOrCompressionWitness

end OptimalMetricGraphEmbeddingBridge

end InfoGeometry.Canonical.OptimalMetricGraphEmbeddingBridge
