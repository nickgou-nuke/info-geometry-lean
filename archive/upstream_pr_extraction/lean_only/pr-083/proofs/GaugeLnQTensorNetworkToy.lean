import proofs.Mirror31PSLnQFlowToy

/-!
# Finite gauge ln(Q) tensor-network toy

Lean records exact finite data for a six-node digest:

* `2 ^ 6 = 64` binary states,
* `6 * 5 / 2 = 15` complete-graph edges,
* `choose3 6 = 20` triples,
* `6 * 2 = 12` two-state table entries,
* list lengths for the displayed edge and triple inventories,
* the imported quantics full dimension `quanticsFullDimension 2 6 = 64`.
-/

namespace GaugeLnQTensorNetworkToy

/-- First finite gauge toy node count. -/
def gaugeNodeCount : ℕ := 6

/-- Binary state count. -/
def gaugeStateCount : ℕ := 2 ^ gaugeNodeCount

/-- Complete graph edge count for six nodes. -/
def gaugeEdgeCount : ℕ := gaugeNodeCount * (gaugeNodeCount - 1) / 2

/-- Triangle count `choose(6,3)`. -/
def choose3 (n : ℕ) : ℕ := n * (n - 1) * (n - 2) / 6

def gaugeTriangleCount : ℕ := choose3 gaugeNodeCount

/-- Two-state positive Q table size. -/
def gaugeQTableEntries : ℕ := gaugeNodeCount * 2

/-- Complete graph edges on six nodes. -/
def gaugeEdges6 : List (ℕ × ℕ) :=
  [(0,1), (0,2), (0,3), (0,4), (0,5),
   (1,2), (1,3), (1,4), (1,5),
   (2,3), (2,4), (2,5),
   (3,4), (3,5), (4,5)]

/-- All listed triples on six complete-graph nodes. -/
def gaugeTriangles6 : List (ℕ × ℕ × ℕ) :=
  [(0,1,2), (0,1,3), (0,1,4), (0,1,5),
   (0,2,3), (0,2,4), (0,2,5),
   (0,3,4), (0,3,5), (0,4,5),
   (1,2,3), (1,2,4), (1,2,5),
   (1,3,4), (1,3,5), (1,4,5),
   (2,3,4), (2,3,5), (2,4,5), (3,4,5)]

@[simp] theorem gauge_node_count_eq : gaugeNodeCount = 6 := rfl

@[simp] theorem gauge_state_count_eq : gaugeStateCount = 64 := rfl

@[simp] theorem gauge_edge_count_eq : gaugeEdgeCount = 15 := rfl

@[simp] theorem gauge_triangle_count_eq : gaugeTriangleCount = 20 := rfl

@[simp] theorem gauge_q_table_entries_eq : gaugeQTableEntries = 12 := rfl

@[simp] theorem gauge_edges6_length : gaugeEdges6.length = 15 := rfl

@[simp] theorem gauge_triangles6_length : gaugeTriangles6.length = 20 := rfl

/-- Finite field ingredients in the toy. -/
inductive GaugeIngredient where
  | matterAmplitude
  | positiveLnQNodePotential
  | u1LinkVariable
  | gaugeCovariantEdgeEnergy
  | triangularWilsonLoop
  | boltzmannWeight
  deriving DecidableEq, Repr

/-- Gauge transform ingredients. -/
inductive GaugeTransformRule where
  | nodeMatterPhase
  | edgeLinkConjugation
  | edgeEnergyInvariant
  | wilsonLoopInvariant
  deriving DecidableEq, Repr

/-- Inventory lists. -/
def gaugeIngredients : List GaugeIngredient :=
  [.matterAmplitude, .positiveLnQNodePotential, .u1LinkVariable,
   .gaugeCovariantEdgeEnergy, .triangularWilsonLoop, .boltzmannWeight]

def gaugeTransformRules : List GaugeTransformRule :=
  [.nodeMatterPhase, .edgeLinkConjugation, .edgeEnergyInvariant, .wilsonLoopInvariant]

@[simp] theorem gauge_ingredient_count : gaugeIngredients.length = 6 := rfl

@[simp] theorem gauge_transform_rule_count : gaugeTransformRules.length = 4 := rfl

/-- Capstone: finite gauge-network bookkeeping compiles. -/
theorem gauge_lnq_tensor_network_toy_synthesis :
    gaugeNodeCount = 6 ∧
    gaugeStateCount = 64 ∧
    gaugeEdgeCount = 15 ∧
    gaugeTriangleCount = 20 ∧
    gaugeEdges6.length = 15 ∧
    gaugeTriangles6.length = 20 ∧
    gaugeQTableEntries = 12 ∧
    gaugeIngredients.length = 6 ∧
    gaugeTransformRules.length = 4 ∧
    QuaternionQuanticsBackendDigest.quanticsFullDimension 2 6 = 64 := by
  exact ⟨gauge_node_count_eq,
    gauge_state_count_eq,
    gauge_edge_count_eq,
    gauge_triangle_count_eq,
    gauge_edges6_length,
    gauge_triangles6_length,
    gauge_q_table_entries_eq,
    gauge_ingredient_count,
    gauge_transform_rule_count,
    rfl⟩

end GaugeLnQTensorNetworkToy
