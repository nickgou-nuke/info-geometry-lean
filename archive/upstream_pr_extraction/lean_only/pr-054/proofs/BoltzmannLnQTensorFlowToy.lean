import proofs.PenroseChiralNuclearTrainsumToy

namespace BoltzmannLnQTensorFlowToy

def nodeCount : ℕ := 6

def stateCount : ℕ := 2 ^ nodeCount

def completeEdgeCount : ℕ := nodeCount * (nodeCount - 1) / 2

def flowStepCount : ℕ := 12

def nodeLabels : List ℕ := [0, 1, 2, 3, 4, 5]

def completeEdges6 : List (ℕ × ℕ) :=
  [(0,1), (0,2), (0,3), (0,4), (0,5),
   (1,2), (1,3), (1,4), (1,5),
   (2,3), (2,4), (2,5),
   (3,4), (3,5),
   (4,5)]

def qTableEntryCount : ℕ := nodeCount * 2

@[simp] theorem node_count_eq : nodeCount = 6 := rfl

@[simp] theorem state_count_eq : stateCount = 64 := rfl

@[simp] theorem complete_edge_count_eq : completeEdgeCount = 15 := rfl

@[simp] theorem flow_step_count_eq : flowStepCount = 12 := rfl

@[simp] theorem node_labels_length : nodeLabels.length = 6 := rfl

@[simp] theorem complete_edges6_length : completeEdges6.length = 15 := rfl

@[simp] theorem q_table_entry_count_eq : qTableEntryCount = 12 := rfl

inductive BoltzmannLnQTerm where
  | nodeLnQ
  | completeGraphPairSpin
  deriving DecidableEq, Repr

inductive LnQFlowIngredient where
  | damping
  | feedbackExpectedLnQ
  | targetLnQObservable
  deriving DecidableEq, Repr

def energyTermFamilies : List BoltzmannLnQTerm := [.nodeLnQ, .completeGraphPairSpin]

def flowIngredients : List LnQFlowIngredient :=
  [.damping, .feedbackExpectedLnQ, .targetLnQObservable]

@[simp] theorem energy_term_families_length : energyTermFamilies.length = 2 := rfl

@[simp] theorem flow_ingredients_length : flowIngredients.length = 3 := rfl

@[simp] theorem quanticsFullDimension_two_six :
    QuaternionQuanticsBackendDigest.quanticsFullDimension 2 6 = 64 := by
  norm_num [QuaternionQuanticsBackendDigest.quanticsFullDimension]

end BoltzmannLnQTensorFlowToy
