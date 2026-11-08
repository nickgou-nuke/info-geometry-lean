import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace SarsSouriauDilaton

open Real

structure EntropicLeaf (State : Type*) where
  entropy : State → ℝ
  base : State

namespace EntropicLeaf

def same_entropy (L : EntropicLeaf State) (q : State) : Prop :=
  L.entropy q = L.entropy L.base

end EntropicLeaf

structure SouriauHamiltonianFlow (State : Type*) (L : EntropicLeaf State) where
  flow : State → State
  tangent_to_leaf : ∀ q, L.same_entropy q → L.same_entropy (flow q)

theorem hamiltonian_flow_preserves_leaf {State : Type*} {L : EntropicLeaf State}
    (F : SouriauHamiltonianFlow State L) {q : State} (hq : L.same_entropy q) :
    L.same_entropy (F.flow q) := F.tangent_to_leaf q hq

structure OrthogonalDilatonFlow (State : Type*) (L : EntropicLeaf State) where
  flow : State → State
  entropy_production : ∀ q, 0 ≤ L.entropy (flow q) - L.entropy q

theorem dilaton_entropy_production_nonneg {State : Type*} {L : EntropicLeaf State}
    (D : OrthogonalDilatonFlow State L) (q : State) :
    0 ≤ L.entropy (D.flow q) - L.entropy q := D.entropy_production q

def souriauBoltzmannWeight (θ β : ℝ) : ℝ := Real.exp (-(θ * β))

def souriauDensity (θ β Z : ℝ) : ℝ := souriauBoltzmannWeight θ β / Z

theorem partition_rescales_density (θ β Z : ℝ) :
    Z * souriauDensity θ β Z = if Z = 0 then 0 else souriauBoltzmannWeight θ β := by
  unfold souriauDensity
  by_cases h : Z = 0
  · simp [h]
  · field_simp [h]
    simp [h]

theorem boltzmann_weight_positive (θ β : ℝ) : 0 < souriauBoltzmannWeight θ β := by
  unfold souriauBoltzmannWeight
  exact Real.exp_pos _

theorem density_positive_of_partition_positive {θ β Z : ℝ} (hZ : 0 < Z) :
    0 < souriauDensity θ β Z := by
  unfold souriauDensity
  exact div_pos (boltzmann_weight_positive θ β) hZ

def dilaton (lam : ℝ) : ℝ := Real.exp lam

def weylScale (lam : ℝ) : ℝ := Real.exp (2 * lam)

def weylMetricComponent (lam g : ℝ) : ℝ := weylScale lam * g

theorem dilaton_square_is_weylScale (lam : ℝ) : dilaton lam ^ 2 = weylScale lam := by
  unfold dilaton weylScale
  rw [sq]
  rw [← Real.exp_add]
  ring_nf

theorem weylScale_positive (lam : ℝ) : 0 < weylScale lam := by
  unfold weylScale
  exact Real.exp_pos _

structure MetriplecticLeafSystem (Obs : Type*) where
  poisson : Obs → Obs → ℝ
  metric : Obs → Obs → ℝ
  H : Obs
  S : Obs
  entropy_poisson_degenerate : ∀ A, poisson S A = 0
  metric_entropy_nonneg : 0 ≤ metric S S
  energy_metric_degenerate : ∀ A, metric H A = 0

theorem unitary_flow_entropy_degenerate {Obs : Type*} (M : MetriplecticLeafSystem Obs) (A : Obs) :
    M.poisson M.S A = 0 := M.entropy_poisson_degenerate A

theorem orthogonal_metric_entropy_nonneg {Obs : Type*} (M : MetriplecticLeafSystem Obs) :
    0 ≤ M.metric M.S M.S := M.metric_entropy_nonneg

theorem metric_flow_energy_degenerate {Obs : Type*} (M : MetriplecticLeafSystem Obs) (A : Obs) :
    M.metric M.H A = 0 := M.energy_metric_degenerate A

inductive SouriauDilatonConcept where
  | Souriau_Lie_Group_Thermodynamics
  | Sars_Weyl_Colimit
  | Entropic_Leaflet
  | Dilaton_Weyl_Gauge_Vector
  | Partition_Function_Normalization
  | Orthogonal_Entropy_Transport
  deriving DecidableEq, Repr

inductive SouriauDilatonEdge where
  | has_leaflet
  | tangent_reversible_flow
  | parameterizes_scale_orthogonal_to_leaves
  | normalizes_by_partition_function
  | generates_orthogonal_entropy_transport
  deriving DecidableEq, Repr

def edgeHolds : SouriauDilatonConcept → SouriauDilatonEdge → SouriauDilatonConcept → Bool
  | SouriauDilatonConcept.Souriau_Lie_Group_Thermodynamics, SouriauDilatonEdge.has_leaflet, SouriauDilatonConcept.Entropic_Leaflet => true
  | SouriauDilatonConcept.Entropic_Leaflet, SouriauDilatonEdge.tangent_reversible_flow, SouriauDilatonConcept.Sars_Weyl_Colimit => true
  | SouriauDilatonConcept.Sars_Weyl_Colimit, SouriauDilatonEdge.parameterizes_scale_orthogonal_to_leaves, SouriauDilatonConcept.Souriau_Lie_Group_Thermodynamics => true
  | SouriauDilatonConcept.Partition_Function_Normalization, SouriauDilatonEdge.normalizes_by_partition_function, SouriauDilatonConcept.Dilaton_Weyl_Gauge_Vector => true
  | SouriauDilatonConcept.Dilaton_Weyl_Gauge_Vector, SouriauDilatonEdge.generates_orthogonal_entropy_transport, SouriauDilatonConcept.Orthogonal_Entropy_Transport => true
  | _, _, _ => false

theorem souriau_dilaton_graph_kernel :
    edgeHolds SouriauDilatonConcept.Souriau_Lie_Group_Thermodynamics SouriauDilatonEdge.has_leaflet SouriauDilatonConcept.Entropic_Leaflet = true ∧
    edgeHolds SouriauDilatonConcept.Entropic_Leaflet SouriauDilatonEdge.tangent_reversible_flow SouriauDilatonConcept.Sars_Weyl_Colimit = true ∧
    edgeHolds SouriauDilatonConcept.Sars_Weyl_Colimit SouriauDilatonEdge.parameterizes_scale_orthogonal_to_leaves SouriauDilatonConcept.Souriau_Lie_Group_Thermodynamics = true ∧
    edgeHolds SouriauDilatonConcept.Partition_Function_Normalization SouriauDilatonEdge.normalizes_by_partition_function SouriauDilatonConcept.Dilaton_Weyl_Gauge_Vector = true ∧
    edgeHolds SouriauDilatonConcept.Dilaton_Weyl_Gauge_Vector SouriauDilatonEdge.generates_orthogonal_entropy_transport SouriauDilatonConcept.Orthogonal_Entropy_Transport = true := by
  decide

theorem souriau_dilaton_kernel :
    (∀ θ β : ℝ, 0 < souriauBoltzmannWeight θ β) ∧
    (∀ θ β Z : ℝ, Z * souriauDensity θ β Z = if Z = 0 then 0 else souriauBoltzmannWeight θ β) ∧
    (∀ lam : ℝ, dilaton lam ^ 2 = weylScale lam) ∧
    (∀ lam : ℝ, 0 < weylScale lam) ∧
    edgeHolds SouriauDilatonConcept.Sars_Weyl_Colimit SouriauDilatonEdge.parameterizes_scale_orthogonal_to_leaves SouriauDilatonConcept.Souriau_Lie_Group_Thermodynamics = true ∧
    edgeHolds SouriauDilatonConcept.Dilaton_Weyl_Gauge_Vector SouriauDilatonEdge.generates_orthogonal_entropy_transport SouriauDilatonConcept.Orthogonal_Entropy_Transport = true := by
  exact ⟨boltzmann_weight_positive, partition_rescales_density, dilaton_square_is_weylScale,
    weylScale_positive, rfl, rfl⟩

end SarsSouriauDilaton

end noncomputable section
