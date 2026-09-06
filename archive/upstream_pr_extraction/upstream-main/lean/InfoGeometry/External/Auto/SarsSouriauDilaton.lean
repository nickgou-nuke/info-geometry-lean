import Mathlib.Tactic

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

end SarsSouriauDilaton

end noncomputable section
