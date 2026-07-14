import InfoGeometry.Canonical.MixtureOfExperts
import InfoGeometry.Meta.Architecture

open scoped BigOperators

namespace CliffordCantorGraphRouting

open InfoGeometry.Canonical.MoE

section Geometry

variable {X Node F : Type*}
variable {n : Nat} [Nonempty (Fin n)]

/--
Typed router geometry carrying three cost lanes:
- graph/topology distance,
- Clifford-feature squared distance,
- Cantor/fractal sparse addressing cost.
-/
@[rep_depth operator]
structure RouterGeometry where
  stateNode : X → Node
  expertNode : ExpertIdx n → Node
  graphDist : Node → Node → ℝ
  graphDist_nonneg : ∀ u v : Node, 0 ≤ graphDist u v
  cliffordFeature : X → F
  expertCenter : ExpertIdx n → F
  cliffordSqDist : F → F → ℝ
  cliffordSqDist_nonneg : ∀ a b : F, 0 ≤ cliffordSqDist a b
  cantorCost : X → ExpertIdx n → ℝ
  cantorCost_nonneg : ∀ x : X, ∀ e : ExpertIdx n, 0 ≤ cantorCost x e
  bias : ExpertIdx n → ℝ

namespace RouterGeometry

@[rep_depth operator]
def graphCost (R : RouterGeometry (X := X) (Node := Node) (F := F) (n := n))
    (x : X) (e : ExpertIdx n) : ℝ :=
  R.graphDist (R.stateNode x) (R.expertNode e)

@[rep_depth operator]
def cliffordCost (R : RouterGeometry (X := X) (Node := Node) (F := F) (n := n))
    (x : X) (e : ExpertIdx n) : ℝ :=
  R.cliffordSqDist (R.cliffordFeature x) (R.expertCenter e)

/-- Weighted multi-lane routing cost (topology + Clifford + Cantor). -/
@[rep_depth operator]
def routingCost (R : RouterGeometry (X := X) (Node := Node) (F := F) (n := n))
    (α β γ : ℝ) (x : X) (e : ExpertIdx n) : ℝ :=
  α * R.graphCost x e + β * R.cliffordCost x e + γ * R.cantorCost x e

/-- Router score used by sparse probabilistic gating. -/
@[rep_depth operator]
def routingScore (R : RouterGeometry (X := X) (Node := Node) (F := F) (n := n))
    (α β γ : ℝ) (x : X) (e : ExpertIdx n) : ℝ :=
  -R.routingCost α β γ x e + R.bias e

omit [Nonempty (Fin n)] in
@[rep_depth transport]
theorem routingCost_nonneg
    (R : RouterGeometry (X := X) (Node := Node) (F := F) (n := n))
    (α β γ : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (x : X) (e : ExpertIdx n) :
    0 ≤ R.routingCost α β γ x e := by
  unfold routingCost graphCost cliffordCost
  exact add_nonneg
    (add_nonneg
      (mul_nonneg hα (R.graphDist_nonneg _ _))
      (mul_nonneg hβ (R.cliffordSqDist_nonneg _ _)))
    (mul_nonneg hγ (R.cantorCost_nonneg _ _))

omit [Nonempty (Fin n)] in
@[rep_depth transport]
theorem routingScore_eq_bias_sub_cost
    (R : RouterGeometry (X := X) (Node := Node) (F := F) (n := n))
    (α β γ : ℝ) (x : X) (e : ExpertIdx n) :
    R.routingScore α β γ x e = R.bias e - R.routingCost α β γ x e := by
  unfold routingScore
  ring

end RouterGeometry

end Geometry

section SoftmaxRouter

variable {X Node F : Type*}
variable {n : Nat} [Nonempty (Fin n)]

open RouterGeometry

/-- Partition function induced by the Clifford/Cantor/graph score. -/
@[rep_depth operator]
noncomputable def routingPartition
    (R : RouterGeometry (X := X) (Node := Node) (F := F) (n := n))
    (α β γ τ : ℝ) (x : X) : ℝ :=
  ∑ e : ExpertIdx n, Real.exp (R.routingScore α β γ x e / τ)

/-- Softmax router weight on the multi-lane score. -/
@[rep_depth operator]
noncomputable def routingSoftmaxWeight
    (R : RouterGeometry (X := X) (Node := Node) (F := F) (n := n))
    (α β γ τ : ℝ) (x : X) (e : ExpertIdx n) : ℝ :=
  Real.exp (R.routingScore α β γ x e / τ) / routingPartition R α β γ τ x

@[rep_depth operator]
lemma routingPartition_pos
    (R : RouterGeometry (X := X) (Node := Node) (F := F) (n := n))
    (α β γ τ : ℝ) (x : X) :
    0 < routingPartition R α β γ τ x := by
  classical
  unfold routingPartition
  apply Finset.sum_pos
  · intro e _
    exact Real.exp_pos _
  · exact Finset.univ_nonempty

@[rep_depth transport]
lemma routingSoftmaxWeight_nonneg
    (R : RouterGeometry (X := X) (Node := Node) (F := F) (n := n))
    (α β γ τ : ℝ) (x : X) (e : ExpertIdx n) :
    0 ≤ routingSoftmaxWeight R α β γ τ x e := by
  unfold routingSoftmaxWeight
  exact div_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt (routingPartition_pos R α β γ τ x))

@[rep_depth transport]
lemma routingSoftmaxWeight_sum_one
    (R : RouterGeometry (X := X) (Node := Node) (F := F) (n := n))
    (α β γ τ : ℝ) (x : X) :
    ∑ e : ExpertIdx n, routingSoftmaxWeight R α β γ τ x e = 1 := by
  classical
  unfold routingSoftmaxWeight
  let Z := routingPartition R α β γ τ x
  have hZ : Z ≠ 0 := (routingPartition_pos R α β γ τ x).ne'
  calc
    ∑ e : ExpertIdx n, Real.exp (R.routingScore α β γ x e / τ) / Z
        = ∑ e : ExpertIdx n, Z⁻¹ * Real.exp (R.routingScore α β γ x e / τ) := by
            refine Finset.sum_congr rfl ?_
            intro e _
            rw [div_eq_inv_mul]
    _ = Z⁻¹ * (∑ e : ExpertIdx n, Real.exp (R.routingScore α β γ x e / τ)) := by
          rw [← Finset.mul_sum]
    _ = (∑ e : ExpertIdx n, Real.exp (R.routingScore α β γ x e / τ)) / Z := by
          rw [div_eq_inv_mul]
    _ = Z / Z := rfl
    _ = 1 := div_self hZ

/-- Sparse mask surface for top-k style gating over the score-softmax weights. -/
@[rep_depth operator]
structure SparseMask (n : Nat) where
  active : ExpertIdx n → Bool

/-- All-active mask recovers ordinary softmax routing. -/
@[rep_depth operator]
def allActiveMask (n : Nat) : SparseMask n where
  active := fun _ => true

/-- Masked score-softmax weight. -/
@[rep_depth operator]
noncomputable def maskedRoutingWeight
    (R : RouterGeometry (X := X) (Node := Node) (F := F) (n := n))
    (mask : SparseMask n) (α β γ τ : ℝ) (x : X) (e : ExpertIdx n) : ℝ :=
  if mask.active e then routingSoftmaxWeight R α β γ τ x e else 0

@[rep_depth transport]
lemma maskedRoutingWeight_nonneg
    (R : RouterGeometry (X := X) (Node := Node) (F := F) (n := n))
    (mask : SparseMask n) (α β γ τ : ℝ) (x : X) (e : ExpertIdx n) :
    0 ≤ maskedRoutingWeight R mask α β γ τ x e := by
  unfold maskedRoutingWeight
  split_ifs with hActive
  · exact routingSoftmaxWeight_nonneg R α β γ τ x e
  · simp

omit [Nonempty (Fin n)] in
@[rep_depth transport]
theorem maskedRoutingWeight_allActive_eq_softmax
    (R : RouterGeometry (X := X) (Node := Node) (F := F) (n := n))
    (α β γ τ : ℝ) (x : X) (e : ExpertIdx n) :
    maskedRoutingWeight R (allActiveMask n) α β γ τ x e
      = routingSoftmaxWeight R α β γ τ x e := by
  unfold maskedRoutingWeight allActiveMask
  simp

end SoftmaxRouter

end CliffordCantorGraphRouting
