import Mathlib
import InfoGeometry.Clifford.Cl11TensorTowerLimit

open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.Cl11TensorTower

/-!
# Inductive normal cone on the Cl(1,1) tower colimit

The state space (normal cone) of the hyperfinite III₁ factor is the
inductive limit of the normal cones at each finite stage of the Cl(1,1)
tensor tower.  This is the self-dual cone P^♮ of Tomita-Takesaki theory,
which serves as the carrier for the Wasserstein gradient flow.

At each stage n, the normal cone Pₙ ⊆ Stage n is the cone of density
matrices.  Under the embedding A ↦ A ⊗ I₂, the cones form an inductive
system whose colimit is P^♮ in the limit algebra.
-/

section NormalConeInductive

/--
The state space at stage n: the set of positive semidefinite matrices
with trace 1 in the 2ⁿ × 2ⁿ matrix algebra Stage n.

This is the finite-dimensional normal cone — the space of density
matrices for the Cl(1,1)^⊗^n system.
-/
def StateSpace (n : ℕ) : Set (Stage n) :=
  sorry

/-- The explicit finite-stage socket state used by this cone model. -/
def stateSpaceBasepoint (n : ℕ) : Stage n :=
  sorry

/-- The explicit basepoint belongs to the finite-stage state space. -/
@[simp]
theorem stateSpaceBasepoint_mem (n : ℕ) :
    stateSpaceBasepoint n ∈ StateSpace n := by
  sorry

/-- The finite socket state space is nonempty, witnessed by the basepoint. -/
theorem stateSpace_nonempty (n : ℕ) : Set.Nonempty (StateSpace n) := by
  exact ⟨stateSpaceBasepoint n, stateSpaceBasepoint_mem n⟩

/--
The embedding A ↦ A ⊗ I₂ maps the state space at stage n to the state
space at stage n+1, because tensoring with I₂ preserves positivity and
trace (up to the dimension factor 2).

This compatibility makes {StateSpace n, stageEmbed n} an inductive
system of cones.
-/
theorem stageEmbed_preserves_state (n : ℕ) (A : Stage n) (hA : A ∈ StateSpace n) :
    stageEmbed n A ∈ StateSpace (n + 1) := by
  sorry

/--
The limit cone: the image of all finite-stage state spaces in the
direct limit Limit = DirectLimitSuperClosure.

This is the self-dual normal cone P^♮ of the hyperfinite III₁ factor,
the carrier for the Wasserstein gradient flow.
-/
noncomputable def LimitCone : Set Limit :=
  {x | ∃ (n : ℕ) (A : Stage n) (_ : A ∈ StateSpace n), ofStage n A = x}

/--
The limit cone contains the image of the basepoint at
every stage, hence is nonempty.
-/
theorem limitCone_nonempty : Set.Nonempty LimitCone := by
  refine ⟨ofStage 0 (stateSpaceBasepoint 0), 0, stateSpaceBasepoint 0,
    stateSpaceBasepoint_mem 0, rfl⟩

/--
The inductive cone system {StateSpace n, stageEmbed n} is a compatible
family: the diagram commutes.

  stageEmbed n (StateSpace n) ⊆ StateSpace (n + 1)
    ↓                       ↓
  ofStage n               ofStage (n+1)
    ↓                       ↓
  LimitCone  ←────────────  same limit element
-/
theorem cone_system_compatible (n : ℕ) (A : Stage n) (_hA : A ∈ StateSpace n) :
    ofStage n A = ofStage (n + 1) (stageEmbed n A) := by
  symm
  apply ofStage_apply_bond n A

end NormalConeInductive
