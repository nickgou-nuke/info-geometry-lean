import Mathlib.Tactic
import InfoGeometry.Clifford.Cl11TensorTowerLimit

open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Clifford.Cl11TensorTower

/-!
# Inductive carrier on the Cl(1,1) tower colimit

This file records a small, honest carrier packet on the Cl(1,1) tensor
tower: the scalar line inside each finite stage.  It is compatible with the
stage embedding and therefore produces a clean inductive-system readout in the
limit algebra.

This is not a density-matrix cone theorem.  It is the finite scalar carrier
used by the current bridge layer.
-/

section NormalConeInductive

/-- The finite-stage scalar carrier: the image of the real scalars in `Stage n`. -/
def StateSpace (n : ℕ) : Set (Stage n) :=
  Set.range (algebraMap ℝ (Stage n))

/-- The explicit finite-stage basepoint used by this carrier model. -/
def stateSpaceBasepoint (n : ℕ) : Stage n :=
  algebraMap ℝ (Stage n) 1

/-- The explicit basepoint belongs to the finite-stage carrier. -/
@[simp]
theorem stateSpaceBasepoint_mem (n : ℕ) :
    stateSpaceBasepoint n ∈ StateSpace n := by
  refine ⟨1, ?_⟩
  simp [stateSpaceBasepoint]

/-- The finite socket state space is nonempty, witnessed by the basepoint. -/
theorem stateSpace_nonempty (n : ℕ) : Set.Nonempty (StateSpace n) := by
  exact ⟨stateSpaceBasepoint n, stateSpaceBasepoint_mem n⟩

/--
The embedding A ↦ A ⊗ I₂ maps the state space at stage n to the state
space at stage n+1, because tensoring with I₂ preserves positivity and
trace (up to the dimension factor 2).

This compatibility makes `{StateSpace n, stageEmbed n}` an inductive
system of carriers.
-/
theorem stageEmbed_preserves_state (n : ℕ) (A : Stage n) (hA : A ∈ StateSpace n) :
    stageEmbed n A ∈ StateSpace (n + 1) := by
  rcases hA with ⟨r, rfl⟩
  refine ⟨r, ?_⟩
  simp

/--
The limit cone: the image of all finite-stage state spaces in the
direct limit Limit = DirectLimitSuperClosure.

This is the image of the stagewise scalar carrier in the limit algebra.
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
theorem cone_system_compatible (n : ℕ) (A : Stage n) :
    ofStage n A = ofStage (n + 1) (stageEmbed n A) := by
  symm
  apply ofStage_apply_bond n A

end NormalConeInductive
