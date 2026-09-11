import Mathlib.Order.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Data.Set.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Preorder
import InfoGeometry.Causal.ProofDAGRepresentation
import InfoGeometry.Canonical.PenrosePosetCategoryFoundation

/-!
# Verified Development States and Proof Dependency Topology

This module formalizes the dual-level architecture for formal mathematical development:

1. **`D_proof` (Theorem Dependency Poset)**:
   - Declarations are nodes ordered by the prerequisite relation: `G.le a b` ("`a` is a prerequisite of `b`").
   - The remaining causal corridor `developmentInterval G S T = forwardCone G S ∩ backwardCone G T`
     **shrinks** as development moves from `S` to a closer prerequisite `S'`:
     `S ≤ S' ≤ T ⟹ developmentInterval G S' T ⊆ developmentInterval G S T`.

2. **`D_state` (Theory-State Order Ideals)**:
   - Verified knowledge states `VerifiedState G` are downward-closed subsets of `α`
     (`G.le a b ∧ b ∈ S ⟹ a ∈ S`).
   - The verified target-directed ideal `verifiedTowardsTarget G V T = V.carrier ∩ backwardCone G T`
     **grows** as verified content is added:
     `V ≤ V' ⟹ verifiedTowardsTarget G V T ⊆ verifiedTowardsTarget G V' T`.
   - Independent verification branches (e.g. CAS outputs, subagent proofs) merge via the
     join of order ideals `join V₁ V₂`.
-/

namespace InfoGeometry.Causal.VerifiedDevelopmentState

open Set
open CategoryTheory
open InfoGeometry.Causal.ProofDAGRepresentation
open InfoGeometry.Canonical.PenrosePosetCategoryFoundation

variable {α : Type*}

section TheoremDependencyPoset

/-- Construct an explicit `PartialOrder α` from a chosen `ProofDAG α`. -/
def toPartialOrder (G : ProofDAG α) : PartialOrder α where
  le := G.le
  le_refl := G.refl
  le_trans := fun _ _ _ hab hbc => G.trans hab hbc
  le_antisymm := fun _ _ hab hba => G.antisymm hab hba

/-- Type synonym wrapping `α` to carry the poset structure of `G` locally. -/
def AsPoset (_ : ProofDAG α) := α

instance (G : ProofDAG α) : PartialOrder (AsPoset G) :=
  toPartialOrder G

/-- The remaining causal corridor (development interval) between current node `S` and target `T`. -/
def developmentInterval (G : ProofDAG α) (S T : α) : Set α :=
  forwardCone G S ∩ backwardCone G T

theorem source_mem_developmentInterval
    (G : ProofDAG α) {S T : α} (hST : G.le S T) :
    S ∈ developmentInterval G S T :=
  ⟨G.refl S, hST⟩

theorem target_mem_developmentInterval
    (G : ProofDAG α) {S T : α} (hST : G.le S T) :
    T ∈ developmentInterval G S T :=
  ⟨hST, G.refl T⟩

/-- The forward cone is antitone: advancing to a later prerequisite node shrinks the forward cone. -/
theorem forwardCone_antitone
    (G : ProofDAG α) {S S' : α} (hSS' : G.le S S') :
    forwardCone G S' ⊆ forwardCone G S := by
  intro x hS'x
  exact G.trans hSS' hS'x

/-- The backward cone is monotone: advancing to a later node expands the backward cone. -/
theorem backwardCone_monotone
    (G : ProofDAG α) {T T' : α} (hTT' : G.le T T') :
    backwardCone G T ⊆ backwardCone G T' := by
  intro x hxT
  exact G.trans hxT hTT'

/-- The remaining development interval strictly shrinks when advancing along prerequisites. -/
theorem developmentInterval_antitone_left
    (G : ProofDAG α) {S S' T : α} (hSS' : G.le S S') :
    developmentInterval G S' T ⊆ developmentInterval G S T :=
  inter_subset_inter_left (backwardCone G T) (forwardCone_antitone G hSS')

/-- Target reachability criterion: target `T` is reachable from `S` if `S ≤ T`. -/
def IsReachableFrom (G : ProofDAG α) (S T : α) : Prop :=
  G.le S T

end TheoremDependencyPoset

section VerifiedStateLattice

/-- A verified knowledge state is a downward-closed subset of declarations:
    if `b` is verified and `a` is a prerequisite of `b`, then `a` is verified. -/
structure VerifiedState (G : ProofDAG α) where
  carrier : Set α
  dependency_closed : ∀ {a b : α}, G.le a b → b ∈ carrier → a ∈ carrier

namespace VerifiedState

variable {G : ProofDAG α}

/-- Theory states are partially ordered by subset inclusion of verified content. -/
instance : PartialOrder (VerifiedState G) where
  le := fun S T => S.carrier ⊆ T.carrier
  le_refl := fun _ => subset_rfl
  le_trans := fun _ _ _ hAB hBC => subset_trans hAB hBC
  le_antisymm := fun S T hST hTS => by
    cases S with | mk s hs =>
    cases T with | mk t ht =>
    congr
    exact subset_antisymm hST hTS

/-- Target closure criterion: target `T` is verified in state `V` if `T ∈ V.carrier`. -/
def IsClosed (V : VerifiedState G) (T : α) : Prop :=
  T ∈ V.carrier

/-- Bridge connecting `VerifiedState G` to Mathlib's native `LowerSet`. -/
def toLowerSet (V : VerifiedState G) : LowerSet (AsPoset G) where
  carrier := V.carrier
  lower' := fun _ _ hab hb => V.dependency_closed hab hb

/-- The target-directed verified knowledge: verified declarations that are prerequisites of `T`. -/
def verifiedTowardsTarget (V : VerifiedState G) (T : α) : Set α :=
  V.carrier ∩ backwardCone G T

/-- State progress monotonicity: expanding the verified state enlarges the target knowledge. -/
theorem verifiedTowardsTarget_monotone
    {V₁ V₂ : VerifiedState G} (T : α) (h : V₁ ≤ V₂) :
    verifiedTowardsTarget V₁ T ⊆ verifiedTowardsTarget V₂ T := by
  rintro x ⟨hxS, hxT⟩
  exact ⟨h hxS, hxT⟩

/-- Strict target progress: adding an unverified prerequisite `Q ∈ ↓T \ V` strictly
    expands the verified target-directed ideal. -/
theorem strict_verified_target_progress
    (V : VerifiedState G) (T Q : α)
    (hQ_prereq : G.le Q T)
    (hQ_unverified : Q ∉ V.carrier)
    (V' : VerifiedState G)
    (hV_le : V ≤ V')
    (hQ_in_V' : Q ∈ V'.carrier) :
    verifiedTowardsTarget V T ⊂ verifiedTowardsTarget V' T := by
  apply ssubset_of_subset_of_ne
  · exact verifiedTowardsTarget_monotone T hV_le
  · intro hEq
    have hQnew : Q ∈ verifiedTowardsTarget V' T := ⟨hQ_in_V', hQ_prereq⟩
    have hQold : Q ∈ verifiedTowardsTarget V T := by rw [hEq]; exact hQnew
    exact hQ_unverified hQold.1

/-- Merging two verified states produces the join of order ideals (e.g. combining
    independent subagent branches or CAS certificate pipelines). -/
def join (V₁ V₂ : VerifiedState G) : VerifiedState G where
  carrier := V₁.carrier ∪ V₂.carrier
  dependency_closed := by
    rintro a b hab (hb₁ | hb₂)
    · exact Or.inl (V₁.dependency_closed hab hb₁)
    · exact Or.inr (V₂.dependency_closed hab hb₂)

@[simp] theorem join_carrier (V₁ V₂ : VerifiedState G) :
    (join V₁ V₂).carrier = V₁.carrier ∪ V₂.carrier :=
  rfl

theorem le_join_left (V₁ V₂ : VerifiedState G) : V₁ ≤ join V₁ V₂ :=
  subset_union_left

theorem le_join_right (V₁ V₂ : VerifiedState G) : V₂ ≤ join V₁ V₂ :=
  subset_union_right

theorem join_le (V₁ V₂ V₃ : VerifiedState G) (h₁ : V₁ ≤ V₃) (h₂ : V₂ ≤ V₃) :
    join V₁ V₂ ≤ V₃ :=
  union_subset h₁ h₂

end VerifiedState

end VerifiedStateLattice

end InfoGeometry.Causal.VerifiedDevelopmentState

