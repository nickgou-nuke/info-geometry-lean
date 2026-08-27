import Mathlib.Order.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Data.Set.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Preorder
import InfoGeometry.Causal.ProofDAGRepresentation
import InfoGeometry.Canonical.PenrosePosetCategoryFoundation

/-!
# Directed Topological Proof Development and Causal Cones

This module formalizes the Topological Progress Principle in native Lean 4 on top
of the repository's existing `ProofDAG` and categorical poset foundations.

## Two-Level Architecture
1. **Dependency Poset Layer (`D_proof`)**:
   - Declarations are nodes ordered by the prerequisite relation: `G.le a b` ("`a` is a prerequisite of `b`").
   - The remaining causal corridor `dependencyCorridor G S T = forwardCone G S ∩ backwardCone G T`
     **shrinks** as development moves from `S` to a closer prerequisite `S'`:
     `S ≤ S' ≤ T ⟹ dependencyCorridor G S' T ⊆ dependencyCorridor G S T`.

2. **Verified State Layer (`D_state`)**:
   - Verified knowledge states `VerifiedState G` are downward-closed subsets of `α`
     (`G.le a b ∧ b ∈ S ⟹ a ∈ S`).
   - The verified target-directed ideal `verifiedToward G V T = V.carrier ∩ backwardCone G T`
     **grows** as verified content is added:
     `V ≤ V' ⟹ verifiedToward G V T ⊆ verifiedToward G V' T`.
   - Independent verification branches (e.g. CAS outputs, subagent proofs) merge via the
     join of order ideals `joinVerifiedState G V₁ V₂`, with proved universal join properties.

## Epistemic Separation
- `forwardCone G S` describes dependency influence (reachability), **not** proof truth.
- `IsClosed G V T` is defined strictly as `T ∈ V.carrier` (actual kernel verification).
-/

namespace InfoGeometry.Causal.TopologicalProofDevelopment

open Set
open CategoryTheory
open InfoGeometry.Causal.ProofDAGRepresentation
open InfoGeometry.Canonical.PenrosePosetCategoryFoundation

variable {α : Type*}

section TheoremDependencyPosetLayer

/-- Any `ProofDAG α` provides an explicit Mathlib `PartialOrder α` (for local instance use). -/
def proofDAGPartialOrder (G : ProofDAG α) : PartialOrder α where
  le := G.le
  le_refl := G.refl
  le_trans := fun _ _ _ hab hbc => G.trans hab hbc
  le_antisymm := fun _ _ hab hba => G.antisymm hab hba

/-- Type synonym wrapping `α` to carry the poset/category structure of `G` locally. -/
def AsPoset (_ : ProofDAG α) := α

instance (G : ProofDAG α) : PartialOrder (AsPoset G) :=
  proofDAGPartialOrder G

/-- The remaining causal corridor (dependency interval) between current node `S` and target `T`. -/
def dependencyCorridor (G : ProofDAG α) (S T : α) : Set α :=
  forwardCone G S ∩ backwardCone G T

theorem source_mem_dependencyCorridor
    (G : ProofDAG α) {S T : α} (hST : G.le S T) :
    S ∈ dependencyCorridor G S T :=
  ⟨G.refl S, hST⟩

theorem target_mem_dependencyCorridor
    (G : ProofDAG α) {S T : α} (hST : G.le S T) :
    T ∈ dependencyCorridor G S T :=
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

/-- The remaining dependency corridor shrinks when advancing along prerequisites. -/
theorem dependencyCorridor_antitone_left
    (G : ProofDAG α) {S S' T : α} (hSS' : G.le S S') :
    dependencyCorridor G S' T ⊆ dependencyCorridor G S T := by
  rintro x ⟨hxForward, hxBack⟩
  exact ⟨forwardCone_antitone G hSS' hxForward, hxBack⟩

/-- Target reachability criterion: target `T` is reachable from `S` in the dependency DAG if `S ≤ T`. -/
def IsReachableFrom (G : ProofDAG α) (S T : α) : Prop :=
  G.le S T

/-- Refinement factorization: if `S ≤ T`, any intermediate prerequisite `Q` with `S ≤ Q ≤ T`
    lies in the remaining dependency corridor. -/
theorem refinement_factorization
    (G : ProofDAG α) (S T Q : α)
    (hSQ : G.le S Q) (hQT : G.le Q T) :
    Q ∈ dependencyCorridor G S T :=
  ⟨hSQ, hQT⟩

/-- No-teleportation law: acyclicity prevents a target from being in the backward cone of its
    strict prerequisites without identity. -/
theorem no_cyclic_shortcut
    (G : ProofDAG α) (A B : α)
    (hAB : G.le A B) (hBA : G.le B A) :
    A = B :=
  G.antisymm hAB hBA

end TheoremDependencyPosetLayer

section VerifiedStateLayer

/-- A verified knowledge state is a downward-closed set of declarations (order ideal):
    if `b` is verified and `a` is a prerequisite of `b`, then `a` is verified. -/
structure VerifiedState (G : ProofDAG α) where
  carrier : Set α
  dependency_closed : ∀ {a b : α}, G.le a b → b ∈ carrier → a ∈ carrier

/-- Target closure criterion: target `T` is verified in state `S` if `T ∈ S.carrier`. -/
def IsClosed (G : ProofDAG α) (S : VerifiedState G) (T : α) : Prop :=
  T ∈ S.carrier

/-- Bridge connecting `VerifiedState G` to Mathlib's native `LowerSet`. -/
def toLowerSet (G : ProofDAG α) (V : VerifiedState G) : LowerSet (AsPoset G) where
  carrier := V.carrier
  lower' := fun _ _ hab hb => V.dependency_closed hab hb

/-- The target-directed verified frontier: verified declarations that lie in the
    backward prerequisite cone of target `T`. -/
def verifiedToward (G : ProofDAG α) (S : VerifiedState G) (T : α) : Set α :=
  S.carrier ∩ backwardCone G T

/-- Monotonicity of target-directed verified progress. -/
theorem verifiedToward_mono (G : ProofDAG α) {S₁ S₂ : VerifiedState G} (T : α)
    (h : S₁.carrier ⊆ S₂.carrier) :
    verifiedToward G S₁ T ⊆ verifiedToward G S₂ T := by
  rintro x ⟨hxS, hxT⟩
  exact ⟨h hxS, hxT⟩

/-- Strict target progress theorem: adding an unverified prerequisite `Q ∈ ↓T \ S` strictly expands
    the target-directed verified frontier towards target `T`. -/
theorem strict_target_progress
    (G : ProofDAG α) (S : VerifiedState G) (T Q : α)
    (hQ_prereq : G.le Q T)
    (hQ_unverified : Q ∉ S.carrier)
    (S' : VerifiedState G)
    (hS_sub : S.carrier ⊆ S'.carrier)
    (hQ_in_S' : Q ∈ S'.carrier) :
    verifiedToward G S T ⊂ verifiedToward G S' T := by
  apply ssubset_of_subset_of_ne
  · exact verifiedToward_mono G T hS_sub
  · intro hEq
    have hQnew : Q ∈ verifiedToward G S' T := ⟨hQ_in_S', hQ_prereq⟩
    have hQold : Q ∈ verifiedToward G S T := by rw [hEq]; exact hQnew
    exact hQ_unverified hQold.1

/-- Merging two verified states (e.g. from independent subagents or CAS pipelines)
    produces a combined verified state (the join of order ideals). -/
def joinVerifiedState (G : ProofDAG α) (S₁ S₂ : VerifiedState G) : VerifiedState G where
  carrier := S₁.carrier ∪ S₂.carrier
  dependency_closed := by
    rintro a b hab (hb₁ | hb₂)
    · exact Or.inl (S₁.dependency_closed hab hb₁)
    · exact Or.inr (S₂.dependency_closed hab hb₂)

@[simp] theorem joinVerifiedState_carrier (G : ProofDAG α) (S₁ S₂ : VerifiedState G) :
    (joinVerifiedState G S₁ S₂).carrier = S₁.carrier ∪ S₂.carrier :=
  rfl

/-- Left inclusion into the join state. -/
theorem le_joinVerifiedState_left (G : ProofDAG α) (S₁ S₂ : VerifiedState G) :
    S₁.carrier ⊆ (joinVerifiedState G S₁ S₂).carrier :=
  subset_union_left

/-- Right inclusion into the join state. -/
theorem le_joinVerifiedState_right (G : ProofDAG α) (S₁ S₂ : VerifiedState G) :
    S₂.carrier ⊆ (joinVerifiedState G S₁ S₂).carrier :=
  subset_union_right

/-- Universal property of the join state: any state containing both branches contains their join. -/
theorem joinVerifiedState_least
    (G : ProofDAG α) (S₁ S₂ S : VerifiedState G)
    (h₁ : S₁.carrier ⊆ S.carrier)
    (h₂ : S₂.carrier ⊆ S.carrier) :
    (joinVerifiedState G S₁ S₂).carrier ⊆ S.carrier := by
  rintro x (hx₁ | hx₂)
  · exact h₁ hx₁
  · exact h₂ hx₂

/-! ### Divide-and-conquer assembly of finitely many verified branches

The binary join is the local merge operation.  Folding it over a list gives
the proof-sized divide-and-conquer assembly used by finite certificate
packets; no theorem is accepted merely because it occurs in the list.
-/

def emptyVerifiedState (G : ProofDAG α) : VerifiedState G where
  carrier := ∅
  dependency_closed := by
    intro a b _ hb
    simp at hb

def foldVerifiedStates (G : ProofDAG α) : List (VerifiedState G) → VerifiedState G
  | [] => emptyVerifiedState G
  | S :: Ss => joinVerifiedState G S (foldVerifiedStates G Ss)

theorem foldVerifiedStates_head_subset
    (G : ProofDAG α) (S : VerifiedState G) (Ss : List (VerifiedState G)) :
    S.carrier ⊆ (foldVerifiedStates G (S :: Ss)).carrier := by
  exact le_joinVerifiedState_left G S (foldVerifiedStates G Ss)

theorem foldVerifiedStates_tail_subset
    (G : ProofDAG α) (S : VerifiedState G) (Ss : List (VerifiedState G)) :
    (foldVerifiedStates G Ss).carrier ⊆ (foldVerifiedStates G (S :: Ss)).carrier := by
  exact le_joinVerifiedState_right G S (foldVerifiedStates G Ss)

theorem foldVerifiedStates_mem
    (G : ProofDAG α) {Ss : List (VerifiedState G)}
    (S : VerifiedState G) (hS : S ∈ Ss) :
    S.carrier ⊆ (foldVerifiedStates G Ss).carrier := by
  induction Ss with
  | nil => simp at hS
  | cons T Ts ih =>
      simp only [List.mem_cons] at hS
      cases hS with
      | inl hST =>
          subst T
          exact foldVerifiedStates_head_subset G S Ts
      | inr hS =>
          exact (ih hS).trans (foldVerifiedStates_tail_subset G T Ts)

theorem mem_foldVerifiedStates_iff
    (G : ProofDAG α) {Ss : List (VerifiedState G)} (x : α) :
    x ∈ (foldVerifiedStates G Ss).carrier ↔
      ∃ S ∈ Ss, x ∈ S.carrier := by
  induction Ss with
  | nil => simp [foldVerifiedStates, emptyVerifiedState]
  | cons S Ss ih =>
      constructor
      · intro hx
        change x ∈ S.carrier ∪ (foldVerifiedStates G Ss).carrier at hx
        rcases hx with hx | hx
        · exact ⟨S, List.mem_cons_self, hx⟩
        · obtain ⟨T, hT, hxT⟩ := ih.mp hx
          exact ⟨T, List.mem_cons_of_mem S hT, hxT⟩
      · rintro ⟨T, hT, hxT⟩
        change x ∈ S.carrier ∪ (foldVerifiedStates G Ss).carrier
        simp only [List.mem_cons] at hT
        cases hT with
        | inl hTS =>
            subst T
            exact Or.inl hxT
        | inr hT =>
            exact Or.inr (ih.mpr ⟨T, hT, hxT⟩)

theorem mem_foldVerifiedStates_of_mem_all
    (G : ProofDAG α) {Ss : List (VerifiedState G)} (x : α)
    (hne : Ss ≠ [])
    (hall : ∀ S ∈ Ss, x ∈ S.carrier) :
    x ∈ (foldVerifiedStates G Ss).carrier := by
  obtain ⟨S, Ss, rfl⟩ := List.exists_cons_of_ne_nil hne
  apply (mem_foldVerifiedStates_iff G x).2
  exact ⟨S, List.mem_cons_self, hall S List.mem_cons_self⟩

theorem foldVerifiedStates_append
    (G : ProofDAG α) (Ss Ts : List (VerifiedState G)) :
    (foldVerifiedStates G (Ss ++ Ts)).carrier =
      (foldVerifiedStates G Ss).carrier ∪ (foldVerifiedStates G Ts).carrier := by
  induction Ss with
  | nil =>
      simp [foldVerifiedStates, emptyVerifiedState]
  | cons S Ss ih =>
      ext x
      simp [foldVerifiedStates, joinVerifiedState, ih, union_assoc]

end VerifiedStateLayer

section CategoricalDistributedPackaging

variable {J : Type*} {P : Type*} [Preorder P]

/-- Packaging theorem: a family of local certified proof leaves indexed by `J` that all support
    target `T` (`∀ j, leaf j ≤ T`) packages as a categorical cocone over the discrete diagram. -/
def distributedProofCocone
    (leaf : J → P) (T : P)
    (h_leaves : ∀ j, leaf j ≤ T) :
    Limits.Cocone (Discrete.functor leaf) :=
  preorderCoconeOfUpperBound (Discrete.functor leaf) (by
    rintro p ⟨j, rfl⟩
    exact h_leaves j.as)

/-- Packaging theorem: if target `T` is proved to be the least upper bound of all certified
    leaves (`IsLUB (range leaf) T`), it packages as a categorical colimit cocone over the proof leaves. -/
def distributedProofColimitCocone
    (leaf : J → P) (T : P)
    (h_lub : IsLUB (range leaf) T) :
    Limits.ColimitCocone (Discrete.functor leaf) :=
  preorderColimitCoconeOfIsLUB (Discrete.functor leaf) (by
    have h_range : range (Discrete.functor leaf).obj = range leaf := by
      ext x
      simp only [mem_range]
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨j.as, rfl⟩
      · rintro ⟨j, rfl⟩
        exact ⟨Discrete.mk j, rfl⟩
    rw [h_range]
    exact h_lub)

end CategoricalDistributedPackaging

section GeneralProofDAGCategoryFunctor

/-- Any `ProofDAG α` embeds as a preorder category diagram over any target category `C`. -/
def proofDAGFunctor (G : ProofDAG α) {C : Type*} [Category C] (F : AsPoset G → C)
    (hF : ∀ {a b : AsPoset G}, G.le a b → (F a ⟶ F b))
    (hF_id : ∀ (a : AsPoset G), hF (G.refl a) = 𝟙 (F a))
    (hF_comp : ∀ {a b c : AsPoset G} (hab : G.le a b) (hbc : G.le b c),
      hF (G.trans hab hbc) = hF hab ≫ hF hbc) :
    AsPoset G ⥤ C where
  obj := F
  map := fun f => hF (leOfHom f)
  map_id := fun a => hF_id a
  map_comp := fun f g => hF_comp (leOfHom f) (leOfHom g)

end GeneralProofDAGCategoryFunctor

end InfoGeometry.Causal.TopologicalProofDevelopment
