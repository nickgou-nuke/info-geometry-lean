/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.OperatorContentNetwork.PeerStore
import InfoGeometry.Canonical.OperatorContentNetwork.DAGEvaluation
import InfoGeometry.Canonical.OperatorContentNetwork.DependencyPoset

/-!
# Causal exchange preserves evaluated operators

Dependency-closed peer domains are lower sets of the actual reachability order.
Merging stores preserves declared program support. A closed peer's computed
matrices survive extension, and compatible closed peers agree after either
exchange order even when their absent-key fallback environments differ.
-/

namespace InfoGeometry.Canonical.OperatorContentNetwork.PeerStore

variable {κ α ι n : Type*}

theorem dependencyClosed_iff_closed (deps : κ → Set κ) (S : Store κ α) :
    DependencyClosed deps S ↔ Dependency.Closed deps (domain S) := by
  constructor
  · intro h d k hk hd
    exact h k hk hd
  · intro h k hk d hd
    exact h hk hd

/-- Stored keys form a lower set in the native order of their prerequisites. -/
theorem dependencyClosed_iff_isLowerSet (deps : κ → Set κ) (rank : κ → ℕ)
    (hRank : ∀ ⦃d k : κ⦄, d ∈ deps k → rank d < rank k) (S : Store κ α) :
    DependencyClosed deps S ↔
      @IsLowerSet κ (Dependency.dependencyOrder rank hRank).toLE (domain S) := by
  rw [dependencyClosed_iff_closed, Dependency.closed_iff_isLowerSet deps rank hRank]

/-- Each node uses only its declared internal dependencies and arbitrary external inputs. -/
def ProgramsSupported (S : Store κ (κ ⊕ ι)) (deps : κ → Set κ) : Prop :=
  ∀ k p, S k = some p →
    p ∈ Algebra.adjoin ℝ (FreeAlgebra.ι ℝ '' RankedDAG.dependencyGenerators (deps k))

theorem programsSupported_merge {S T : Store κ (κ ⊕ ι)} {deps : κ → Set κ}
    (hS : ProgramsSupported S deps) (hT : ProgramsSupported T deps) :
    ProgramsSupported (merge S T) deps := by
  intro k p hp
  rcases (merge_eq_some_iff S T k p).1 hp with hs | ⟨_, ht⟩
  · exact hS k p hs
  · exact hT k p ht

section Evaluation

variable [Fintype n] [DecidableEq n]
variable (S T : Store κ (κ ⊕ ι)) (deps : κ → Set κ) (rank : κ → ℕ)
variable (hRank : ∀ k d, d ∈ deps k → rank d < rank k)
variable (hS : ProgramsSupported S deps) (hT : ProgramsSupported T deps)

include hRank hS hT

/-- Left-retained entries of a closed peer have the same computed matrices after exchange. -/
theorem resolve_merge_left (hClosed : DependencyClosed deps S)
    (ν : ι → Operator n) (fallbackS fallbackM : κ → Operator n)
    {k : κ} {p : Program (κ ⊕ ι)} (hk : S k = some p) :
    RankedDAG.resolve S rank ν fallbackS k =
      RankedDAG.resolve (merge S T) rank ν fallbackM k := by
  exact RankedDAG.resolve_extension S deps rank hRank hS
    (fun k p hp d hd => hClosed k ⟨p, hp⟩ hd)
    (merge S T) deps rank hRank (programsSupported_merge hS hT)
    (extends_merge_left S T) ν fallbackS fallbackM k p hk

/-- Compatibility retains the right peer's entries and hence all its closed computations. -/
theorem resolve_merge_right (hCompatible : Compatible S T)
    (hClosed : DependencyClosed deps T)
    (ν : ι → Operator n) (fallbackT fallbackM : κ → Operator n)
    {k : κ} {p : Program (κ ⊕ ι)} (hk : T k = some p) :
    RankedDAG.resolve T rank ν fallbackT k =
      RankedDAG.resolve (merge S T) rank ν fallbackM k := by
  exact RankedDAG.resolve_extension T deps rank hRank hT
    (fun k p hp d hd => hClosed k ⟨p, hp⟩ hd)
    (merge S T) deps rank hRank (programsSupported_merge hS hT)
    (extends_merge_right hCompatible) ν fallbackT fallbackM k p hk

/-- Compatible exchange converges on every retained computation, with arbitrary defaults. -/
theorem resolve_merge_converges (hCompatible : Compatible S T)
    (hClosedS : DependencyClosed deps S) (hClosedT : DependencyClosed deps T)
    (ν : ι → Operator n) (fallbackST fallbackTS : κ → Operator n)
    {k : κ} {p : Program (κ ⊕ ι)} (hk : merge S T k = some p) :
    RankedDAG.resolve (merge S T) rank ν fallbackST k =
      RankedDAG.resolve (merge T S) rank ν fallbackTS k := by
  rw [← (merge_comm_iff S T).2 hCompatible]
  exact RankedDAG.resolve_fallback_independent (merge S T) deps rank hRank
    (programsSupported_merge hS hT)
    (fun k p hp d hd => dependencyClosed_merge hClosedS hClosedT k ⟨p, hp⟩ hd)
    ν fallbackST fallbackTS k p hk

end Evaluation

end InfoGeometry.Canonical.OperatorContentNetwork.PeerStore
