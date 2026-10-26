/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic

/-!
# Darwin Commit Taxonomy

Formal types for the evolutionary commit graph and its link to the
repository's declaration DNA (`decls`/`edges`).

This module does not prove that evolution is optimal; it models the
structure claimed by `tools/infra/darwin_commit_graph.py` and
`tools/infra/darwin_commit_taxonomy.py`, keeping the Arango schema and
the Lean schema aligned.
-/

namespace InfoGeometry.Graph

/-- Rank of an evolutionary commit node. -/
inductive TaxonRank where
  | domain
  | kingdom
  | phylum
  | classLevel
  | order
  | family
  | genus
  | species
deriving Repr, DecidableEq

namespace TaxonRank

/-- Taxonomic rank order for monotonicity reasoning. -/
def rankIndex : TaxonRank → ℕ
  | domain => 0
  | kingdom => 1
  | phylum => 2
  | classLevel => 3
  | order => 4
  | family => 5
  | genus => 6
  | species => 7

/-- Rank order is injective. -/
theorem rankIndex_injective (a b : TaxonRank) : rankIndex a = rankIndex b → a = b := by
  intro h
  cases a <;> cases b <;>
  simp_all [rankIndex]

/-- Any two ranks are comparable by `rankIndex`. -/
theorem rankIndex_total (a b : TaxonRank) :
  rankIndex a ≤ rankIndex b ∨ rankIndex b ≤ rankIndex a := by
  exact Nat.le_total (rankIndex a) (rankIndex b)

end TaxonRank

/-- A commit node in the evolutionary Arango graph. -/
structure CommitNode where
  hash : String
  author : String
  date : String
  taxonRank : TaxonRank
  diffHash : String
  leanVerified : Bool
  modulePaths : List String

/-- A typed edge in the evolutionary commit graph. -/
inductive CommitEdgeKind where
  | parent_of
  | touches
deriving Repr, DecidableEq

/-- Edge between two commit nodes. -/
structure CommitEdge where
  src : CommitNode
  dst : CommitNode
  edgeKind : CommitEdgeKind

/-- Bridge edge from a commit to a declaration DNA node. -/
structure CommitDeclEdge where
  commit : CommitNode
  path : String
  edgeKind : CommitEdgeKind := CommitEdgeKind.touches

/-- Any two commit ranks are comparable by `rankIndex`. -/
theorem commit_rank_total (c parent : CommitNode) :
  TaxonRank.rankIndex parent.taxonRank ≤ TaxonRank.rankIndex c.taxonRank ∨
    TaxonRank.rankIndex c.taxonRank ≤ TaxonRank.rankIndex parent.taxonRank := by
  exact Nat.le_total (TaxonRank.rankIndex parent.taxonRank) (TaxonRank.rankIndex c.taxonRank)

/-- Distinct commits can share a non-empty module path; this does not imply theorem equivalence. -/
theorem shared_path_not_equivalence {a b : CommitNode} :
  a.modulePaths = b.modulePaths →
    a.hash ≠ b.hash →
      a.modulePaths ≠ [] →
        ∃ path, path ∈ a.modulePaths ∧ path ∈ b.modulePaths := by
  intro h_eq h_hash h_nonempty
  have h_ne : b.modulePaths ≠ [] := by
    rw [← h_eq]
    exact h_nonempty
  cases h_list : b.modulePaths with
  | nil =>
    exfalso
    have h_a_eq_nil : a.modulePaths = [] := by
      rw [h_eq]
      exact h_list
    exact h_nonempty h_a_eq_nil
  | cons path paths =>
    have h_cons : b.modulePaths = path :: paths := h_list
    use path
    constructor
    · -- path ∈ a.modulePaths
      have h_a_cons : a.modulePaths = path :: paths := by
        rw [h_eq]
        exact h_cons
      rw [h_a_cons]
      simp
    · -- path ∈ b.modulePaths
      simp

end InfoGeometry.Graph
