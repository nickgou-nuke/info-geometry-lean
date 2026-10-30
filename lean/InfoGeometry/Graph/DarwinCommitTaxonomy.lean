/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic

/-!
# Darwin Commit History and Change Facets

Formal data types for exact Git parent edges and non-hierarchical weak change
labels. A change label is a classification observation, not an ancestor,
species, declaration identity, or proof of mathematical equivalence.
-/

namespace InfoGeometry.Graph

/-! Stable category identifiers shared with `evolution_taxonomy.py`. -/
inductive ChangeCategory where
  | revertBackout
  | securityHardening
  | bugFix
  | testEvolution
  | documentationDeveloperUx
  | refactorRestructure
  | performanceOptimization
  | buildToolingCi
  | dependencyVendorSync
  | releaseVersioningMeta
  | localizationPortability
  | featureIntroduction
deriving Repr, DecidableEq

namespace ChangeCategory

/-- Stable machine-readable identifier used by the weak-label producer. -/
def id : ChangeCategory → String
  | revertBackout => "revertBackout"
  | securityHardening => "securityHardening"
  | bugFix => "bugFix"
  | testEvolution => "testEvolution"
  | documentationDeveloperUx => "documentationDeveloperUx"
  | refactorRestructure => "refactorRestructure"
  | performanceOptimization => "performanceOptimization"
  | buildToolingCi => "buildToolingCi"
  | dependencyVendorSync => "dependencyVendorSync"
  | releaseVersioningMeta => "releaseVersioningMeta"
  | localizationPortability => "localizationPortability"
  | featureIntroduction => "featureIntroduction"

/-- Distinct change facets have distinct serialized category identifiers. -/
theorem id_injective : Function.Injective id := by
  intro a b h
  cases a <;> cases b <;> simp_all [id]

end ChangeCategory

/-- Provenance class for one weak category match. -/
inductive ChangeLabelEvidence where
  | subjectBodyRule
  | pathHint
  | defaultNoRuleMatch
  | other
deriving Repr, DecidableEq

/-- One non-hierarchical, evidence-bearing change facet. -/
structure CommitChangeLabel where
  category : ChangeCategory
  ruleWeightPercent : Fin 101
  evidenceKinds : List ChangeLabelEvidence
deriving Repr, DecidableEq

/-- A commit node in the evolutionary Arango graph. -/
structure CommitNode where
  hash : String
  author : String
  date : String
  pathChangeHash : String
  changeLabels : List CommitChangeLabel
  modulePaths : List String

/-- A typed edge in the evolutionary commit graph. -/
inductive CommitEdgeKind where
  | parent_of
  | touches
deriving Repr, DecidableEq

/-- Edge between commits; for `parent_of`, `src` is the parent and `dst` its child. -/
structure CommitEdge where
  src : CommitNode
  dst : CommitNode
  edgeKind : CommitEdgeKind

/-- Bridge edge from a commit to a declaration DNA node. -/
structure CommitDeclEdge where
  commit : CommitNode
  path : String
  edgeKind : CommitEdgeKind := CommitEdgeKind.touches

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
