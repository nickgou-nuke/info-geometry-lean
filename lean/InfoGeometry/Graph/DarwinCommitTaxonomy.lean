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

namespace CommitNode

/-- A commit record carries evidence for a category when its label list has
an entry with that category. This is a property of the Lean record schema;
it does not assert which labels the Python classifier emits for a real commit. -/
def hasCategory (node : CommitNode) (category : ChangeCategory) : Prop :=
  ∃ label, label ∈ node.changeLabels ∧ label.category = category

/-- The schema permits a single commit record to retain two distinct category
labels. This records multi-label capacity, not an output claim about the
heuristic classifier. -/
theorem schema_allows_bugfix_and_refactor (base : CommitNode) :
    let node := { base with changeLabels :=
      [⟨ChangeCategory.bugFix, 0, []⟩,
       ⟨ChangeCategory.refactorRestructure, 0, []⟩] }
    node.hasCategory ChangeCategory.bugFix ∧
      node.hasCategory ChangeCategory.refactorRestructure := by
  constructor
  · exact ⟨⟨ChangeCategory.bugFix, 0, []⟩, by simp, rfl⟩
  · exact ⟨⟨ChangeCategory.refactorRestructure, 0, []⟩, by simp, rfl⟩

end CommitNode

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
  /-- Position in the child's ordered Git parent list; absent on non-parent edges. -/
  parentSlot : Option Nat
  parentSlot_consistent :
    (edgeKind = CommitEdgeKind.parent_of) ↔ parentSlot.isSome

/-- Every recorded ancestry edge retains its ordered position among the
child's Git parents. -/
theorem CommitEdge.parent_of_has_parentSlot (edge : CommitEdge)
    (hParent : edge.edgeKind = CommitEdgeKind.parent_of) :
    ∃ slot, edge.parentSlot = some slot := by
  have hSome : edge.parentSlot.isSome := edge.parentSlot_consistent.mp hParent
  cases hSlot : edge.parentSlot with
  | none => simp [hSlot] at hSome
  | some slot => exact ⟨slot, rfl⟩

/-! The topological JSON exporter and the Arango commit graph are distinct
carriers. Keep the exporter's rank and compressed-link parent index separate
from the Arango `CommitNode`/`CommitEdge` records above. -/

/-- Commit reference together with the oldest-first rank emitted by
`phylogeny_export.py`. -/
structure RankedCommitRef where
  hash : String
  topologicalIndex : Nat

/-- A parent-to-child link in the exported DAG, retaining the child's ordered
parent index. -/
structure ExportedParentLink where
  src : RankedCommitRef
  dst : RankedCommitRef
  parentIndex : Nat

/-- One consecutive parent-to-child hop in a compressed export path. -/
structure ExpandedParentHop where
  parent : RankedCommitRef
  child : RankedCommitRef
  parentIndex : Nat

/-- A displayed link whose interior commits were suppressed by the exporter.
`chain` stores those hidden commits in parent-to-child order. -/
structure CompressedParentLink where
  src : RankedCommitRef
  dst : RankedCommitRef
  parentIndex : Nat
  chain : List RankedCommitRef

/-- Expand an ordered path into consecutive hops. The final hop retains the
original Git parent-list slot; intermediate hops use slot zero, as in the
exporter's expansion of a compressed link. -/
def expandParentPath : List RankedCommitRef → Nat → List ExpandedParentHop
  | [], _ => []
  | [_], _ => []
  | [parent, child], parentIndex => [⟨parent, child, parentIndex⟩]
  | parent :: child :: rest, parentIndex =>
      ⟨parent, child, 0⟩ :: expandParentPath (child :: rest) parentIndex

/-- Adjacent vertices in a ranked path occur in strict topological order. -/
def StrictlyRankedPath : List RankedCommitRef → Prop
  | [] => True
  | [_] => True
  | parent :: child :: rest =>
      parent.topologicalIndex < child.topologicalIndex ∧
        StrictlyRankedPath (child :: rest)

/-- Every hop created by expansion preserves the strict rank order of its
adjacent path vertices. -/
theorem expandParentPath_rank_increasing (path : List RankedCommitRef)
    (parentIndex : Nat) (hPath : StrictlyRankedPath path) :
    ∀ hop ∈ expandParentPath path parentIndex,
      hop.parent.topologicalIndex < hop.child.topologicalIndex := by
  induction path with
  | nil => simp [expandParentPath]
  | cons parent tail ih =>
      cases tail with
      | nil => simp [expandParentPath]
      | cons child rest =>
          cases rest with
          | nil =>
              simp only [StrictlyRankedPath] at hPath
              simp [expandParentPath, hPath]
          | cons next rest' =>
              rcases hPath with ⟨hHead, hTail⟩
              simp only [expandParentPath, List.mem_cons]
              intro hop hHop
              rcases hHop with rfl | hHop
              · exact hHead
              · exact ih hTail hop hHop

/-- The hop expansion of a path has one fewer hop than vertices. -/
theorem expandParentPath_length (path : List RankedCommitRef) (parentIndex : Nat) :
    (expandParentPath path parentIndex).length = path.length - 1 := by
  induction path with
  | nil => simp [expandParentPath]
  | cons parent tail ih =>
      cases tail with
      | nil => simp [expandParentPath]
      | cons child rest =>
          cases rest with
          | nil => simp [expandParentPath]
          | cons next rest' =>
              simp only [expandParentPath, List.length_cons]
              simp only [List.length_cons] at ih
              rw [ih]
              omega

/-- Every path with at least one hop ends in the hop carrying the supplied
parent-list slot. -/
theorem expandParentPath_last_parentIndex (path : List RankedCommitRef)
    (parentIndex : Nat) (hPath : 2 ≤ path.length) :
    (expandParentPath path parentIndex).getLast?.map ExpandedParentHop.parentIndex =
      some parentIndex := by
  induction path with
  | nil => simp at hPath
  | cons parent tail ih =>
      cases tail with
      | nil => simp at hPath
      | cons child rest =>
          cases rest with
          | nil => simp [expandParentPath]
          | cons next rest' =>
              have hTail : 2 ≤ (child :: next :: rest').length := by simp
              have hTailLast := ih hTail
              have hTailNe :
                  expandParentPath (child :: next :: rest') parentIndex ≠ [] := by
                intro hnil
                have hlen := expandParentPath_length (child :: next :: rest') parentIndex
                rw [hnil] at hlen
                simp only [List.length_cons, List.length_nil] at hlen
                omega
              rw [show expandParentPath (parent :: child :: next :: rest') parentIndex =
                [⟨parent, child, 0⟩] ++
                  expandParentPath (child :: next :: rest') parentIndex by rfl]
              rw [List.getLast?_append_of_ne_nil _ hTailNe]
              exact hTailLast

/-- The expanded path corresponding to one compressed link. -/
def expandCompressedParentLink (link : CompressedParentLink) :
    List ExpandedParentHop :=
  expandParentPath (link.src :: link.chain ++ [link.dst]) link.parentIndex

/-- Expanding a compressed link with `k` hidden commits yields `k + 1` hops. -/
theorem expandCompressedParentLink_length (link : CompressedParentLink) :
    (expandCompressedParentLink link).length = link.chain.length + 1 := by
  change (expandParentPath (link.src :: link.chain ++ [link.dst]) link.parentIndex).length = _
  rw [expandParentPath_length]
  simp only [List.length_cons, List.length_append, List.length_nil]
  omega

/-- Compression and re-expansion preserve the merge-parent slot on the final
edge, even when intermediate commits are hidden. -/
theorem expandCompressedParentLink_last_parentIndex (link : CompressedParentLink) :
    (expandCompressedParentLink link).getLast?.map ExpandedParentHop.parentIndex =
      some link.parentIndex := by
  apply expandParentPath_last_parentIndex
  simp only [List.length_cons, List.length_append, List.length_nil]
  omega

/-- A link with no hidden commits expands to its single original Git edge,
including the child's parent-list slot. -/
theorem expandCompressedParentLink_direct (link : CompressedParentLink)
    (hChain : link.chain = []) :
    expandCompressedParentLink link =
      [⟨link.src, link.dst, link.parentIndex⟩] := by
  rcases link with ⟨src, dst, parentIndex, chain⟩
  change chain = [] at hChain
  subst chain
  rfl

/-- One raw commit record in the exporter's uncompressed parent view. The
array order is the order supplied by Git (`parents[0]` is the first parent). -/
structure OrderedCommitParents where
  child : RankedCommitRef
  parents : Array RankedCommitRef

/-- Convert one indexed entry of a raw ordered parent list to the exporter's
parent-to-child edge convention. -/
def orderedParentLinkAt (record : OrderedCommitParents)
    (slot : Fin record.parents.size) : ExportedParentLink :=
  { src := record.parents[slot]
    dst := record.child
    parentIndex := slot.val }

/-- The uncompressed parent edges of one commit, enumerated in the exact
order of its raw Git parent array. -/
def orderedParentLinks (record : OrderedCommitParents) : List ExportedParentLink :=
  (List.finRange record.parents.size).map (orderedParentLinkAt record)

/-- A raw commit contributes exactly one ordered edge for each Git parent. -/
theorem orderedParentLinks_length (record : OrderedCommitParents) :
    (orderedParentLinks record).length = record.parents.size := by
  simp [orderedParentLinks]

/-- The edge at slot `i` occurs in the raw ordered edge list. -/
theorem orderedParentLinkAt_mem (record : OrderedCommitParents)
    (slot : Fin record.parents.size) :
    orderedParentLinkAt record slot ∈ orderedParentLinks record := by
  simp [orderedParentLinks]

/-- Every enumerated edge carries a parent slot within the raw array bounds. -/
theorem orderedParentLinks_parentIndex_lt (record : OrderedCommitParents)
    (edge : ExportedParentLink) (hEdge : edge ∈ orderedParentLinks record) :
    edge.parentIndex < record.parents.size := by
  rcases List.mem_map.mp hEdge with ⟨slot, _hSlot, hEq⟩
  rw [← hEq]
  change slot.val < record.parents.size
  exact slot.isLt

/-- Raw parent edges for a commit collection, retaining record order and each
record's Git parent-array order. -/
def orderedCommitParentLinks (records : List OrderedCommitParents) :
    List ExportedParentLink :=
  records.flatMap orderedParentLinks

/-- The raw edge count is exactly the sum of the parent counts, including
multiple-parent merge commits and repeated entries. -/
theorem orderedCommitParentLinks_length (records : List OrderedCommitParents) :
    (orderedCommitParentLinks records).length =
      (records.map fun record => record.parents.size).sum := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
      simp [orderedCommitParentLinks, orderedParentLinks_length]

/-- Every flattened raw edge retains provenance in a commit's ordered parent
array, with a slot bounded by that array's size. -/
theorem orderedCommitParentLinks_source_and_slot
    (records : List OrderedCommitParents) (edge : ExportedParentLink)
    (hEdge : edge ∈ orderedCommitParentLinks records) :
    ∃ record, record ∈ records ∧ edge ∈ orderedParentLinks record ∧
      edge.parentIndex < record.parents.size := by
  rcases List.mem_flatMap.mp hEdge with ⟨record, hRecord, hLocal⟩
  exact ⟨record, hRecord, hLocal,
    orderedParentLinks_parentIndex_lt record edge hLocal⟩

/-- Distinct parent-list positions remain distinct edges, even when a malformed
or unusual input repeats the same parent identifier. -/
theorem orderedParentLinkAt_injective (record : OrderedCommitParents) :
    Function.Injective (orderedParentLinkAt record) := by
  intro i j h
  have hIndex := congrArg ExportedParentLink.parentIndex h
  exact Fin.ext hIndex

/-- Parent-to-child reachability generated directly from raw ordered parent
arrays, before any display-graph compression. -/
def orderedCommitParentStep (records : List OrderedCommitParents)
    (parent child : RankedCommitRef) : Prop :=
  ∃ record, record ∈ records ∧ ∃ slot : Fin record.parents.size,
    (orderedParentLinkAt record slot).src = parent ∧
    (orderedParentLinkAt record slot).dst = child

/-- If every parent in the raw arrays has smaller exporter rank than its
child, the parent relation is well-founded and hence acyclic. -/
theorem orderedCommitParentStep_wellFounded
    (records : List OrderedCommitParents)
    (hRank : ∀ record ∈ records, ∀ slot : Fin record.parents.size,
      (record.parents[slot]).topologicalIndex < record.child.topologicalIndex) :
    WellFounded (orderedCommitParentStep records) := by
  apply (InvImage.wf (fun node : RankedCommitRef => node.topologicalIndex)
    (Nat.lt_wfRel).2).mono
  intro parent child hStep
  rcases hStep with ⟨record, hRecord, slot, hSrc, hDst⟩
  simp [orderedParentLinkAt] at hSrc hDst
  subst parent
  subst child
  exact hRank record hRecord slot

/-- Parent-to-child step in the ranked export view. -/
def exportedParentStep (links : List ExportedParentLink)
    (parent child : RankedCommitRef) : Prop :=
  ∃ link, link ∈ links ∧ link.dst = child ∧ link.src = parent

/-- The edge list and the endpoint reachability relation are two views of
the same raw ordered parent arrays; projection to endpoints forgets only the
parent slot, not an edge or its multiplicity. -/
theorem orderedParentStep_iff_exportedParentStep
    (records : List OrderedCommitParents) (parent child : RankedCommitRef) :
    orderedCommitParentStep records parent child ↔
      exportedParentStep (orderedCommitParentLinks records) parent child := by
  constructor
  · rintro ⟨record, hRecord, slot, hSrc, hDst⟩
    refine ⟨orderedParentLinkAt record slot, ?_, hDst, hSrc⟩
    exact List.mem_flatMap.mpr ⟨record, hRecord,
      orderedParentLinkAt_mem record slot⟩
  · rintro ⟨link, hLink, hDst, hSrc⟩
    rcases List.mem_flatMap.mp hLink with ⟨record, hRecord, hLocal⟩
    rcases List.mem_map.mp hLocal with ⟨slot, _hSlot, hEq⟩
    refine ⟨record, hRecord, slot, ?_, ?_⟩
    · rw [hEq]
      exact hSrc
    · rw [hEq]
      exact hDst

/-- Oldest-first ranks also certify acyclicity when ancestry is read from the
flattened exported edge list rather than directly from the parent arrays. -/
theorem orderedCommitParentLinks_wellFounded
    (records : List OrderedCommitParents)
    (hRank : ∀ record ∈ records, ∀ slot : Fin record.parents.size,
      (record.parents[slot]).topologicalIndex < record.child.topologicalIndex) :
    WellFounded (exportedParentStep (orderedCommitParentLinks records)) := by
  apply (orderedCommitParentStep_wellFounded records hRank).mono
  intro parent child hStep
  exact (orderedParentStep_iff_exportedParentStep records parent child).mpr hStep

/-- A topological rank certificate makes the recorded parent relation
well-founded. This is the algebraic form of the exporter's oldest-first
`index`; it is conditional on the imported edge list preserving that rank. -/
theorem exportedParentStep_wellFounded (links : List ExportedParentLink)
    (hRank : ∀ link ∈ links,
      link.src.topologicalIndex < link.dst.topologicalIndex) :
    WellFounded (exportedParentStep links) := by
  apply (InvImage.wf (fun node : RankedCommitRef => node.topologicalIndex)
    (Nat.lt_wfRel).2).mono
  intro parent child hStep
  rcases hStep with ⟨link, hMem, hDst, hSrc⟩
  subst child
  subst parent
  exact hRank link hMem

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
