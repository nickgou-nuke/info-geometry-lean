/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.CategoryTheory.Category.Preorder
import InfoGeometry.Graph.DarwinCommitTaxonomy
import InfoGeometry.Meta.EpistemicCompilerIntegration

/-!
# Repository-evolution evidence in the epistemic archetype pipeline

This module gives current-source inventory summaries, Git parent links, weak
commit labels, and compiler-export receipts separate typed fields. They are
observations, not Lean proofs. A typed archetype can be promoted only by
supplying a proof of its exact claim.

The archetype graph is ordered by workflow stage *within a fixed evidence
lane*. Directed paths and presented path homotopies therefore transport the
existing compilation order without identifying source organization, Git
ancestry, weak taxonomy, or compiler exports with one another.
-/

namespace InfoGeometry.MetaCompiler.RepositoryEvolution

open CategoryTheory
open InfoGeometry.Epistemology.EpistemicFunctor
open InfoGeometry.MetaCompiler.Integration
open InfoGeometry.Epistemology.ArchetypeHomotopyFramework
open InfoGeometry.Topology

/-- Summary fields emitted by the current-source map. Role names remain
strings so this Lean carrier does not silently freeze the Python classifier's
path-based vocabulary. -/
structure SourceOntologyObservation where
  schema : String
  gitHead : Option String
  pathCount : Nat
  roleCounts : List (String × Nat)
  worktreeDirty : Bool
  worktreeConsistentDuringScan : Option Bool
  deriving Repr, DecidableEq

/-- A summary of compiler-export provenance. Hashes and counts are navigation
and integrity metadata; this structure does not contain declaration proofs. -/
structure CompilerDeclarationExportObservation where
  status : String
  sourceHash : Option String
  oleanHash : Option String
  declarationCount : Nat
  edgeCount : Nat
  deriving Repr, DecidableEq

/-- Separate evidence carriers emitted by the repository-evolution pipeline.
Git parent links retain their ordered parent slot. Commit labels remain the
weak labels in the existing `CommitNode` schema. -/
structure RepositoryEvolutionObservation where
  sourceOntology : SourceOntologyObservation
  phylogenyHead : Option String
  parentLinks : List InfoGeometry.Graph.ExportedParentLink
  weakTaxonomy : List InfoGeometry.Graph.CommitNode
  compilerExport : Option CompilerDeclarationExportObservation

/-- The alignment claim requires a shared, present HEAD value. In particular,
`none = none` does not count as evidence that the snapshots are aligned. -/
def RepositoryEvolutionObservation.headsAligned
    (observation : RepositoryEvolutionObservation) : Prop :=
  ∃ head, observation.sourceOntology.gitHead = some head ∧
    observation.phylogenyHead = some head

/-- Metadata lane for one archetype. These tags describe provenance, not a
causal order or a mathematical theorem. -/
inductive EvidenceLane where
  | currentSourceOntology
  | gitParentPhylogeny
  | weakCommitTaxonomy
  | compilerDeclarationExport
  | crossLaneConsistency
  deriving DecidableEq, Repr

/-- A repository archetype couples the existing kernel-gated archetype with
an evidence-lane tag and provenance text. The latter two fields do not enter
its claim or supply its proof. -/
structure RepositoryTypedArchetype (Input : Type) (status : Status) where
  lane : EvidenceLane
  provenance : String
  typed : TypedArchetype Input status

namespace RepositoryTypedArchetype

/-- Promotion changes only the status-indexed proof evidence. Lane, provenance,
name, phase, and claim are preserved. -/
def promoteToProved {Input : Type} {status : Status}
    (archetype : RepositoryTypedArchetype Input status)
    (proof : ∀ input, archetype.typed.claim input) :
    RepositoryTypedArchetype Input .proved :=
  { lane := archetype.lane
    provenance := archetype.provenance
    typed := archetype.typed.promoteToProved proof }

/-- Discharge remains available only for a kernel-proved underlying archetype. -/
theorem discharge {Input : Type}
    (archetype : RepositoryTypedArchetype Input .proved) (input : Input) :
    archetype.typed.claim input :=
  archetype.typed.discharge input

end RepositoryTypedArchetype

/-- A source-map inventory claim about one supplied observation. A positive
path count is still only a claim about the record, not independent evidence
that a scan was complete or correct. -/
def sourcePathInventoryCandidate (observation : RepositoryEvolutionObservation) :
    RepositoryTypedArchetype Unit .candidate where
  lane := .currentSourceOntology
  provenance := "current-source map summary"
  typed := {
    name := `sourcePathInventoryCandidate
    phase := InfoGeometry.MetaCompiler.Phase.toNat
      InfoGeometry.MetaCompiler.Phase.primaMateriaIntake
    claim := fun _ => 0 < observation.sourceOntology.pathCount
    evidence := PUnit.unit
  }

/-- A Git-phylogeny claim that the supplied snapshot contains a parent link.
The link itself retains its ordered Git parent slot. -/
def gitParentLinkCandidate (observation : RepositoryEvolutionObservation) :
    RepositoryTypedArchetype Unit .candidate where
  lane := .gitParentPhylogeny
  provenance := "exported Git parent-link summary"
  typed := {
    name := `gitParentLinkCandidate
    phase := InfoGeometry.MetaCompiler.Phase.toNat
      InfoGeometry.MetaCompiler.Phase.primaMateriaIntake
    claim := fun _ => observation.parentLinks ≠ []
    evidence := PUnit.unit
  }

/-- A weak-taxonomy claim about whether the supplied commit records include
any labels. It does not assert label correctness or convert labels to parent
edges. -/
def weakTaxonomyLabelCandidate (observation : RepositoryEvolutionObservation) :
    RepositoryTypedArchetype Unit .candidate where
  lane := .weakCommitTaxonomy
  provenance := "weak commit labels in the Darwin taxonomy schema"
  typed := {
    name := `weakTaxonomyLabelCandidate
    phase := InfoGeometry.MetaCompiler.Phase.toNat
      InfoGeometry.MetaCompiler.Phase.primaMateriaIntake
    claim := fun _ => ∃ node ∈ observation.weakTaxonomy, node.changeLabels ≠ []
    evidence := PUnit.unit
  }

/-- A compiler-export claim recording only that a metadata summary was
supplied. Its hashes and counts are not theorem evidence. -/
def compilerExportObservedCandidate (observation : RepositoryEvolutionObservation) :
    RepositoryTypedArchetype Unit .candidate where
  lane := .compilerDeclarationExport
  provenance := "compiler declaration export receipt summary"
  typed := {
    name := `compilerExportObservedCandidate
    phase := InfoGeometry.MetaCompiler.Phase.toNat
      InfoGeometry.MetaCompiler.Phase.primaMateriaIntake
    claim := fun _ => observation.compilerExport.isSome
    evidence := PUnit.unit
  }

/-- A candidate claim for a particular source-map/phylogeny snapshot. The
source and Git observations themselves do not discharge this claim. -/
def headAlignmentCandidate (observation : RepositoryEvolutionObservation) :
    RepositoryTypedArchetype Unit .candidate where
  lane := .crossLaneConsistency
  provenance := "current-source map and Git phylogeny snapshot summaries"
  typed := {
    name := `headAlignmentCandidate
    phase := InfoGeometry.MetaCompiler.Phase.toNat
      InfoGeometry.MetaCompiler.Phase.typedMathematicalProjection
    claim := fun _ => observation.headsAligned
    evidence := PUnit.unit
  }

/-- A proof of the actual shared, present HEAD promotes precisely the
corresponding candidate claim; no source-map or Git record manufactures it. -/
def certifyHeadAlignment (observation : RepositoryEvolutionObservation)
    (alignment : observation.headsAligned) :
    RepositoryTypedArchetype Unit .proved :=
  (headAlignmentCandidate observation).promoteToProved (fun _ => alignment)

@[simp] theorem certifyHeadAlignment_preserves_lane
    (observation : RepositoryEvolutionObservation)
    (alignment : observation.headsAligned) :
    (certifyHeadAlignment observation alignment).lane = .crossLaneConsistency := rfl

@[simp] theorem certifyHeadAlignment_preserves_claim
    (observation : RepositoryEvolutionObservation)
    (alignment : observation.headsAligned) :
    (certifyHeadAlignment observation alignment).typed.claim =
      (headAlignmentCandidate observation).typed.claim := rfl

/-! ## Lane-preserving workflow poset and directed paths -/

/-- A workflow stage tagged by its repository-evidence lane. The order permits
workflow progression only within the same lane. -/
structure RepositoryArchetypeStage where
  lane : EvidenceLane
  workflow : CompilationArchetype
  deriving DecidableEq

instance : PartialOrder RepositoryArchetypeStage where
  le a b := a.lane = b.lane ∧ a.workflow ≤ b.workflow
  le_refl a := ⟨rfl, le_rfl⟩
  le_trans := by
    intro a b c hab hbc
    exact ⟨hab.1.trans hbc.1, le_trans hab.2 hbc.2⟩
  le_antisymm a b hab hba := by
    cases a with
    | mk laneA stageA =>
      cases b with
      | mk laneB stageB =>
        have hLane : laneA = laneB := hab.1
        subst laneB
        have hStage : stageA = stageB := le_antisymm hab.2 hba.2
        subst stageB
        rfl

instance : DecidableLE RepositoryArchetypeStage := fun a b =>
  inferInstanceAs (Decidable (a.lane = b.lane ∧ a.workflow ≤ b.workflow))

theorem not_le_of_different_lane {a b : RepositoryArchetypeStage}
    (hLane : a.lane ≠ b.lane) : ¬ a ≤ b := by
  intro hab
  exact hLane hab.1

/-- Candidate/validated items remain at raw intake; only `.proved` items enter
the existing proof-evidence branch of the compilation poset. -/
def RepositoryTypedArchetype.stage {Input : Type} {status : Status}
    (archetype : RepositoryTypedArchetype Input status) :
    RepositoryArchetypeStage :=
  ⟨archetype.lane, statusEvidenceStage status⟩

/-- Nodes in the repository-archetype graph retain their status index. -/
abbrev RepositoryArchetypeNode (Input : Type) :=
  Σ status : Status, RepositoryTypedArchetype Input status

/-- Edges are precisely monotone workflow transitions within one evidence
lane. They do not assert that Git ancestry, weak labels, or source roles imply
one another. -/
def repositoryArchetypeDigraph (Input : Type) : ChiralDigraph where
  Vertex := RepositoryArchetypeNode Input
  edge := fun source target => source.2.stage ≤ target.2.stage
  edge_decidable := fun _ _ => inferInstance
  sector := fun _ => .left
  allowedTransition := fun _ _ => True
  transition_decidable := fun _ _ => isTrue trivial
  edge_allowed := by intro source target _; trivial

/-- The graph-to-preorder morphism into the existing lane-indexed compiler
poset. Its edge proof is exactly the edge relation of the source graph. -/
def repositoryArchetypeStageHom {Input : Type} :
    ChiralDigraphHom (repositoryArchetypeDigraph Input)
      (InfoGeometry.Epistemology.ArchetypeHomotopyFramework.prerequisiteGraph
        RepositoryArchetypeStage) :=
  InfoGeometry.Epistemology.ArchetypeHomotopyFramework.prerequisiteGraphHom
    (fun node => node.2.stage) (fun edge => edge)

/-- A directed path preserves the evidence lane and advances only in the
existing compilation order. -/
theorem repositoryArchetype_path_order {Input : Type}
    {source target : RepositoryArchetypeNode Input}
    (path : DirectedPath (repositoryArchetypeDigraph Input) source target) :
    source.2.lane = target.2.lane ∧
      statusEvidenceStage source.1 ≤ statusEvidenceStage target.1 := by
  have h := InfoGeometry.Epistemology.ArchetypeHomotopyFramework.mapPath_le
    (repositoryArchetypeStageHom (Input := Input)) path
  exact h

/-- A declared directed path presentation acts on the repository's
lane-preserving workflow poset through the existing homotopy-category owner. -/
def repositoryPresentedPathFunctor {Input : Type}
    {P : DirectedPathPresentation (repositoryArchetypeDigraph Input)} :
    PresentedPathCategory P ⥤ RepositoryArchetypeStage :=
  InfoGeometry.Epistemology.ArchetypeHomotopyFramework.presentedPathFunctor
    (repositoryArchetypeStageHom (Input := Input))

end InfoGeometry.MetaCompiler.RepositoryEvolution
