/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Meta.RepositoryEvolutionArchetypes

namespace InfoGeometry.MetaCompiler.RepositoryEvolution.Tests

open InfoGeometry.MetaCompiler
open InfoGeometry.MetaCompiler.RepositoryEvolution
open InfoGeometry.Epistemology.EpistemicFunctor
open InfoGeometry.MetaCompiler.Integration
open InfoGeometry.Topology

def alignedObservation : RepositoryEvolutionObservation where
  sourceOntology := {
    schema := "info_geometry.refactoring_map.v1"
    gitHead := some "abc"
    pathCount := 1
    roleCounts := [("lean_source", 1)]
    worktreeDirty := false
    worktreeConsistentDuringScan := some true
  }
  phylogenyHead := some "abc"
  parentLinks := []
  weakTaxonomy := []
  compilerExport := none

def missingHeadsObservation : RepositoryEvolutionObservation where
  sourceOntology := {
    schema := "info_geometry.refactoring_map.v1"
    gitHead := none
    pathCount := 0
    roleCounts := []
    worktreeDirty := true
    worktreeConsistentDuringScan := none
  }
  phylogenyHead := none
  parentLinks := []
  weakTaxonomy := []
  compilerExport := none

def parentLinkExample : InfoGeometry.Graph.ExportedParentLink :=
  { src := ⟨"parent", 0⟩, dst := ⟨"child", 1⟩, parentIndex := 0 }

def labelledCommitExample : InfoGeometry.Graph.CommitNode where
  hash := "child"
  author := "example"
  date := "2026-01-01"
  pathChangeHash := "path-change"
  changeLabels := [⟨.bugFix, 50, [.pathHint]⟩]
  modulePaths := ["lean/InfoGeometry/Example.lean"]

def populatedObservation : RepositoryEvolutionObservation where
  sourceOntology := {
    schema := "info_geometry.refactoring_map.v1"
    gitHead := some "child"
    pathCount := 1
    roleCounts := [("lean_source", 1)]
    worktreeDirty := false
    worktreeConsistentDuringScan := some true
  }
  phylogenyHead := some "child"
  parentLinks := [parentLinkExample]
  weakTaxonomy := [labelledCommitExample]
  compilerExport := some {
    status := "source_olean_and_export_hashes_verified"
    sourceHash := some "source-digest"
    oleanHash := some "olean-digest"
    declarationCount := 1
    edgeCount := 0
  }

def registeredSourceInventoryCandidate : TypedArchetype Unit .candidate :=
  (sourcePathInventoryCandidate alignedObservation).typed

#register_archetype registeredSourceInventoryCandidate

def registeredGitParentCandidate : TypedArchetype Unit .candidate :=
  (gitParentLinkCandidate alignedObservation).typed

#register_archetype registeredGitParentCandidate

def registeredWeakTaxonomyCandidate : TypedArchetype Unit .candidate :=
  (weakTaxonomyLabelCandidate alignedObservation).typed

#register_archetype registeredWeakTaxonomyCandidate

def registeredCompilerExportCandidate : TypedArchetype Unit .candidate :=
  (compilerExportObservedCandidate alignedObservation).typed

#register_archetype registeredCompilerExportCandidate

def registeredHeadAlignmentCandidate : TypedArchetype Unit .candidate :=
  (headAlignmentCandidate alignedObservation).typed

#register_archetype registeredHeadAlignmentCandidate

def populatedGitParentCandidate : TypedArchetype Unit .candidate :=
  (gitParentLinkCandidate populatedObservation).typed

#register_archetype populatedGitParentCandidate

def populatedWeakTaxonomyCandidate : TypedArchetype Unit .candidate :=
  (weakTaxonomyLabelCandidate populatedObservation).typed

#register_archetype populatedWeakTaxonomyCandidate

def populatedCompilerExportCandidate : TypedArchetype Unit .candidate :=
  (compilerExportObservedCandidate populatedObservation).typed

#register_archetype populatedCompilerExportCandidate

example : alignedObservation.headsAligned := ⟨"abc", rfl, rfl⟩

example : ¬ RepositoryArchetypeStage.mk .gitParentPhylogeny .rawStreamToken ≤
    RepositoryArchetypeStage.mk .weakCommitTaxonomy .rawStreamToken := by
  apply not_le_of_different_lane
  decide

example : registeredSourceInventoryCandidate.claim () := by
  change 0 < 1
  decide

example : populatedGitParentCandidate.claim () := by
  change [parentLinkExample] ≠ []
  simp

example : populatedWeakTaxonomyCandidate.claim () := by
  refine ⟨labelledCommitExample, ?_, ?_⟩
  · simp [populatedObservation]
  · simp [labelledCommitExample]

example : populatedCompilerExportCandidate.claim () := by
  change (some _ : Option CompilerDeclarationExportObservation).isSome
  simp

example : labelledCommitExample.hasCategory InfoGeometry.Graph.ChangeCategory.bugFix := by
  exact ⟨⟨InfoGeometry.Graph.ChangeCategory.bugFix, 50, [.pathHint]⟩,
    by simp [labelledCommitExample], rfl⟩

example : ¬ registeredGitParentCandidate.claim () := by simp [registeredGitParentCandidate,
  gitParentLinkCandidate, alignedObservation]

example : ¬ registeredWeakTaxonomyCandidate.claim () := by simp [registeredWeakTaxonomyCandidate,
  weakTaxonomyLabelCandidate, alignedObservation]

example : ¬ registeredCompilerExportCandidate.claim () := by simp [registeredCompilerExportCandidate,
  compilerExportObservedCandidate, alignedObservation]

example : ¬ missingHeadsObservation.headsAligned := by
  rintro ⟨head, hSource, hPhylogeny⟩
  cases hSource

private def alignedCandidateNode : RepositoryArchetypeNode Unit :=
  ⟨.candidate, headAlignmentCandidate alignedObservation⟩

private def alignedProvedNode : RepositoryArchetypeNode Unit :=
  ⟨.proved, certifyHeadAlignment alignedObservation (by
    exact ⟨"abc", rfl, rfl⟩)⟩

private theorem candidate_to_proved_edge :
    (repositoryArchetypeDigraph Unit).edge
      alignedCandidateNode alignedProvedNode := by
  change alignedCandidateNode.2.stage ≤ alignedProvedNode.2.stage
  exact ⟨rfl, by decide⟩

example :
    alignedCandidateNode.2.lane = alignedProvedNode.2.lane ∧
      statusEvidenceStage .candidate ≤ statusEvidenceStage .proved := by
  let path : DirectedPath (repositoryArchetypeDigraph Unit)
      alignedCandidateNode alignedProvedNode :=
    .cons candidate_to_proved_edge
      (DirectedPath.refl (G := repositoryArchetypeDigraph Unit) alignedProvedNode)
  exact repositoryArchetype_path_order path

example :
    (certifyHeadAlignment alignedObservation (by exact ⟨"abc", rfl, rfl⟩)).typed.claim () := by
  exact (certifyHeadAlignment alignedObservation
    (by exact ⟨"abc", rfl, rfl⟩)).typed.discharge ()

end InfoGeometry.MetaCompiler.RepositoryEvolution.Tests
