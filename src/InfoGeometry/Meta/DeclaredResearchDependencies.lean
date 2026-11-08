/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Causal.CertifiedDependencyCompiler
import InfoGeometry.OperatorAlgebra.PeirceSpine.Tetraktys

namespace InfoGeometry.MetaCompiler.DeclaredResearchGraph

open InfoGeometry.Causal.FiniteDependencySchedule
open InfoGeometry.Causal.FiniteDependencyCompiler
open InfoGeometry.Causal.ProofCarryingSchedule
open InfoGeometry.Causal.CertifiedDependencyCompiler

inductive RepoArchetype
  | qedTwoPoint
  | matheronCovariogram
  | fisherRaoIsometry
  | carnotInformation
  | souriauKMS
  | metaEpistemicCompiler
  deriving DecidableEq, Repr

instance : Fintype RepoArchetype where
  elems := {.qedTwoPoint, .matheronCovariogram, .fisherRaoIsometry,
    .carnotInformation, .souriauKMS, .metaEpistemicCompiler}
  complete x := by
    cases x <;> decide

open RepoArchetype

def prerequisites : RepoArchetype → Finset RepoArchetype
  | qedTwoPoint => {qedTwoPoint}
  | matheronCovariogram => {qedTwoPoint, matheronCovariogram}
  | fisherRaoIsometry => {qedTwoPoint, matheronCovariogram, fisherRaoIsometry}
  | carnotInformation =>
      {qedTwoPoint, matheronCovariogram, fisherRaoIsometry, carnotInformation}
  | souriauKMS => {qedTwoPoint, matheronCovariogram, fisherRaoIsometry, souriauKMS}
  | metaEpistemicCompiler =>
      {qedTwoPoint, matheronCovariogram, fisherRaoIsometry,
        carnotInformation, souriauKMS, metaEpistemicCompiler}

instance : PartialOrder RepoArchetype where
  le earlier later := earlier ∈ prerequisites later
  le_refl target := by cases target <;> decide
  le_trans := by
    intro earlier middle later
    cases earlier <;> cases middle <;> cases later <;> decide
  le_antisymm := by
    intro earlier later
    cases earlier <;> cases later <;> decide

instance : DecidableLE RepoArchetype := fun earlier later =>
  inferInstanceAs (Decidable (earlier ∈ prerequisites later))

instance : DecidableLT RepoArchetype := fun earlier later =>
  decidable_of_iff (earlier ≤ later ∧ ¬ later ≤ earlier) lt_iff_le_not_ge.symm

theorem prerequisite_iff_le (earlier later : RepoArchetype) :
    earlier ∈ prerequisites later ↔ earlier ≤ later := Iff.rfl

theorem admissible_iff_prerequisites
    (environment : Finset RepoArchetype) (target : RepoArchetype) :
    IsAdmissible environment target ↔ (prerequisites target \ {target}) ⊆ environment := by
  constructor
  · intro admissible earlier membership
    rcases Finset.mem_sdiff.mp membership with ⟨ancestor, different⟩
    have distinct : earlier ≠ target := by simpa using different
    exact admissible earlier (lt_of_le_of_ne ancestor distinct)
  · intro included earlier precedes
    apply included
    exact Finset.mem_sdiff.mpr ⟨precedes.le, by simpa using ne_of_lt precedes⟩

theorem dependency_relation_acyclic (target : RepoArchetype) :
    ¬ Relation.TransGen ((· < ·) : RepoArchetype → RepoArchetype → Prop) target target :=
  no_strict_dependency_cycle target

theorem carnot_and_souriau_incomparable :
    ¬ carnotInformation ≤ souriauKMS ∧ ¬ souriauKMS ≤ carnotInformation := by decide

theorem qed_is_universal_ancestor (target : RepoArchetype) :
    qedTwoPoint ≤ target := by cases target <;> decide

theorem qed_admissible_in_empty_env : IsAdmissible ∅ qedTwoPoint := by decide

def foundation : Finset RepoArchetype :=
  {qedTwoPoint, matheronCovariogram, fisherRaoIsometry}

theorem ready_after_foundation_iff (target : RepoArchetype) :
    IsReady foundation target ↔ target = carnotInformation ∨ target = souriauKMS := by
  cases target <;> decide

theorem capstone_admissible_iff_branches (environment : Finset RepoArchetype)
    (foundation_present : foundation ⊆ environment) :
    IsAdmissible environment metaEpistemicCompiler ↔
      carnotInformation ∈ environment ∧ souriauKMS ∈ environment := by
  rw [admissible_iff_prerequisites]
  constructor
  · intro included
    exact ⟨included (by decide), included (by decide)⟩
  · rintro ⟨carnot_present, souriau_present⟩ target membership
    cases target with
    | qedTwoPoint => exact foundation_present (by decide)
    | matheronCovariogram => exact foundation_present (by decide)
    | fisherRaoIsometry => exact foundation_present (by decide)
    | carnotInformation => exact carnot_present
    | souriauKMS => exact souriau_present
    | metaEpistemicCompiler => simp at membership

theorem meta_compiler_admissible_when_branches_closed :
    IsAdmissible {qedTwoPoint, matheronCovariogram, fisherRaoIsometry,
      carnotInformation, souriauKMS} metaEpistemicCompiler := by decide

theorem premature_compilation_rejected :
    ¬ IsAdmissible {qedTwoPoint, matheronCovariogram, fisherRaoIsometry,
      carnotInformation} metaEpistemicCompiler := by decide

theorem declared_branch_insertions_commute :
    ValidSchedule foundation [carnotInformation, souriauKMS] ∧
      ValidSchedule foundation [souriauKMS, carnotInformation] ∧
      insert souriauKMS (insert carnotInformation foundation) =
        insert carnotInformation (insert souriauKMS foundation) :=
  ready_pair_commutes (by decide) (by decide) (by decide)

def schedule : List RepoArchetype :=
  [qedTwoPoint, matheronCovariogram, fisherRaoIsometry,
    carnotInformation, souriauKMS, metaEpistemicCompiler]

def alternateSchedule : List RepoArchetype :=
  [qedTwoPoint, matheronCovariogram, fisherRaoIsometry,
    souriauKMS, carnotInformation, metaEpistemicCompiler]

theorem schedules_valid :
    ValidSchedule ∅ schedule ∧ ValidSchedule ∅ alternateSchedule := by decide

theorem schedules_complete :
    schedule.toFinset = Finset.univ ∧ alternateSchedule.toFinset = Finset.univ := by decide

theorem reversed_schedule_compiles :
    compile ∅ schedule.reverse = some alternateSchedule := by decide

theorem schedule_compilation_fixed : compile ∅ schedule = some schedule :=
  compile_of_valid schedules_valid.1

theorem missing_branch_compilation_fails :
    compile ∅ [qedTwoPoint, matheronCovariogram, fisherRaoIsometry,
      carnotInformation, metaEpistemicCompiler] = none := by decide

def emptyCertifiedState (statement : RepoArchetype → Prop) : CertifiedState statement where
  environment := ∅
  dependency_closed := by
    intro later earlier precedes membership
    exact False.elim (Finset.notMem_empty _ membership)
  proofs := by
    intro target membership
    exact False.elim (Finset.notMem_empty _ membership)

theorem declared_compilation_with_evidence (statement : RepoArchetype → Prop)
    (rules : ProofRules statement) :
    ∃ completed, compileCertified rules (emptyCertifiedState statement) schedule.reverse =
        some completed ∧ completed.environment = Finset.univ ∧ ∀ target, statement target := by
  obtain ⟨completed, compiled, complete, proofs⟩ :=
    compileCertified_proves_target rules (emptyCertifiedState statement) Finset.univ
      schedule.reverse (Finset.empty_subset _) (by
        intro later earlier precedes membership
        exact Finset.mem_univ earlier) (by decide) (by
        change schedule.reverse.toFinset = Finset.univ \ ∅
        decide)
  exact ⟨completed, compiled, complete, fun target => proofs target (Finset.mem_univ target)⟩

theorem readiness_does_not_supply_proof :
    IsReady (∅ : Finset RepoArchetype) qedTwoPoint ∧
      ¬ HasProofs (fun _ : RepoArchetype => (0 : ℕ) = 1) {qedTwoPoint} := by
  refine ⟨by decide, ?_⟩
  intro evidence
  exact Nat.zero_ne_one (evidence qedTwoPoint (by simp))

theorem successful_scheduling_does_not_supply_proofs :
    compile ∅ schedule = some schedule ∧
      ¬ HasProofs (fun _ : RepoArchetype => (0 : ℕ) = 1) schedule.toFinset := by
  refine ⟨schedule_compilation_fixed, ?_⟩
  intro evidence
  exact Nat.zero_ne_one (evidence qedTwoPoint (by decide))

section NonCommutativeOperatorRealization

open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {B : Type*} [Ring B]

def repoArchetypeOperatorWitness (P A C : B) : RepoArchetype → B
  | .qedTwoPoint => P
  | .matheronCovariogram => conePlus P A
  | .fisherRaoIsometry => coneMinus P C
  | .carnotInformation => genPhi P A C
  | .souriauKMS => genSig P A C
  | .metaEpistemicCompiler => genV P A C

theorem declared_research_dependencies_operator_tetraktys
    {P : B} (hP : P * P = P) (A C : B) :
    repoArchetypeOperatorWitness P A C .qedTwoPoint *
      repoArchetypeOperatorWitness P A C .qedTwoPoint =
      repoArchetypeOperatorWitness P A C .qedTwoPoint ∧
    (repoArchetypeOperatorWitness P A C .matheronCovariogram) ^ 2 = 0 ∧
    (repoArchetypeOperatorWitness P A C .fisherRaoIsometry) ^ 2 = 0 ∧
    (repoArchetypeOperatorWitness P A C .carnotInformation) ^ 2 =
      repoArchetypeOperatorWitness P A C .metaEpistemicCompiler ∧
    (repoArchetypeOperatorWitness P A C .souriauKMS) ^ 2 -
      (repoArchetypeOperatorWitness P A C .metaEpistemicCompiler) ^ 2 = 0 := by
  dsimp only [repoArchetypeOperatorWitness]
  rcases archetype_A3_nilpotent_cones_and_tetraktys_table (P := P) hP A C with
    ⟨_, _, hPhiSq, _, _, _, _, _, _, _, hSigmaSq, _, _, _⟩
  refine ⟨hP, ?_, ?_, ?_, ?_⟩
  · simpa [pow_two] using
      (archetype_A3_nilpotent_cones_and_tetraktys_table (P := P) hP A C).1
  · simpa [pow_two] using
      (archetype_A3_nilpotent_cones_and_tetraktys_table (P := P) hP A C).2.1
  · simpa [pow_two] using hPhiSq
  · simpa [pow_two] using sub_eq_zero.mpr hSigmaSq

end NonCommutativeOperatorRealization

end InfoGeometry.MetaCompiler.DeclaredResearchGraph
