import DAG.Basic
import InfoGeometry.Meta.DeclarationDependencyBridge

namespace InfoGeometry.MetaCompiler.EnvironmentBridge

open DeclarationBridge
open InfoGeometry.Causal.FiniteDependencySchedule
open InfoGeometry.Causal.ProofCarryingSchedule
open InfoGeometry.Causal.CertifiedDependencyCompiler

/-- Dependency edges from checked declarations, using the repository extractor. -/
def DependsOn (environment : Lean.Environment) (prerequisite target : Lean.Name) : Prop :=
  ∃ info, environment.toKernelEnv.find? target = some info ∧
    ∃ kind, (prerequisite, kind) ∈ DAG.edgesFromConstantInfo info

def NamesClosed (environment : Lean.Environment) (names : Finset Lean.Name) : Prop :=
  ∀ target ∈ names, ∀ prerequisite, DependsOn environment prerequisite target →
    prerequisite ∈ names

def NamesPresent (environment : Lean.Environment) (names : Finset Lean.Name) : Prop :=
  ∀ target ∈ names, ∃ info, environment.toKernelEnv.find? target = some info

variable {Node : Type*} [PartialOrder Node] [DecidableEq Node]

/-- Imported declarations form an explicit closed baseline; new nodes are ordered. -/
structure EnvironmentCorrespondence (environment : Lean.Environment)
    (Node : Type*) [PartialOrder Node] where
  baseline : Finset Lean.Name
  declaration : Node ↪ Lean.Name
  baseline_closed : NamesClosed environment baseline
  baseline_present : NamesPresent environment baseline
  node_present : ∀ node, ∃ info,
    environment.toKernelEnv.find? (declaration node) = some info
  node_fresh : ∀ node, declaration node ∉ baseline
  resolve : ∀ target prerequisite, DependsOn environment prerequisite (declaration target) →
    prerequisite ∈ baseline ∨
      ∃ source, declaration source = prerequisite ∧ source < target

variable {environment : Lean.Environment}

def EnvironmentCorrespondence.toDependencyCorrespondence
    (bridge : EnvironmentCorrespondence environment Node) : DependencyCorrespondence Node where
  declaration := bridge.declaration
  depends prerequisite target :=
    DependsOn environment prerequisite target ∧ prerequisite ∉ bridge.baseline
  resolve := by
    intro target prerequisite dependency
    rcases bridge.resolve target prerequisite dependency.1 with imported | represented
    · exact False.elim (dependency.2 imported)
    · exact represented

def EnvironmentCorrespondence.availableNames
    (bridge : EnvironmentCorrespondence environment Node) (nodes : Finset Node) :
    Finset Lean.Name :=
  bridge.baseline ∪ nodes.image bridge.declaration

theorem EnvironmentCorrespondence.availableNames_present
    (bridge : EnvironmentCorrespondence environment Node) (nodes : Finset Node) :
    NamesPresent environment (bridge.availableNames nodes) := by
  intro target membership
  rcases Finset.mem_union.mp membership with imported | represented
  · exact bridge.baseline_present target imported
  · obtain ⟨node, _, rfl⟩ := Finset.mem_image.mp represented
    exact bridge.node_present node

theorem EnvironmentCorrespondence.availableNames_closed
    (bridge : EnvironmentCorrespondence environment Node) {nodes : Finset Node}
    (closed : bridge.toDependencyCorrespondence.Closed nodes) :
    NamesClosed environment (bridge.availableNames nodes) := by
  intro target membership prerequisite dependency
  rcases Finset.mem_union.mp membership with imported | represented
  · exact Finset.mem_union_left _ (bridge.baseline_closed target imported prerequisite dependency)
  · obtain ⟨node, present, rfl⟩ := Finset.mem_image.mp represented
    by_cases imported : prerequisite ∈ bridge.baseline
    · exact Finset.mem_union_left _ imported
    · obtain ⟨source, sourcePresent, sameName⟩ :=
        closed node present prerequisite ⟨dependency, imported⟩
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨source, sourcePresent, sameName⟩)

theorem EnvironmentCorrespondence.prefix_closed
    (bridge : EnvironmentCorrespondence environment Node)
    {initial : Finset Node} {schedule : List Node}
    (closed : IsLowerSet (initial : Set Node))
    (valid : ValidSchedule initial schedule) (count : Nat) :
    NamesClosed environment
      (bridge.availableNames (initial ∪ (schedule.take count).toFinset)) := by
  exact bridge.availableNames_closed
    (bridge.toDependencyCorrespondence.prefix_closed closed valid count)

theorem missing_dependency_prevents_closure
    {names : Finset Lean.Name} {prerequisite target : Lean.Name}
    (present : target ∈ names) (dependency : DependsOn environment prerequisite target)
    (missing : prerequisite ∉ names) : ¬ NamesClosed environment names := by
  intro closed
  exact missing (closed target present prerequisite dependency)

variable [Fintype Node] [DecidableLT Node]

theorem compiled_environment_closed
    (bridge : EnvironmentCorrespondence environment Node)
    {statement : Node → Prop} (rules : ProofRules statement)
    (initial completed : CertifiedState statement) (pending : List Node)
    (computed : compileCertified rules initial pending = some completed) :
    completed.environment = initial.environment ∪ pending.toFinset ∧
      NamesPresent environment (bridge.availableNames completed.environment) ∧
      NamesClosed environment (bridge.availableNames completed.environment) ∧
      HasProofs statement completed.environment := by
  obtain ⟨_, _, _, _, coverage⟩ := compileCertified_sound computed
  exact ⟨coverage, bridge.availableNames_present _,
    bridge.availableNames_closed
      (bridge.toDependencyCorrespondence.closed_of_isLowerSet completed.dependency_closed),
    completed.proofs⟩

end InfoGeometry.MetaCompiler.EnvironmentBridge
