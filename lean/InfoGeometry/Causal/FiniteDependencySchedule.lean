import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Preorder.Finite
import Mathlib.Order.UpperLower.Basic
import Mathlib.Tactic

namespace InfoGeometry.Causal.FiniteDependencySchedule

variable {Node : Type*} [PartialOrder Node] [DecidableEq Node]

def IsAdmissible (environment : Finset Node) (target : Node) : Prop :=
  ∀ prerequisite, prerequisite < target → prerequisite ∈ environment

def IsReady (environment : Finset Node) (target : Node) : Prop :=
  target ∉ environment ∧ IsAdmissible environment target

def ValidSchedule : Finset Node → List Node → Prop
  | _, [] => True
  | environment, target :: remaining =>
      IsReady environment target ∧ ValidSchedule (insert target environment) remaining

instance [Fintype Node] [DecidableLT Node] (environment : Finset Node) (target : Node) :
    Decidable (IsAdmissible environment target) :=
  inferInstanceAs (Decidable (∀ prerequisite, prerequisite < target → prerequisite ∈ environment))

instance [Fintype Node] [DecidableLT Node] (environment : Finset Node) (target : Node) :
    Decidable (IsReady environment target) :=
  inferInstanceAs (Decidable (target ∉ environment ∧ IsAdmissible environment target))

instance decidableValidSchedule [Fintype Node] [DecidableLT Node]
    (environment : Finset Node) (schedule : List Node) :
    Decidable (ValidSchedule environment schedule) :=
  match schedule with
  | [] => isTrue trivial
  | target :: remaining =>
      haveI := decidableValidSchedule (insert target environment) remaining
      inferInstanceAs
        (Decidable (IsReady environment target ∧ ValidSchedule (insert target environment) remaining))

omit [DecidableEq Node] in
theorem no_strict_dependency_cycle (target : Node) :
    ¬ Relation.TransGen ((· < ·) : Node → Node → Prop) target target := by
  rw [Relation.transGen_eq_self (r := ((· < ·) : Node → Node → Prop))
    (fun {_ _ _} first second => lt_trans first second)]
  exact lt_irrefl target

omit [DecidableEq Node] in
theorem admissible_mono {environment larger : Finset Node} {target : Node}
    (inclusion : environment ⊆ larger) (admissible : IsAdmissible environment target) :
    IsAdmissible larger target :=
  fun prerequisite precedes => inclusion (admissible prerequisite precedes)

theorem insert_isLowerSet {environment : Finset Node} {target : Node}
    (closed : IsLowerSet (environment : Set Node))
    (admissible : IsAdmissible environment target) :
    IsLowerSet (↑(insert target environment) : Set Node) := by
  intro later earlier precedes membership
  rcases Finset.mem_insert.mp membership with rfl | membership
  · rcases lt_or_eq_of_le precedes with strict | rfl
    · exact Finset.mem_insert_of_mem (admissible earlier strict)
    · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (closed precedes membership)

omit [DecidableEq Node] in
theorem distinct_ready_incomparable {environment : Finset Node} {first second : Node}
    (firstReady : IsReady environment first) (secondReady : IsReady environment second)
    (distinct : first ≠ second) : ¬ first ≤ second ∧ ¬ second ≤ first := by
  constructor
  · intro precedes
    exact firstReady.1 (secondReady.2 first (lt_of_le_of_ne precedes distinct))
  · intro precedes
    exact secondReady.1 (firstReady.2 second (lt_of_le_of_ne precedes distinct.symm))

theorem ready_after_distinct_insert {environment : Finset Node} {first second : Node}
    (ready : IsReady environment second) (distinct : second ≠ first) :
    IsReady (insert first environment) second := by
  refine ⟨?_, admissible_mono (Finset.subset_insert _ _) ready.2⟩
  simpa only [Finset.mem_insert, not_or] using And.intro distinct ready.1

theorem ready_pair_commutes {environment : Finset Node} {first second : Node}
    (firstReady : IsReady environment first) (secondReady : IsReady environment second)
    (distinct : first ≠ second) :
    ValidSchedule environment [first, second] ∧
      ValidSchedule environment [second, first] ∧
      insert second (insert first environment) = insert first (insert second environment) := by
  exact ⟨⟨firstReady, ready_after_distinct_insert secondReady distinct.symm, trivial⟩,
    ⟨secondReady, ready_after_distinct_insert firstReady distinct, trivial⟩,
    Finset.insert_comm _ _ _⟩

theorem exists_ready_in_remaining {environment targetSet : Finset Node}
    (closed : IsLowerSet (targetSet : Set Node))
    (remaining : (targetSet \ environment).Nonempty) :
    ∃ target ∈ targetSet \ environment, IsReady environment target := by
  obtain ⟨target, minimal⟩ := (targetSet \ environment).exists_minimal remaining
  refine ⟨target, minimal.1, (Finset.mem_sdiff.mp minimal.1).2, ?_⟩
  intro prerequisite precedes
  by_contra missing
  have inRemaining : prerequisite ∈ targetSet \ environment :=
    Finset.mem_sdiff.mpr ⟨closed precedes.le (Finset.mem_sdiff.mp minimal.1).1, missing⟩
  exact (not_le_of_gt precedes) (minimal.2 inRemaining precedes.le)

theorem validSchedule_fresh {environment : Finset Node} {schedule : List Node}
    (valid : ValidSchedule environment schedule) :
    ∀ target ∈ schedule, target ∉ environment := by
  induction schedule generalizing environment with
  | nil => simp
  | cons first remaining inductionHypothesis =>
    intro target membership
    rcases List.mem_cons.mp membership with rfl | membership
    · exact valid.1.1
    · exact fun present => inductionHypothesis valid.2 target membership
        (Finset.mem_insert_of_mem present)

theorem validSchedule_nodup {environment : Finset Node} {schedule : List Node}
    (valid : ValidSchedule environment schedule) : schedule.Nodup := by
  induction schedule generalizing environment with
  | nil => exact List.nodup_nil
  | cons first remaining inductionHypothesis =>
    refine List.nodup_cons.mpr ⟨?_, inductionHypothesis valid.2⟩
    intro repeated
    exact validSchedule_fresh valid.2 first repeated (Finset.mem_insert_self _ _)

theorem validSchedule_pairwise {environment : Finset Node} {schedule : List Node}
    (valid : ValidSchedule environment schedule) :
    schedule.Pairwise (fun earlier later => ¬ later ≤ earlier) := by
  induction schedule generalizing environment with
  | nil => exact List.Pairwise.nil
  | cons first remaining inductionHypothesis =>
    refine List.pairwise_cons.mpr ⟨?_, inductionHypothesis valid.2⟩
    intro later membership precedes
    rcases lt_or_eq_of_le precedes with strict | rfl
    · exact validSchedule_fresh valid.2 later membership
        (Finset.mem_insert_of_mem (valid.1.2 later strict))
    · exact validSchedule_fresh valid.2 later membership (Finset.mem_insert_self _ _)

theorem validSchedule_card {environment : Finset Node} {schedule : List Node}
    (valid : ValidSchedule environment schedule) :
    (environment ∪ schedule.toFinset).card = environment.card + schedule.length := by
  induction schedule generalizing environment with
  | nil => simp
  | cons first remaining inductionHypothesis =>
    have count := inductionHypothesis valid.2
    rw [Finset.card_insert_of_notMem valid.1.1] at count
    simpa [Finset.insert_union, Finset.union_insert, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using count

theorem validSchedule_isLowerSet {environment : Finset Node} {schedule : List Node}
    (closed : IsLowerSet (environment : Set Node))
    (valid : ValidSchedule environment schedule) :
    IsLowerSet (↑(environment ∪ schedule.toFinset) : Set Node) := by
  induction schedule generalizing environment with
  | nil => simpa using closed
  | cons first remaining inductionHypothesis =>
    simpa [Finset.insert_union, Finset.union_insert] using
      inductionHypothesis (insert_isLowerSet closed valid.1.2) valid.2

theorem exists_complete_schedule (environment targetSet : Finset Node)
    (inclusion : environment ⊆ targetSet)
    (closed : IsLowerSet (targetSet : Set Node)) :
    ∃ schedule, ValidSchedule environment schedule ∧
      environment ∪ schedule.toFinset = targetSet := by
  classical
  generalize sizeEquation : (targetSet \ environment).card = size
  induction size using Nat.strong_induction_on generalizing environment with
  | h size inductionHypothesis =>
    by_cases empty : targetSet \ environment = ∅
    · refine ⟨[], trivial, ?_⟩
      simpa using Finset.Subset.antisymm inclusion (Finset.sdiff_eq_empty_iff_subset.mp empty)
    · obtain ⟨target, membership, ready⟩ :=
        exists_ready_in_remaining closed (Finset.nonempty_iff_ne_empty.mpr empty)
      have targetIn : target ∈ targetSet := (Finset.mem_sdiff.mp membership).1
      have remainder : targetSet \ insert target environment =
          (targetSet \ environment).erase target := by
        ext node
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
        tauto
      have smaller : (targetSet \ insert target environment).card < size := by
        rw [remainder, ← sizeEquation]
        exact Finset.card_erase_lt_of_mem membership
      obtain ⟨schedule, valid, complete⟩ :=
        inductionHypothesis _ smaller (insert target environment)
          (Finset.insert_subset targetIn inclusion) rfl
      refine ⟨target :: schedule, ⟨ready, valid⟩, ?_⟩
      simpa [Finset.insert_union, Finset.union_insert] using complete

theorem exists_topological_schedule [Fintype Node] :
    ∃ schedule : List Node, ValidSchedule ∅ schedule ∧
      schedule.Nodup ∧ schedule.toFinset = Finset.univ := by
  obtain ⟨schedule, valid, complete⟩ := exists_complete_schedule
    (∅ : Finset Node) Finset.univ (Finset.empty_subset _) (by
      intro later earlier precedes membership
      exact Finset.mem_univ earlier)
  exact ⟨schedule, valid, validSchedule_nodup valid, by simpa using complete⟩

end InfoGeometry.Causal.FiniteDependencySchedule
